/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Gereon Kremer, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Wrapper for CaDiCaL SAT Solver.
 *
 * Implementation of the CaDiCaL SAT solver for cvc5 (bit-vectors).
 */

#include "prop/cadical.h"

#include "base/check.h"
#include "prop/theory_proxy.h"
#include "util/resource_manager.h"
#include "util/statistics_registry.h"

namespace cvc5::internal {
namespace prop {

/* -------------------------------------------------------------------------- */

using CadicalLit = int;
using CadicalVar = int;

// helper functions
namespace {

SatValue toSatValue(int result)
{
  if (result == 10) return SAT_VALUE_TRUE;
  if (result == 20) return SAT_VALUE_FALSE;
  Assert(result == 0);
  return SAT_VALUE_UNKNOWN;
}

// Note: CaDiCaL returns lit/-lit for true/false. Older versions returned 1/-1.
SatValue toSatValueLit(int value)
{
  if (value > 0) return SAT_VALUE_TRUE;
  Assert(value < 0);
  return SAT_VALUE_FALSE;
}

CadicalLit toCadicalLit(const SatLiteral lit)
{
  return lit.isNegated() ? -lit.getSatVariable() : lit.getSatVariable();
}

SatLiteral toSatLiteral(CadicalLit lit)
{
  return SatLiteral(std::abs(lit), lit < 0);
}

CadicalVar toCadicalVar(SatVariable var) { return var; }

}  // namespace helper functions

class CadicalPropagator : public CaDiCaL::ExternalPropagator
{
 public:
  CadicalPropagator(prop::TheoryProxy* proxy,
                    context::Context* context,
                    CaDiCaL::Solver& solver)
      : d_proxy(proxy), d_context(*context), d_solver(solver)
  {
    d_var_info.emplace_back();  // 0: Not used
  }

  /** Store current assignment, notify theories of assigned theory literals. */
  void notify_assignment(int lit, bool is_fixed) override
  {
    if (d_found_solution)
    {
      return;
    }

    SatLiteral slit = toSatLiteral(lit);
    SatVariable var = slit.getSatVariable();
    Assert(var < d_var_info.size());

    auto& info = d_var_info[var];

    // Only consider active variables
    if (!info.is_active)
    {
      return;
    }

    bool is_decision = d_solver.is_decision(lit);

    Trace("cadical::propagator")
        << "notif::assignment: [" << (is_decision ? "d" : "p") << "] " << slit
        << " (fixed: " << is_fixed << ", level: " << d_decisions.size() << ")"
        << std::endl;

    // Save decision variables
    if (is_decision)
    {
      d_decisions.back() = slit;
    }

    Assert(info.assignment == 0 || info.assignment == lit);
    Assert(info.assignment == 0 || is_fixed);
    if (is_fixed)
    {
      Assert(!info.is_fixed);
      info.is_fixed = true;
    }
    // Only notify theory proxy if variable was assigned a new value, not if it
    // got fixed after assignment already happend.
    if (info.assignment == 0)
    {
      info.assignment = lit;
      d_assignments.push_back(slit);
      if (info.is_theory_atom)
      {
        Trace("cadical::propagator") << "enqueue: " << slit << std::endl;
        Trace("cadical::propagator") << "node:    " << d_proxy->getNode(slit) << std::endl;
        d_proxy->enqueueTheoryLiteral(slit);
      }
    }
  }

  /** Push new decision level. */
  void notify_new_decision_level() override
  {
    d_context.push();
    d_assignment_control.push_back(d_assignments.size());
    d_decisions.emplace_back();
    Trace("cadical::propagator")
        << "notif::decision: new level " << d_decisions.size() << std::endl;
  }

  /** Backtrack to given level. */
  void notify_backtrack(size_t level) override
  {
    Trace("cadical::propagator") << "notif::backtrack: " << level << std::endl;

    // CaDiCaL may notify us about backtracks of decisions that we were not
    // notified about. We can safely ignore them.
    if (d_decisions.size() <= level)
    {
      Assert(d_decisions.size() == 0);
      return;
    }
    d_found_solution = false;

    Assert(d_decisions.size() > level);
    Assert(d_context.getLevel() > level);
    for (size_t cur_level = d_decisions.size(); cur_level > level; --cur_level)
    {
      d_context.pop();
      d_decisions.pop_back();
    }

    // Backtrack assignments, resend fixed theory literals that got backtracked
    Assert(!d_assignment_control.empty());
    size_t pop_to = d_assignment_control[level];
    d_assignment_control.resize(level);

    std::vector<SatLiteral> reenqueue_fixed;
    while (pop_to < d_assignments.size())
    {
      SatLiteral lit = d_assignments.back();
      d_assignments.pop_back();
      SatVariable var = lit.getSatVariable();
      auto& info = d_var_info[var];
      if (info.is_fixed)
      {
        if (info.is_theory_atom)
        {
          Assert(info.is_active);
          reenqueue_fixed.push_back(lit);
        }
      }
      else
      {
        Trace("cadical::propagator") << "unassign: " << var << std::endl;
        info.assignment = 0;
      }
    }

    d_proxy->notifyBacktrack(level);
    d_propagations.clear();

    // Re-enqueue fixed theory literals that got removed.
    for (auto it = reenqueue_fixed.rbegin(), end = reenqueue_fixed.rend();
         it != end;
         ++it)
    {
      SatLiteral lit = *it;
      Trace("cadical::propagator") << "re-enqueue: " << lit << std::endl;
      d_proxy->enqueueTheoryLiteral(lit);
      d_assignments.push_back(lit);
    }
    Trace("cadical::propagator") << "notif::backtrack end" << std::endl;
  }

  /**
   * Check whether current model is consistent with the theories.
   *
   * Perform a full effort check and theory propgations.
   */
  bool cb_check_found_model(const std::vector<int>& model) override
  {
    Trace("cadical::propagator") << "cb::check_found_model" << std::endl;
    bool recheck = false;

    if (d_found_solution)
    {
      return true;
    }

    // Check full model. Theory engine may trigger a recheck, unless new
    // variables were added during check. If so, we break out of the check and
    // have the SAT solver extend the model with the new variables.
    size_t size = d_var_info.size();
    do
    {
      Trace("cadical::propagator")
          << "full check (recheck: " << recheck << ")" << std::endl;
      d_proxy->theoryCheck(theory::Theory::Effort::EFFORT_FULL);
      theory_propagate();
      for (const SatLiteral& p : d_propagations)
      {
        Trace("cadical::propagator")
            << "add propagation reason: " << p << std::endl;
        SatClause clause;
        d_proxy->explainPropagation(p, clause);
        add_clause(clause);
      }
      d_propagations.clear();

      if (!d_new_clauses.empty())
      {
        // Will again call cb_check_found_model() after clauses were added.
        recheck = false;
      }
      else
      {
        recheck = d_proxy->theoryNeedCheck();
      }
    } while (d_var_info.size() == size && recheck);

    bool res = done();
    Trace("cadical::propagator")
        << "cb::check_found_model end: done: " << res << std::endl;
    return res;
  }

  int cb_decide() override
  {
    if (d_found_solution)
    {
      return 0;
    }
    bool stopSearch = false;
    bool requirePhase = false;
    SatLiteral lit = d_proxy->getNextDecisionRequest(requirePhase, stopSearch);
    // We found a partial model, let's check it.
    if (stopSearch)
    {
      d_found_solution = cb_check_found_model({});
      if (d_found_solution)
      {
        Trace("cadical::propagator") << "Found solution" << std::endl;
        d_found_solution = d_proxy->isDecisionEngineDone();
        if (!d_found_solution)
        {
          Trace("cadical::propagator")
              << "Decision engine not done" << std::endl;
          stopSearch = false;
          lit = d_proxy->getNextDecisionRequest(requirePhase, stopSearch);
        }
      }
      else
      {
        Trace("cadical::propagator") << "No solution found yet" << std::endl;
      }
    }
    if (!stopSearch && lit != undefSatLiteral)
    {
      int8_t phase = d_var_info[lit.getSatVariable()].phase;
      if (phase != 0)
      {
        if ((phase == -1 && !lit.isNegated())
            || (phase == 1 && lit.isNegated()))
        {
          lit = ~lit;
        }
      }
      Trace("cadical::propagator") << "cb::decide: " << lit << std::endl;
      return toCadicalLit(lit);
    }
    Trace("cadical::propagator") << "cb::decide: 0" << std::endl;
    return 0;
  }

  /**
   * Perform standard theory check and theory propagation, return next theory
   * propagation.
   */
  int cb_propagate() override
  {
    if (d_found_solution)
    {
      return 0;
    }
    Trace("cadical::propagator") << "cb::propagate" << std::endl;
    if (d_propagations.empty())
    {
      d_proxy->theoryCheck(theory::Theory::Effort::EFFORT_STANDARD);
      theory_propagate();
    }
    return next_propagation();
  }

  /** Add next reason literal to the SAT solver. */
  int cb_add_reason_clause_lit(int propagated_lit) override
  {
    // Get reason for propagated_lit.
    if (!d_processing_reason)
    {
      Assert(d_reason.empty());
      SatLiteral slit = toSatLiteral(propagated_lit);
      SatClause clause;
      d_proxy->explainPropagation(slit, clause);
      d_reason.insert(d_reason.end(), clause.begin(), clause.end());
      d_processing_reason = true;
      Trace("cadical::propagator")
          << "cb::reason: " << slit << ", size: " << d_reason.size()
          << std::endl;
    }

    // We are done processing the reason for propagated_lit.
    if (d_reason.empty())
    {
      d_processing_reason = false;
      return 0;
    }

    // Return next literal of the reason for propagated_lit.
    Trace("cadical::propagator")
        << "cb::reason: " << toSatLiteral(propagated_lit) << " "
        << d_reason.front() << std::endl;
    int lit = toCadicalLit(d_reason.front());
    d_reason.erase(d_reason.begin());
    return lit;
  }

  /** Checks whether we have a buffered clause to add. */
  bool cb_has_external_clause() override { return !d_new_clauses.empty(); }

  /** Add next clause literal to the SAT solver. */
  int cb_add_external_clause_lit() override
  {
    Assert(!d_new_clauses.empty());
    CadicalLit lit = d_new_clauses.front();
    d_new_clauses.erase(d_new_clauses.begin());
    Trace("cadical::propagator")
        << "external_clause: " << toSatLiteral(lit) << std::endl;
    return lit;
  }

  const std::vector<SatLiteral>& get_decisions() const { return d_decisions; }

  /** Get the current assignment of lit. */
  SatValue value(SatLiteral lit) const
  {
    SatVariable var = lit.getSatVariable();
    SatValue val = SAT_VALUE_UNKNOWN;
    int32_t assign = d_var_info[var].assignment;
    if (assign != 0)
    {
      val = toSatValueLit(lit.isNegated() ? -assign : assign);
    }
    Trace("cadical::propagator")
        << "value: " << lit << ": " << val << std::endl;
    return val;
  }

  /**
   * Buffers new clause, which will be added later via the
   * cb_add_external_clause_lit() callback.
   *
   * Note: Filters out clauses satisfied by fixed literals.
   */
  void add_clause(const SatClause& clause)
  {
    std::vector<CadicalLit> lits;
    for (const SatLiteral& lit : clause)
    {
      SatVariable var = lit.getSatVariable();
      const auto& info = d_var_info[var];
      if (info.is_fixed)
      {
        int32_t val = lit.isNegated() ? -info.assignment : info.assignment;
        Assert(val != 0);
        if (val > 0)
        {
          // Clause satisfied by fixed literal, no clause added
          return;
        }
      }
      // Trace("cadical::propagator") << " " << lit;
      // d_new_clauses.push_back(toCadicalLit(lit));
      lits.push_back(toCadicalLit(lit));
    }
    // Trace("cadical::propagator") << " 0" << std::endl;
    // d_new_clauses.push_back(0);
    if (!lits.empty())
    {
      d_new_clauses.insert(d_new_clauses.end(), lits.begin(), lits.end());
      d_new_clauses.push_back(0);
    }
  }

  /**
   * Add new CaDiCaL variable.
   * @param var            The variable to add.
   * @param level          The current user assertion level.
   * @param is_theory_atom True if variable is a theory atom.
   * @param in_search      True if SAT solver is currently in search().
   */
  void add_new_var(const SatVariable& var,
                   uint32_t level,
                   bool is_theory_atom,
                   bool in_search)
  {
    Assert(d_var_info.size() == var);

    // Boolean variables are not theory atoms, but may still occur in
    // lemmas/conflicts sent to the SAT solver. Hence, we have to observe them
    // since CaDiCaL expects all literals sent back to be observed.
    d_solver.add_observed_var(toCadicalVar(var));
    d_active_vars.push_back(var);
    Trace("cadical::propagator")
        << "new var: " << var << " (level: " << level
        << ", is_theory_atom: " << is_theory_atom
        << ", in_search: " << in_search << ")" << std::endl;
    auto& info = d_var_info.emplace_back();
    info.level = level;
    info.is_theory_atom = is_theory_atom;
  }

  /**
   * Checks whether the theory engine is done and the current model is
   * consistent.
   */
  bool done() const
  {
    if (!d_new_clauses.empty())
    {
      Trace("cadical::propagator") << "not done: pending clauses" << std::endl;
      return false;
    }
    if (d_proxy->theoryNeedCheck())
    {
      Trace("cadical::propagator")
          << "not done: theory need check" << std::endl;
      return false;
    }
    if (d_found_solution)
    {
      Trace("cadical::propagator")
          << "done: found partial solution" << std::endl;
    }
    else
    {
      Trace("cadical::propagator")
          << "done: full assignment consistent" << std::endl;
    }
    return true;
  }

  void user_push()
  {
    d_active_vars_control.push_back(d_active_vars.size());
    Trace("cadical::propagator")
        << "user push: " << d_active_vars_control.size() << std::endl;
  }

  /**
   * Pop user assertion level.
   * @param level The current assertion level (pre pop). We need this to keep
   *              track of which fixed literal to re-enqueue.
   */
  void user_pop(uint32_t level)
  {
    Trace("cadical::propagator")
        << "user pop: " << d_active_vars_control.size() << std::endl;
    size_t pop_to = d_active_vars_control.back();
    d_active_vars_control.pop_back();

    // Unregister popped variables so that CaDiCaL does not notify us anymore
    // about assignments.
    Assert(pop_to <= d_active_vars.size());
    while (d_active_vars.size() > pop_to)
    {
      SatVariable var = d_active_vars.back();
      d_active_vars.pop_back();
      // d_solver.remove_observed_var(toCadicalVar(var));
      d_var_info[var].is_active = false;
      Trace("cadical::propagator") << "set inactive: " << var << std::endl;
    }

    // Re-enqueue fixed theory literals on level 0
    for (SatLiteral lit : d_assignments)
    {
      if (d_var_info[lit.getSatVariable()].level < level)
      {
        Trace("cadical::propagator") << "re-enqueue: " << lit << std::endl;
        d_proxy->enqueueTheoryLiteral(lit);
      }
    }
  }

  bool is_fixed(SatVariable var) const { return d_var_info[var].is_fixed; }

  /**
   * Record preferred phase of variable.
   * @param var The variable.
   * @param phase The phase, -1 if negative, 1 if positive, 0 if no phase
   *              is configured.
   */
  void phase(SatVariable var, uint8_t phase) { d_var_info[var].phase = phase; }

 private:
  /** Retrieve theory propagations and add them to the propagations list. */
  void theory_propagate()
  {
    SatClause propagated_lits;
    d_proxy->theoryPropagate(propagated_lits);
    Trace("cadical::propagator")
        << "new propagations: " << propagated_lits.size() << std::endl;

    for (const auto& lit : propagated_lits)
    {
      Trace("cadical::propagator") << "new propagation: " << lit << std::endl;
      d_propagations.push_back(lit);
    }
  }

  /** Return next propagation. */
  int next_propagation()
  {
    if (d_propagations.empty())
    {
      return 0;
    }
    SatLiteral next = d_propagations.front();
    d_propagations.erase(d_propagations.begin());
    Trace("cadical::propagator") << "propagate: " << next << std::endl;
    return toCadicalLit(next);
  }

  /** The associated theory proxy. */
  prop::TheoryProxy* d_proxy = nullptr;

  /** The SAT context. */
  context::Context& d_context;
  CaDiCaL::Solver& d_solver;

  /** Struct to store information on variables. */
  struct VarInfo
  {
    uint32_t level = 0;           // the assertion level on creation
    bool is_theory_atom = false;  // is variable a theory atom
    bool is_fixed = false;        // has variable fixed assignment
    bool is_active = true;        // is variable active
    int32_t assignment = 0;       // current variable assignment
    int8_t phase = 0;             // preferred phase
  };
  /** Maps SatVariable to corresponding info struct. */
  std::vector<VarInfo> d_var_info;

  /**
   * Currently active variables, can get inactive on user pops.
   * Dependent on user context.
   */
  std::vector<SatVariable> d_active_vars;
  /**
   * Control stack to mananage d_active_vars on user pop.
   *
   * Note: We do not use a User-context-dependent CDList here, since we neeed
   *       to know which variables are popped and thus become inactive.
   */
  std::vector<size_t> d_active_vars_control;

  /**
   * Variable assignment notifications.
   *
   * Used to unassign variables on backtrack.
   */
  std::vector<SatLiteral> d_assignments;
  /**
   * Control stack to manage d_assignments when backtracking on SAT level.
   *
   * Note: We do not use a SAT-context-depenent CDList for d_assignments, since
   *       we need to know which non-fixed variables are unassigned on
   *       backtrack.
   */
  std::vector<size_t> d_assignment_control;

  /**
   * Stores all observed decision variables.
   *
   * Note: May contain undefSatLiteral for unobserved decision variables.
   */
  std::vector<SatLiteral> d_decisions;

  /** Used by cb_propagate() to return propagated literals. */
  std::vector<SatLiteral> d_propagations;

  /**
   * Used by add_clause() to buffer added clauses, which will be added via
   * cb_add_reason_clause_lit().
   */
  std::vector<CadicalLit> d_new_clauses;

  /**
   * Flag indicating whether cb_add_reason_clause_lit() is currently
   * processing a reason.
   */
  bool d_processing_reason = false;
  /** Reason storage to process current reason in cb_add_reason_clause_lit(). */
  std::vector<SatLiteral> d_reason;

  bool d_found_solution = false;
};

CadicalSolver::CadicalSolver(Env& env,
                             StatisticsRegistry& registry,
                             const std::string& name)
    : EnvObj(env),
      d_solver(new CaDiCaL::Solver()),
      d_context(nullptr),
      // Note: CaDiCaL variables start with index 1 rather than 0 since negated
      //       literals are represented as the negation of the index.
      d_nextVarIdx(1),
      d_observedVars(env.getUserContext()),
      d_inSatMode(false),
      d_assertionLevel(0),
      d_statistics(registry, name)
{
}

void CadicalSolver::init()
{
  d_true = newVar();
  d_false = newVar();

  // walk and lucky phase are not using the external propagator, disable for now
  d_solver->set("walk", 0);
  d_solver->set("lucky", 0);

  d_solver->set("quiet", 1);  // CaDiCaL is verbose by default
  d_solver->add(toCadicalVar(d_true));
  d_solver->add(0);
  d_solver->add(-toCadicalVar(d_false));
  d_solver->add(0);
}

CadicalSolver::~CadicalSolver() {}

/**
 * Terminator class that notifies CaDiCaL to terminate when the resource limit
 * is reached (used for resource limits specified via --rlimit or --tlimit).
 */
class ResourceLimitTerminator : public CaDiCaL::Terminator
{
 public:
  ResourceLimitTerminator(ResourceManager& resmgr) : d_resmgr(resmgr){};

  bool terminate() override
  {
    d_resmgr.spendResource(Resource::BvSatStep);
    return d_resmgr.out();
  }

 private:
  ResourceManager& d_resmgr;
};

void CadicalSolver::setResourceLimit(ResourceManager* resmgr)
{
  d_terminator.reset(new ResourceLimitTerminator(*resmgr));
  d_solver->connect_terminator(d_terminator.get());
}

SatValue CadicalSolver::_solve(const std::vector<SatLiteral>& assumptions)
{
  if (d_propagator)
  {
    Trace("cadical::propagator") << "solve start" << std::endl;
  }
  TimerStat::CodeTimer codeTimer(d_statistics.d_solveTime);
  d_assumptions.clear();
  SatValue res;
  for (const SatLiteral& lit : assumptions)
  {
    if (d_propagator)
    {
      Trace("cadical::propagator") << "assume: " << lit << std::endl;
    }
    d_solver->assume(toCadicalLit(lit));
    d_assumptions.push_back(lit);
  }
  d_in_search = true;
  res = toSatValue(d_solver->solve());
  if (d_propagator)
  {
    Assert(res != SAT_VALUE_TRUE || d_propagator->done());
    Trace("cadical::propagator") << "solve done: " << res << std::endl;
  }
  d_in_search = false;
  ++d_statistics.d_numSatCalls;
  d_inSatMode = (res == SAT_VALUE_TRUE);
  return res;
}

/* SatSolver Interface ------------------------------------------------------ */

ClauseId CadicalSolver::addClause(SatClause& clause, bool removable)
{
  if (d_propagator && TraceIsOn("cadical::propagator"))
  {
    Trace("cadical::propagator") << "addClause (" << removable << "):";
    for (const SatLiteral& lit : clause)
    {
      Trace("cadical::propagator") << " " << lit;
    }
    Trace("cadical::propagator") << " 0" << std::endl;
  }
  if (d_in_search && d_propagator)
  {
    d_propagator->add_clause(clause);
  }
  else
  {
    for (const SatLiteral& lit : clause)
    {
      d_solver->add(toCadicalLit(lit));
    }
    d_solver->add(0);
  }
  ++d_statistics.d_numClauses;
  return ClauseIdError;
}

ClauseId CadicalSolver::addXorClause(SatClause& clause,
                                     bool rhs,
                                     bool removable)
{
  Unreachable() << "CaDiCaL does not support adding XOR clauses.";
}

SatVariable CadicalSolver::newVar(bool isTheoryAtom, bool canErase)
{
  ++d_statistics.d_numVariables;
  if (d_propagator)
  {
    d_propagator->add_new_var(
        d_nextVarIdx, d_assertionLevel, isTheoryAtom, d_in_search);
  }
  return d_nextVarIdx++;
}

SatVariable CadicalSolver::trueVar() { return d_true; }

SatVariable CadicalSolver::falseVar() { return d_false; }

SatValue CadicalSolver::solve() { return _solve({}); }

SatValue CadicalSolver::solve(long unsigned int&)
{
  Unimplemented() << "Setting limits for CaDiCaL not supported yet";
};

SatValue CadicalSolver::solve(const std::vector<SatLiteral>& assumptions)
{
  return _solve(assumptions);
}

bool CadicalSolver::setPropagateOnly()
{
  d_solver->limit("decisions", 0); /* Gets reset after next solve() call. */
  return true;
}

void CadicalSolver::getUnsatAssumptions(std::vector<SatLiteral>& assumptions)
{
  for (const SatLiteral& lit : d_assumptions)
  {
    if (d_solver->failed(toCadicalLit(lit)))
    {
      assumptions.push_back(lit);
    }
  }
}

void CadicalSolver::interrupt() { d_solver->terminate(); }

SatValue CadicalSolver::value(SatLiteral l) { return d_propagator->value(l); }

SatValue CadicalSolver::modelValue(SatLiteral l)
{
  Assert(d_inSatMode);
  return toSatValueLit(d_solver->val(toCadicalLit(l)));
}

uint32_t CadicalSolver::getAssertionLevel() const { return d_assertionLevel; }

bool CadicalSolver::ok() const { return d_inSatMode; }

CadicalSolver::Statistics::Statistics(StatisticsRegistry& registry,
                                      const std::string& prefix)
    : d_numSatCalls(registry.registerInt(prefix + "cadical::calls_to_solve")),
      d_numVariables(registry.registerInt(prefix + "cadical::variables")),
      d_numClauses(registry.registerInt(prefix + "cadical::clauses")),
      d_solveTime(registry.registerTimer(prefix + "cadical::solve_time"))
  {
}

/* CDCLTSatSolver Interface ------------------------------------------------- */

void CadicalSolver::initialize(context::Context* context,
                               prop::TheoryProxy* theoryProxy,
                               context::UserContext* userContext,
                               ProofNodeManager* pnm)
{
  d_context = context;
  d_proxy = theoryProxy;
  d_propagator.reset(new CadicalPropagator(theoryProxy, context, *d_solver));
  d_solver->connect_external_propagator(d_propagator.get());

  init();
}

void CadicalSolver::push()
{
  ++d_assertionLevel;
  d_context->push();  // SAT context for cvc5
  d_propagator->user_push();
}

void CadicalSolver::pop()
{
  // TODO
  // Notify sat proof manager that we have popped and now potentially we need to
  // retrieve the proofs for the clauses inserted into optimized levels
  // if (needProof())
  //{
  //  d_pfManager->notifyPop();
  //}

  d_context->pop();  // SAT context for cvc5
  d_propagator->user_pop(d_assertionLevel);
  --d_assertionLevel;
  // CaDiCaL issues notify_backtrack(0) when done, we don't have to call this
  // explicitly here
}

void CadicalSolver::resetTrail()
{
  // Reset SAT context to decision level 0
  d_propagator->notify_backtrack(0);
}

void CadicalSolver::preferPhase(SatLiteral lit)
{
  Trace("cadical::propagator") << "phase: " << lit << std::endl;
  d_solver->phase(toCadicalLit(lit));
  d_propagator->phase(lit.getSatVariable(), lit.isNegated() ? -1 : 1);
}

bool CadicalSolver::isDecision(SatVariable var) const
{
  return d_solver->is_decision(toCadicalVar(var));
}

bool CadicalSolver::isFixed(SatVariable var) const
{
  if (d_propagator)
  {
    return d_propagator->is_fixed(var);
  }
  return d_solver->fixed(toCadicalVar(var));
}

std::vector<SatLiteral> CadicalSolver::getDecisions() const
{
  std::vector<SatLiteral> decisions;
  for (SatLiteral lit : d_propagator->get_decisions())
  {
    if (lit != 0)
    {
      decisions.push_back(lit);
    }
  }
  return decisions;
}

std::vector<Node> CadicalSolver::getOrderHeap() const { return {}; }

std::shared_ptr<ProofNode> CadicalSolver::getProof()
{
  // TODO
  return nullptr;
}

SatProofManager* CadicalSolver::getProofManager()
{
  // TODO
  return nullptr;
}

/* -------------------------------------------------------------------------- */
}  // namespace prop
}  // namespace cvc5::internal
