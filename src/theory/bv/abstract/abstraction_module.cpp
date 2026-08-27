/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The bit-vector arithmetic abstraction module.
 */

#include "theory/bv/abstract/abstraction_module.h"

#include <algorithm>

#include "expr/node_manager.h"
#include "options/bv_options.h"
#include "smt/env.h"
#include "theory/bv/theory_bv.h"
#include "theory/bv/theory_bv_utils.h"

namespace cvc5::internal {
namespace theory {
namespace bv {
namespace abstract {

AbstractionModule::AbstractionModule(Env& env, TheoryBV* bv)
    : EnvObj(env),
      d_bv(bv),
      d_absSize(options().bv.bvAbstractionSize),
      d_valLimiter(options().bv.bvAbstractionValueLimiter),
      d_lemmas(nodeManager()),
      d_bitblasted(userContext()),
      d_emitted(userContext()),
      d_stats(statisticsRegistry())
{
}

AbstractionModule::Statistics::Statistics(StatisticsRegistry& reg)
    : d_numAbstractions(
          reg.registerInt("theory::bv::abstraction::numAbstractions")),
      d_numChecks(reg.registerInt("theory::bv::abstraction::numChecks")),
      d_numLemmasTier12(
          reg.registerInt("theory::bv::abstraction::numLemmasTier12")),
      d_numLemmasTier3(
          reg.registerInt("theory::bv::abstraction::numLemmasTier3")),
      d_numLemmasTier4(
          reg.registerInt("theory::bv::abstraction::numLemmasTier4")),
      d_numLemmasSuppressed(
          reg.registerInt("theory::bv::abstraction::numLemmasSuppressed"))
{
}

bool AbstractionModule::abstractable(TNode n) const
{
  Kind k = n.getKind();
  if (k != Kind::BITVECTOR_MULT && k != Kind::BITVECTOR_UDIV
      && k != Kind::BITVECTOR_UREM)
  {
    return false;
  }
  // The lemma schemes are binary; cvc5 allows n-ary BITVECTOR_MULT.
  if (n.getNumChildren() != 2)
  {
    return false;
  }
  return utils::getSize(n) >= d_absSize;
}

Node AbstractionModule::abstractNode(TNode node)
{
  Assert(abstractable(node));
  auto it = d_cache.find(node);
  // If the cached node is different from `node`, it must be an abstraction
  // constant. Hence, we don't have to check for d_abs2node.find(it->second).
  if (it != d_cache.end() && !it->second.isNull() && it->second != node)
  {
    return it->second;
  }
  // A fresh, opaque constant of the same sort. It is deliberately *not* a
  // purification skolem: the abstraction must stay an unconstrained
  // over-approximation, never silently re-expanded to `op` during rewriting
  // or model construction.
  Node t = NodeManager::mkDummySkolem("bvabs", node.getType());
  d_abs2node.emplace(t, node);
  // Note: We do not insert into d_cache here: the caller writes the mapping
  // through a live iterator, which an insertion could invalidate (rehash).
  ++d_stats.d_numAbstractions;
  return t;
}

Node AbstractionModule::abstract(TNode fact)
{
  // Refinement lemmas are asserted in their final form, their atoms must not
  // be abstracted (see d_noAbstract). Note that we return before touching
  // d_cache: even if `fact` was abstracted before (as an input atom), not
  // abstracting it here is the conservative direction.
  if (d_noAbstract.find(fact) != d_noAbstract.end())
  {
    return fact;
  }

  NodeManager* nm = nodeManager();
  std::vector<TNode> visit{fact};
  do
  {
    TNode cur = visit.back();
    auto it = d_cache.find(cur);
    if (it == d_cache.end())
    {
      // Do not descend into terms of other theories (e.g., array selects).
      // The bit-blaster treats them as opaque leaves (variables), and they are
      // the terms shared with the other theory. Rebuilding below such a term
      // would create a NEW node (e.g., a select over an abstracted index)
      // distinct from the shared one: the other theory would continue to
      // reason about the original while this solver constrains the copy,
      // silently disconnecting the two (unsound under theory combination).
      theory::TheoryId tid = d_env.theoryOf(cur);
      if (cur.getNumChildren() > 0 && tid != theory::THEORY_BV
          && tid != theory::THEORY_BOOL)
      {
        d_cache.emplace(cur, cur);
        visit.pop_back();
        continue;
      }
      d_cache.emplace(cur, Node::null());
      visit.insert(visit.end(), cur.begin(), cur.end());
      continue;
    }
    if (it->second.isNull())
    {
      bool rebuild = false;
      std::vector<Node> children;
      if (cur.getMetaKind() == kind::metakind::PARAMETERIZED)
      {
        children.push_back(cur.getOperator());
      }
      for (const TNode& child : cur)
      {
        Node abs = d_cache.at(child);
        Assert(!abs.isNull());
        rebuild = rebuild || abs != child;
        children.push_back(abs);
      }
      Node ret = rebuild ? nm->mkNode(cur.getKind(), children) : Node(cur);
      if (abstractable(ret))
      {
        ret = abstractNode(ret);
      }
      it->second = rewrite(ret);
    }
    visit.pop_back();
  } while (!visit.empty());

  Node afact = d_cache.at(fact);
  // Abstracting must not make a fact trivially true or false. This would
  // happen for the atoms of refinement lemmas, e.g., the tier-4 lemma
  // `t = op(x, s)` collapses to `t = t`. These are guarded by d_noAbstract
  // above, this is a safety net in case such an atom reaches us in a form we
  // did not record (e.g., with its arguments reordered by rewriting).
  //
  // Note that if `fact` itself is not trivial, not abstracting it is sound (it
  // only means that we bit-blast the corresponding circuit).
  if (afact.isConst() && !rewrite(fact).isConst())
  {
    Trace("bv-abstraction") << "abstract: not abstracting " << fact
                            << " (would collapse to " << afact << ")"
                            << std::endl;
    return fact;
  }
  return afact;
}

bool AbstractionModule::wasAdded(const Node& lemma)
{
  return d_emitted.contains(rewrite(lemma));
}

void AbstractionModule::addLemma(std::vector<Node>& lemmas, const Node& lemma)
{
  Node rlemma = rewrite(lemma);
  Assert(!d_emitted.contains(rlemma));
  d_emitted.insert(rlemma);
  // Record the atoms of the lemma as not to be abstracted. We record the atoms
  // of both the lemma and its rewritten form since a solver that sends the
  // lemma to the inference manager gets its (preprocessed, thus rewritten)
  // atoms back as asserted facts.
  utils::collectBVAtoms(lemma, d_noAbstract);
  utils::collectBVAtoms(rlemma, d_noAbstract);
  lemmas.push_back(lemma);
}

void AbstractionModule::check(std::vector<Node>& lemmas)
{
  ++d_stats.d_numChecks;
  NodeManager* nm = nodeManager();
  Node falseNode = nm->mkConst(false);
  std::vector<Node> args(3);
  std::vector<Node> vals(3);
  for (const auto& [t, n] : d_abs2node)
  {
    Assert(abstractable(n));
    // A term that was refined via tier 4 is fully constrained by the
    // bit-blasted circuit, there is nothing left to refine. Note that such a
    // term may still look inconsistent below if the current model does not
    // assign all bits of the circuit (the value queries zero-fill in that
    // case), in which case adding further lemmas would not make progress.
    if (d_bitblasted.contains(t))
    {
      continue;
    }
    Kind kind = n.getKind();
    TNode x = n[0];
    TNode s = n[1];
    Node xval = d_bv->getValue(x);
    Node sval = d_bv->getValue(s);
    Node tval = d_bv->getValue(t);
    Assert(xval.isConst() && sval.isConst() && tval.isConst());

    // The abstraction `t = op(x, s)` is consistent with the model iff the
    // actual operator applied to the operand values equals the value of `t`.
    // If so, there is nothing to refine for this node.
    Node value = rewrite(nm->mkNode(kind, xval, sval));
    if (value == tval)
    {
      continue;
    }

    // Tier 1/2: add the FIRST Table-2 lemma scheme (in registry order, which
    // follows Bitwuzla's) that is violated under the current model, i.e.,
    // whose instantiation constant-folds to false when x, s, t are substituted
    // by their model values. Only one lemma is added per term per refinement
    // round (as in Bitwuzla), so the SAT solver is not swamped with all
    // violated schemes at once.
    //
    // Note: We do not use the Evaluator here since it only substitutes
    //       *variable* keys (it matches `args` entries only for nodes with
    //       isVar()) and leaves a compound key unsubstituted (thus would
    //       evaluate to a non-constant, and so miss the violation).
    args = {x, s, t};
    vals = {xval, sval, tval};
    bool violated = false;
    for (const std::unique_ptr<AbstractionLemma>& lemma : d_lemmas.lemmas(kind))
    {
      Node inst = lemma->instance(x, s, t);
      if (inst.isNull())
      {
        inst = lemma->instance(x, s, t, xval, sval);
      }
      if (inst.isNull())
      {
        // Value lemma not applicable under the current model values (e.g. the
        // POW2 schemes when the value is not a power of two).
        continue;
      }
      Node subst =
          inst.substitute(args.begin(), args.end(), vals.begin(), vals.end());
      if (rewrite(subst) == falseNode)
      {
        // Skip schemes that were already added for this term. They cannot rule
        // out any model that was not ruled out before, thus adding them again
        // would not make progress. Continue with the next violated scheme.
        if (wasAdded(inst))
        {
          ++d_stats.d_numLemmasSuppressed;
          continue;
        }
        addLemma(lemmas, inst);
        violated = true;
        break;
      }
    }
    // If a Table-2 lemma ruled out this spurious model, move on.
    if (violated)
    {
      ++d_stats.d_numLemmasTier12;
      continue;
    }

    // No tier-1/2 lemma violated, fall back to value instantiation if we have
    // not exhausted the instantiation budget for this term yet.
    uint64_t budget = utils::getSize(t) / d_valLimiter;
    if (d_valueInstCount[t] < budget)
    {
      // Tier 3: value instantiation.
      Node lemma =
          nm->mkNode(Kind::IMPLIES,
                     {nm->mkNode(Kind::AND, {x.eqNode(xval), s.eqNode(sval)}),
                      t.eqNode(value)});
      if (!wasAdded(lemma))
      {
        addLemma(lemmas, lemma);
        ++d_valueInstCount[t];
        ++d_stats.d_numLemmasTier3;
        continue;
      }
      // We already added this value instantiation, escalate to tier 4 instead
      // of not making progress.
      ++d_stats.d_numLemmasSuppressed;
    }
    // Tier 4: bit-blasting fallback. Assert t = op(x, s), forcing the real
    // circuit to be bit-blasted; `t` is fully constrained from now on.
    addLemma(lemmas, t.eqNode(nm->mkNode(kind, x, s)));
    d_bitblasted.insert(t);
    ++d_stats.d_numLemmasTier4;
  }
}

#ifdef CVC5_ASSERTIONS
bool AbstractionModule::isModelConsistent()
{
  NodeManager* nm = nodeManager();
  for (const auto& [t, n] : d_abs2node)
  {
    Assert(abstractable(n));
    Node xval = d_bv->getValue(n[0]);
    Node sval = d_bv->getValue(n[1]);
    Node tval = d_bv->getValue(t);
    if (!xval.isConst() || !sval.isConst() || !tval.isConst())
    {
      continue;
    }
    if (rewrite(nm->mkNode(n.getKind(), xval, sval)) != tval)
    {
      return false;
    }
  }
  return true;
}
#endif

bool AbstractionModule::isAbstracted(TNode node) const
{
  auto it = d_cache.find(node);
  // Note: The cache also holds null visit markers (while abstract() runs) and
  //       rebuilt terms for nodes above an abstracted subterm. Hence, we also
  //       have to check if there exists a mapping in d_abs2node.
  return it != d_cache.end() && !it->second.isNull() && it->second != node
         && d_abs2node.find(it->second) != d_abs2node.end();
}

TNode AbstractionModule::getAbstraction(TNode node) const
{
  Assert(isAbstracted(node));
  return d_cache.at(node);
}

}  // namespace abstract
}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal
