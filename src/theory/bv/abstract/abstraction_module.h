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
 *
 * Implements the abstraction module of the CEGAR strategy of "Scalable
 * Bit-Blasting with Abstractions" (Niemetz, Preiner, Zohar, CAV 2024).
 *
 * Every "expensive" arithmetic term `op(x, s)` (op in {bvmul, bvudiv, bvurem})
 * whose bit-width is at least a configurable threshold is replaced by a fresh
 * bit-vector constant `t` of the same sort. This over-approximates the formula
 * (the multiplier/divider circuit is never bit-blasted). If an abstraction for
 * is consistent wrt. the semantics of the abstracted arithmetic operation,
 * it is refined via a tiered refined strategy. The first tier is implemented
 * by the lemma schemes in abstraction_lemmas.h.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BV__ABSTRACT__BV_ABSTRACTION_H
#define CVC5__THEORY__BV__ABSTRACT__BV_ABSTRACTION_H

#include <unordered_map>

#include "expr/node.h"
#include "smt/env_obj.h"
#include "theory/bv/abstract/abstraction_lemmas.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {
namespace theory {
namespace bv {

class TheoryBV;

namespace abstract {

/** An arithmetic term `op(x, s)` that has been abstracted by a constant. */
struct AbstractedTerm
{
  /** The operator kind (BITVECTOR_MULT, BITVECTOR_UDIV or BITVECTOR_UREM). */
  Kind d_kind;
  /** The first operand. */
  Node d_x;
  /** The second operand. */
  Node d_s;
};

/**
 * The bit-vector arithmetic abstraction module.
 *
 * Owned by BVSolverBitblast and constructed only when --bv-abstraction is set.
 */
class AbstractionModule : protected EnvObj
{
 public:
  /**
   * Constructor.
   * @param env The associated environment.
   * @param bv  The associated TheoryBV.
   */
  AbstractionModule(Env& env, TheoryBV* bv);

  /**
   * Replace every abstractable arithmetic subterm of `fact` by a fresh
   * constant, recording the abstraction map. Abstractable terms are binary
   * bvmul/bvudiv/bvurem nodes whose bit-width is at least the abstraction
   * threshold (option --bv-abstraction-bitwidth).
   *
   * The atom/Boolean structure of `fact` is preserved; only arithmetic
   * subterms are substituted. Equal terms share the same abstraction constant.
   *
   * @param fact The fact to abstract.
   * @return The abstracted fact (equal to `fact` if nothing was abstracted).
   */
  Node abstract(TNode fact);

  /**
   * Check the current model for consistency with every abstracted term and
   * collect tier-1/2 refinement lemmas (the Table-2 schemes in
   * abstraction_lemmas.h) that are violated under the model.
   *
   * For each abstracted term `t = op(x, s)` the operands and `t` are evaluated
   * to their model values via `getValue`, and every lemma scheme for `op` whose
   * instantiation evaluates to false under the model is added to `lemmas`. An
   * empty result means the model is consistent with all abstracted terms.
   *
   * @param getValue Returns the model value of a (sub)term, recursively
   *                 evaluated from its leaves (e.g. TheoryBV::getValue). May
   *                 return a non-constant if the value is undetermined.
   * @param lemmas   Output list of violated refinement lemmas to assert.
   */
  void check(std::vector<Node>& lemmas);

  /**
   * @return True if `n` is an abstraction constant introduced by this module.
   */
  bool isAbstraction(TNode n) const;

  /** @return True if arithmetic term `n` has been abstracted by a constant. */
  bool isAbstractedTerm(TNode n) const
  {
    return d_termToAbs.find(n) != d_termToAbs.end();
  }

  /**
   * @return The abstraction introduced for given node. Asserts that the
   *         node has been abstracted.
   */
  TNode getAbstraction(TNode n) const;

  /** @return The map from abstraction constants to their abstracted terms. */
  const std::unordered_map<Node, AbstractedTerm>& getAbstractions() const
  {
    return d_absToTerm;
  }

  /** @return The refinement lemma registry. */
  const LemmaRegistry& getLemmaRegistry() const { return d_lemmas; }

  /**
   * @return True if every abstracted term is consistent with the current model,
   * i.e. `op(v_x, v_s) == v_t` for each `t = op(x, s)`. Used as a debug check
   * after the refinement loop concludes sat.
   */
  bool isModelConsistent();

  /** @return True if `n` is a term that should be abstracted. */
  bool abstractable(TNode n) const;

 private:
  TheoryBV* d_bv;

  /**
   * Return the abstraction constant for arithmetic term `op`, creating a fresh
   * one (and recording it) on first encounter.
   */
  Node abstractTerm(TNode op);

  /** Minimum bit-width to abstract (option --bv-abstraction-bitwidth). */
  uint64_t d_threshold;

  /** The refinement lemma schemes, used by the refinement loop. */
  LemmaRegistry d_lemmas;

  /** Map from abstraction constant `t` to the abstracted term `op(x, s)`. */
  std::unordered_map<Node, AbstractedTerm> d_absToTerm;

  /** Map from arithmetic term `op(x, s)` to its abstraction constant `t`. */
  std::unordered_map<Node, Node> d_termToAbs;

  /** Memoization cache for abstract(). */
  std::unordered_map<Node, Node> d_cache;

  /**
   * Number of tier-3 value-instantiation lemmas added so far for each
   * abstraction constant. Once this reaches the per-term budget
   * (bit-width / bvAbstractionValueInstDivisor), the tier-4 bit-blasting
   * fallback is used instead.
   */
  std::unordered_map<Node, uint64_t> d_valueInstCount;

  /** Statistics for the abstraction module. */
  struct Statistics
  {
    Statistics(StatisticsRegistry& reg);
    /** Number of arithmetic terms abstracted. */
    IntStat d_numAbstractions;
    /** Number of refinement consistency checks (refinement rounds). */
    IntStat d_numChecks;
    /** Number of tier-1/2 (Table-2 scheme) refinement lemmas added. */
    IntStat d_numLemmasTier12;
    /** Number of tier-3 value-instantiation refinement lemmas added. */
    IntStat d_numLemmasTier3;
    /** Number of tier-4 bit-blasting fallback lemmas added. */
    IntStat d_numLemmasTier4;
  } d_stats;
};

}  // namespace abstract
}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal

#endif
