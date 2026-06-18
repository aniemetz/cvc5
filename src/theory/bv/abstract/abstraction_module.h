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
 * Implements the abstraction half of the CEGAR strategy of "Scalable
 * Bit-Blasting with Abstractions" (Niemetz, Preiner, Zohar, CAV 2024): every
 * "expensive" arithmetic term `op(x, s)` (op in {bvmul, bvudiv, bvurem}) whose
 * bit-width is at least a configurable threshold is replaced by a fresh
 * bit-vector constant `t` of the same sort. This over-approximates the formula
 * (the multiplier/divider circuit is never bit-blasted); consistency is later
 * restored by the refinement loop via the lemma schemes in
 * abstraction_lemmas.h.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BV__ABSTRACT__BV_ABSTRACTION_H
#define CVC5__THEORY__BV__ABSTRACT__BV_ABSTRACTION_H

#include <unordered_map>

#include "expr/node.h"
#include "smt/env_obj.h"
#include "theory/bv/abstract/abstraction_lemmas.h"

namespace cvc5::internal {
namespace theory {
namespace bv {
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
  AbstractionModule(Env& env);

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

  /** @return True if `n` is an abstraction constant introduced by this module.
   */
  bool isAbstraction(TNode n) const;

  /**
   * @return The arithmetic term abstracted by constant `n`. `n` must be an
   *         abstraction constant (see isAbstraction()).
   */
  const AbstractedTerm& getAbstractedTerm(TNode n) const;

  /** @return The map from abstraction constants to their abstracted terms. */
  const std::unordered_map<Node, AbstractedTerm>& getAbstractions() const
  {
    return d_absToTerm;
  }

  /** @return The refinement lemma registry. */
  const LemmaRegistry& getLemmaRegistry() const { return d_lemmas; }

 private:
  /** @return True if `n` is a term that should be abstracted. */
  bool abstractable(TNode n) const;

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
};

}  // namespace abstract
}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal

#endif
