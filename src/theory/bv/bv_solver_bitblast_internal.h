/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Bit-blast solver that sends bit-blast lemmas directly to the internal
 * MiniSat.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BV__BV_SOLVER_BITBLAST_INTERNAL_H
#define CVC5__THEORY__BV__BV_SOLVER_BITBLAST_INTERNAL_H

#include "proof/eager_proof_generator.h"
#include "smt/env_obj.h"
#include "theory/bv/abstract/abstraction_module.h"
#include "theory/bv/bitblast/proof_bitblaster.h"
#include "theory/bv/bv_solver.h"

namespace cvc5::internal {
namespace theory {
namespace bv {

class TheoryBV;

/**
 * Bit-blasting solver that sends bit-blasting lemmas directly to the
 * internal MiniSat. It is also ablo to handle atoms of kind
 * BITVECTOR_EAGER_ATOM.
 *
 * Sends lemmas atom <=> bb(atom) to MiniSat on preNotifyFact().
 */
class BVSolverBitblastInternal : public BVSolver
{
 public:
  BVSolverBitblastInternal(Env& env,
                           TheoryState* state,
                           TheoryInferenceManager& inferMgr,
                           TheoryBV* bv);
  ~BVSolverBitblastInternal() = default;

  bool needsEqualityEngine(EeSetupInfo& esi) override;

  void preRegisterTerm(CVC5_UNUSED TNode n) override {}

  bool preCheck(Theory::Effort level) override;

  void postCheck(Theory::Effort level) override;

  bool preNotifyFact(TNode atom,
                     bool pol,
                     TNode fact,
                     bool isPrereg,
                     bool isInternal) override;

  TrustNode explain(TNode n) override;

  std::string identify() const override { return "BVSolverBitblastInternal"; };

  bool collectModelValues(TheoryModel* m,
                          const std::set<Node>& termSet) override;

  Node getValue(TNode node, bool initialize) override;

  bool isModelConsistent() const override { return d_isModelConsistent; }

 private:
  /**
   * Sends a bit-blasting lemma fact <=> d_bitblaster.bbAtom(afact) to the
   * inference manager, where `afact` is the abstraction of `fact` if
   * abstraction is enabled, and `fact` otherwise.
   */
  void addBBLemma(TNode fact);
  /**
   * Sends a bit-blasting lemma fact <=> d_bitblaster.bbAtom(afact) to the
   * inference manager, where `afact` is either `fact` or its abstraction. If
   * `afact` is a constant (e.g., the abstraction of a tier-4 atom), the lemma
   * is fact <=> afact.
   */
  void addBBLemma(TNode fact, TNode afact);

  /** Bit-blaster used to bit-blast atoms/terms. */
  std::unique_ptr<BBProof> d_bitblaster;
  /** Proof generator for unpacking BITVECTOR_EAGER_ATOM. */
  std::unique_ptr<EagerProofGenerator> d_epg;

  /** The associated CEGAR abstraction module for bit-vector arithmetic. */
  std::unique_ptr<abstract::AbstractionModule> d_am;

  /**
   * Cache if current model is consistent. Can only ever be inconsistent in the
   * case of abstraction.
   */
  bool d_isModelConsistent;

  /**
   * The number of lemmas the inference manager had sent at the beginning of
   * the current check, used to determine if lemmas were sent in this check
   * before postCheck().
   */
  uint32_t d_numLemmasPreCheck;
};

}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal

#endif
