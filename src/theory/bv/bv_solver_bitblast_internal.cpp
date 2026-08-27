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

#include "theory/bv/bv_solver_bitblast_internal.h"

#include "options/bv_options.h"
#include "proof/conv_proof_generator.h"
#include "theory/bv/bitblast/bitblast_proof_generator.h"
#include "theory/bv/theory_bv.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/theory_model.h"

namespace cvc5::internal {
namespace theory {
namespace bv {

/* -------------------------------------------------------------------------- */

BVSolverBitblastInternal::BVSolverBitblastInternal(
    Env& env, TheoryState* s, TheoryInferenceManager& inferMgr, TheoryBV* bv)
    : BVSolver(env, *s, inferMgr),
      d_bitblaster(new BBProof(env, s, false)),
      d_epg(new EagerProofGenerator(d_env)),
      d_am(options().bv.bvAbstraction ? new abstract::AbstractionModule(env, bv)
                                      : nullptr),
      d_isModelConsistent(true)
{
  // Abstraction is not supported with proofs yet: the bit-blasting lemma
  // relates the original atom to the bit-blasting of its abstraction, which
  // the bit-blasting proof generator cannot justify. Option --bv-abstraction is
  // disabled if proofs are enabled, see SetDefaults::incompatibleWithProofs().
  AlwaysAssert(d_am == nullptr || !d_env.isTheoryProofProducing())
      << "bit-vector abstraction is not supported with proofs";
}

void BVSolverBitblastInternal::addBBLemma(TNode fact)
{
  // Abstract arithmetic subterms before bit-blasting; the fresh abstraction
  // constants are bit-blasted as variables, so the multiplier/divider circuits
  // are never built. Note that the left-hand side of the lemma below is the
  // original atom `fact`: that is the literal the SAT solver decides and the
  // term the equality engine reasons about, only the circuit it is equivalent
  // to is abstracted. This over-approximates and is refined in postCheck().
  Node afact = d_am ? d_am->abstract(fact) : Node(fact);

  if (!d_bitblaster->hasBBAtom(afact))
  {
    d_bitblaster->bbAtom(afact);
  }
  NodeManager* nm = nodeManager();

  Node atom_bb = d_bitblaster->getStoredBBAtom(afact);
  Node lemma = nm->mkNode(Kind::EQUAL, fact, atom_bb);

  if (!d_env.isTheoryProofProducing())
  {
    d_im.lemma(lemma, InferenceId::BV_BITBLAST_INTERNAL_BITBLAST_LEMMA);
  }
  else
  {
    TrustNode tlem =
        TrustNode::mkTrustLemma(lemma, d_bitblaster->getProofGenerator());
    d_im.trustedLemma(tlem, InferenceId::BV_BITBLAST_INTERNAL_BITBLAST_LEMMA);
  }
}

bool BVSolverBitblastInternal::needsEqualityEngine(CVC5_UNUSED EeSetupInfo& esi)
{
  // Disable equality engine if --bitblast=eager is enabled.
  return options().bv.bitblastMode != options::BitblastMode::EAGER;
}

void BVSolverBitblastInternal::postCheck(Theory::Effort level)
{
  // Only refine at full effort: at standard effort the propositional model is
  // partial and refining against it is wasted work.
  if (d_am == nullptr || level != Theory::Effort::EFFORT_FULL)
  {
    return;
  }

  if (d_state.isInConflict())
  {
    // The current model is irrelevant, the solver will backtrack.
    d_isModelConsistent = false;
    return;
  }

  // CEGAR refinement: check the current model against the abstracted
  // arithmetic terms and send the violated refinement lemmas. In contrast to
  // BVSolverBitblast, which bit-blasts to a SAT solver instance that is local
  // to the solver and thus runs its own refinement loop, we send the lemmas to
  // the inference manager and do a single refinement round per check. The
  // CDCL(T) loop of the theory engine is the refinement loop: as long as we
  // send lemmas, the engine will not conclude sat (and will not compute care
  // graphs or build a model based on an inconsistent model value).
  std::vector<Node> lemmas;
  d_am->check(lemmas);
  d_isModelConsistent = lemmas.empty();
  if (d_isModelConsistent)
  {
    Assert(d_am->isModelConsistent()) << "BV abstraction reported a consistent "
                                         "model but the model is inconsistent "
                                         "with an abstracted term";
    return;
  }
  Trace("bv-abstraction") << "postCheck: adding " << lemmas.size()
                          << " lemma(s)" << std::endl;
  bool sent = false;
  for (const Node& lem : lemmas)
  {
    sent |= d_im.lemma(lem, InferenceId::BV_ABSTRACTION_REFINEMENT);
  }
  // The abstraction module only ever adds lemmas that were not added before,
  // hence the inference manager cannot have dropped all of them as duplicates.
  // If it did, we would report an inconsistent model as sat.
  AlwaysAssert(sent) << "BV abstraction did not make progress";
}

bool BVSolverBitblastInternal::preNotifyFact(CVC5_UNUSED TNode atom,
                                             CVC5_UNUSED bool pol,
                                             CVC5_UNUSED TNode fact,
                                             CVC5_UNUSED bool isPrereg,
                                             CVC5_UNUSED bool isInternal)
{
  if (fact.getKind() == Kind::NOT)
  {
    fact = fact[0];
  }

  if (utils::isBVAtom(fact))
  {
    addBBLemma(fact);
  }
  else if (fact.getKind() == Kind::BITVECTOR_EAGER_ATOM)
  {
    TNode n = fact[0];

    NodeManager* nm = nodeManager();
    Node lemma = nm->mkNode(Kind::EQUAL, fact, n);

    if (!d_env.isTheoryProofProducing())
    {
      d_im.lemma(lemma, InferenceId::BV_BITBLAST_INTERNAL_EAGER_LEMMA);
    }
    else
    {
      TrustNode tlem =
          d_epg->mkTrustNode(lemma, ProofRule::BV_EAGER_ATOM, {}, {fact});
      d_im.trustedLemma(tlem, InferenceId::BV_BITBLAST_INTERNAL_EAGER_LEMMA);
    }

    std::unordered_set<Node> bv_atoms;
    utils::collectBVAtoms(n, bv_atoms);
    for (const Node& nn : bv_atoms)
    {
      addBBLemma(nn);
    }
  }

  // Disable the equality engine in --bitblast=eager mode. Otherwise return
  // false to enable equality engine reasoning in Theory.
  return options().bv.bitblastMode == options::BitblastMode::EAGER;
}

TrustNode BVSolverBitblastInternal::explain(TNode n)
{
  Trace("bv-bitblast-internal") << "explain called on " << n << std::endl;
  return d_im.explainLit(n);
}

bool BVSolverBitblastInternal::collectModelValues(TheoryModel* m,
                                                  const std::set<Node>& termSet)
{
  return d_bitblaster->collectModelValues(m, termSet);
}

Node BVSolverBitblastInternal::getValue(TNode node, bool initialize)
{
  if (node.isConst())
  {
    return node;
  }

  NodeManager* nm = node.getNodeManager();
  if (!d_bitblaster->hasBBTerm(node))
  {
    return initialize ? utils::mkConst(nm, utils::getSize(node), 0u) : Node();
  }

  Valuation& val = d_state.getValuation();

  std::vector<Node> bits;
  d_bitblaster->getBBTerm(node, bits);
  Integer value(0), one(1), zero(0), bit;
  for (size_t i = 0, size = bits.size(), j = size - 1; i < size; ++i, --j)
  {
    bool satValue;
    if (val.hasSatValue(bits[j], satValue))
    {
      bit = satValue ? one : zero;
    }
    else
    {
      if (!initialize) return Node();
      bit = zero;
    }
    value = value * 2 + bit;
  }
  return utils::mkConst(nm, bits.size(), value);
}

}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal
