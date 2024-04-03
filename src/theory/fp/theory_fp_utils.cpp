/******************************************************************************
 * Top contributors (to current version):
 *   Martin Brain, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * [[ Add one-line brief description here ]]
 *
 * [[ Add lengthier description here ]]
 * \todo document this file
 */
#include "theory/fp/theory_fp_utils.h"
#include "expr/skolem_manager.h"
#include "expr/sort_to_term.h"

namespace cvc5::internal {
namespace theory {
namespace fp {
namespace utils {

Integer getCardinality(const TypeNode& type)
{
  Assert(type.getKind() == Kind::FLOATINGPOINT_TYPE);

  FloatingPointSize fps = type.getConst<FloatingPointSize>();

  /*
   * 1                    NaN
   * 2*1                  Infinities
   * 2*1                  Zeros
   * 2*2^(s-1)            Subnormal
   * 2*((2^e)-2)*2^(s-1)  Normal
   *
   *  = 1 + 2*2 + 2*((2^e)-1)*2^(s-1)
   *  =       5 + ((2^e)-1)*2^s
   */

  return Integer(5)
         + Integer(2).pow(fps.significandWidth())
               * (Integer(2).pow(fps.exponentWidth()) - Integer(1));
}

Node minMaxUF(NodeManager* nm, TNode node)
{
  Kind kind = node.getKind();
  Assert(kind == Kind::FLOATINGPOINT_MIN
         || kind == Kind::FLOATINGPOINT_MIN_TOTAL
         || kind == Kind::FLOATINGPOINT_MAX
         || kind == Kind::FLOATINGPOINT_MAX_TOTAL);

  TypeNode type = node.getType();
  Assert(type.getKind() == Kind::FLOATINGPOINT_TYPE);

  return nm->mkNode(Kind::APPLY_UF,
                    nm->getSkolemManager()->mkSkolemFunction(
                        kind == Kind::FLOATINGPOINT_MIN
                                || kind == Kind::FLOATINGPOINT_MIN_TOTAL
                            ? SkolemId::FP_MIN_ZERO
                            : SkolemId::FP_MAX_ZERO,
                        {nm->mkConst(SortToTerm(type))}),
                    node[0],
                    node[1]);
}

Node ubvSbvUF(NodeManager* nm, TNode node)
{
  Kind kind = node.getKind();
  Assert(kind == Kind::FLOATINGPOINT_TO_UBV
         || kind == Kind::FLOATINGPOINT_TO_UBV_TOTAL
         || kind == Kind::FLOATINGPOINT_TO_SBV
         || kind == Kind::FLOATINGPOINT_TO_SBV_TOTAL);

  TypeNode type = node.getType();
  Assert(type.getKind() == Kind::BITVECTOR_TYPE);

  return nm->mkNode(Kind::APPLY_UF,
                    nm->getSkolemManager()->mkSkolemFunction(
                        kind == Kind::FLOATINGPOINT_TO_SBV
                                || kind == Kind::FLOATINGPOINT_TO_SBV_TOTAL
                            ? SkolemId::FP_TO_SBV
                            : SkolemId::FP_TO_UBV,
                        {nm->mkConst(SortToTerm(type)),
                         nm->mkConst(SortToTerm(node[0].getType())),
                         nm->mkConst(SortToTerm(node[1].getType()))}),
                    node[0],
                    node[1]);
}
}  // namespace utils
}  // namespace fp
}  // namespace theory
}  // namespace cvc5::internal
