/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Martin Brain, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Expand definitions for floating-point arithmetic.
 */

#include "theory/fp/fp_expand_defs.h"

#include "expr/skolem_manager.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/fp/theory_fp_utils.h"
#include "util/floatingpoint.h"

namespace cvc5::internal {
namespace theory {
namespace fp {

FpExpandDefs::FpExpandDefs(context::UserContext* u) : d_toRealMap(u) {}

Node FpExpandDefs::toRealUF(Node node)
{
  Assert(node.getKind() == Kind::FLOATINGPOINT_TO_REAL);
  TypeNode t(node[0].getType());
  Assert(t.getKind() == Kind::FLOATINGPOINT_TYPE);

  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  ComparisonUFMap::const_iterator i(d_toRealMap.find(t));

  Node fun;
  if (i == d_toRealMap.end())
  {
    std::vector<TypeNode> args(1);
    args[0] = t;
    fun = sm->mkDummySkolem("floatingpoint_to_real_infinity_and_NaN_case",
                            nm->mkFunctionType(args, nm->realType()),
                            "floatingpoint_to_real_infinity_and_NaN_case");
    d_toRealMap.insert(t, fun);
  }
  else
  {
    fun = (*i).second;
  }
  return nm->mkNode(Kind::APPLY_UF, fun, node[0]);
}

TrustNode FpExpandDefs::expandDefinition(Node node)
{
  Trace("fp-expandDefinition")
      << "FpExpandDefs::expandDefinition(): " << node << std::endl;

  Node res = node;
  Kind kind = node.getKind();
  NodeManager* nm = NodeManager::currentNM();

  if (kind == Kind::FLOATINGPOINT_MIN || kind == Kind::FLOATINGPOINT_MAX)
  {
    Node iszero = nm->mkNode(Kind::AND,
                             nm->mkNode(Kind::FLOATINGPOINT_IS_ZERO, node[0]),
                             nm->mkNode(Kind::FLOATINGPOINT_IS_ZERO, node[1]));
    Node choice = nm->mkNode(Kind::ITE,
                             nm->mkNode(Kind::EQUAL,
                                        utils::minMaxUF(nm, node),
                                        theory::bv::utils::mkOne(1)),
                             node[0],
                             node[1]);
    res = nm->mkNode(Kind::ITE,
                     iszero,
                     choice,
                     nm->mkNode(kind == Kind::FLOATINGPOINT_MIN
                                    ? Kind::FLOATINGPOINT_MIN_TOTAL
                                    : Kind::FLOATINGPOINT_MAX_TOTAL,
                                node[0],
                                node[1]));
  }
  else if (kind == Kind::FLOATINGPOINT_TO_UBV)
  {
    res = nm->mkNode(nm->mkConst(FloatingPointToUBVTotal(
                         node.getOperator().getConst<FloatingPointToUBV>())),
                     node[0],
                     node[1],
                     utils::ubvSbvUF(nm, node));
  }
  else if (kind == Kind::FLOATINGPOINT_TO_SBV)
  {
    res = nm->mkNode(nm->mkConst(FloatingPointToSBVTotal(
                         node.getOperator().getConst<FloatingPointToSBV>())),
                     node[0],
                     node[1],
                     utils::ubvSbvUF(nm, node));
  }
  else if (kind == Kind::FLOATINGPOINT_TO_REAL)
  {
    res = NodeManager::currentNM()->mkNode(
        Kind::FLOATINGPOINT_TO_REAL_TOTAL, node[0], toRealUF(node));
  }

  if (res != node)
  {
    Trace("fp-expandDefinition") << "FpExpandDefs::expandDefinition(): " << node
                                 << " rewritten to " << res << std::endl;
    return TrustNode::mkTrustRewrite(node, res, nullptr);
  }
  return TrustNode::null();
}

}  // namespace fp
}  // namespace theory
}  // namespace cvc5::internal
