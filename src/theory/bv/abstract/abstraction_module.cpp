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

#include "expr/node_manager.h"
#include "options/bv_options.h"
#include "theory/bv/theory_bv_utils.h"

namespace cvc5::internal {
namespace theory {
namespace bv {
namespace abstract {

AbstractionModule::AbstractionModule(Env& env)
    : EnvObj(env),
      d_threshold(options().bv.bvAbstractionSize),
      d_lemmas(nodeManager())
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
  return utils::getSize(n) >= d_threshold;
}

Node AbstractionModule::abstractTerm(TNode op)
{
  auto it = d_termToAbs.find(op);
  if (it != d_termToAbs.end())
  {
    return it->second;
  }
  // A fresh, opaque constant of the same sort. It is deliberately *not* a
  // purification skolem: the abstraction must stay an unconstrained
  // over-approximation, never silently re-expanded to `op` during rewriting or
  // model construction.
  Node t = NodeManager::mkDummySkolem("bvabs", op.getType());
  d_termToAbs.emplace(op, t);
  d_absToTerm.emplace(t, AbstractedTerm{op.getKind(), op[0], op[1]});
  return t;
}

Node AbstractionModule::abstract(TNode fact)
{
  NodeManager* nm = nodeManager();
  std::vector<TNode> visit{fact};
  do
  {
    TNode cur = visit.back();
    auto it = d_cache.find(cur);
    if (it == d_cache.end())
    {
      // First time we see `cur`: mark it and queue its children.
      d_cache.emplace(cur, Node::null());
      visit.insert(visit.end(), cur.begin(), cur.end());
      continue;
    }
    if (it->second.isNull())
    {
      // Children are processed; rebuild `cur` from their abstractions.
      bool childChanged = false;
      std::vector<Node> children;
      if (cur.getMetaKind() == kind::metakind::PARAMETERIZED)
      {
        children.push_back(cur.getOperator());
      }
      for (const TNode& child : cur)
      {
        Node abstractedChild = d_cache.at(child);
        Assert(!abstractedChild.isNull());
        childChanged = childChanged || abstractedChild != child;
        children.push_back(abstractedChild);
      }
      Node ret = childChanged ? nm->mkNode(cur.getKind(), children) : Node(cur);
      // Abstract `ret` itself if it is an abstractable arithmetic term.
      if (abstractable(ret))
      {
        ret = abstractTerm(ret);
      }
      d_cache[cur] = ret;
    }
    visit.pop_back();
  } while (!visit.empty());
  return d_cache.at(fact);
}

bool AbstractionModule::isAbstraction(TNode n) const
{
  return d_absToTerm.find(n) != d_absToTerm.end();
}

const AbstractedTerm& AbstractionModule::getAbstractedTerm(TNode n) const
{
  auto it = d_absToTerm.find(n);
  Assert(it != d_absToTerm.end());
  return it->second;
}

}  // namespace abstract
}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal
