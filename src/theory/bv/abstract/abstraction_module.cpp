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
#include "theory/bv/theory_bv.h"
#include "theory/bv/theory_bv_utils.h"

namespace cvc5::internal {
namespace theory {
namespace bv {
namespace abstract {

AbstractionModule::AbstractionModule(Env& env, TheoryBV* bv)
    : EnvObj(env),
      d_bv(bv),
      // Some lemma schemes are not valid for bit-vectors of size 1 or 2 (see
      // the size invariants asserted in abstraction_lemmas.cpp).
      // Following Bitwuzla, since for these sizes the bit-level circuits for
      // the abstracted operators are usually trivial, we never abstract below
      // size 3 instead of guarding each lemma separately, so the refinement
      // loop can apply every scheme unconditionally.
      d_threshold(std::max<uint64_t>(options().bv.bvAbstractionSize, 3)),
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
  // over-approximation, never silently re-expanded to `op` during rewriting
  // or model construction.
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

void AbstractionModule::check(std::vector<Node>& lemmas)
{
  NodeManager* nm = nodeManager();
  Node falseNode = nm->mkConst(false);
  uint64_t lim = std::max<uint64_t>(options().bv.bvAbstractionValueLimiter, 1);
  std::vector<Node> args(3);
  std::vector<Node> vals(3);
  for (const auto& [t, abstr] : d_absToTerm)
  {
    Kind kind = abstr.d_kind;
    Node x = abstr.d_x;
    Node s = abstr.d_s;
    Node valX = d_bv->getValue(x);
    Node valS = d_bv->getValue(s);
    Node valT = d_bv->getValue(t);
    Assert(valX.isConst() && valS.isConst() && valT.isConst())
        << "non-const operand value: " << valX << " " << valS << " " << valT;

    // The abstraction `t = op(x, s)` is consistent with the model iff the
    // actual operator applied to the operand values equals the value of `t`. If
    // so, there is nothing to refine for this term.
    Node value = rewrite(nm->mkNode(kind, valX, valS));
    if (value == valT)
    {
      continue;
    }

    // Tier 1/2: collect every Table-2 lemma scheme that is violated under the
    // current model, i.e., whose instantiation constant-folds to false when
    // x, s, t are substituted by their model values.
    //
    // Note: We do not use the Evaluator here since it only substitutes
    //       *variable* keys (it matches `args` entries only for nodes with
    //       isVar()) and leaves a compound key unsubstituted (thus would
    //       evaluate to a non-constant, and so miss the violation).
    args = {x, s, t};
    vals = {valX, valS, valT};
    size_t numLemmas = lemmas.size();
    for (const std::unique_ptr<AbstractionLemma>& lemma : d_lemmas.lemmas(kind))
    {
      Node inst = lemma->instance(x, s, t);
      if (inst.isNull())
      {
        inst = lemma->instance(valX, valS, valT, x, s, t);
      }
      if (inst.isNull())
      {
        continue;
      }
      Node subst =
          inst.substitute(args.begin(), args.end(), vals.begin(), vals.end());
      if (rewrite(subst) == falseNode)
      {
        lemmas.push_back(inst);
      }
    }
    // If a Table-2 lemma ruled out this spurious model, move on.
    if (lemmas.size() != numLemmas)
    {
      continue;
    }

    // No tier-1/2 lemma violated, fall back to value instantiation if we have
    // not exhausted the instantiation budget for this term yet.
    uint64_t budget = utils::getSize(t) / lim;
    if (d_valueInstCount[t] < budget)
    {
      // Tier 3: value instantiation. Rule out this single spurious model value
      // with (x = v_x AND s = v_s) => t = (v_x op v_s).
      Node prem = nm->mkNode(Kind::AND, x.eqNode(valX), s.eqNode(valS));
      lemmas.push_back(nm->mkNode(Kind::IMPLIES, prem, t.eqNode(value)));
      ++d_valueInstCount[t];
    }
    else
    {
      // Tier 4: bit-blasting fallback. Assert t = op(x, s), forcing the real
      // circuit to be bit-blasted; `t` is fully constrained from now on.
      lemmas.push_back(t.eqNode(nm->mkNode(kind, x, s)));
    }
  }
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
