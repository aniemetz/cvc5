/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Util functions for theory FP.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__FP__UTILS_H
#define CVC5__THEORY__FP__UTILS_H

#include "expr/type_node.h"
#include "util/integer.h"

namespace cvc5::internal {
namespace theory {
namespace fp {
namespace utils {

/**
 * Get the cardinality of the given FP type node.
 * @param type The type node.
 * @return The cardinality.
 */
Integer getCardinality(const TypeNode& type);

/**
 * Helper to create a function application on a fresh UF for the undefined zero
 * case of fp.min/fp.max. The UF is instantiated with the operands of the given
 * fp.min/fp.max node.
 * @param nm The node manager.
 * @param node The fp.min/fp.min_total/fp.max/fp.max_total node to create the
 *             UF and its application for.
 * @return The function application.
 */
Node minMaxUF(NodeManager* nm, TNode node);

/**
 * Helper to create a function application on a fresh UF for the undefined
 * cases of fp.to_ubv/fp.to_sbv. The UF is instantiated with the operands of
 * the given fp.to_ubv/fp.to_sbv node.
 * @param nm The node manager.
 * @param node The fp.to_sbv/fp.to_sbv_total/fp.to_ubv/fp.to_ubv_total node to
 *             create the UF and its application for.
 * @return The function application.
 */
Node ubvSbvUF(NodeManager* nm, TNode node);
}  // namespace utils
}  // namespace fp
}  // namespace theory
}  // namespace cvc5::internal
#endif
