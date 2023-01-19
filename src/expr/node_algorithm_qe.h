#include "cvc5_private.h"

#ifndef CVC5__EXPR__NODE_ALGORITHM_QE_H
#define CVC5__EXPR__NODE_ALGORITHM_QE_H

#include <unordered_map>
#include <vector>

#include "expr/node.h"
#include "expr/type_node.h"

namespace cvc5::internal {
namespace expr {

/**
 * Convert 
*/
Node normalise(Node n);

/**
 * Get set of coefficients of the variable v in term n.
*/
void getCoefficients(std::string boundVarName, Node n, std::vector<Integer>& s_coefs);

Integer getLcmCoefficients(std::string boundVarName, Node n);

/**
 * Rewrite inequalities in node n to conjunctions of inequalities containing only '<'
*/
Node rewriteIq(Node n);

/**
 * Convert modulo constraints (of the form a mod q = b mod q)
*/
Node simplifyMod();


}  // namespace expr
}  // namespace cvc5::internal

#endif