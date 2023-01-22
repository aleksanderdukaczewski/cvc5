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
 * Normalise the formula and make all non-zero coefficients of bound variable either 1 or −1
 * Step 1 of the procedure 
*/
Node normaliseFormula(Node n);

/**
 * Subdivide the formula according to term orderings and residue classes.
 * Step 2 of the procedure
*/
Node subdivideFormula(Node n);

/**
 * Get set of coefficients of the variable v in term n.
*/
void getCoefficients(Node n, Node var_node, std::vector<Integer>& v_coefs);

/**
 * Check if two nodes evaluate to the same string representation (== operator implementation on Node only compares NodeValue pointers)
*/
bool sameVar(Node n, Node m);

/**
 * 
*/
Node substituteCoefficients(Node n, Integer k, Integer a, Node var_node);

Node normaliseCoefficients(Node n, Integer k, Node var_node);

/**
 * Rewrite inequalities in node n to 
 * conjunctions of inequalities containing only '<'
*/
Node rewriteIq(Node n);

}  // namespace expr
}  // namespace cvc5::internal

#endif