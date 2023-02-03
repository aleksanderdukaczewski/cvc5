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
 * Step I: Normalise the formula and make all non-zero coefficients of bound variable either 1 or −1
*/
std::pair<Node, std::vector<Node>> normaliseFormula(Node n);

/**
 * Step II: Subdivide the formula according to term orderings and residue classes.
*/
Node subdivideFormula(Node n);

/**
 * Step III: Split the range of y into segments.
*/
Node splitRange(Node n);

/**
 * Step IV: Compute the number of solutions for each segment.
*/
Node computeNumSolutions(Node n);

/**
 * Step V: Sum up the solutions.
*/
Node sumSolutions(Node n);

/**
 * Get set of coefficients of the variable v in term n.
*/
void getCoefficients(Node n, Node bound_var_node, std::vector<Integer>& v_coefs);

/**
 * Check if two nodes evaluate to the same string representation (== operator implementation on Node only compares NodeValue pointers)
*/
bool sameVar(Node n, Node m);

/**
 * Recursive function that looks for inequalities of
 * the form t < 0, where the bound variable (from bound_var_node) 
 * could occur in the lhs. If such inequality is found, then extract 
 * the coefficient of bound variable and call substituteCoefficients on the LHS.
*/
Node normaliseCoefficients(Node n,
                           Node bound_var_node,
                           Integer k,
                           std::unordered_set<Node>& T);

Node removeBoundVariable(Node n, Node bound_var, Integer& bound_var_coef);

/**
 * Rewrite inequalities in node n to 
 * conjunctions of inequalities containing only '<'
*/
Node rewriteIq(Node n);

/**
 * Calculate T (the set of all y-free terms t such that t, y−t or −y+t belongs to lin(n)).
*/
void calculateTerms(Node n, Node var_node, std::unordered_set<Node>& s_terms);

Node removeBoundVariable(Node n, Node var_node, bool& negated);

void getModuli(Node n, std::vector<Integer>& s_mod);

std::unordered_set<Node> getOrderings(std::unordered_set<Node>& T);

}  // namespace expr
}  // namespace cvc5::internal

#endif