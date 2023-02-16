#include "cvc5_private.h"

#ifndef CVC5__EXPR__NODE_ALGORITHM_QE_H
#define CVC5__EXPR__NODE_ALGORITHM_QE_H

#include <unordered_map>
#include <vector>

#include "expr/node.h"
#include "expr/type_node.h"
#include "ordering_engine.h"
#include "theory/rewriter.h"

namespace cvc5::internal {
namespace expr {

/**
 * Normalise the coefficients of the bounded variable and produce an equivalent
 * formula in which all non-zero coefficients of bv are normalised to 1 or -1.
 * @param q
 * @return Normalised formula and set of terms T
 */
//std::pair<Node, std::vector<Node>> normaliseFormula(Node q);

/**
 * Find all coefficients of var_node in n and its children, add them to v_coefs.
 * @param n The node under investigation
 * @param var_node The node whose coefficients are collected
 * @param s_coefs The vector the coefficients are added to
 */
//void getCoefficients(Node& n,
//                     Node& bound_var_node,
//                     std::unordered_set<Node>& s_coefs);

Node simplifyModuloConstraints(Node n, theory::Rewriter* rr);

/**
 * Check if two nodes evaluate to the same string representation (== operator implementation on Node only compares NodeValue pointers)
*/
//bool sameVar(Node n, Node m);

/**
 * Recursive function that looks for inequalities of
 * the form t < 0, where the bound variable (from bound_var_node) 
 * could occur in the lhs. If such inequality is found, then extract 
 * the coefficient of bound variable and call substituteCoefficients on the LHS.
*/
//Node normaliseCoefficients(Node n,
//                           Node bound_var_node,
//                           Integer k,
//                           std::unordered_set<Node>& T);

//Node removeBoundVariable(Node n, Node bound_var, Integer& bound_var_coef);

/**
 * Rewrite inequalities in node n to 
 * conjunctions of inequalities containing only '<'
*/
Node rewrite_qe(Node n);

/**
 * Calculate T (the set of all y-free terms t such that t, y−t or −y+t belongs to lin(n)).
*/
void calculateTerms(Node n, Node var_node, std::unordered_set<Node>& s_terms);

Node removeBoundVariable(Node n, Node var_node, bool& negated);

void getModuli(Node n, std::unordered_set<Node>& s_mod);

std::unordered_set<Node> getOrderings(std::unordered_set<Node>& T);

}  // namespace expr
}  // namespace cvc5::internal

#endif