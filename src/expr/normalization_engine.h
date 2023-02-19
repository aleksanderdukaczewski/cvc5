#include "cvc5_private.h"

#ifndef CVC5_NORMALIZATION_ENGINE_H
#define CVC5_NORMALIZATION_ENGINE_H

#include "expr/node.h"
#include "theory/rewriter.h"
#include "normalization_engine.h"

namespace cvc5::internal {

class NormalizationEngine
{
 public:
  NormalizationEngine(theory::Rewriter* rewriter);
  ~NormalizationEngine();

  /**
   * Normalises the coefficients of the bound variable from q so that they are equal to -1 or 1,
   * and simplifies all modulo constraints
   * @param q The counting quantified formula we want to normalize
   * @return an equivalent formula in which all non-zero coefficients of the bound variable from are
   *         normalized to -1 or 1 and modulo constraints are simple
   */
  Node normalizeFormula(Node& q, std::vector<Node>& terms_v);
  /**
   * Using a depth-first solution, simplify modulo constraints in formula n as per Lemma 1
   * and recursively build a transformed abstract syntax tree.
   * @param n the formula to be rewritten
   * @return an equivalent formula where all modulo constraints are simple.
   */
  Node simplifyModuloConstraints(Node n);
  /**
   * Rewrite formulas with relations {LT, LEQ, GT, GEQ, EQUAL} into inequalities of the form t < 0
   * using a depth-first solution, recursively building the rewritten abstract syntax tree
   * @param n the formula to be rewritten
   * @return an equivalent formula where all inequalities and equalities
   *         have been rewritten into terms of the form t < 0
   */
  Node rewrite_qe(Node n);

 private:
  /**
   * Given a node where the bound variable occurs at most once, extract its coefficient.
   * @param n The formula under consideration
   * @param bv Node containing the bound variable
   * @return the coefficient of bv in n if present, else 0
   */
  Integer extractCoefficient(Node n, Node bv);
  /**
   * Normalize all coefficients of bv in occuring in n to -1 or 1. Using a depth-first
   * solution, recursively build an abstract syntax tree representing the resulting formula.
   * @param n node under investigation
   * @param bv node containing the bound variable
   * @param k a reference to an Integer object representing the lcm
   *          of the absolute values of all coefficients of bv appearing in n
   * @param terms_v the vector that all bv-free terms are added to
   * @return an equivalent formula in which all non-zero coefficients of the bound variable from are
   *         normalized to -1 or 1
   */
  Node normalizeCoefficients(Node& n,
                             Node& bv,
                             Integer& k,
                             std::vector<Node>& terms_v);
  /**
   * Remove the bound variable bv from node n, save the coefficient of bv in bv_coef
   * @param n the node under investigation
   * @param bv node containing the bound variable
   * @param bv_coef reference to an Integer object storing the bound variable's coefficient
   * @return node n after removing the bound variable.
   */
  Node removeBoundVariable(Node n, Node bv, Integer& bv_coef);
  /**
   * Given expression n and a variable var, search for var's coefficients
   * in nodes of the form (var), (-var), (x*var), (var*x)
   * @param n the node under investigation
   * @param var the variable node whose coefficients the function looks for
   * @param s_coefs the set which coefficients are added to
   */
  void getCoefficients(Node& n, Node& var, std::unordered_set<Node>& s_coefs);
  /**
   * Helper function for simplifyModuloCostraints. Given a modulo constraint n process it
   * into an equivalent combination of simple modulo constraints that do not
   * contain any new moduli or variables
   * @param n node representing a modulo constraint (= 0 (mod t q)), where q is a CONST_INTEGER
   * @return an equivalent combination of simple modulo constraints
   *         that do not introduce any new moduli or variables
   */
  Node processModuloConstraint(Node& n);

  /**
   * A pointer to a Rewriter object needed by the NormalizationEngine to
   * simplify arithmetic expressions in processModuloConstraint and
   * normalizeCoefficients.
   */
  theory::Rewriter* d_rewriter;
};

}  // namespace cvc5::internal

#define CVC5_NORMALIZATION_ENGINE_H

#endif  // CVC5_NORMALIZATION_ENGINE_H
