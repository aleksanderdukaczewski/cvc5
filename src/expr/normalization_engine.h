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

  std::pair<Node, std::vector<Node>> normalizeFormula(Node& q);
  Node simplifyModuloConstraints(Node n);
  Node rewrite_qe(Node n);

 private:
  Integer getCoefficient(Node n, Node bound_var);
  Node normalizeCoefficients(Node& n,
                             Node& bv_node,
                             Integer& k,
                             std::vector<Node>& T);
  Node removeBoundVariable(Node n, Node bound_var, Integer& bound_var_coef);
  void getCoefficients(Node& n, Node& var_node, std::unordered_set<Node>& s_coefs);
  Node processModuloConstraint(Node& n);

  theory::Rewriter* d_rewriter;
};

}  // namespace cvc5::internal

#define CVC5_NORMALIZATION_ENGINE_H

#endif  // CVC5_NORMALIZATION_ENGINE_H
