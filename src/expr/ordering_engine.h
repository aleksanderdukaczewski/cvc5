//
// Created by Aleksander Dukaczewski on 30/01/2023.
//

#include "cvc5_private.h"

#ifndef CVC5_ORDERINGS_H
#define CVC5_ORDERINGS_H

#include "expr/node.h"
#include "smt/smt_driver.h"
#include "smt/quant_elim_solver.h"
#include "theory/rewriter.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace expr {

struct Ordering
{
  std::vector<Node> terms;
  std::vector<Kind_t> rels;
};

class OrderingEngine
{
 public:
  OrderingEngine(std::vector<Node>& terms, theory::Rewriter* d_rewriter);
  ~OrderingEngine();
  std::vector<Node> familyToNodes(std::vector<Ordering>& fam);

  std::vector<Ordering> computeOrderings();
  std::vector<Node> getSegments(Node& bound_var, Ordering& ord);
  static std::vector<std::unordered_map<std::string, Node>>
  generateResidueClassMappings(
      int range, std::vector<Node>& variables);
  Node assignResidueClass(std::unordered_map<std::string, Node> assignment,
                          std::vector<Node> variables,
                          Integer m);
  static Node getTermAssignment(Node t,
                         std::unordered_map<std::string, Node>& assignment,
                         std::vector<Node>& variables);
  bool countSolutions(
      Ordering& ord,
      std::unordered_map<std::string, Node>& assignment,
      std::vector<Node>& variables,
      Integer& m,
      Node& q,
      std::vector<int>& p,
      std::vector<int>& r,
      std::vector<int>& c);
  Ordering makePairwiseNonEqual(Ordering& ord);
  Node evaluateOrdering(Node &q, Ordering& ord, Node& segment, std::unordered_map<std::string, Node>& assignment, std::vector<Node>& variables, Integer& m);
  Node orderingToNode(Ordering& ord);

 private:
  std::vector<Ordering> computeFamily(int j, std::vector<Ordering>& fam);
  bool satisfiableOrdering(Ordering& ord);
  static void getCombinationsRec(
      std::vector<int> assignment,
      std::vector<std::vector<int>>& combinations,
      int index,
      int r,
      int start,
      int end);

  std::vector<Node> d_terms;
  theory::Rewriter* d_rewriter;
};

}  // namespace expr
}  // namespace cvc5::internal
#endif  // CVC5_ORDERINGS_H