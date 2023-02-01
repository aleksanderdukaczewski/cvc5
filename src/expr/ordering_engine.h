//
// Created by Aleksander Dukaczewski on 30/01/2023.
//

#include "cvc5_private.h"

#ifndef CVC5_ORDERINGS_H
#define CVC5_ORDERINGS_H

#include "expr/node.h"
#include "smt/smt_driver.h"

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
  OrderingEngine(std::vector<Node> terms);
  ~OrderingEngine();

  std::vector<Ordering> computeOrderings();
  std::vector<Node> familyToNodes(std::vector<Ordering>& fam);
  Node orderingToNode(Ordering& ord);
  std::vector<Node> getSegments(Node bound_var, Ordering ord);

 private:
  std::vector<Ordering> computeFamily(int j, std::vector<Ordering>& fam);
  bool satisfiableOrdering(Ordering& ord);

  std::vector<Node> d_terms;
};

}  // namespace expr
}  // namespace cvc5::internal
#endif  // CVC5_ORDERINGS_H
