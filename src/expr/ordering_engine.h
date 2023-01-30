//
// Created by Aleksander Dukaczewski on 30/01/2023.
//

#include "cvc5_private.h"

#ifndef CVC5_ORDERINGS_H
#define CVC5_ORDERINGS_H

#include "expr/node.h"
#include "smt/smt_driver.h"

namespace cvc5::internal {
namespace expr {

struct Ordering
{
  std::vector<Node> terms_v;
  std::vector<kind::Kind_t> rels_v;
};

class OrderingEngine
{
 public:
  OrderingEngine(smt::SmtDriverSingleCall& sdcs, std::vector<Node> T);

  ~OrderingEngine();

  std::vector<Node> computeOrderings();

 private:
  std::vector<Ordering> computeFamily(int j, std::vector<Ordering>& fam);
  Node orderingToNode(Ordering& ord);
  std::vector<Node> familyToNodes(std::vector<Ordering>& fam);
  bool satisfiableOrdering(Ordering& ord);

  smt::SmtDriverSingleCall& d_sdsc;
  std::vector<Node> d_terms;
};


}  // namespace expr
}  // namespace cvc5::internal
#endif  // CVC5_ORDERINGS_H
