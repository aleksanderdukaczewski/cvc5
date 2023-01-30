//
// Created by Aleksander Dukaczewski on 30/01/2023.
//

#include "expr/ordering_engine.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace expr {

OrderingEngine::OrderingEngine(smt::SmtDriverSingleCall& sdsc, std::vector<Node> terms) : d_sdsc(sdsc), d_terms(terms) {}

OrderingEngine::~OrderingEngine() {}

std::vector<Node> OrderingEngine::computeOrderings()
{
  std::vector<Ordering> fam;
  for (int j = 1; j <= d_terms.size(); ++j)
  {
    fam = computeFamily(j, fam);
  }
  return familyToNodes(fam);
}

std::vector<Ordering> OrderingEngine::computeFamily(int j, std::vector<Ordering>& prev_fam)
{
  std::vector<Ordering> fam;
  if (j == 1)
  {
    std::vector<Node> terms_v;
    std::vector<Kind> rels_v;
    terms_v.push_back(d_terms.at(0));
    Ordering ord = {terms_v, rels_v};
    fam.push_back(ord);
  }
  else
  {
    Node curr_term = d_terms.at(j-1);

    for (Ordering& ord : prev_fam)
    {
      for (int i = 1; i <= j-1; ++i)
      {
        Ordering new_ord = ord;
        new_ord.rels_v.insert(new_ord.rels_v.begin() + i-1,EQUAL);
        new_ord.terms_v.insert(new_ord.terms_v.begin() + i-1,curr_term);
        if (satisfiableOrdering(new_ord))
        {
          fam.push_back(new_ord);
        }

        new_ord = ord;
        new_ord.rels_v.insert(new_ord.rels_v.begin() + i-1, LT);
        new_ord.terms_v.insert(new_ord.terms_v.begin() + i-1, curr_term);
        if (satisfiableOrdering(new_ord))
        {
          fam.push_back(new_ord);
        }

        new_ord = ord;
        new_ord.rels_v.insert(new_ord.rels_v.begin() + i-1, LT);
        new_ord.terms_v.insert(new_ord.terms_v.begin() + i, curr_term);
        if (satisfiableOrdering(new_ord))
        {
          fam.push_back(new_ord);
        }
      }
    }
  }

  return fam;
}

Node OrderingEngine::orderingToNode(Ordering& ord)
{
  Node n;
  NodeManager* nm = NodeManager::currentNM();
  for (int i = 0; i < ord.terms_v.size(); ++i)
  {
    if (i == 0)
    {
      n = ord.terms_v[i];
    }
    else
    {
      n = nm->mkNode(kind::AND, n,nm->mkNode(ord.rels_v[i-1], ord.terms_v[i-1], ord.terms_v[i]));
    }
  }

  return n;
}

std::vector<Node> OrderingEngine::familyToNodes(std::vector<Ordering>& fam)
{
  std::vector<Node> nodes;
  for (Ordering& ord : fam)
  {
    nodes.push_back(orderingToNode(ord));
  }
  return nodes;
}

bool OrderingEngine::satisfiableOrdering(Ordering& ord)
{
  return d_sdsc.checkSat(std::vector<Node>{orderingToNode(ord) }) == Result::SAT;
}

}  // namespace expr
}  // namespace cvc5::internal
