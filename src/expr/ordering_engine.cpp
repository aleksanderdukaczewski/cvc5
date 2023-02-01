//
// Created by Aleksander Dukaczewski on 30/01/2023.
//

#include "expr/ordering_engine.h"
#include "smt/solver_engine.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace expr {

OrderingEngine::OrderingEngine(std::vector<Node> terms) : d_terms(terms) {}

OrderingEngine::~OrderingEngine() {}

std::vector<Ordering> OrderingEngine::computeOrderings()
{
//  Trace("smt-qe") << "computeOrderings: trying to compute orderings for the set T = " << d_terms << std::endl;

  std::vector<Ordering> fam;
  for (int j = 1; j <= d_terms.size(); ++j)
  {
    fam = computeFamily(j, fam);
  }

//  Trace("smt-qe") << "computeOrderings: finished all iterations of computeFamily" << d_terms << std::endl;

  return fam;
}

std::vector<Ordering> OrderingEngine::computeFamily(int j, std::vector<Ordering>& prev_fam)
{
//  Trace("smt-qe") << "computeFamily: computing family for term number j = " << j << std::endl;

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
        new_ord.rels.insert(new_ord.rels.begin() + i-1,EQUAL);
        new_ord.terms.insert(new_ord.terms.begin() + i-1,curr_term);
        if (satisfiableOrdering(new_ord))
        {
//          Trace("smt-qe") << "ADDING ORDERING TO FAMILY" << std::endl;
          fam.push_back(new_ord);
        }

        new_ord = ord;
        new_ord.rels.insert(new_ord.rels.begin() + i-1, LT);
        new_ord.terms.insert(new_ord.terms.begin() + i-1, curr_term);
        if (satisfiableOrdering(new_ord))
        {
//          Trace("smt-qe") << "ADDING ORDERING TO FAMILY" << std::endl;
          fam.push_back(new_ord);
        }

        new_ord = ord;
        new_ord.rels.insert(new_ord.rels.begin() + i-1, LT);
        new_ord.terms.insert(new_ord.terms.begin() + i, curr_term);
        if (satisfiableOrdering(new_ord))
        {
//          Trace("smt-qe") << "ADDING ORDERING TO FAMILY" << std::endl;
          fam.push_back(new_ord);
        }
      }
    }
  }

  return fam;
}

Node OrderingEngine::orderingToNode(Ordering& ord)
{
//  Trace("smt-qe") << "satisfiableOrdering: considering ordering with terms: " << ord.terms << std::endl << " and relations: ";

//  for (auto& k : ord.rels)
//  {
//    Trace("smt-qe") << kind::toString(k) << " ";
//  }
//  Trace("smt-qe") << std::endl;

  Node n;
  NodeManager* nm = NodeManager::currentNM();
  for (int i = 1; i < ord.terms.size(); ++i)
  {
    Node RHS = nm->mkNode(ord.rels[i-1], ord.terms[i-1], ord.terms[i]);
//    Trace("smt-qe") << "new RHS = " << RHS << " and LHS = " << n << std::endl;
    if (i == 1)
    {
      n = RHS;
    }
    else
    {
      n = nm->mkNode(kind::AND, n, RHS);
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
  SolverEngine se;
  return se.checkSat(orderingToNode(ord)) == Result::SAT;
}

std::vector<Node> getSegments(Node bound_var, Ordering ord)
{
  std::vector<Node> seg;
  NodeManager* nm = NodeManager::currentNM();
  std::vector<Node> terms;
  std::vector<Kind_t> rels;
  Ordering new_ord = {terms, rels};

  ord.rels.push_back(ord.rels[0]);
  for (int i = 0; i < ord.rels.size(); ++i)
  {
    if (ord.rels[i] != EQUAL)
    {
      new_ord.rels.push_back(ord.rels[i]);
      new_ord.terms.push_back(ord.terms[i+1]);
    }
  }

  seg.push_back(nm->mkNode(LT, bound_var, new_ord.terms[0]));
  seg.push_back(nm->mkNode(EQUAL, bound_var, new_ord.terms[0]));
  for (int i = 1; i < new_ord.terms.size(); ++i)
  {
    seg.push_back(nm->mkNode(AND,
        nm->mkNode(LT, new_ord.terms[i-1], bound_var),
        nm->mkNode(LT, bound_var, new_ord.terms[i])
        ));
    seg.push_back(nm->mkNode(EQUAL, bound_var, new_ord.terms[i]));
  }
  seg.push_back(nm->mkNode(LT, new_ord.terms[new_ord.terms.size()-1], bound_var));

  return seg;
}

}  // namespace expr
}  // namespace cvc5::internal
