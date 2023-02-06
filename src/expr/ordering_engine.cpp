//
// Created by Aleksander Dukaczewski on 30/01/2023.
//

#include "expr/node_algorithm.h"
#include "expr/ordering_engine.h"

#include "smt/solver_engine.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace expr {

OrderingEngine::OrderingEngine(std::vector<Node> terms) : d_terms(terms) {}

OrderingEngine::~OrderingEngine() {}

std::vector<Ordering> OrderingEngine::computeOrderings()
{
  //  Trace("smt-qe") << "computeOrderings: trying to compute orderings for the
  //  set T = " << d_terms << std::endl;

  std::vector<Ordering> fam;
  for (int j = 1; j <= d_terms.size(); ++j)
  {
    fam = computeFamily(j, fam);
  }

  //  Trace("smt-qe") << "computeOrderings: finished all iterations of
  //  computeFamily" << d_terms << std::endl;

  return fam;
}

std::vector<Ordering> OrderingEngine::computeFamily(
    int j, std::vector<Ordering>& prev_fam)
{
  //  Trace("smt-qe") << "computeFamily: computing family for term number j = "
  //  << j << std::endl;

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
    Node curr_term = d_terms.at(j - 1);

    for (Ordering& ord : prev_fam)
    {
      for (int i = 1; i <= j - 1; ++i)
      {
        Ordering new_ord = ord;
        new_ord.rels.insert(new_ord.rels.begin() + i - 1, EQUAL);
        new_ord.terms.insert(new_ord.terms.begin() + i - 1, curr_term);
        if (satisfiableOrdering(new_ord))
        {
          //          Trace("smt-qe") << "ADDING ORDERING TO FAMILY" <<
          //          std::endl;
          fam.push_back(new_ord);
        }

        new_ord = ord;
        new_ord.rels.insert(new_ord.rels.begin() + i - 1, LT);
        new_ord.terms.insert(new_ord.terms.begin() + i - 1, curr_term);
        if (satisfiableOrdering(new_ord))
        {
          //          Trace("smt-qe") << "ADDING ORDERING TO FAMILY" <<
          //          std::endl;
          fam.push_back(new_ord);
        }

        new_ord = ord;
        new_ord.rels.insert(new_ord.rels.begin() + i - 1, LT);
        new_ord.terms.insert(new_ord.terms.begin() + i, curr_term);
        if (satisfiableOrdering(new_ord))
        {
          //          Trace("smt-qe") << "ADDING ORDERING TO FAMILY" <<
          //          std::endl;
          fam.push_back(new_ord);
        }
      }
    }
  }

  return fam;
}

Node OrderingEngine::orderingToNode(Ordering& ord)
{
  //  Trace("smt-qe") << "satisfiableOrdering: considering ordering with terms:
  //  " << ord.terms << std::endl << " and relations: ";

  //  for (auto& k : ord.rels)
  //  {
  //    Trace("smt-qe") << kind::toString(k) << " ";
  //  }
  //  Trace("smt-qe") << std::endl;

  Node n;
  NodeManager* nm = NodeManager::currentNM();
  for (int i = 1; i < ord.terms.size(); ++i)
  {
    Node RHS = nm->mkNode(ord.rels[i - 1], ord.terms[i - 1], ord.terms[i]);
    //    Trace("smt-qe") << "new RHS = " << RHS << " and LHS = " << n <<
    //    std::endl;
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

std::vector<Node> OrderingEngine::getSegments(Node& bound_var, Ordering& ord)
{
  std::vector<Node> segments;
  NodeManager* nm = NodeManager::currentNM();
  std::vector<Node> terms;
  std::vector<Kind_t> rels;
  Ordering new_ord = {terms, rels};

  Trace("smt-qe") << "getSegments: calling on bound_var = " << bound_var << " of kind: " << bound_var.getKind() << " and ord = " << orderingToNode(ord) << std::endl;

  new_ord.terms.push_back(ord.terms[0]);
  for (int i = 1; i < ord.terms.size(); ++i)
  {
    if (ord.rels[i-1] != EQUAL)
    {
      new_ord.rels.push_back(ord.rels[i-1]);
      new_ord.terms.push_back(ord.terms[i]);
    }
  }

  Trace("smt-qe") << "getSegments: new ordering = " << orderingToNode(new_ord) << std::endl;

  segments.push_back(nm->mkNode(LT, bound_var, new_ord.terms[0]));
  segments.push_back(nm->mkNode(EQUAL, bound_var, new_ord.terms[0]));
  for (int i = 1; i < new_ord.terms.size(); ++i)
  {
    segments.push_back(nm->mkNode(AND,
                             nm->mkNode(LT, new_ord.terms[i - 1], bound_var),
                             nm->mkNode(LT, bound_var, new_ord.terms[i])));
    segments.push_back(nm->mkNode(EQUAL, bound_var, new_ord.terms[i]));
  }
  segments.push_back(
      nm->mkNode(LT, new_ord.terms[new_ord.terms.size() - 1], bound_var));

  return segments;
}

std::vector<std::unordered_map<std::string, Node>>
OrderingEngine::generateResidueClassMappings(int range,
                                             std::vector<Node>& variables)
{
  Trace("smt-qe") << "generateResidueClassMappings: call on variables : "
                  << variables << std::endl;
  std::vector<std::vector<int>> combinations;
  std::vector<int> assignment(variables.size(), 0);
  getCombinationsRec(
      assignment, combinations, 0, variables.size(), 0, range - 1);

  //  Trace("smt-qe") << "Generated combinations : " << std::endl;
  //  for (auto& as : combinations)
  //  {
  //    for (int i : as)
  //    {
  //      Trace("smt-qe") << i << " ";
  //    }
  //    Trace("smt-qe") << std::endl;
  //  }

  NodeManager* nm = NodeManager::currentNM();
  std::vector<std::unordered_map<std::string, Node>> mappings;
  for (auto& comb : combinations)
  {
    std::unordered_map<std::string, Node> mapping;
    for (int i = 0; i < comb.size(); ++i)
    {
      std::pair<std::string, Node> p(variables[i].toString(),
                                     nm->mkConstInt(Rational(comb[i])));
      mapping.insert(p);
    }
    mappings.push_back(mapping);
  }

  return mappings;
}

Node OrderingEngine::assignResidueClass(
    Ordering ord,
    std::unordered_map<std::string, Node> assignment,
    std::vector<Node> variables,
    Integer m)
{
  Node ret = orderingToNode(ord);
  NodeManager* nm = NodeManager::currentNM();

  for (Node& var : variables)
  {
    Node assigned_var = assignment.at(var.toString());
    Node modulo_constraint = nm->mkNode(
        EQUAL,
        nm->mkNode(INTS_MODULUS, assigned_var, nm->mkConstInt(Rational(m))),
        nm->mkNode(INTS_MODULUS, var, nm->mkConstInt(Rational(m))));
    ret = nm->mkNode(AND, ret, modulo_constraint);
  }

  return ret;
}

Node evaluateInequalities(Node& conj, Node cur, Node& q)
{
//  Trace("smt-qe") << "evaluateInequality: cur = " << cur << ", conj = " << conj << std::endl;

  if (cur.getKind() == LT)
  {
    Trace("smt-qe") << "INEQUALITY FOUND! cur = " << cur  << std::endl;

    SolverEngine se;
    NodeManager* nm = NodeManager::currentNM();
//    se.assertFormula(nm->mkNode(EXISTS_EXACTLY, q[0], q[1], conj));
    se.assertFormula(conj);
    Trace("smt-qe") << "evaluateInequalities: current assertions: " << se.getAssertions() << std::endl;
    Result isSat = se.checkSat(nm->mkNode(EXISTS_EXACTLY, q[0], q[1], cur));
    if (isSat == Result::SAT)
    {
      Trace("smt-qe") << "SAT! " << std::endl;
      return nm->mkConst<bool>(true);
    }
    else
    {
      Trace("sme-qe") << "UNSAT! " << std::endl;
      return nm->mkConst<bool>(false);
    }
  }

  NodeBuilder nb(cur.getKind());
  for (int i = 0; i < cur.getNumChildren(); ++i)
  {
//    Trace("smt-qe") << "Making a recursive call for cur[" << i << "] = " << cur[i] << " of kind = " << cur[i].getKind() << " , cur = " << cur  << std::endl;

    nb << (cur[i].getNumChildren() > 0 ? evaluateInequalities(conj, cur[i], q) : cur[i]);
  }
  Node ret = nb;
  return ret;
}

Node evaluateModuloConstraints(Node& conj, Node cur, Node& q)
{
  NodeManager* nm = NodeManager::currentNM();
  if (cur.getKind() == EQUAL && (cur[0].getKind() == INTS_MODULUS || cur[1].getKind() == INTS_MODULUS))
  {
    std::unordered_set<Node> syms;
    getSymbols(cur, syms);
    Trace("smt-qe") << "evaluateModuloConstraints: " << syms << std::endl;
    if (syms.find(q[0][0]) == syms.end())
    {
      SolverEngine se;
      if (se.checkSat(nm->mkNode(EXISTS_EXACTLY, q[0], q[1], nm->mkNode(AND, conj, cur))) == Result::SAT)
      {
        return nm->mkConst<bool>(true);
      }
      else
      {
        return nm->mkConst<bool>(false);
      }
    }
    else
    {
      return cur;
    }
  }

  NodeBuilder nb(cur.getKind());
  for (int i = 0; i < cur.getNumChildren(); ++i)
  {
    nb << (cur[i].getNumChildren() > 0 ? evaluateModuloConstraints(conj, cur[i], q) : cur[i]);
  }

  Node ret = nb;
  return ret;
}

Node OrderingEngine::evaluateOrdering(
    Node& q,
    Ordering& ord,
    Node& segment,
    std::unordered_map<std::string, Node>& assignment,
    std::vector<Node>& variables,
    Integer& m)
{
  Node bigGamma = assignResidueClass(ord, assignment, variables, m);
  NodeManager* nm = NodeManager::currentNM();
  Node conj = nm->mkNode(AND, nm->mkNode(kind::EXISTS_EXACTLY, q[0], q[1], segment), bigGamma);

//  Trace("smt-qe") << "Segment: " << segment << " has type " << segment.getKind() << " and  children " << std::endl
//          << segment[0] << segment[0].getKind() << segment[1].getKind() << std::endl;
  std::unordered_set<Node> freeVars;
  getFreeVariables(segment, freeVars);

  Trace("smt-qe") << "evaluateOrdering: calculating with bigGamma = " << bigGamma << " and segment = " << segment << std::endl;

  SolverEngine se;
//  Trace("smt-qe") << "Conjunction conj = " << conj << " is " << (se.checkSat(conj) == Result::SAT ? "satisfiable" : "unsatisfiable") << std::endl;

  if (se.checkSat(conj) != Result::SAT)
  {
    Trace("smt-qe") << "BIG_GAMMA IS UNSAT" << std::endl;
  }
  else
  {
    Trace("smt-qe") << "BIG_GAMMA IS SAT" << std::endl;
  }

  Node ret = evaluateInequalities(conj, q[2], q);
  ret = evaluateModuloConstraints(conj, ret, q);
  return ret;
}

void OrderingEngine::getCombinationsRec(
    std::vector<int> assignment,
    std::vector<std::vector<int>>& combinations,
    int index,
    int r,
    int start,
    int end)
{
  Trace("smt-qe") << "getCombinationsRec: call with index = " << index
                  << std::endl
                  << "with r = " << r << " and with assignment: " << std::endl;

  if (index == r)
  {
    Trace("smt-qe") << "SAVING ASSIGNMENT: ";
    for (int i : assignment)
    {
      Trace("smt-qe") << i << " ";
    }
    Trace("smt-qe") << std::endl;
    combinations.push_back(assignment);
    return;
  }

  for (int j = start; j <= end; j++)
  {
    Trace("smt-qe") << "j = " << j << std::endl;
    assignment[index] = j;
    getCombinationsRec(assignment, combinations, index + 1, r, j, end);
  }
  return;
}

}  // namespace expr
}  // namespace cvc5::internal
