//
// Created by Aleksander Dukaczewski on 30/01/2023.
//

#include "expr/ordering_engine.h"

#include "expr/node_algorithm.h"
#include "smt/solver_engine.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {

OrderingEngine::OrderingEngine(theory::Rewriter* rewriter) : d_rewriter(rewriter) {}

OrderingEngine::~OrderingEngine() {}

std::vector<Ordering> OrderingEngine::computeOrderings(std::vector<Node>& terms)
{
  std::vector<Ordering> fam;
  for (int j = 1; j <= terms.size(); ++j)
  {
    fam = computeFamily(j, fam, terms);
  }

  return fam;
}

std::vector<Ordering> OrderingEngine::computeFamily(
    int j, std::vector<Ordering>& prev_fam, std::vector<Node>& terms)
{
  std::vector<Ordering> fam;
  if (j == 1)
  {
    std::vector<Node> terms_v;
    std::vector<Kind> rels_v;
    terms_v.push_back(terms.at(0));
    Ordering ord = {terms_v, rels_v};
    fam.push_back(ord);
  }
  else
  {
    Node curr_term = terms.at(j - 1);

    for (Ordering& ord : prev_fam)
    {
      for (int i = 1; i <= j - 1; ++i)
      {
        Ordering new_ord = ord;
        new_ord.rels.insert(new_ord.rels.begin() + i - 1, EQUAL);
        new_ord.terms.insert(new_ord.terms.begin() + i - 1, curr_term);
        if (satisfiableOrdering(new_ord))
        {
          fam.push_back(new_ord);
        }

        new_ord = ord;
        new_ord.rels.insert(new_ord.rels.begin() + i - 1, LT);
        new_ord.terms.insert(new_ord.terms.begin() + i - 1, curr_term);
        if (satisfiableOrdering(new_ord))
        {
          fam.push_back(new_ord);
        }

        new_ord = ord;
        new_ord.rels.insert(new_ord.rels.begin() + i - 1, LT);
        new_ord.terms.insert(new_ord.terms.begin() + i, curr_term);
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
  if (ord.terms.size() == 1)
  {
   return ord.terms[0];
  }
  else
  {
    for (int i = 1; i < ord.terms.size(); ++i)
    {
      Node RHS = nm->mkNode(ord.rels[i - 1], ord.terms[i - 1], ord.terms[i]);
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

Ordering OrderingEngine::makePairwiseNonEqual(Ordering& ord)
{
  std::vector<Node> terms;
  std::vector<Kind_t> rels;
  Ordering new_ord = {terms, rels};

  new_ord.terms.push_back(ord.terms[0]);
  for (int i = 1; i < ord.terms.size(); ++i)
  {
    if (ord.rels[i - 1] != EQUAL)
    {
      new_ord.rels.push_back(ord.rels[i - 1]);
      new_ord.terms.push_back(ord.terms[i]);
    }
  }

  return new_ord;
}

std::vector<Node> OrderingEngine::getSegments(Node& bound_var, Ordering& ord)
{
  std::vector<Node> segments;
  NodeManager* nm = NodeManager::currentNM();
  Ordering new_ord = makePairwiseNonEqual(ord);

  segments.push_back(nm->mkNode(LT, bound_var, new_ord.terms[0]));
  segments.push_back(nm->mkNode(EQUAL, bound_var, new_ord.terms[0]));
  for (int i = 1; i < new_ord.terms.size(); ++i)
  {
    segments.push_back(
        nm->mkNode(AND,
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
  std::vector<std::vector<int>> combinations;
  std::vector<int> assignment(variables.size(), 0);
  getCombinationsRec(
      assignment, combinations, 0, variables.size(), 0, range - 1);

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
    std::unordered_map<std::string, Node> assignment,
    std::vector<Node> variables,
    Integer m)
{
  NodeManager* nm = NodeManager::currentNM();
  Node ret = nm->mkConst<bool>(true);

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

void OrderingEngine::getCombinationsRec(
    std::vector<int> assignment,
    std::vector<std::vector<int>>& combinations,
    int index,
    int r,
    int start,
    int end)
{
  if (index == r)
  {
    combinations.push_back(assignment);
    return;
  }

  for (int j = start; j <= end; ++j)
  {
    assignment[index] = j;
    getCombinationsRec(assignment, combinations, index + 1, r, j, end);
  }
}

Node OrderingEngine::evaluateInequalities(Node& conj, Node cur, Node& q)
{
  SolverEngine se;
  NodeManager* nm = NodeManager::currentNM();

  if (cur.getKind() == LT)
  {
    se.assertFormula(conj);
    Result isSat = se.checkSat(nm->mkNode(EXISTS_EXACTLY, q[0], q[1], cur));
    return nm->mkConst<bool>(isSat == Result::SAT);
  }

  NodeBuilder nb(cur.getKind());
  for (int i = 0; i < cur.getNumChildren(); ++i)
  {
    nb << (cur[i].getNumChildren() > 0 ? evaluateInequalities(conj, cur[i], q)
                                       : cur[i]);
  }
  Node ret = nb;
  return ret;
}

Node OrderingEngine::evaluateModuloConstraints(Node& conj, Node cur, Node& q)
{
  NodeManager* nm = NodeManager::currentNM();
  if (cur.getKind() == EQUAL
      && (cur[0].getKind() == INTS_MODULUS || cur[1].getKind() == INTS_MODULUS))
  {
    std::unordered_set<Node> syms;
    expr::getSymbols(cur, syms);
    if (syms.find(q[0][0]) == syms.end())
    {
      SolverEngine se;
      if (se.checkSat(nm->mkNode(
              EXISTS_EXACTLY, q[0], q[1], nm->mkNode(AND, conj, cur)))
          == Result::SAT)
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
    nb << (cur[i].getNumChildren() > 0
               ? evaluateModuloConstraints(conj, cur[i], q)
               : cur[i]);
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
  NodeManager* nm = NodeManager::currentNM();
  Node bigGamma = nm->mkNode(AND, assignResidueClass(assignment, variables, m), orderingToNode(ord));
  Node conj = nm->mkNode(
      AND, nm->mkNode(kind::EXISTS_EXACTLY, q[0], q[1], segment), bigGamma);

  std::unordered_set<Node> freeVars;
  expr::getFreeVariables(segment, freeVars);

  Node ret = evaluateInequalities(conj, q[2], q);
  ret = evaluateModuloConstraints(conj, ret, q);
  return ret;
}

Node OrderingEngine::getTermAssignment(Node t,
                       std::unordered_map<std::string, Node>& assignment,
                       std::vector<Node>& variables)
{
  for (Node& var : variables)
  {
    TNode residue_class = assignment.at(var.toString());
    t = t.substitute(var, residue_class);
  }

  return t;
}

int extractInt(TNode& n)
{
  return n.getConst<Rational>().getNumerator().getSignedInt();
}

bool OrderingEngine::countSolutions(
    Ordering& ord,
    std::unordered_map<std::string, Node>& assignment,
    std::vector<Node>& variables,
    Integer& m,
    Node& q,
    std::vector<int>& p,
    std::vector<int>& r,
    std::vector<int>& c)
{
  NodeManager* nm = NodeManager::currentNM();
  SolverEngine se;
  Node trueNode = nm->mkConst<bool>(true);
  std::vector<Node> pairwise_ne_t = makePairwiseNonEqual(ord).terms;
  int l = pairwise_ne_t.size();
  int m_int = m.getSignedInt();

  std::pair<Node, Node> segs(nm->mkNode(LT, q[0][0], pairwise_ne_t[0]),
                             nm->mkNode(LT, pairwise_ne_t[l - 1], q[0][0]));
  if (se.checkSat(
          evaluateOrdering(q, ord, segs.first, assignment, variables, m))
          == Result::SAT
      || se.checkSat(
             evaluateOrdering(q, ord, segs.second, assignment, variables, m))
             == Result::SAT)
  {
    return false;
  }

  for (int j = 0; j < l; ++j)
  {
    Node seg = nm->mkNode(EQUAL, q[0][0], pairwise_ne_t[j]);
    Node evaluated_ord =
         evaluateOrdering(q, ord, seg, assignment, variables, m);

    TNode r_t = d_rewriter->rewrite(getTermAssignment(pairwise_ne_t[j], assignment, variables));
    evaluated_ord = evaluated_ord.substitute(q[0][0], r_t);

    c[j] = (d_rewriter->rewrite(evaluated_ord) == trueNode) ? 1 : 0;

    if (j == 0) continue;

    seg = nm->mkNode(AND,
                     nm->mkNode(LT, pairwise_ne_t[j - 1], q[0][0]),
                     nm->mkNode(LT, q[0][0], pairwise_ne_t[j]));

    for (int i = 0; i < m.getSignedInt(); ++i)
    {
      TNode i_node = nm->mkConstInt(i);
      if (d_rewriter->rewrite(evaluated_ord.substitute(q[0][0], i_node)) == trueNode)
      {
       p[j]++;
      }
    }

    TNode r_t_prev = d_rewriter->rewrite(getTermAssignment(pairwise_ne_t[j-1], assignment, variables));

    int u1_j = extractInt(r_t_prev);
    int u2_j = u1_j+1;
    while (u2_j % m_int != extractInt(r_t_prev) % m_int)
    {
      u2_j++;
    }

    int r_j_prime = 0;
    for (int i = u1_j+1; i <= u2_j-1; ++i)
    {
      Node i_node = nm->mkConstInt(Rational(i));
      TNode temp = i_node;
      if (d_rewriter->rewrite(evaluated_ord.substitute(q[0][0], temp)) == trueNode)
      {
       r_j_prime++;
      }
    }

    r[j] = -p[j] * (u2_j - u1_j) + m_int * r_j_prime;
  }

  return true;
}
}  // namespace cvc5::internal
