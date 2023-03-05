//
// Created by Aleksander Dukaczewski on 30/01/2023.
//

#include "expr/solution_counter.h"

#include "expr/node_algorithm.h"
#include "smt/solver_engine.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {

Node Ordering::getNode()
{
  Node n;
  NodeManager* nm = NodeManager::currentNM();
  if (terms.size() == 1)
  {
    return terms[0];
  }
  else
  {
    NodeBuilder ret(AND);
    for (int i = 1; i < terms.size(); ++i)
    {
      Node RHS = nm->mkNode(rels[i - 1], terms[i - 1], terms[i]);
      if (terms.size() == 2)
      {
        return RHS;
      }
      else
      {
        ret << RHS;
      }
    }
    return ret;
  }
}

SolutionCounter::SolutionCounter(theory::Rewriter* rewriter)
    : d_rewriter(rewriter)
{
}

SolutionCounter::~SolutionCounter() {}

std::vector<Ordering> SolutionCounter::computeOrderings(
    std::unordered_set<Node>& terms_s)
{
  std::vector<Ordering> fam;
  std::vector<Node> terms_v(terms_s.begin(), terms_s.end());
  for (int j = 1; j <= terms_s.size(); ++j)
  {
    std::unordered_set<Node> cache;
    fam = computeFamily(j, fam, terms_v, cache);
  }

  return fam;
}

std::vector<Ordering> SolutionCounter::computeFamily(
    int j,
    std::vector<Ordering>& prev_fam,
    std::vector<Node>& terms,
    std::unordered_set<Node>& cache)
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
        // Equivalent ordering may have been created, check in cache
        Node rewritten_new_ord = d_rewriter->rewrite(new_ord.getNode());
        const bool already_checked = cache.find(rewritten_new_ord) != cache.end();
        if (!already_checked && satisfiableOrdering(new_ord))
        {
          fam.push_back(new_ord);
          cache.insert(rewritten_new_ord);
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

std::vector<Node> SolutionCounter::familyToNodes(std::vector<Ordering>& fam)
{
  std::vector<Node> nodes;
  for (Ordering& ord : fam)
  {
    nodes.push_back(ord.getNode());
  }
  return nodes;
}

bool SolutionCounter::satisfiableOrdering(Ordering& ord)
{
  SolverEngine se;
  return se.checkSat(ord.getNode()) == Result::SAT;
}

Ordering SolutionCounter::makePairwiseNonEqual(Ordering& ord)
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

std::vector<Node> SolutionCounter::getSegments(Node& bv, Ordering& ord)
{
  std::vector<Node> segments;
  NodeManager* nm = NodeManager::currentNM();
  Ordering new_ord = makePairwiseNonEqual(ord);

  segments.push_back(nm->mkNode(LT, bv, new_ord.terms[0]));
  segments.push_back(nm->mkNode(EQUAL, bv, new_ord.terms[0]));
  for (int i = 1; i < new_ord.terms.size(); ++i)
  {
    segments.push_back(nm->mkNode(AND,
                                  nm->mkNode(LT, new_ord.terms[i - 1], bv),
                                  nm->mkNode(LT, bv, new_ord.terms[i])));
    segments.push_back(nm->mkNode(EQUAL, bv, new_ord.terms[i]));
  }
  segments.push_back(
      nm->mkNode(LT, new_ord.terms[new_ord.terms.size() - 1], bv));

  return segments;
}

Node SolutionCounter::assignResidueClass(
    std::unordered_map<std::string, Node> assignment,
    std::vector<Node> variables,
    Integer m)
{
//  Trace("smt-qe") << "assignResidueClass: calling on variables = " << variables
//                  << " m = " << m.toString() << " and assignment:" << std::endl;
//
//  for (auto& p : assignment)
//  {
//    Trace("smt-qe") << p.first << " : " << p.second << std::endl;
//  }

  NodeManager* nm = NodeManager::currentNM();
  NodeBuilder ret(AND);
  for (Node& var : variables)
  {
    Node assigned_var = assignment.at(var.toString());
    Node modulo_constraint = nm->mkNode(
        EQUAL,
        nm->mkNode(INTS_MODULUS, assigned_var, nm->mkConstInt(Rational(m))),
        nm->mkNode(INTS_MODULUS, var, nm->mkConstInt(Rational(m))));
    if (variables.size() == 1) return modulo_constraint;
    ret << modulo_constraint;
  }

//  Trace("smt-qe") << "assignResidueClass: returning ret = " << ret << std::endl;
  return ret;

  //  Node trueNode = nm->mkConst<bool>(true);
  //  Node ret = trueNode;
  //
  //  for (Node& var : variables)
  //  {
  //    Node assigned_var = assignment.at(var.toString());
  //    Node modulo_constraint = nm->mkNode(
  //        EQUAL,
  //        nm->mkNode(INTS_MODULUS, assigned_var, nm->mkConstInt(Rational(m))),
  //        nm->mkNode(INTS_MODULUS, var, nm->mkConstInt(Rational(m))));
  //    ret = (ret == trueNode) ? modulo_constraint
  //                            : nm->mkNode(AND, ret, modulo_constraint);
  //  }
  //
  //  Trace("smt-qe") << "assignResidueClass: returning ret = " << ret <<
  //  std::endl;
  //
  //  return ret;
}

std::vector<std::unordered_map<std::string, Node>>
SolutionCounter::generateResidueClassMappings(int range,
                                              std::vector<Node>& variables)
{
  std::vector<std::vector<int>> combinations;
  std::vector<int> assignment(variables.size(), 0);
  getCombinationsRec(assignment, combinations, 0, variables.size(), range - 1);

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

void SolutionCounter::getCombinationsRec(
    std::vector<int> assignment,
    std::vector<std::vector<int>>& combinations,
    int i,
    int target_length,
    int range)
{
  if (i == target_length)
  {
    combinations.push_back(assignment);
    return;
  }

  for (int j = 0; j <= range; ++j)
  {
    assignment[i] = j;
    getCombinationsRec(assignment, combinations, i + 1, target_length, range);
  }
}

Node SolutionCounter::evaluateInequalities(Node& conj, Node curr, Node& q)
{
  SolverEngine se;
  NodeManager* nm = NodeManager::currentNM();

  if (curr.getKind() == LT)
  {
    se.assertFormula(nm->mkNode(EXISTS, q[0], conj));
    Result isSat = se.checkSat(nm->mkNode(EXISTS, q[0], curr));

    Node ret = nm->mkConst<bool>(isSat == Result::SAT);
    return ret;
  }

  NodeBuilder nb(curr.getKind());
  for (int i = 0; i < curr.getNumChildren(); ++i)
  {
    nb << (curr[i].getNumChildren() > 0 ? evaluateInequalities(conj, curr[i], q)
                                        : curr[i]);
  }
  return nb;
}

Node SolutionCounter::evaluateModuloConstraints(Node& conj, Node curr, Node& q)
{
  NodeManager* nm = NodeManager::currentNM();
  Node bv = q[0][0];
  if (curr.getKind() == EQUAL
      && (curr[0].getKind() == INTS_MODULUS
          || curr[1].getKind() == INTS_MODULUS))
  {
//    Trace("smt-qe") << "evaluateModuloConstraints: calling on conj = " << conj
//                    << " and curr = " << curr << std::endl;
    //    std::unordered_set<Node> syms;
    //    expr::getSymbols(curr, syms);
    if (!expr::hasBoundVar(curr))
    {
      SolverEngine se;
//      se.assertFormula(nm->mkNode(EXISTS_EXACTLY, q[0], q[1], conj));
      se.assertFormula(nm->mkNode(EXISTS, q[0], conj));
//      Trace("smt-qe") << "Asserted conj" << std::endl;
//      Trace("smt-qe") << "Assertions: " << se.getAssertions() << std::endl;
      return nm->mkConst<bool>(se.checkSat(nm->mkNode(EXISTS, q[0], curr)) == Result::SAT);
    }
    else
    {
//      Trace("smt-qe") << "evaluateModuloConstraints: returningn curr = " << curr
//                      << std::endl;
      return curr;
    }
  }

  NodeBuilder nb(curr.getKind());
  for (int i = 0; i < curr.getNumChildren(); ++i)
  {
    nb << (curr[i].getNumChildren() > 0
               ? evaluateModuloConstraints(conj, curr[i], q)
               : curr[i]);
  }

  Node ret = nb;
  return ret;
}

Node SolutionCounter::evaluateOrdering(
    Node& q,
    Ordering& ord,
    Node& segment,
    std::unordered_map<std::string, Node>& assignment,
    std::vector<Node>& variables,
    Integer& m)
{
  NodeManager* nm = NodeManager::currentNM();
  Node bigGamma = nm->mkNode(
      AND, assignResidueClass(assignment, variables, m), ord.getNode());
  Node conj = nm->mkNode(
      AND, segment, bigGamma);

  Node ret = evaluateInequalities(conj, q[2], q);
  ret = evaluateModuloConstraints(conj, ret, q);
  return ret;
}

Node SolutionCounter::getTermAssignment(
    Node n,
    std::unordered_map<std::string, Node>& assignment,
    std::vector<Node>& variables)
{
  for (Node& var : variables)
  {
    TNode residue_class = assignment.at(var.toString());
    n = n.substitute(var, residue_class);
  }

  return n;
}

int SolutionCounter::extractInt(TNode& n)
{
  return n.getConst<Rational>().getNumerator().getSignedInt();
}

bool SolutionCounter::countSolutions(
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
  std::vector<Node> processed_t = makePairwiseNonEqual(ord).terms;
  int l = processed_t.size();
  int m_int = m.getSignedInt();

  std::pair<Node, Node> segs(nm->mkNode(LT, q[0][0], processed_t[0]),
                             nm->mkNode(LT, processed_t[l - 1], q[0][0]));

  Node ord1 = nm->mkNode(EXISTS, q[0], evaluateOrdering(q, ord, segs.first, assignment, variables, m));
  Node ord2 = nm->mkNode(EXISTS, q[0], evaluateOrdering(q, ord, segs.second, assignment, variables, m));
  if (se.checkSat(ord1) == Result::SAT || se.checkSat(ord2) == Result::SAT)
  {
    return false;
  }

  for (int j = 0; j < l; ++j)
  {
    Node seg = nm->mkNode(EQUAL, q[0][0], processed_t[j]);
    Node evaluated_ord =
        evaluateOrdering(q, ord, seg, assignment, variables, m);

    TNode r_t = d_rewriter->rewrite(
        getTermAssignment(processed_t[j], assignment, variables));
    evaluated_ord = evaluated_ord.substitute(q[0][0], r_t);

    c[j] = (d_rewriter->rewrite(evaluated_ord) == trueNode) ? 1 : 0;

    if (j == 0) continue;

    seg = nm->mkNode(AND,
                     nm->mkNode(LT, processed_t[j - 1], q[0][0]),
                     nm->mkNode(LT, q[0][0], processed_t[j]));

    if (expr::hasBoundVar(evaluated_ord))
    {
      for (int i = 0; i < m.getSignedInt(); ++i)
      {
        TNode i_node = nm->mkConstInt(i);
        Node rewritten =
            d_rewriter->rewrite(evaluated_ord.substitute(q[0][0], i_node));
        if (rewritten == trueNode)
        {
          p[j]++;
        }
      }
    }
    else
    {
      p[j] = m.getSignedInt();
    }

    TNode r_t_prev = d_rewriter->rewrite(
        getTermAssignment(processed_t[j - 1], assignment, variables));

    int u1_j = extractInt(r_t_prev);
    int u2_j = u1_j + 1;
    while (Integer(u2_j).euclidianDivideRemainder(Integer(m_int)) != Integer(extractInt(r_t)).euclidianDivideRemainder(Integer(m_int)))
    {
      u2_j++;
    }

    int r_j_prime = 0;
    for (int i = u1_j + 1; i <= u2_j - 1; ++i)
    {
      Node i_node = nm->mkConstInt(Rational(i));
      TNode temp = i_node;
      if (d_rewriter->rewrite(evaluated_ord.substitute(q[0][0], temp))
          == trueNode)
      {
        r_j_prime++;
      }
    }

    r[j] = -p[j] * (u2_j - u1_j) + m_int * r_j_prime;
  }

  return true;
}
}  // namespace cvc5::internal
