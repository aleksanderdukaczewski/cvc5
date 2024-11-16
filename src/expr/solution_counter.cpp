//
// Created by Aleksander Dukaczewski on 30/01/2023.
//

#include "expr/solution_counter.h"

#include "expr/node_algorithm.h"
#include "smt/solver_engine.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {

Ordering::Ordering(std::vector<Node> terms, std::vector<Kind_t> rels) :
      d_terms(terms), d_rels(rels)
{
}

Ordering::~Ordering(){}

Node Ordering::getNode()
{
  Node n;
  NodeManager* nm = NodeManager::currentNM();
  if (d_terms.size() == 1)
  {
    return d_terms[0];
  }
  else
  {
    NodeBuilder ret(Kind::AND);
    for (int i = 1; i < d_terms.size(); ++i)
    {
      Node RHS = nm->mkNode(d_rels[i - 1], d_terms[i - 1], d_terms[i]);
      if (d_terms.size() == 2)
      {
        return RHS;
      }
      else
      {
        ret << RHS;
      }
    }
    return ret.getNumChildren() == 1 ? ret[0] : ret;
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
    Ordering ord(terms_v, rels_v);
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
        new_ord.d_rels.insert(new_ord.d_rels.begin() + i - 1, Kind::EQUAL);
        new_ord.d_terms.insert(new_ord.d_terms.begin() + i - 1, curr_term);
        // Equivalent ordering may have been created, check in cache
        Node rewritten_new_ord = d_rewriter->rewrite(new_ord.getNode());
        const bool already_checked = cache.find(rewritten_new_ord) != cache.end();
        if (!already_checked && new_ord.isSatisfiable())
        {
          fam.push_back(new_ord);
          cache.insert(rewritten_new_ord);
        }

        new_ord = ord;
        new_ord.d_rels.insert(new_ord.d_rels.begin() + i - 1, Kind::LT);
        new_ord.d_terms.insert(new_ord.d_terms.begin() + i - 1, curr_term);
        if (new_ord.isSatisfiable())
        {
          fam.push_back(new_ord);
        }

        new_ord = ord;
        new_ord.d_rels.insert(new_ord.d_rels.begin() + i - 1, Kind::LT);
        new_ord.d_terms.insert(new_ord.d_terms.begin() + i, curr_term);
        if (new_ord.isSatisfiable())
        {
          fam.push_back(new_ord);
        }
      }
    }
  }

  return fam;
}

std::vector<Node> Ordering::familyToNodes(std::vector<Ordering>& fam)
{
  std::vector<Node> nodes;
  for (Ordering& ord : fam)
  {
    nodes.push_back(ord.getNode());
  }
  return nodes;
}

bool Ordering::isSatisfiable()
{
  SolverEngine se;
  return se.checkSat(getNode()) == Result::SAT;
}

Ordering Ordering::makePairwiseNonEqual()
{
  std::vector<Node> terms;
  std::vector<Kind_t> rels;
  Ordering new_ord = {terms, rels};

  new_ord.d_terms.push_back(d_terms[0]);
  for (int i = 1; i < d_terms.size(); ++i)
  {
    if (d_rels[i - 1] != Kind::EQUAL)
    {
      new_ord.d_rels.push_back(d_rels[i - 1]);
      new_ord.d_terms.push_back(d_terms[i]);
    }
  }

  return new_ord;
}

std::vector<Node> SolutionCounter::getSegments(Node& bv, Ordering& ord)
{
  std::vector<Node> segments;
  NodeManager* nm = NodeManager::currentNM();
  Ordering new_ord = ord.makePairwiseNonEqual();

  segments.push_back(nm->mkNode(Kind::LT, bv, new_ord.d_terms[0]));
  segments.push_back(nm->mkNode(Kind::EQUAL, bv, new_ord.d_terms[0]));
  for (int i = 1; i < new_ord.d_terms.size(); ++i)
  {
    segments.push_back(nm->mkNode(Kind::AND,
                                  nm->mkNode(Kind::LT, new_ord.d_terms[i - 1], bv),
                                  nm->mkNode(Kind::LT, bv, new_ord.d_terms[i])));
    segments.push_back(nm->mkNode(Kind::EQUAL, bv, new_ord.d_terms[i]));
  }
  segments.push_back(
      nm->mkNode(Kind::LT, new_ord.d_terms[new_ord.d_terms.size() - 1], bv));

  return segments;
}

Node SolutionCounter::assignResidueClass(
    std::unordered_map<std::string, Node> assignment,
    std::vector<Node> variables,
    Integer m)
{
  NodeManager* nm = NodeManager::currentNM();
  NodeBuilder ret(Kind::AND);
  for (Node& var : variables)
  {
    Node assigned_var = assignment.at(var.toString());
    Node modulo_constraint = nm->mkNode(
        Kind::EQUAL,
        nm->mkNode(Kind::INTS_MODULUS, assigned_var, nm->mkConstInt(Rational(m))),
        nm->mkNode(Kind::INTS_MODULUS, var, nm->mkConstInt(Rational(m))));
    ret << modulo_constraint;
  }

  switch (ret.getNumChildren())
  {
    case 0:
      return nm->mkConst(true);
    case 1:
      return ret[0];
    default:
      return ret;
  }

//  return ret.getNumChildren() == 1 ? ret[0] : ret;
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
    std::vector<int> combination,
    std::vector<std::vector<int>>& combinations,
    int i,
    int target_length,
    int range)
{
  if (i == target_length)
  {
    combinations.push_back(combination);
    return;
  }

  for (int j = 0; j <= range; ++j)
  {
    combination[i] = j;
    getCombinationsRec(combination, combinations, i + 1, target_length, range);
  }
}

Node SolutionCounter::evaluateInequalities(Node& conj, Node curr, Node& bv)
{
  SolverEngine se;
  NodeManager* nm = NodeManager::currentNM();

  std::vector<Node> bvl;
  bvl.push_back(bv);
  Node bvlNode = nm->mkNode(Kind::BOUND_VAR_LIST, bvl);

  if (curr.getKind() == Kind::LT)
  {
    Node boundConj = nm->mkNode(Kind::EXISTS, bvlNode, conj);

    Result isSat = se.checkSat(nm->mkNode(Kind::AND, boundConj, nm->mkNode(Kind::EXISTS, bvlNode, curr)));

    Node ret = nm->mkConst<bool>(isSat == Result::SAT);
    return ret;
  }

  NodeBuilder nb(curr.getKind());
  for (int i = 0; i < curr.getNumChildren(); ++i)
  {
    nb << (curr[i].getNumChildren() > 0 ? evaluateInequalities(conj, curr[i], bv)
                                        : curr[i]);
  }
  return nb;
}

Node SolutionCounter::evaluateModuloConstraints(Node& conj, Node curr, Node& q)
{
  NodeManager* nm = NodeManager::currentNM();
  Node bv = q[0];

  if (curr.getKind() == Kind::EQUAL
      && (curr[0].getKind() == Kind::INTS_MODULUS
          || curr[1].getKind() == Kind::INTS_MODULUS))
  {
    if (!expr::hasBoundVar(curr))
    {
      SolverEngine se;
      std::vector<Node> bvl;
      bvl.push_back(q[0]);
      Node bvlNode = nm->mkNode(Kind::BOUND_VAR_LIST, bvl);
      se.assertFormula(nm->mkNode(Kind::EXISTS, bvlNode, conj));
      return nm->mkConst<bool>(se.checkSat(nm->mkNode(Kind::EXISTS, bvlNode, curr)) == Result::SAT);
    }
    else
    {
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

Node SolutionCounter::evaluateFormula(
    Node& q,
    Ordering& ord,
    Node& segment,
    std::unordered_map<std::string, Node>& assignment,
    std::vector<Node>& variables,
    Integer& m)
{
  NodeManager* nm = NodeManager::currentNM();
  Node bigGamma = nm->mkNode(
      Kind::AND, assignResidueClass(assignment, variables, m), ord.getNode());
  Node conj = nm->mkNode(
      Kind::AND, segment, bigGamma);

  Node bv = q[0];
  Node ret = evaluateInequalities(conj, q[2], bv);
  ret = evaluateModuloConstraints(conj, ret, q);
  return ret;
}

Node SolutionCounter::substituteAllVars(
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
  std::vector<Node> processed_t = ord.makePairwiseNonEqual().d_terms;
  int l = processed_t.size();
  int m_int = m.getSignedInt();

  std::pair<Node, Node> segs(nm->mkNode(Kind::LT, q[0], processed_t[0]),
                             nm->mkNode(Kind::LT, processed_t[l - 1], q[0]));


  std::vector<Node> bvl;
  bvl.push_back(q[0]);

  Node bvlNode = nm->mkNode(Kind::BOUND_VAR_LIST, bvl);
  Node ord1 = nm->mkNode(Kind::EXISTS, bvlNode,
                 evaluateFormula(q, ord, segs.first, assignment, variables, m));
  Node ord2 = nm->mkNode(Kind::EXISTS, bvlNode,
      evaluateFormula(q, ord, segs.second, assignment, variables, m));

  if (se.checkSat(ord1) == Result::SAT || se.checkSat(ord2) == Result::SAT)
  {
    return false;
  }

  for (int j = 0; j < l; ++j)
  {
    Node seg = nm->mkNode(Kind::EQUAL, q[0], processed_t[j]);
    Node evaluated_ord = evaluateFormula(q, ord, seg, assignment, variables, m);

    TNode r_t = d_rewriter->rewrite(
        substituteAllVars(processed_t[j], assignment, variables));
    if (expr::hasBoundVar(evaluated_ord))
    {
      evaluated_ord = evaluated_ord.substitute(q[0], r_t);
    }
    c[j] = (d_rewriter->rewrite(evaluated_ord) == trueNode) ? 1 : 0;

    if (j == 0) continue;

    seg = nm->mkNode(Kind::AND,
                     nm->mkNode(Kind::LT, processed_t[j - 1], q[0]),
                     nm->mkNode(Kind::LT, q[0], processed_t[j]));

    if (expr::hasBoundVar(evaluated_ord))
    {
      for (int i = 0; i < m.getSignedInt(); ++i)
      {
        TNode i_node = nm->mkConstInt(i);
        Node rewritten =
            d_rewriter->rewrite(evaluated_ord.substitute(q[0], i_node));
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
        substituteAllVars(processed_t[j - 1], assignment, variables));

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
      if (d_rewriter->rewrite(evaluated_ord.substitute(q[0], temp))
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
