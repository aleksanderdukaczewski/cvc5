#include "normalization_engine.h"

#include "expr/node_algorithm.h"
#include "expr/node_algorithm_qe.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;
using namespace cvc5::internal::expr;

namespace cvc5::internal {

std::pair<Node, std::vector<Node>> NormalizationEngine::normalizeFormula(
    Node& q)
{
  Trace("smt-qe") << "normalizeFormula: calling on q = " << q << std::endl;
  Node bound_var_node = q[0][0];
  std::unordered_set<Node> s_coefs;
  getCoefficients(q, bound_var_node, s_coefs);
  Integer k(1);
  for (const auto& coef : s_coefs)
  {
    Integer coef_i = coef.getConst<Rational>().getNumerator().abs();
    k = k.lcm(coef_i);
  }

  NodeManager* nm = NodeManager::currentNM();
  std::vector<Node> T;
  T.push_back(nm->mkConstInt(0));

  Node bounded_expr = q[2];
  Node expr = nm->mkNode(
      AND,
      normalizeCoefficients(bounded_expr, bound_var_node, k, T),
      nm->mkNode(EQUAL,
                 nm->mkNode(INTS_MODULUS, bound_var_node, nm->mkConstInt(k)),
                 nm->mkConstInt(0)));
  q = nm->mkNode(q.getKind(), q[0], q[1], expr);

  std::pair<Node, std::vector<Node>> ret(q, T);
  Trace("smt-qe") << "normalizeFormula: returning " << ret << std::endl;
  return ret;
}

Integer NormalizationEngine::getCoefficient(Node n, Node bound_var)
{
  if (!expr::hasBoundVar(n))
  {
    return Integer(0);
  }
  else
  {
    if (n.getKind() == NEG && n[0] == bound_var)
    {
      return Integer(-1);
    }
    else if (n == bound_var)
    {
      return Integer(1);
    }
    else if (n.getKind() == MULT)
    {
      if (bound_var == n[0])
      {
        return n[1].getConst<Rational>().getNumerator();
      }
      else
      {
        return n[0].getConst<Rational>().getNumerator();
      }
    }
    else
    {
      return Integer(0);
    }
  }
}

Node NormalizationEngine::normalizeCoefficients(Node& n,
                                                Node& bv_node,
                                                Integer& k,
                                                std::vector<Node>& T)
{
  Trace("smt-qe") << "normalizeCoefficients: running on n = " << n << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  if (n.getKind() == LT)
  {
    Integer a = Integer(0);
    Node bv_free_n = removeBoundVariable(n[0], bv_node, a);
    if (a.isZero())
    {
      T.push_back(bv_free_n);
      return bv_free_n;
    }
    Integer term_coef = k.exactQuotient(a);
    if (!term_coef.isOne())
    {
      bv_free_n =
          nm->mkNode(MULT, nm->mkConstInt(Rational(term_coef)), bv_free_n);
    }
    T.push_back(nm->mkNode(NEG, bv_free_n));

    Node lhs = a.strictlyPositive()
                   ? nm->mkNode(ADD, bv_node, bv_free_n)
                   : nm->mkNode(SUB, nm->mkNode(NEG, bv_node), bv_free_n);

    Trace("smt-qe") << "normalizeCoefficients: returning " << n << std::endl;

    return nm->mkNode(LT, lhs, nm->mkConstInt(Rational(0)));
  }
  else if (n.getKind() == EQUAL && n[0].getKind() == INTS_MODULUS
           && n[1].getKind() == CONST_INTEGER)
  {
    if (n[0][0] != bv_node)
    {
      return n;
    }
    Node new_modulus = nm->mkNode(MULT, nm->mkConstInt(k), n[0][1]);
    return nm->mkNode(EQUAL,
                      nm->mkNode(INTS_MODULUS,
                                 nm->mkNode(MULT, nm->mkConstInt(k), bv_node),
                                 new_modulus),
                      nm->mkNode(INTS_MODULUS,
                                 nm->mkNode(MULT, nm->mkConstInt(k), n[1]),
                                 new_modulus));
  }
  else
  {
    NodeBuilder nb(n.getKind());
    for (int i = 0; i < n.getNumChildren(); i++)
    {
      Node child = n[i];
      nb << normalizeCoefficients(child, bv_node, k, T);
    }
    Node ret = nb;

    return ret;
  }
}

Node NormalizationEngine::removeBoundVariable(Node n,
                                              Node bound_var,
                                              Integer& bound_var_coef)
{
  if (n.getNumChildren() > 0)
  {
    if (n.getKind() == ADD || n.getKind() == SUB || n.getKind() == MULT
        || n.getKind() == NEG)
    {
      NodeManager* nm = NodeManager::currentNM();
      if (hasBoundVar(n[0]) || hasBoundVar(n[1]))
      {
        Node bv_term = hasBoundVar(n[0]) ? n[0] : n[1];
        Node bv_free_term = hasBoundVar(n[0]) ? n[1] : n[0];
        bound_var_coef = getCoefficient(bv_term, bound_var);

        if (n.getKind() == SUB)
        {
          if (hasBoundVar(n[0]))
          {
            return nm->mkNode(
                NEG, removeBoundVariable(n[1], bound_var, bound_var_coef));
          }
          else
          {
            return nm->mkNode(
                NEG, removeBoundVariable(n[0], bound_var, bound_var_coef));
          }
        }
        else
        {
          return removeBoundVariable(bv_free_term, bound_var, bound_var_coef);
        }
      }
      else if (n.getNumChildren() == 2)
      {
        return nm->mkNode(n.getKind(),
                          removeBoundVariable(n[0], bound_var, bound_var_coef),
                          removeBoundVariable(n[1], bound_var, bound_var_coef));
      }
      else
      {
        return nm->mkNode(n.getKind(),
                          removeBoundVariable(n[0], bound_var, bound_var_coef));
      }
    }
    return n;
  }
  else
  {
    // A leaf node in the AST, CONST_INTEGER or VARIABLE that is
    // guaranteed not to be the bound variable or a negation of it
    return n;
  }
}

void NormalizationEngine::getCoefficients(Node& n, Node& var_node, std::unordered_set<Node>& s_coefs)
{
  for (int i = 0; i < n.getNumChildren(); ++i)
  {
    Node child = n[i];
    if (child.getKind() == MULT)
    {
      if (child[0].isConst() && child[1].isVar()
          && child[1] == var_node)
      {
        s_coefs.insert(child[0]);
      }
      else if (child[1].isConst() && child[0].isVar()
               && child[0] == var_node)
      {
        s_coefs.insert(child[1]);
      }
    }
    getCoefficients(child, var_node, s_coefs);
  }
}

}  // namespace cvc5::internal
