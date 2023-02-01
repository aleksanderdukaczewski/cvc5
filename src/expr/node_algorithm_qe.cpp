#include "expr/node_algorithm_qe.h"

#include "expr/attribute.h"
#include "expr/dtype.h"
#include "expr/node.h"
#include "expr/node_algorithm.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace expr {

void getCoefficients(Node n, Node var_node, std::vector<Integer>& v_coefs)
{
  // Trace("smt-qe") << "node has type " << n.getKind() << std::endl;
  for (int i = 0; i < n.getNumChildren(); ++i)
  {
    Node child = n[i];

    if (child.getKind() == MULT && child.getNumChildren() == 2)
    {
      if (child[0].isConst() && child[1].isVar()
          && child[1].getName() == var_node.toString())
      {
        v_coefs.push_back(child[0].getConst<Rational>().getNumerator());
      }
      else if (child[1].isConst() && child[0].isVar()
               && child[0].getName() == var_node.toString())
      {
        v_coefs.push_back(child[1].getConst<Rational>().getNumerator());
      }
    }

    getCoefficients(child, var_node, v_coefs);
  }
}

Node normaliseCoefficients(Node n,
                           Node bound_var_node,
                           Integer k,
                           std::vector<Node>& T)
{
  Trace("smt-qe") << "normaliseCoefficients: running on n = " << n << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  if (n.getKind() == LT)
  {
    Integer a = Integer(0);
    Node bv_free_n = removeBoundVariable(n[0], bound_var_node, a);
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
               ? nm->mkNode(ADD, bound_var_node, bv_free_n)
               : nm->mkNode(SUB, nm->mkNode(NEG, bound_var_node), bv_free_n);

    return nm->mkNode(LT, lhs, nm->mkConstInt(Rational(0)));
  }
  else
  {
    NodeBuilder nb(n.getKind());
    for (int i = 0; i < n.getNumChildren(); i++)
    {
      nb << normaliseCoefficients(n[i], bound_var_node, k, T);
    }

    return nb;
  }
}

std::pair<Node, std::vector<Node>> normaliseFormula(Node n)
{
  Node bound_var_node = n[0][0];
  std::vector<Integer> v_coefs;
  getCoefficients(n, bound_var_node, v_coefs);
  Integer k(1);
  for (Integer& coef : v_coefs)
  {
    k = k.lcm(coef.abs());
  }

  NodeManager* nm = NodeManager::currentNM();
  std::vector<Node> T;
  T.push_back(nm->mkConstInt(0));

  Node expr = nm->mkNode(
      AND,
      normaliseCoefficients(n[2], bound_var_node, k, T),
      nm->mkNode(EQUAL,
                 nm->mkNode(INTS_MODULUS, bound_var_node, nm->mkConstInt(k)),
                 nm->mkConstInt(Rational(0))));
  n = nm->mkNode(n.getKind(), n[0], n[1], expr);

  std::pair<Node, std::vector<Node>> ret(n, T);
  return ret;
}

void getModuli(Node n, std::vector<Integer>& s_mod)
{
  if (n.getKind() == EQUAL && n[1].getKind() == CONST_INTEGER
      && n[1].getConst<Rational>().isZero() && n[0].getKind() == INTS_MODULUS
      && n[0][1].getKind() == CONST_INTEGER)
  {
    s_mod.push_back(n[0][1].getConst<Rational>().getNumerator());
  }
  else if (n.getNumChildren() > 0)
  {
    for (int i = 0; i < n.getNumChildren(); ++i)
    {
      getModuli(n[i], s_mod);
    }
  }
}

Node rewriteIq(Node n)
{
  NodeManager* nm = NodeManager::currentNM();
  Node zeroNode = nm->mkConstInt(Rational(0));
  Node oneNode = nm->mkConstInt(Rational(1));

  if (n.getKind() == GT)
  {
    if (n[1] != zeroNode)
    {
      n = nm->mkNode(LT, nm->mkNode(SUB, n[1], n[0]), zeroNode);
    }
    else
    {
      n = nm->mkNode(LT, nm->mkNode(NEG, n[0]), n[1]);
    }
  }
  else if (n.getKind() == LT)
  {
    if (n[1] != zeroNode)
    {
      n = nm->mkNode(LT, nm->mkNode(SUB, n[0], n[1]), zeroNode);
    }
  }
  else if (n.getKind() == LEQ)
  {
    if (n[1] != zeroNode)
    {
      n = nm->mkNode(
          LT, nm->mkNode(SUB, nm->mkNode(SUB, n[0], n[1]), oneNode), zeroNode);
    }
    else
    {
      n = nm->mkNode(LT, nm->mkNode(SUB, n[0], oneNode), zeroNode);
    }
  }
  else if (n.getKind() == GEQ)
  {
    if (n[1] != zeroNode)
    {
      n = nm->mkNode(
          LT, nm->mkNode(SUB, nm->mkNode(SUB, n[1], n[0]), oneNode), zeroNode);
    }
    else
    {
      n = nm->mkNode(
          LT, nm->mkNode(SUB, nm->mkNode(NEG, n[0]), oneNode), zeroNode);
    }
  }

  switch (n.getNumChildren())
  {
    case 1: return nm->mkNode(n.getKind(), rewriteIq(n[0]));
    case 2: return nm->mkNode(n.getKind(), rewriteIq(n[0]), rewriteIq(n[1]));
    case 3:
      return nm->mkNode(
          n.getKind(), rewriteIq(n[0]), rewriteIq(n[1]), rewriteIq(n[2]));
    default: return n;
  }
}

bool sameVar(Node n1, Node n2)
{
  return n1.isVar() && n2.isVar() && n1.toString() == n2.toString();
}

bool hasBoundVar(Node n, Node bound_var)
{
  return sameVar(n, bound_var)  // n is a node representing the bound variable
         || (n.getKind() == NEG
             && sameVar(n[0], bound_var))  // n is a node representing negation
                                           // of the bound variable
         || (n.getKind() == MULT  // n is a node representing a multiplication
                                  // of the bound variable.
             && (sameVar(bound_var, n[0]) || sameVar(bound_var, n[1]))
             && (n[1].getKind() == CONST_INTEGER
                 || n[0].getKind() == CONST_INTEGER));
}

Integer getCoefficient(Node n, Node bound_var)
{
  if (!hasBoundVar(n, bound_var))
  {
    return Integer(0);
  }
  else
  {
    if (n.getKind() == NEG && sameVar(n[0], bound_var))
    {
      return Integer(0);
    }
    else if (sameVar(n, bound_var))
    {
      return Integer(1);
    }
    else if (n.getKind() == MULT)
    {
      if (sameVar(bound_var, n[0]))
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

Node removeBoundVariable(Node n, Node bound_var, Integer& bound_var_coef)
{
  Trace("smt-qe") << "removeBoundVariable: running on node : " << n << std::endl;

  if (n.getNumChildren() > 0)
  {
    if (n.getKind() == ADD || n.getKind() == SUB || n.getKind() == MULT
        || n.getKind() == NEG)
    {
      NodeManager* nm = NodeManager::currentNM();
      if (hasBoundVar(n[0], bound_var) || hasBoundVar(n[1], bound_var))
      {
        Node bv_term = hasBoundVar(n[0], bound_var) ? n[0] : n[1];
        Node bv_free_term = hasBoundVar(n[0], bound_var) ? n[1] : n[0];
        bound_var_coef = getCoefficient(bv_term, bound_var);

        if (n.getKind() == SUB)
        {
          if (hasBoundVar(n[0], bound_var))
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
    Trace("smt-qe") << "removeBoundVariable: returning leaf " << n << std::endl;
    return n;
  }
}

}  // namespace expr
}  // namespace cvc5::internal
