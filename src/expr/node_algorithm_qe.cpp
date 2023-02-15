#include "expr/node_algorithm_qe.h"

#include "expr/attribute.h"
#include "expr/dtype.h"
#include "expr/node.h"
#include "expr/node_algorithm.h"
#include "ordering_engine.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace expr {

void getCoefficients(Node& n, Node& var_node, std::unordered_set<Node>& s_coefs)
{
  for (int i = 0; i < n.getNumChildren(); ++i)
  {
    Node child = n[i];
    if (child.getKind() == MULT)
    {
      if (child[0].isConst() && child[1].isVar()
          && child[1].getName() == var_node.toString())
      {
        s_coefs.insert(child[0]);
      }
      else if (child[1].isConst() && child[0].isVar()
               && child[0].getName() == var_node.toString())
      {
        s_coefs.insert(child[1]);
      }
    }
    getCoefficients(child, var_node, s_coefs);
  }
}

Node processModuloConstraint(Node& n, theory::Rewriter* rr)
{
  NodeManager* nm = NodeManager::currentNM();
  Node trueNode = nm->mkConst<bool>(true);
  Node falseNode = nm->mkConst<bool>(false);
  Node modulus = n[0][1];

  std::unordered_set<TNode> variables;
  getVariables(n, variables);
  std::vector<Node> vars_v(variables.begin(), variables.end());

  int mod_rhs = n[0][1].getConst<Rational>().getNumerator().getSignedInt();
  std::vector<std::unordered_map<std::string, Node>> residueClasses =
      OrderingEngine::generateResidueClassMappings(mod_rhs, vars_v);

  Node ret = falseNode;
  for (auto& r : residueClasses)
  {
    Node evaluated_term = OrderingEngine::getTermAssignment(n, r, vars_v);
    evaluated_term = rr->rewrite(evaluated_term);

    if (rr->rewrite(evaluated_term) == falseNode)
    {
      continue;
    }

    Node local_disjunct = trueNode;
    for (const auto& var : variables)
    {
      Node temp = nm->mkNode(
          EQUAL, nm->mkNode(INTS_MODULUS, var, modulus), r.at(var.toString()));
      local_disjunct = local_disjunct == trueNode
                           ? temp
                           : nm->mkNode(AND, local_disjunct, temp);
    }
    if (ret == falseNode)
    {
      ret = local_disjunct;
    }
    else
    {
      ret = nm->mkNode(OR, ret, local_disjunct);
    }
  }

  return ret;
}

Node simplifyModuloConstraints(Node n, theory::Rewriter* rewriter)
{
  if (n.getKind() == EQUAL && n[0].getKind() == INTS_MODULUS)
  {
    return processModuloConstraint(n, rewriter);
  }

  NodeBuilder nb(n.getKind());
  for (int i = 0; i < n.getNumChildren(); ++i)
  {
    nb << (n[i].getNumChildren() > 0 ? simplifyModuloConstraints(n[i], rewriter)
                                     : n[i]);
  }
  return nb;
}

Node normaliseCoefficients(Node& n,
                           Node& bv_node,
                           Integer& k,
                           std::vector<Node>& T)
{
  Trace("smt-qe") << "normaliseCoefficients: running on n = " << n << std::endl;
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

    Node lhs =
        a.strictlyPositive()
            ? nm->mkNode(ADD, bv_node, bv_free_n)
            : nm->mkNode(SUB, nm->mkNode(NEG, bv_node), bv_free_n);

    Trace("smt-qe") << "normaliseCoefficients: returning " << n << std::endl;

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
    return nm->mkNode(
        EQUAL,
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
      nb << normaliseCoefficients(child, bv_node, k, T);
    }
    Node ret = nb;

    return ret;
  }
}

std::pair<Node, std::vector<Node>> normaliseFormula(Node q)
{
  Trace("smt-qe") << "normaliseFormula: calling on q = " << q << std::endl;

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
      normaliseCoefficients(bounded_expr, bound_var_node, k, T),
      nm->mkNode(EQUAL,
                 nm->mkNode(INTS_MODULUS, bound_var_node, nm->mkConstInt(k)),
                 nm->mkConstInt(0)));
  q = nm->mkNode(q.getKind(), q[0], q[1], expr);

  std::pair<Node, std::vector<Node>> ret(q, T);

  Trace("smt-qe") << "normaliseFormula: returning " << ret << std::endl;
  return ret;
}

void getModuli(Node n, std::unordered_set<Node>& s_mod)
{
  if (n.getKind() == EQUAL && n[1].getKind() == CONST_INTEGER
      && n[1].getConst<Rational>().isZero() && n[0].getKind() == INTS_MODULUS
      && n[0][1].getKind() == CONST_INTEGER)
  {
    s_mod.insert(n[0][1]);
  }
  else if (n.getNumChildren() > 0)
  {
    for (int i = 0; i < n.getNumChildren(); ++i)
    {
      getModuli(n[i], s_mod);
    }
  }
}

Node rewrite_qe(Node n)
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
  else if (n.getKind() == EQUAL)
  {
    if (n[0].getKind() == INTS_MODULUS && n[1].getKind() == INTS_MODULUS
        && n[0][1] == n[1][1])
    {
      n = nm->mkNode(
          EQUAL,
          nm->mkNode(INTS_MODULUS, nm->mkNode(SUB, n[0][0], n[1][0]), n[0][1]),
          zeroNode);
    }
    else
    {
      n = nm->mkNode(
          AND,
          nm->mkNode(
              LT,
              nm->mkNode(SUB, nm->mkNode(SUB, n[1], n[0]), nm->mkConstInt(1)),
              zeroNode),
          nm->mkNode(
              LT,
              nm->mkNode(SUB, nm->mkNode(SUB, n[0], n[1]), nm->mkConstInt(1)),
              zeroNode));
    }
  }

  switch (n.getNumChildren())
  {
    case 1: return nm->mkNode(n.getKind(), rewrite_qe(n[0]));
    case 2: return nm->mkNode(n.getKind(), rewrite_qe(n[0]), rewrite_qe(n[1]));
    case 3:
      return nm->mkNode(
          n.getKind(), rewrite_qe(n[0]), rewrite_qe(n[1]), rewrite_qe(n[2]));
    default: return n;
  }
}

bool sameVar(Node n1, Node n2)
{
  return n1.isVar() && n2.isVar() && n1.toString() == n2.toString();
}

bool hasBoundVar(Node n, Node bound_var)
{
  return n == bound_var  // n is a node representing the bound variable
         || (n.getKind() == NEG
             && n[0] == bound_var)  // n is a node representing negation
                                           // of the bound variable
         || (n.getKind() == MULT  // n is a node representing a multiplication
                                  // of the bound variable.
             && ((bound_var == n[0]) || bound_var == n[1])
             && (n[1].getKind() == CONST_INTEGER
                 || n[0].getKind() == CONST_INTEGER));
}

Integer getCoefficient(Node n, Node bound_var)
{
  if (!hasBoundVar(n))
  {
    return Integer(0);
  }
  else
  {
    if (n.getKind() == NEG && sameVar(n[0], bound_var))
    {
      return Integer(-1);
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

}  // namespace expr
}  // namespace cvc5::internal
