#include "normalization_engine.h"

#include "expr/node_algorithm.h"
#include "expr/solution_counter.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;
using namespace cvc5::internal::expr;

namespace cvc5::internal {

NormalizationEngine::NormalizationEngine(theory::Rewriter* rewriter) : d_rewriter(rewriter) {}

NormalizationEngine::~NormalizationEngine() {}

Node NormalizationEngine::normalizeFormula(Node& q, std::vector<Node>& terms_v)
{
  NodeManager* nm = NodeManager::currentNM();
  Node bv = q[0][0];
  Node bounded_expr = q[2];

  // Find all coefficients of the bound variable in q.
  std::unordered_set<Node> s_coefs;
  getCoefficients(bounded_expr, bv, s_coefs);

  // Calculate k, the lcm of the absolute values of all coefficients of bv.
  Integer k(1);
  for (const auto& coef : s_coefs)
  {
    Integer coef_i = coef.getConst<Rational>().getNumerator().abs();
    k = k.lcm(coef_i);
  }

  terms_v.push_back(nm->mkConstInt(0));

  // Normalise the coefficients in the formula and conjunct it with a new simple
  // modulo constraint on the bound variable.
  Node normalized_expr =
      nm->mkNode(AND,
                 normalizeCoefficients(bounded_expr, bv, k, terms_v),
                 nm->mkNode(EQUAL,
                            nm->mkNode(INTS_MODULUS, bv, nm->mkConstInt(k)),
                            nm->mkConstInt(0)));
  q = nm->mkNode(q.getKind(), q[0], q[1], normalized_expr);

  // Return the normalized formula.
  return q;
}

Integer NormalizationEngine::extractCoefficient(Node n, Node bv)
{
  if (!expr::hasBoundVar(n))
  {
    return Integer(0);
  }
  else
  {
    // n is a negation of bv
    if (n.getKind() == NEG && n[0] == bv)
    {
      return Integer(-1);
    }
    // n is bv itself
    else if (n == bv)
    {
      return Integer(1);
    }
    // n is bv multiplied by an integer constant;
    else if (n.getKind() == MULT)
    {
      // bv is on the LHS, coefficient on RHS
      if (bv == n[0])
      {
        return n[1].getConst<Rational>().getNumerator();
      }
      // bv is on the RHS, coefficient on LHS
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
                                                Node& bv,
                                                Integer& k,
                                                std::vector<Node>& terms_v)
{
  NodeManager* nm = NodeManager::currentNM();
  if (n.getKind() == LT)
  {
    Integer a = Integer(0);
    Node bv_free_n = removeBoundVariable(n[0], bv, a);
    if (a.isZero())
    {
      terms_v.push_back(bv_free_n);
      return bv_free_n;
    }
    Integer term_coef = k.exactQuotient(a);
    if (!term_coef.isOne())
    {
      bv_free_n =
          nm->mkNode(MULT, nm->mkConstInt(Rational(term_coef)), bv_free_n);
    }
    terms_v.push_back(d_rewriter->rewrite(nm->mkNode(NEG, bv_free_n)));

    Node lhs = a.strictlyPositive()
                   ? nm->mkNode(ADD, bv, bv_free_n)
                   : nm->mkNode(SUB, nm->mkNode(NEG, bv), bv_free_n);

    return nm->mkNode(LT, lhs, nm->mkConstInt(Rational(0)));
  }
  else if (n.getKind() == EQUAL && n[0].getKind() == INTS_MODULUS
           && n[1].getKind() == CONST_INTEGER)
  {
    if (n[0][0] != bv)
    {
      return n;
    }
    Node new_modulus = nm->mkNode(MULT, nm->mkConstInt(k), n[0][1]);
    return nm->mkNode(EQUAL,
                      nm->mkNode(INTS_MODULUS,
                                 nm->mkNode(MULT, nm->mkConstInt(k), bv),
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
      nb << normalizeCoefficients(child, bv, k, terms_v);
    }
    Node ret = nb;

    return ret;
  }
}

Node NormalizationEngine::removeBoundVariable(Node n,
                                              Node bv,
                                              Integer& bv_coef)
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
        bv_coef = extractCoefficient(bv_term, bv);

        if (n.getKind() == SUB)
        {
          if (hasBoundVar(n[0]))
          {
            return nm->mkNode(
                NEG, removeBoundVariable(n[1], bv, bv_coef));
          }
          else
          {
            return nm->mkNode(
                NEG, removeBoundVariable(n[0], bv, bv_coef));
          }
        }
        else
        {
          return removeBoundVariable(bv_free_term, bv, bv_coef);
        }
      }
      else if (n.getNumChildren() == 2)
      {
        return nm->mkNode(n.getKind(),
                          removeBoundVariable(n[0], bv, bv_coef),
                          removeBoundVariable(n[1], bv, bv_coef));
      }
      else
      {
        return nm->mkNode(n.getKind(),
                          removeBoundVariable(n[0], bv, bv_coef));
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

void NormalizationEngine::getCoefficients(Node& n, Node& var, std::unordered_set<Node>& s_coefs)
{
  for (int i = 0; i < n.getNumChildren(); ++i)
  {
    Node child = n[i];
    if (child.getKind() == MULT)
    {
      if (child[0].isConst() && child[1].isVar()
          && child[1] == var)
      {
        s_coefs.insert(child[0]);
      }
      else if (child[1].isConst() && child[0].isVar()
               && child[0] == var)
      {
        s_coefs.insert(child[1]);
      }
    }
    getCoefficients(child, var, s_coefs);
  }
}

Node NormalizationEngine::processModuloConstraint(Node& n)
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
      SolutionCounter::generateResidueClassMappings(mod_rhs, vars_v);

  Node ret = falseNode;
  for (auto& r : residueClasses)
  {
    Node evaluated_term = SolutionCounter::getTermAssignment(n, r, vars_v);
    evaluated_term = d_rewriter->rewrite(evaluated_term);
    if (d_rewriter->rewrite(evaluated_term) == falseNode)
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

Node NormalizationEngine::simplifyModuloConstraints(Node n)
{
  if (n.getKind() == EQUAL && (n[0].getKind() == INTS_MODULUS || n[1].getKind() == INTS_MODULUS))
  {
    return processModuloConstraint(n);
  }

  NodeBuilder nb(n.getKind());
  for (int i = 0; i < n.getNumChildren(); ++i)
  {
    nb << (n[i].getNumChildren() > 0 ? simplifyModuloConstraints(n[i]) : n[i]);
  }
  return nb;
}

Node NormalizationEngine::rewrite_qe(Node n)
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

}  // namespace cvc5::internal
