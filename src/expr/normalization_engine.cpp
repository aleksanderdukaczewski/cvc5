
#include "normalization_engine.h"
#include "expr/node_algorithm.h"
#include "expr/solution_counter.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;
using namespace cvc5::internal::expr;

namespace cvc5::internal {

NormalizationEngine::NormalizationEngine(theory::Rewriter* rewriter) : d_rewriter(rewriter) {}

NormalizationEngine::~NormalizationEngine() {}

Node NormalizationEngine::normalizeFormula(Node& q,
                                           std::unordered_set<Node>& terms_s)
{
  NodeManager* nm = NodeManager::currentNM();
  Node bv = q[0][0], bounded_expr = q[2];

  // Find all coefficients of the bound variable in q.
  std::unordered_set<Node> s_coefs;
  getCoefficients(bounded_expr, bv, s_coefs);

  // Calculate k, the lcm of the absolute values of all coefficients of bv.
  Integer k(1);
  for (const Node& coef : s_coefs)
  {
    Integer coef_i = coef.getConst<Rational>().getNumerator().abs();
    k = k.lcm(coef_i);
  }

  Trace("smt-qe") << "k = " << k << std::endl;
  terms_s.insert(nm->mkConstInt(0));

  // Normalise the coefficients in the formula and conjunct it with a new simple
  // modulo constraint on the bound variable.
  Node normalized_expr =
      nm->mkNode(AND,
                 normalizeCoefficients(bounded_expr, bv, k, terms_s),
                 nm->mkNode(EQUAL,
                            nm->mkNode(INTS_MODULUS, bv, nm->mkConstInt(k)),
                            nm->mkConstInt(0)));
  q = nm->mkNode(q.getKind(), q[0], q[1], normalized_expr);

  // Return the normalized formula.
  return q;
}

Integer NormalizationEngine::extractInteger(Node n)
{
  return n.getConst<Rational>().getNumerator();
}

Integer NormalizationEngine::extractCoefficient(Node n, Node& bv)
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
  else if (n.getKind() == MULT
           && (n[0] == bv || n[1] == bv)
           && (n[0].getKind() == CONST_INTEGER || n[1].getKind() == CONST_INTEGER))
  {
    return (bv == n[0]) ? extractInteger(n[1]) : extractInteger(n[0]);
  }
  else
  {
    for (int i = 0; i < n.getNumChildren(); ++i)
    {
      Integer extracted_coef = extractCoefficient(n[i], bv);
      if (hasBoundVar(n) &&  extracted_coef != Integer(0))
      {
        return extracted_coef;
      }
    }
    return Integer(0);
  }
}

Node NormalizationEngine::normalizeCoefficients(Node& n,
                                                Node& bv,
                                                Integer& k, std::unordered_set<Node>& terms_s)
{
  NodeManager* nm = NodeManager::currentNM();
  if (n.getKind() == LT)
  {
    Integer a = Integer(0);

    Node bv_free_n = removeBoundVariable(d_rewriter->rewrite(n[0]), bv, a);

    if (a.isZero())
    {
      terms_s.insert(bv_free_n);
      return bv_free_n;
    }

    Integer term_coef = k.exactQuotient(a);
    if (!term_coef.isOne())
    {
      bv_free_n =
          nm->mkNode(MULT, nm->mkConstInt(term_coef), bv_free_n);
    }
    terms_s.insert(d_rewriter->rewrite(nm->mkNode(NEG, bv_free_n)));

    Node lhs = a.strictlyPositive()
                   ? nm->mkNode(ADD, bv, bv_free_n)
                   : nm->mkNode(SUB, nm->mkNode(NEG, bv), bv_free_n);

    return nm->mkNode(LT, lhs, nm->mkConstInt(0));
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
      nb << normalizeCoefficients(child, bv, k, terms_s);
    }

    return nb;
  }
}

bool isMultipliedBoundVar(Node n, Node bv)
{
  return n.getKind() == MULT
             && ((n[0] == bv
                  && n[1].getKind() == CONST_INTEGER)
                 || (n[1] == bv
                     && n[0].getKind() == CONST_INTEGER));
}

Node NormalizationEngine::removeBoundVariable(Node n,
                                              Node bv,
                                              Integer& bv_coef)
{
  NodeManager* nm = NodeManager::currentNM();
  Node zeroNode = nm->mkConstInt(0);
  if (isMultipliedBoundVar(n, bv))
  {
    Node coef_node = n[0] == bv ? n[1] : n[0];
    bv_coef = extractInteger(coef_node);
    return zeroNode;
  }
  else if (n == bv)
  {
    bv_coef = Integer(1);
    return zeroNode;
  }
  else if (n.getNumChildren() == 0)
  {
    return n;
  }
  else
  {
    NodeBuilder nb(n.getKind());
    for (int i = 0; i < n.getNumChildren(); ++i)
    {
      nb << removeBoundVariable(n[i], bv, bv_coef);
    }
    return nb;
  }
}

void NormalizationEngine::getCoefficients(Node& n, Node& var, std::unordered_set<Node>& s_coefs)
{
  std::vector<Node> toProcess;
  toProcess.push_back(n);

  do
  {
    Node cur = toProcess.back();
    toProcess.pop_back();
    if (cur.getKind() == MULT)
    {
      if (cur[0].isConst() && cur[1].isVar()
          && cur[1] == var)
      {
        s_coefs.insert(cur[0]);
      }
      else if (cur[1].isConst() && cur[0].isVar()
               && cur[0] == var)
      {
        s_coefs.insert(cur[1]);
      }
    }
    toProcess.insert(toProcess.end(), cur.begin(), cur.end());
  } while (!toProcess.empty());
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

    ret = (ret == falseNode) ? local_disjunct
                             : nm->mkNode(OR, ret, local_disjunct);
  }

  return ret;
}

Node NormalizationEngine::simplifyModuloConstraints(Node n)
{
  // Rewrite the node if it represents a modulo constraint
  if (n.getKind() == EQUAL && (n[0].getKind() == INTS_MODULUS || n[1].getKind() == INTS_MODULUS))
  {
    return processModuloConstraint(n);
  }

  // Recursively simplify modulo constraint
  NodeBuilder nb(n.getKind());
  for (int i = 0; i < n.getNumChildren(); ++i)
  {
    nb << (n[i].getNumChildren() > 0 ? simplifyModuloConstraints(n[i]) : n[i]);
  }
  return nb;
}

Node NormalizationEngine::rewriteQe(Node n)
{
  NodeManager* nm = NodeManager::currentNM();
  Node zeroNode = nm->mkConstInt(0);
  Node oneNode = nm->mkConstInt(1);

  // Transform (a > b) -> (b - a < 0)
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
  // Transform (a < b) -> (a - b < 0)
  else if (n.getKind() == LT)
  {
    if (n[1] != zeroNode)
    {
      n = nm->mkNode(LT, nm->mkNode(SUB, n[0], n[1]), zeroNode);
    }
  }
  else if (n.getKind() == LEQ)
  {
    // Transform (a <= b) -> (a - b - 1 < 0)
    if (n[1] != zeroNode)
    {
      n = nm->mkNode(
          LT, nm->mkNode(SUB, nm->mkNode(SUB, n[0], n[1]), oneNode), zeroNode);
    }
    // Transform (a <= 0) -> (a - 1 < 0)
    else
    {
      n = nm->mkNode(LT, nm->mkNode(SUB, n[0], oneNode), zeroNode);
    }
  }
  else if (n.getKind() == GEQ)
  {
    // Transform (a >= b) -> (b - a - 1 < 0)
    if (n[1] != zeroNode)
    {
      n = nm->mkNode(
          LT, nm->mkNode(SUB, nm->mkNode(SUB, n[1], n[0]), oneNode), zeroNode);
    }
    // Transform (a >= 0) -> (- a - 1 < 0)
    else
    {
      n = nm->mkNode(
          LT, nm->mkNode(SUB, nm->mkNode(NEG, n[0]), oneNode), zeroNode);
    }
  }
  else if (n.getKind() == EQUAL)
  {
    // Transform ((a mod q) = (b mod q)) -> ((a - b) mod q = 0)
    if (n[0].getKind() == INTS_MODULUS && n[1].getKind() == INTS_MODULUS
        && n[0][1] == n[1][1])
    {
      n = nm->mkNode(
          EQUAL,
          nm->mkNode(INTS_MODULUS, nm->mkNode(SUB, n[0][0], n[1][0]), n[0][1]),
          zeroNode);
    }
    // Transform (a = b) -> (b - a - 1 < 0) AND (a - b - 1 < 0)
    else
    {
      n = nm->mkNode(
          AND,
          nm->mkNode(
              LT,
              nm->mkNode(SUB, nm->mkNode(SUB, n[1], n[0]), oneNode),
              zeroNode),
          nm->mkNode(
              LT,
              nm->mkNode(SUB, nm->mkNode(SUB, n[0], n[1]), oneNode),
              zeroNode));
    }
  }

  // After rewriting n, recursively rewrite its children if not a leaf
  switch (n.getNumChildren())
  {
    case 1: return nm->mkNode(n.getKind(), rewriteQe(n[0]));
    case 2: return nm->mkNode(n.getKind(), rewriteQe(n[0]), rewriteQe(n[1]));
    case 3: return nm->mkNode(n.getKind(), rewriteQe(n[0]), rewriteQe(n[1]), rewriteQe(n[2]));
    default: return n;
  }
}

}  // namespace cvc5::internal
