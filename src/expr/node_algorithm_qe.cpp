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

bool hasBoundVar(Node n, Node bound_var)
{
  return n == bound_var  // n is a node representing the bound variable
         || (n.getKind() == NEG
             && n[0] == bound_var)  // n is a node representing negation
                                    // of the bound variable
         || (n.getKind() == MULT    // n is a node representing a multiplication
                                    // of the bound variable.
             && ((bound_var == n[0]) || bound_var == n[1])
             && (n[1].getKind() == CONST_INTEGER
                 || n[0].getKind() == CONST_INTEGER));
}

}  // namespace expr
}  // namespace cvc5::internal
