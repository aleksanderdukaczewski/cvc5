#include "expr/node_algorithm_qe.h"
#include "expr/node_algorithm.h"

#include "expr/attribute.h"
#include "expr/dtype.h"
#include "expr/node.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace expr {

void getCoefficients(Node n, Node var_node, std::vector<Integer>& v_coefs)
{
   // Trace("smt-qe") << "node has type " << n.getKind() << std::endl;
   for (int i = 0; i < n.getNumChildren(); ++i) {
        Node child = n[i];

        if (child.getKind() == MULT && child.getNumChildren() == 2)
        {
            if (child[0].isConst() && child[1].isVar() && child[1].getName() == var_node.toString())
            {
               v_coefs.push_back(child[0].getConst<Rational>().getNumerator());
            }
            else if (child[1].isConst() && child[0].isVar() && child[0].getName() == var_node.toString())
            {
               v_coefs.push_back(child[1].getConst<Rational>().getNumerator());
            }
        }

        getCoefficients(child, var_node, v_coefs);
   } 
}

bool sameVar(Node n1, Node n2) 
{
   return n1.isVar() && n2.isVar() && n1.toString() == n2.toString();
}

Node substituteCoefficients(Node n, Integer k, Integer a, Node var_node)
{
   // Found a node that directly references the bound variable
   if (sameVar(var_node, n)) 
   {
      return n; // found the node referencing the bound variable, leave it as it is
   }
   // Found a node that is a negation of the bound variable
   else if (n.getKind() == NEG && sameVar(var_node, n[0])) 
   {
      return n[0];
   }
   // Found a node that is the bound variable with a coefficient
   else if (n.getKind() == MULT && (sameVar(var_node, n[0]) || sameVar(var_node, n[1])))
   {
      return sameVar(var_node, n[0]) ? n[0] : n[1];  
   }
   // Found a node that represents a variable or an integent constant
   else if (n.getKind() == VARIABLE || n.getKind() == CONST_INTEGER) {
      NodeManager* nm = NodeManager::currentNM();
      // if constant equal to zero, return the node as it is
      if (n.getKind() == CONST_INTEGER && n.getConst<Rational>().isZero()) 
      {
         return n; 
      }
      // if a>0: ay+t<0 −> y+(k/a)·t<0
      else if (a.strictlyPositive()) 
      {
         Integer ratio = k.exactQuotient(a);
         return ratio.isOne() ? n : nm->mkNode(MULT, nm->mkConstInt(Rational(ratio)), n);
      }
      // if a<0: ay+t<0 −> −ky−(k/a)·t<0
      else 
      {
         Integer ratio = k.exactQuotient(-a); 
         return nm->mkNode(MULT, nm->mkConstInt(Rational(ratio)), n);
      }
   }
   // For nodes of kinds AND, OR, etc. apply the function to the node's children recursively
   else if (n.getNumChildren() > 0)
   {
      // Trace("smt-qe") << "Running a node builder with the node n = " << n << std::endl;
      NodeBuilder nb(n.getKind());
      for (int i = 0; i < n.getNumChildren(); ++i)
      {
         nb << substituteCoefficients(n[i], k, a, var_node);
      } 
      Node ret = nb;
      // Trace("smt-qe") << "built " << ret << std::endl;
      return ret;
   }
   else {
      return n;
   }
}

Node normaliseCoefficients(Node n, Integer k, Node var_node)
{
   if (n.getKind() == LT)
   {
      Node lhs = n[0];
      std::vector<Integer> v_coefs;
      getCoefficients(n,var_node,v_coefs);

      if (v_coefs.size() == 1)
      {
         Integer a = v_coefs.at(0);
         return substituteCoefficients(n, k, a, var_node);
      }
      else
      {
         return substituteCoefficients(n, k, Integer(1), var_node);
      }
   }
   else
   {
      NodeBuilder nb(n.getKind());
      for (int i = 0; i < n.getNumChildren(); i++)
      {
         nb << normaliseCoefficients(n[i], k, var_node);
      }
      return nb;
   }
}

Node normaliseFormula(Node n)
{   
   Node bv_node = n[0][0];
   std::vector<Integer> v_coefs;
   getCoefficients(n, bv_node, v_coefs);
   Integer k(1);
   for (Integer coef : v_coefs)
   {
      k = k.lcm(coef);
   }

   NodeManager* nm = NodeManager::currentNM();
   Node expr = nm->mkNode(
       AND,
       normaliseCoefficients(n[2], k, bv_node),
       nm->mkNode(EQUAL,
                  nm->mkConstInt(Rational(0)),
                  nm->mkNode(INTS_MODULUS, bv_node, nm->mkConstInt(k))));
   n = nm->mkNode(n.getKind(), n[0], n[1], expr);

   return n;   
}

Node subdivideFormula(Node n)
{
   return n;
}

Node splitRange(Node n)
{
   return n;
}

Node computeNumSolutions(Node n) 
{
   return n;
}

Node sumSolutions(Node n)
{
   return n;
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
         n = nm->mkNode(LT, nm->mkNode(NEG,n[0]), n[1]);
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
         n = nm->mkNode(LT, nm->mkNode(SUB, nm->mkNode(SUB, n[0], n[1]), oneNode), zeroNode);
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
         n = nm->mkNode(LT, nm->mkNode(SUB, nm->mkNode(SUB, n[1], n[0]), oneNode), zeroNode);
      }
      else
      {
         n = nm->mkNode(LT, nm->mkNode(SUB, nm->mkNode(NEG, n[0]), oneNode), zeroNode);
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

void calculateTerms(Node n, std::unordered_set<Node>& s_terms)
{  

}

}  // namespace expr
}  // namespace cvc5::internal
