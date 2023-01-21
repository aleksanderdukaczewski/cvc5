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
   Trace("smt-qe") << "running substituteCoefficients on n = " << n << std::endl;

   if (sameVar(var_node, n)) 
   {
      return n; // found the node referencing the bound variable, leave it as it is
   }
   else if (n.getKind() == NEG && sameVar(var_node, n[0])) 
   {
      return n[0];
   }
   else if (n.getKind() == MULT && (sameVar(var_node, n[0]) || sameVar(var_node, n[1])))
   {
      Trace("smt-qe") << "Found a node that is the bound variable with a coefficient: " << n << std::endl;
      return sameVar(var_node, n[0]) ? n[0] : n[1];  
   }
   // TO DO
   else if (n.getKind() == VARIABLE || n.getKind() == CONST_INTEGER) {
      NodeManager* nm = NodeManager::currentNM();
      if (a.strictlyPositive())  
         return nm->mkNode(MULT, nm->mkConstInt(Rational(k.exactQuotient(a))), n);
      else
         return nm->mkNode(MULT, nm->mkConstInt(Rational(k.exactQuotient(-a))), n);
   }
   else if (n.getNumChildren() > 0)
   {
      Trace("smt-qe") << "Running a node builder with the node n = " << n << std::endl;
      NodeBuilder nb(n.getKind());
      for (int i = 0; i < n.getNumChildren(); ++i)
      {
         nb << substituteCoefficients(n[i], k, a, var_node);
      } 
      Node ret = nb;
      Trace("smt-qe") << "built " << ret << std::endl;
      return ret;
   }
   else {
      return n;
   }
}

Node normaliseCoefficients(Node n, Integer k, Node var_node)
{
   Trace("smt-qe") << "normaliseCoefficients: currently considered node = " << n << std::endl;
   if (n.getKind() == LT)
   {
      Node lhs = n[0];
      std::vector<Integer> v_coefs;
      getCoefficients(n,var_node,v_coefs);

      if (v_coefs.size() == 1)
      {
         Integer a = v_coefs.at(0);
         Trace("smt-qe") << "found one coef = " << a.toString() << std::endl;
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
      Trace("smt-qe") << " normaliseCoefficients: returning " << nb << std::endl;
      return nb;
   }
}

Node normalise(Node n)
{   
   std::vector<Integer> v_coefs;
   Node bv_node = n[0][0];
   
   Trace("smt-qe") << "going to get coefficients" << std::endl;
   getCoefficients(n, bv_node, v_coefs);
   Integer k(1);
   for (Integer coef : v_coefs)
   {
      k = k.lcm(coef);
   }
   Trace("smt-qe") << "calculated lcm: " << k.toString() << std::endl;
   return normaliseCoefficients(n[2], k, bv_node);   
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

}  // namespace expr
}  // namespace cvc5::internal
