#include "expr/node_algorithm_qe.h"

#include "expr/attribute.h"
#include "expr/dtype.h"
#include "expr/node.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace expr {

void getCoefficients(std::string varName, Node n, std::vector<Integer>& v_coefs)
{
   for (int i = 0; i < n.getNumChildren(); ++i) {
        Node child = n[i];

        if (child.getKind() == MULT && child.getNumChildren() == 2)
        {
            if (child[0].isConst() && child[1].isVar() && child[1].getName() == varName)
            {
               v_coefs.push_back(child[0].getConst<Rational>().getNumerator());
            }
            else if (child[1].isConst() && child[0].isVar() && child[0].getName() == varName)
            {
               v_coefs.push_back(child[1].getConst<Rational>().getNumerator());
            }
        }

        getCoefficients(varName, child, v_coefs);
   } 
}

Integer getLcmCoefficients(std::string varName, Node n)
{
   std::vector<Integer> v_coefs;
   getCoefficients(varName, n, v_coefs);

   Integer ret(1);
   for (Integer coef : v_coefs)
   {
      ret = ret.lcm(coef);
   }

   return ret;
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