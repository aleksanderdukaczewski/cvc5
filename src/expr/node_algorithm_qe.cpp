#include "expr/node_algorithm_qe.h"

#include "expr/attribute.h"
#include "expr/dtype.h"
#include "expr/node.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace expr {

void getCoefficients(std::string boundVarName, Node n, std::vector<Integer>& v_coefs)
{
   for (int i = 0; i < n.getNumChildren(); ++i) {
        Node child = n[i];

        if (child.getKind() == MULT && child.getNumChildren() == 2)
        {
            if (child[0].isConst() && child[1].isVar() && child[1].getName() == boundVarName)
            {
               v_coefs.push_back(child[0].getConst<Rational>().getNumerator());
            }
            else if (child[1].isConst() && child[0].isVar() && child[0].getName() == boundVarName)
            {
               v_coefs.push_back(child[1].getConst<Rational>().getNumerator());
            }
        }
        
        getCoefficients(boundVarName, child, v_coefs);
   } 
}

Integer getLcmCoefficients(std::string boundVarName, Node n)
{
   std::vector<Integer> v_coefs;
   getCoefficients(boundVarName, n, v_coefs);

   Integer ret(1);
   for (Integer coef : v_coefs)
   {
      ret = ret.lcm(coef);
   }

   return ret;
}


}  // namespace expr
}  // namespace cvc5::internal