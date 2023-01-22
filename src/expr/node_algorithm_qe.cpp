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
   NodeManager* nm = NodeManager::currentNM();
   // Found a node that directly references the bound variable
   if (sameVar(var_node, n) ||
       // Found a node that is a negation of the bound variable
       (n.getKind() == NEG && sameVar(var_node, n[0])))
   {
      return n; // found the node referencing the bound variable, leave it as it is
   }
   // Found a node that is the bound variable with a coefficient
   else if (n.getKind() == MULT && (sameVar(var_node, n[0]) || sameVar(var_node, n[1])))
   {
      // return sameVar(var_node, n[0]) ? n[0] : n[1];  
      Node coef_node = sameVar(var_node, n[0]) ? n[1] : n[0];
      Integer coef_val = coef_node.getConst<Rational>().getNumerator();
      if (coef_val.strictlyPositive())
      {
         return var_node;
      }
      else
      {
         return nm->mkNode(NEG, var_node);
      }
   }
   // Found a node that represents a variable or an integent constant
   else if (n.getKind() == VARIABLE || n.getKind() == CONST_INTEGER) {
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
   std::unordered_set<Node> T;
   T.insert(NodeManager::currentNM()->mkConstInt(Rational(0)));
   Node bound_var_node = n[0][0];
   Node formula_node = n[2];

   Trace("smt-qe") << "bound var: " << bound_var_node << std::endl
                   << "formula: " << formula_node << std::endl;

   calculateTerms(formula_node, bound_var_node, T);

   Trace("smt-qe") << "Calculated set T: " << T << std::endl;

   std::unordered_set<Node> orderings = getOrderings(T);

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

bool isVarOrNeg(Node n, Node var_node)
{
   return sameVar(n, var_node) || (n.getKind() == NEG && sameVar(n[0], var_node));
}

// bool binopHasVarOrNeg(Node n, Node var_node)
// {
//     return (sameVar(n[0], var_node) || sameVar(n[1], var_node))
//             || (n[0].getKind() == NEG && sameVar(n[0][0], var_node))
//             || (n[1].getKind() == NEG && sameVar(n[1][0], var_node));
// }

// TO DO
Node removeBoundVariable(Node n, Node var_node, bool& negated)
{
   // Trace("smt-qe") << "removeBoundVariable: node is " << n << std::endl;
   if (n.getNumChildren() > 0)
   {
      if (n.getKind() == ADD || n.getKind() == SUB || n.getKind() == MULT)
      {
         NodeManager* nm = NodeManager::currentNM();
         if (isVarOrNeg(n[0], var_node) || isVarOrNeg(n[1], var_node))
         {
            // Trace("smt-qe") << "removeBoundVariable: binop contains bound variable " << n << std::endl;
            Node var_term = isVarOrNeg(n[0], var_node) ? n[0] : n[1];
            Node non_var_term = isVarOrNeg(n[0], var_node) ? n[1] : n[0];

            // Trace("smt-qe") << "var_term: " << var_term << std::endl
            //                 << "non_var_term: " << non_var_term << std::endl;

            if (var_term.getKind() == NEG) {
               negated = true;
            }
            if (n.getKind() == SUB && isVarOrNeg(n[0], var_node)) 
            {
               return nm->mkNode(NEG, removeBoundVariable(n[1], var_node, negated));  
            }
            else
            {
               return removeBoundVariable(non_var_term, var_node, negated);
            }
         }
         else 
         {
            return nm->mkNode(n.getKind(),
                              removeBoundVariable(n[0], var_node, negated),
                              removeBoundVariable(n[1], var_node, negated));
         }
      }
      return n;
   }
   else
   {
      // A leaf node in the AST, CONST_INTEGER or VARIABLE that is 
      // guaranteed not to be the bound variable or a negation of it
      // Trace("smt-qe") << "removeBoundVariable: returning leaf " << n << std::endl;
      return n;
   }
}

// TO DO
void calculateTerms(Node n, Node var_node, std::unordered_set<Node>& s_terms)
{  
   // Trace("smt-qe") << "calculateTerms: current node = " << n << std::endl;

   if (n.getKind() == LT) 
   {
      Trace("smt-qe") << "calculateTerms: term is of kind LT: " << n << std::endl;
      NodeManager* nm = NodeManager::currentNM();
      bool negated = false;
      Node term = removeBoundVariable(n[0], var_node, negated);
      if (!negated) {
         term = nm->mkNode(NEG, term);
      }
      Trace("smt-qe") << "calculateTerms: transformed LHS of the inequality : " << term << std::endl;
      if (term.getKind() == NEG && term[0].getKind() == NEG) 
      {
         term = term[0][0];
      }
      if (term.getKind() == NEG && term[0].getKind() == SUB)
      {
         term = nm->mkNode(SUB, term[0][1], term[0][0]);
      }
      s_terms.insert(term);
   }
   else
   {
      // Trace("smt-qe") << "calculateTerms: term is not LT: " << n << std::endl;
 
      for (int i = 0; i < n.getNumChildren(); ++i)
      {
         calculateTerms(n[i], var_node, s_terms);
      }
   }
}

// TO DO
std::unordered_set<Node> getOrderings(std::unordered_set<Node>& T)
{
   std::unordered_set<Node> orderings;

   return orderings;
}

}  // namespace expr
}  // namespace cvc5::internal
