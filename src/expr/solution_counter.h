
#ifndef CVC5_ORDERINGS_H
#define CVC5_ORDERINGS_H

#include "expr/node.h"
#include "smt/smt_driver.h"
#include "smt/quant_elim_solver.h"
#include "theory/rewriter.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {

struct Ordering
{
  std::vector<Node> terms;
  std::vector<Kind_t> rels;
  /**
   * Convert the ordering to an equivalent node representation
   * @return node representing the ordering
   */
  Node getNode();
};

class SolutionCounter
{
 public:
  SolutionCounter(theory::Rewriter* d_rewriter);
  ~SolutionCounter();

  /**
   * Convert all orderings in the vector fam to nodes
   * @param fam vector of Ordering objects to be converted to nodes
   * @return vector of nodes equivalent to fam
   */
  std::vector<Node> familyToNodes(std::vector<Ordering>& fam);
  /**
   * Using a dynamic programming algorithm, compute the vector of all satisfiable orderings on nodes from the vector terms.
   * @param terms_s
   * @return a vector of satisfiable orderings of nodes from terms.
   */
  std::vector<Ordering> computeOrderings(std::unordered_set<Node>& terms_s);
  /**
   * Generate a vector of segments for a bound variable bv and ordering ord, as described in Step III of the procedure.
   * @param bv node representing the bound variable.
   * @param ord the ordering used to generate the segments.
   * @return a vector of nodes representing the segment
   */
  std::vector<Node> getSegments(Node& bv, Ordering& ord);
  /**
   * Generate assignments of residue classes to variables by recursively generating combinations of
   * numbers from 0 to range-1 of length variables.size() and putting them in a vector
   * of unordered_maps with keys representing the variable names.
   * @param range the upper bound of the integers to calculate combinations of (lower bound = 0)
   * @param variables vector of variables occurring in the investigated formula
   * @return a vector of unordered_maps representing the assignment of residue classes.
   */
  static std::vector<std::unordered_map<std::string, Node>>
  generateResidueClassMappings(int range, std::vector<Node>& variables);
  /**
   * Given a map representing an assignment of residue classes to variables, a vector
   * of variables and lcm of all moduli occurring in the investigated formula and create a conjunction
   * of modulo constraints modulo m as in substep 8 of the procedure.
   * @param assignment map representing assignment of residue classes to variables
   * @param variables vector of nodes with variables
   * @param m lcm of all moduli occurring in the investigated formula
   * @return conjunction of assignments of modulo classes to variables
   */
  Node assignResidueClass(std::unordered_map<std::string, Node> assignment,
                          std::vector<Node> variables,
                          Integer m);
  /**
   * Given a map assignment representing assigment of residue classes to variables,
   * use NodeTemplate::substitute to substitute all variables occurring in n with their residue classes.
   * @param n A term without a bound variable
   * @param assignment A map with assignment of residue classes to variables
   * @param variables Vector of nodes each representing a variable occurring in the main formula
   * @return n with residue classes substituted for variables
   */
  static Node getTermAssignment(Node n,
                         std::unordered_map<std::string, Node>& assignment,
                         std::vector<Node>& variables);
  /**
   * As in the Step IV of the procedure, consider each segment constructed from pairwise non-equal
   * terms from ord and the bound variable from q, then compute vectors of numbers p, r and c.
   * @param ord Ordering to construct segments from
   * @param assignment map representing assignment of residue classes to variables
   * @param variables vector representing non-bound variables from q
   * @param m lcm of all moduli in formula q
   * @param q formula under investigation
   * @param p reference to a vector of int as described in Step IV of the procedure
   * @param r reference to a vector of int as described in Step IV of the procedure
   * @param c reference to a vector of int as described in Step IV of the procedure
   * @return true if the ordering is satisfiable with the given assignment, else false
   */
  bool countSolutions(
      Ordering& ord,
      std::unordered_map<std::string, Node>& assignment,
      std::vector<Node>& variables,
      Integer& m,
      Node& q,
      std::vector<int>& p,
      std::vector<int>& r,
      std::vector<int>& c);
  /**
   * Given an ordering ord, construct a new ordering with pairwise non-equal terms from ord and LT as all every relation.
   * @param ord the ordering under investigation
   * @return ordering where all terms are pairwise non-equal
   */
  Ordering makePairwiseNonEqual(Ordering& ord);
  /**
   * As in lemma 3 of the procedure, calculate a boolean combination of simple modulo constraints
   * on the bound variable that does not introduce any new moduli by substituting other modulo constraints
   * and inequalities with their truth values asserted by ord and segment.
   * @param q Node representing the original quantified formula
   * @param ord Ordering to be evaluated
   * @param segment segment used to evaluate ord
   * @param assignment map representing assignment of residue classes to variables
   * @param variables vector representing non-bound variables from q
   * @param m lcm of all moduli in formula q
   * @return expression equivalent to q after substituting inequalities and modulo
   *         constraints where q's bound variable does not occur with their truth values.
   */
  Node evaluateOrdering(Node &q, Ordering& ord, Node& segment, std::unordered_map<std::string, Node>& assignment, std::vector<Node>& variables, Integer& m);

 private:
  /**
   * Helper function for computeOrderings that
   * @param j iteration
   * @param prev_fam Family computed in the previous iteration
   * @param terms set of terms to compute orderings from
   * @return A new family of orderings based on a previous one
   */
  std::vector<Ordering> computeFamily(int j,
                                      std::vector<Ordering>& prev_fam,
                                      std::vector<Node>& terms);
  /**
   * Using a local SolverEngine instance, check if ord is satisfiable.
   * @param ord Ordering to be checked for satisfiability
   * @return true if ord is satisfiable else false
   */
  bool satisfiableOrdering(Ordering& ord);
  /**
   * Using a recursive depth-first solution, evaluate the truth values of all modulo constraints in
   * node curr where the bound variable doesn't occur, and
   * @param conj Conjunction of a segment and big gamma (conjunction of ordering and assignment of residue classes to variables)
   * @param curr The node currently under investigation
   * @param q Node representing the original quantified formula
   * @return Node representing curr after substituting all modulo constraints with their truth values asserted by conj
   */
  Node evaluateModuloConstraints(Node& conj, Node curr, Node& q);
  /**
   * Using a recursive depth-first solution, evaluate the truth values of all inequalities in
   * node curr using the node conj representing the conjunction of a segment and big gamma
   * (conjunction of ordering and assignment of residue classes to variables)
   * @param conj Conjunction of a segment and big gamma (conjunction of ordering and assignment of residue classes to variables)
   * @param curr The node currently under investigation
   * @param q Node representing the original quantified formula
   * @return Node representing curr after substituting all inequalities with their truth values asserted by conj
   */
  Node evaluateInequalities(Node& conj, Node curr, Node& q);
  /**
   * Recursive function to generate combinations of numbers from
   * 0 to r-1 with repetition using a depth-first method.
   * @param assignment Currently generated vector of int representing the assignment to variable classes.
   * @param combinations The reference to vector containing
   * @param index The current index for inserting a number into the combination
   * @param r The range of numbers used to generate the combinations.
   * @param start The index in assignment to start insertions from
   * @param end The index in assignment to end insertions at
   */
  static void getCombinationsRec(
      std::vector<int> assignment,
      std::vector<std::vector<int>>& combinations,
      int index,
      int r,
      int start,
      int end);

  /**
   * Given a TNode n of kind CONST_INTEGER, extract int value from it
   * @param n node of kind CONST_INTEGER
   * @return integer stored in the node.
   */
  int extractInt(TNode& n);

  /**
   * A pointer to a Rewriter object needed by the NormalizationEngine to
   * simplify arithmetic expressions in processModuloConstraint and
   * normalizeCoefficients.
   */
  theory::Rewriter* d_rewriter;
};

}  // namespace cvc5::internal

#endif  // CVC5_ORDERINGS_H
