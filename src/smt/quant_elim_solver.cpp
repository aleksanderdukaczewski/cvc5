/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The solver for quantifier elimination queries.
 */

#include "smt/quant_elim_solver.h"

#include "base/modal_exception.h"
#include "expr/node_algorithm.h"
#include "expr/normalization_engine.h"
#include "expr/skolem_manager.h"
#include "expr/solution_counter.h"
#include "expr/subs.h"
#include "expr/subtype_elim_node_converter.h"
#include "smt/smt_driver.h"
#include "smt/smt_solver.h"
#include "theory/quantifiers/cegqi/nested_qe.h"
#include "theory/quantifiers_engine.h"
#include "theory/theory_engine.h"
#include "util/string.h"

using namespace cvc5::internal::theory;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace smt {

QuantElimSolver::QuantElimSolver(Env& env, SmtSolver& sms)
    : EnvObj(env), d_smtSolver(sms)
{
}

QuantElimSolver::~QuantElimSolver() {}

Node QuantElimSolver::getQuantifierElimination(Node q,
                                               bool doFull,
                                               bool isInternalSubsolver)
{
  NodeManager* nm = NodeManager::currentNM();

  if (q.getKind() == EXISTS_EXACTLY)
  {
    Trace("smt-qe") << "QuantElimSolver: get qe counted" << std::endl;
    Trace("smt-qe") << "Node q: " << q << std::endl;
    NormalizationEngine ne(d_env.getRewriter());
    // Rewrite the expression
    Node rewrittenExpr = ne.rewriteQe(q[2]);
    Trace("smt-qe") << "Rewritten expr: " << rewrittenExpr << std::endl;

    rewrittenExpr = ne.simplifyModuloConstraints(rewrittenExpr);
    q = nm->mkNode(q.getKind(), q[0], q[1], rewrittenExpr);
    Trace("smt-qe") << "expr after simplifying modulo constraints: " << rewrittenExpr << std::endl;

    std::unordered_set<Node> terms_s;
    q = ne.normalizeFormula(q, terms_s);
    Trace("smt-qe") << "QuantElimSolver: after normalising the formula : " << q
                    << std::endl << "terms_s = " << terms_s << std::endl;

    SolutionCounter sc(d_env.getRewriter());
    std::vector<Ordering> orderings = sc.computeOrderings(terms_s);
    Trace("smt-qe") << "orderings: " << Ordering::familyToNodes(orderings)
                    << std::endl;

    std::unordered_set<Node> moduli;
    expr::getModuli(q, moduli);
    Integer m = Integer(1);
    for (const auto& mod : moduli)
    {
      Integer mod_i = mod.getConst<Rational>().getNumerator();
      m = m.lcm(mod_i);
    }

    std::unordered_set<Node> Z;
    expr::getSymbols(q, Z);
    std::vector<Node> Z_vect(Z.begin(), Z.end());
    Trace("smt-qe") << "Variables (not bound)" << Z_vect << std::endl;
    std::vector<std::unordered_map<std::string, Node>> mappings =
        SolutionCounter::generateResidueClassMappings(m.getSignedInt(), Z_vect);

    Node falseNode = nm->mkConst<bool>(false);
    NodeBuilder ret(OR);
    Trace("smt-qe") << "number of orderings: " << orderings.size() << std::endl;
    Trace("smt-qe") << "number of mappings: " << mappings.size() << std::endl;

    for (auto& ord: orderings)
    {
      for (auto& residue_class : mappings)
      {
        Ordering processed_ord = ord.makePairwiseNonEqual();
        int l = processed_ord.d_terms.size();
        std::vector<int> p(l, 0), r(l, 0), c(l, 0);
        if (!sc.countSolutions(ord, residue_class, Z_vect, m, q, p, r, c))
        {
          continue;
        }

        NodeBuilder sum1(ADD);
        for (int j = 1; j < l; ++j)
        {
          sum1 << nm->mkNode(ADD,
                             nm->mkConstInt(r[j]),
                             nm->mkNode(MULT,
                                        nm->mkConstInt(p[j]),
                                        nm->mkNode(SUB,
                                                   processed_ord.d_terms[j],
                                                   processed_ord.d_terms[j - 1])));
        }

        NodeBuilder sum2(ADD);
        for (int j = 0; j < l; ++j)
        {
          sum2 << nm->mkConstInt(c[j]);
        }

        Node sum1Node;
        switch(sum1.getNumChildren())
        {
          case 0:
            sum1Node = nm->mkConstInt(0);
            break;
          case 1:
            sum1Node = sum1[0];
            break;
          default:
            sum1Node = sum1;
        }

        Node sum2Node;
        switch(sum2.getNumChildren())
        {
          case 0:
            sum1Node = nm->mkConstInt(0);
            break;
          case 1:
            sum2Node = sum2[0];
            break;
          default:
            sum2Node = sum2;
        }

        Node bigGamma =
            nm->mkNode(AND,
                       sc.assignResidueClass(residue_class, Z_vect, m),
                       ord.getNode());
        Node disjunct = nm->mkNode(
            AND,
            bigGamma,
            nm->mkNode(
                EQUAL,
                nm->mkNode(MULT, nm->mkConstInt(m), q[1]),
                nm->mkNode(
                    ADD, sum1Node, nm->mkNode(MULT, nm->mkConstInt(m), sum2Node))));

        if (rewrite(disjunct) != falseNode)
        {
          ret << disjunct;
        }
      }
    }
    switch (ret.getNumChildren())
    {
      case 0:
        return falseNode;
      case 1:
        return ret[0];
      default:
        return ret;
    }
  }
  else
  {
    Trace("smt-qe") << "QuantElimSolver: get qe : " << q << std::endl;
    if (q.getKind() != EXISTS && q.getKind() != FORALL)
    {
      throw ModalException(
          "Expecting a quantified formula as argument to get-qe.");
    }
    // ensure the body is rewritten
    q = nm->mkNode(q.getKind(), q[0], rewrite(q[1]));
    // do nested quantifier elimination if necessary
    q = quantifiers::NestedQe::doNestedQe(d_env, q, true);
    Trace("smt-qe") << "QuantElimSolver: after nested quantifier elimination : "
                    << q << std::endl;
    // tag the quantified formula with the quant-elim attribute
    TypeNode t = nm->booleanType();
    TheoryEngine* te = d_smtSolver.getTheoryEngine();
    Assert(te != nullptr);
    Node keyword =
        nm->mkConst(String(doFull ? "quant-elim" : "quant-elim-partial"));
    Node n_attr = nm->mkNode(INST_ATTRIBUTE, keyword);
    n_attr = nm->mkNode(INST_PATTERN_LIST, n_attr);
    std::vector<Node> children;
    children.push_back(q[0]);
    children.push_back(q.getKind() == EXISTS ? q[1] : q[1].negate());
    children.push_back(n_attr);
    Node ne = nm->mkNode(EXISTS, children);
    Trace("smt-qe-debug") << "Query for quantifier elimination : " << ne
                          << std::endl;
    Assert(ne.getNumChildren() == 3);
    // use a single call driver
    SmtDriverSingleCall sdsc(d_env, d_smtSolver);
    Result r = sdsc.checkSat(std::vector<Node>{ne.notNode()});
    Trace("smt-qe") << "Query returned " << r << std::endl;
    if (r.getStatus() != Result::UNSAT)
    {
      if (r.getStatus() != Result::SAT && doFull)
      {
        verbose(1)
            << "While performing quantifier elimination, unexpected result : "
            << r << " for query." << std::endl;
        // failed, return original
        return q;
      }
      QuantifiersEngine* qe = te->getQuantifiersEngine();
      // must use original quantified formula to compute QE, which ensures that
      // e.g. term formula removal is not run on the body. Notice that we assume
      // that the (single) quantified formula is preprocessed, rewritten
      // version of the input quantified formula q.
      std::vector<Node> inst_qs;
      qe->getInstantiatedQuantifiedFormulas(inst_qs);
      Node topq;
      // Find the quantified formula corresponding to the quantifier elimination
      for (const Node& qinst : inst_qs)
      {
        Trace("smt-qe") << "qinst: " << qinst << std::endl;
        // Should have the same attribute mark as above
        if (qinst.getNumChildren() == 3 && qinst[2] == n_attr)
        {
          topq = qinst;
          break;
        }
      }
      Node ret;
      if (!topq.isNull())
      {
        Assert(topq.getKind() == FORALL);
        Trace("smt-qe") << "Get qe based on preprocessed quantified formula "
                        << topq << std::endl;
        std::vector<Node> insts;
        qe->getInstantiations(topq, insts);
        // note we do not convert to witness form here, since we could be
        // an internal subsolver (SolverEngine::isInternalSubsolver).
        ret = nm->mkAnd(insts);
        if (q.getKind() == EXISTS)
        {
          ret = rewrite(ret.negate());
        }
        Trace("smt-qe") << "Initialized formula: "
                        << ret << std::endl;
      }
      else
      {
        ret = nm->mkConst(q.getKind() != EXISTS);
      }
      // do extended rewrite to minimize the size of the formula aggressively
      ret = extendedRewrite(ret);
      // if we are not an internal subsolver, convert to witness form, since
      // internally generated skolems should not escape
      if (!isInternalSubsolver)
      {
        ret = SkolemManager::getOriginalForm(ret);
      }
      // make so that the returned formula does not involve arithmetic subtyping
      SubtypeElimNodeConverter senc;
      ret = senc.convert(ret);
      Trace("smt-qe") << "Returning "
                      << ret << std::endl;
      return ret;
    }
    // otherwise, just true/false
    return nm->mkConst(q.getKind() == EXISTS);
  }
}

}  // namespace smt
}  // namespace cvc5::internal