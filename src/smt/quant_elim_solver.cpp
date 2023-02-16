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
#include "expr/skolem_manager.h"
#include "expr/subs.h"
#include "expr/subtype_elim_node_converter.h"
#include "smt/smt_driver.h"
#include "smt/smt_solver.h"
#include "theory/quantifiers/cegqi/nested_qe.h"
#include "theory/quantifiers_engine.h"
#include "theory/theory_engine.h"
#include "util/string.h"

#include "expr/node_algorithm.h"
#include "expr/ordering_engine.h"
#include "expr/normalization_engine.h"

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
    Trace("smt-qe") << "Node q: " << q <<  " of kind " << q.getKind() << std::endl;
    NormalizationEngine ne(d_env.getRewriter());
    Node rewrittenExpr = ne.rewrite_qe(q[2]);
    Trace("smt-qe") << "Rewritten expr: " << rewrittenExpr << std::endl;

    // ensure the body is rewritten
    rewrittenExpr = ne.simplifyModuloConstraints(rewrittenExpr);
    q = nm->mkNode(q.getKind(), q[0], q[1], rewrittenExpr);
    Trace("smt-qe") << "expr after simplifying modulo constraints: " << rewrittenExpr << std::endl;

    // do nested quantifier elimination if necessary (Nested counting quantifier
    // elimination not supported yet.)
    q = quantifiers::NestedQe::doNestedQe(d_env, q, true);
    Trace("smt-qe") << "QuantElimSolver: after nested quantifier elimination : "
                    << q << std::endl;

    std::pair<Node, std::vector<Node>> normalised_p = NormalizationEngine::normalizeFormula(q);
    q = normalised_p.first;
    std::vector<Node> T = normalised_p.second;

    for (int i = 0; i < T.size(); ++i)
    {
      T[i] = rewrite(T[i]);
    }

    Trace("smt-qe") << "QuantElimSolver: after normalising the formula : " << q
                    << std::endl
                    << "set T: " << T << std::endl;

    OrderingEngine ordEng(T, d_env.getRewriter());
    std::vector<Ordering> orderings = ordEng.computeOrderings();
    Trace("smt-qe") << "orderings: " << ordEng.familyToNodes(orderings)
                    << std::endl;

    std::unordered_set<Node> Z;
    expr::getSymbols(q, Z);

    std::unordered_set<Node> moduli;
    expr::getModuli(q, moduli);
    Integer m = Integer(1);
    for (const auto& mod : moduli)
    {
      Integer mod_i = mod.getConst<Rational>().getNumerator();
      m = m.lcm(mod_i);
    }

    std::vector<Node> Z_vect;
    std::copy(Z.begin(), Z.end(), std::back_inserter(Z_vect));

    std::vector<std::unordered_map<std::string, Node>> mappings =
        ordEng.generateResidueClassMappings(3, Z_vect);

    for (auto& ord: orderings)
    {
      for (auto& residue_class: mappings)
      {
        Ordering processed_ord = ordEng.makePairwiseNonEqual(ord);
        int l = processed_ord.terms.size();
        std::vector<int> p(l,0), r(l,0), c(l,0);
        if (!ordEng.countSolutions(ord, residue_class, Z_vect, m, q, p, r, c))
        {
          continue;
        }

        Node sum1 = nm->mkConstInt(0);
        for (int j = 1; j < l; ++j)
        {
          sum1 = nm->mkNode(
              ADD,
              sum1,
              nm->mkNode(ADD,
                         nm->mkConstInt(r[j]),
                         nm->mkNode(MULT,
                                    nm->mkConstInt(p[j]),
                                    nm->mkNode(SUB,
                                               processed_ord.terms[j],
                                               processed_ord.terms[j - 1]))));
        }

        Node sum2 = nm->mkConstInt(0);
        for (int j = 0; j < l; ++j)
        {
          sum2 = nm->mkNode(ADD, sum2, nm->mkConstInt(c[j]));
        }

        Node phi = nm->mkNode(
            EQUAL,
            nm->mkNode(MULT, nm->mkConstInt(m), q[1]),
            nm->mkNode(ADD, sum1, nm->mkNode(MULT, nm->mkConstInt(m), sum2)));
      }
    }
    return q;
  }
  else
  {
    Trace("smt-qe") << "QuantElimSolver: get qe : " << q << std::endl;
    if (q.getKind() != EXISTS && q.getKind() != FORALL)
    {
      throw ModalException(
          "Expecting a quantified formula as argument to get-qe.");
    }

    Trace("smt-qe") << "q[0] = " << q[0] << " of kind = " << q[0].getKind() << std::endl
                    << "q[0][0] = " << q[0][0] << " of kind = " << q[0][0].getKind() << std::endl
//                    << "q[0][1] = " << q[0][1] << " of kind = " << q[0][1].getKind() << std::endl
                    << "q[1] = " << q[1] << " of kind = " << q[1].getKind() << std::endl;

    std::unordered_set<Node> s;
    expr::getFreeVariables(q, s);
    Trace("smt-qe") << "Subterms of q: " << s << std::endl;

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
    Trace("smt-qe-debug") << "n_attr : " << n_attr
                        << std::endl;
    std::vector<Node> children;
    children.push_back(q[0]);

    // Trace("smt-qe") << "kind is " << toString(q.getKind())
    //               << std::endl;
    // Trace("smt-qe") << "q[1] is " << q[1]
    //               << std::endl;

    children.push_back(q.getKind() == EXISTS ? q[1] : q[1].negate());
    children.push_back(n_attr);
    Node ne = nm->mkNode(EXISTS, children);
    Trace("smt-qe-debug") << "Query for quantifier elimination : " << ne
                          << std::endl;
    Assert(ne.getNumChildren() == 3);
    // use a single call driver
    SmtDriverSingleCall sdsc(d_env, d_smtSolver);
    Trace("smt-qe") << "Formula for query " << ne << std::endl;
    Trace("smt-qe") << "Formula after applying notNode() " << ne.notNode() << std::endl;
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
        Trace("smt-qe") << "QuantElimSolver returned : " << ret << std::endl;
        Trace("smt-qe") << "rewritten formula that QuantElimSolver returned : " << rewrite(ret) << std::endl;
        if (q.getKind() == EXISTS)
        {
          ret = rewrite(ret.negate());
          Trace("smt-qe") << "Negation of previously returned value (query has existential quantifier): " << ret << std::endl;
        }
      }
      else
      {
        ret = nm->mkConst(q.getKind() != EXISTS);
      }

      // do extended rewrite to minimize the size of the formula aggressively
      // Trace("smt-qe") << "ret before extendedRewrite: " << ret << std::endl;
      ret = extendedRewrite(ret);
      // Trace("smt-qe") << "ret after extendedRewrite: " << ret << std::endl;

      // if we are not an internal subsolver, convert to witness form, since
      // internally generated skolems should not escape
      if (!isInternalSubsolver)
      {
        ret = SkolemManager::getOriginalForm(ret);
      }
      // make so that the returned formula does not involve arithmetic subtyping
      SubtypeElimNodeConverter senc;
      ret = senc.convert(ret);
      return ret;
    }
    // otherwise, just true/false
    return nm->mkConst(q.getKind() == EXISTS);
  }
}

}  // namespace smt
}  // namespace cvc5::internal