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
#include "expr/node_algorithm_qe.h"

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

    Trace("smt-qe") <<
      "Node q: " << q << std::endl << 
      "Node q's kind: " << q.getKind() << std::endl <<
      "q[0]: " << q[0] << std::endl <<
      "q[1]: " << q[1] << std::endl << 
      "q[2]: " << q[2] << std::endl;

    // ensure the body is rewritten
    q = nm->mkNode(q.getKind(), q[0], q[1], expr::rewriteIq(q[2]));
    Trace("smt-qe") << "Rewritten q: " << q << std::endl;

    // do nested quantifier elimination if necessary (Nested counting quantifier elimination not supported yet.)
    q = quantifiers::NestedQe::doNestedQe(d_env, q, true);
    Trace("smt-qe") << "QuantElimSolver: after nested quantifier elimination : "
                    << q << std::endl;
    
    std::unordered_set<TNode> vs;
    std::unordered_set<Node> syms;
    expr::getVariables(q,vs);
    expr::getSymbols(q,syms);

    Trace("smt-qe") << "variables : " << vs << std::endl;
    Trace("smt-qe") << "symbols: " << syms << std::endl;

    Node phi1 = expr::normalise(q); 

    return phi1;
  }
  else 
  {
    Trace("smt-qe") << "QuantElimSolver: get qe : " << q << std::endl;
    if (q.getKind() != EXISTS && q.getKind() != FORALL)
    {
      throw ModalException(
          "Expecting a quantified formula as argument to get-qe.");
    }

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