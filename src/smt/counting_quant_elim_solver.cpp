/***********************************************************
 * Contributors:
 *  Aleksander Dukaczewski (Uni. of Warwick)
 * 
 * This file is part of a fork of the cvc5 project, which 
 * is the student's dissertation project (CS310 module)
 * 
 * The solver for quantifier elimination queries with Presburger arithmetic with counting quantifiers.
 */

#include "smt/counting_quant_elim_solver.h"

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

using namespace cvc5::internal::theory;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace smt {

CountingQuantElimSolver::CountingQuantElimSolver(Env& env, SmtSolver& sms)
    : EnvObj(env), d_smtSolver(sms)
{
}

CountingQuantElimSolver::~CountingQuantElimSolver() {}

Node CountingQuantElimSolver::getQuantifierElimination(Node q,
                                               bool doFull,
                                               bool isInternalSubsolver)
{
    Node ret;
    return ret;
}

}  // namespace smt
}  // namespace cvc5::internal