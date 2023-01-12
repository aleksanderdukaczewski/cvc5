/***********************************************************
 * Contributors:
 *  Aleksander Dukaczewski (Uni. of Warwick)
 * 
 * This file is part of a fork of the cvc5 project, which 
 * is the student's dissertation project (CS310 module)
 * 
 * The solver for quantifier elimination queries with Presburger arithmetic with counting quantifiers.
 */

#include "cvc5_private.h"

#ifndef CVC5__SMT__COUNTING_QUANT_ELIM_SOLVER_H
#define CVC5__SMT__COUNTING_QUANT_ELIM_SOLVER_H

#include "expr/node.h"
#include "smt/assertions.h"
#include "smt/env_obj.h"

namespace cvc5::internal {
namespace smt {

class SmtSolver;

class CountingQuantElimSolver : protected EnvObj
{
    public:
        CountingQuantElimSolver(Env& env, SmtSolver& sms);
        ~CountingQuantElimSolver();
        Node getQuantifierElimination(Node q, bool doFull, bool isInternalSubsolver);

    private:
        /** The SMT solver, which is used during doQuantifierElimination. */
        SmtSolver& d_smtSolver;
};

}  // namespace smt
}  // namespace cvc5::internal

#endif /* CVC5__SMT__COUNTING_QUANT_ELIM_SOLVER_H */
