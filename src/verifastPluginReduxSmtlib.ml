module R = Redux
module Sp = Smtlibprover
module S = Smtlib
module P = Proverapi
module C = Combineprovers

let _ =
  Verifast.register_prover "redux+smtlib"
    "\nRun redux and perform an SMTLib dump."
    (
      fun client ->
      let redux_ctxt =
        (new R.context ():
           R.context :> (unit, R.symbol, (R.symbol, R.termnode) R.term) P.context)
      in
      let smtlib_ctxt =
        (new Sp.smtlib_context():
           Sp.smtlib_context :> (S.sort, S.symbol, S.term) P.context)
      in
      client#run (C.combine redux_ctxt smtlib_ctxt C.Sync)
    )