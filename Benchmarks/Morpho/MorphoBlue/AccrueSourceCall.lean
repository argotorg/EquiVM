import Benchmarks.Morpho.MorphoBlue.AccrueSourceStart
import Benchmarks.Morpho.MorphoBlue.BorrowRateABI

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

abbrev accrueIrmBody : List Stmt :=
  match accrueInterestFunction.body[2]! with
  | .ite _ yes _ => yes
  | _ => []

def accrueBeforeCall (p : MarketParamsWords) (imms : Store) (elapsed : UInt256) (evm : EVM.State) : Frame :=
  { accrueAfterElapsed p imms elapsed with locals :=
    (((accrueAfterElapsed p imms elapsed).locals.insert "irm"
      (.address (AccountAddress.ofNat p.irm.toNat))).insert "marketState"
        (marketStateValue evm.accountMap evm.executionEnv p.id)) }

def accrueAfterCall (p : MarketParamsWords) (imms : Store) (elapsed : UInt256)
    (evm : EVM.State) (rate : UInt256) : Frame :=
  { accrueBeforeCall p imms elapsed evm with locals :=
    (accrueBeforeCall p imms elapsed evm).locals.insert "borrowRate" (.int (Int.ofNat rate.toNat)) }

theorem accrueBeforeCall_locals (p : MarketParamsWords) (imms : Store) (elapsed : UInt256) (evm : EVM.State) :
    MarketLocals p (accrueBeforeCall p imms elapsed evm).locals :=
  ((accrueElapsed_locals p imms elapsed).insert "irm" _ (by decide)).insert "marketState" _ (by decide)

theorem accrueAfterCall_locals (p : MarketParamsWords) (imms : Store) (elapsed : UInt256)
    (evm : EVM.State) (rate : UInt256) :
    MarketLocals p (accrueAfterCall p imms elapsed evm rate).locals :=
  (accrueBeforeCall_locals p imms elapsed evm).insert "borrowRate" _ (by decide)

theorem morphoAccrueCallPrelude (p : MarketParamsWords) (imms : Store) (elapsed : UInt256) (evm : EVM.State) :
    ABlock config evm (accrueAfterElapsed p imms elapsed) accrueIrmBody
      (accrueBeforeCall p imms elapsed evm) (accrueIrmBody.drop 2) := by
  apply (ABlock.start.letStep ((accrueElapsed_locals p imms elapsed).evalIrm imms evm)).letStep
  have hl := (accrueElapsed_locals p imms elapsed).insert "irm"
    (.address (AccountAddress.ofNat p.irm.toNat)) (by decide)
  exact evalMarketState evm _ imms (.var "id") p.id hl.market (hl.evalId imms evm)

theorem accrue_eval_call_receiver (p : MarketParamsWords) (imms : Store) (elapsed : UInt256) (evm : EVM.State) :
    evalExpr? config (accrueBeforeCall p imms elapsed evm) evm (.var "irm") =
      .ok (.address (AccountAddress.ofNat p.irm.toNat)) := by
  simp only [evalExpr?, accrueBeforeCall,
    store_get_ne (k := "marketState") (a := "irm") _ _ (by decide), store_get_self, EvalResult.ofOption]

theorem accrue_eval_call_args (p : MarketParamsWords) (imms : Store) (elapsed : UInt256) (evm : EVM.State) :
    evalExprs? config (accrueBeforeCall p imms elapsed evm) evm [.var "marketParams", .var "marketState"] =
      .ok [p.value, marketStateValue evm.accountMap evm.executionEnv p.id] := by
  have hp := (accrueBeforeCall_locals p imms elapsed evm).evalParams imms evm
  change evalExpr? config (accrueBeforeCall p imms elapsed evm) evm (.var "marketParams") = .ok p.value at hp
  have hm : evalExpr? config (accrueBeforeCall p imms elapsed evm) evm (.var "marketState") =
      .ok (marketStateValue evm.accountMap evm.executionEnv p.id) := by
    simp only [evalExpr?, accrueBeforeCall, store_get_self, EvalResult.ofOption]
  simp only [evalExprs?, hp, hm, pure, bind, EvalResult.bind]

theorem decodeBorrowRate_word {out : ByteArray} (hlen : 32 ≤ out.size) (hhi : out.size < 2 ^ 255) :
    config.externalABI.decode? "borrowRate" out = some [.int (Int.ofNat (calldataWord out 0).toNat)] := by
  rw [decodeBorrowRate_ok hlen hhi, ← calldataWord_bytes hlen, fromByteArrayBigEndian_toByteArray]

theorem morphoAccrueSourceCallOk (p : MarketParamsWords) (imms : Store) (elapsed : UInt256)
    (evm evm' : EVM.State) (out : ByteArray)
    (hcall : typedCallViaEVM config evm (AccountAddress.ofNat p.irm.toNat) "borrowRate" 0
      [p.value, marketStateValue evm.accountMap evm.executionEnv p.id] (true, evm', out))
    (hlen : 32 ≤ out.size) (hout : out.size < 2 ^ 138) :
    ExecStmt config (accrueBeforeCall p imms elapsed evm) evm accrueIrmBody[2]!
      (.ok (accrueAfterCall p imms elapsed evm (calldataWord out 0)) evm') := by
  have htarget : EVM.address (AccountAddress.ofNat p.irm.toNat).val =
      AccountAddress.ofNat p.irm.toNat := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt (AccountAddress.ofNat p.irm.toNat).isLt
  rw [← htarget] at hcall
  change ExecStmt config (accrueBeforeCall p imms elapsed evm) evm
    (.externalCall (.var "irm") "borrowRate" (.intLit 0) [.var "marketParams", .var "marketState"] "borrowRate")
    (.ok (accrueAfterCall p imms elapsed evm (calldataWord out 0)) evm')
  exact ExecStmt.externalCallSuccess (value := [.int (Int.ofNat (calldataWord out 0).toNat)])
    (accrue_eval_call_receiver p imms elapsed evm)
    (by simp only [evalExpr?, pure]) (accrue_eval_call_args p imms elapsed evm) hcall
    (decodeBorrowRate_word hlen (by omega))

theorem morphoAccrueSourceCallReverts (p : MarketParamsWords) (imms : Store) (elapsed : UInt256)
    (evm evm' : EVM.State) (z : Bool) (out : ByteArray)
    (hcall : typedCallViaEVM config evm (AccountAddress.ofNat p.irm.toNat) "borrowRate" 0
      [p.value, marketStateValue evm.accountMap evm.executionEnv p.id] (z, evm', out))
    (hbad : ¬ (z = true ∧ 32 ≤ out.size)) :
    ExecBlock config (accrueAfterElapsed p imms elapsed) evm accrueIrmBody .reverted := by
  apply (morphoAccrueCallPrelude p imms elapsed evm).run
  apply ExecBlock.consRevert
  have htarget : EVM.address (AccountAddress.ofNat p.irm.toNat).val =
      AccountAddress.ofNat p.irm.toNat := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt (AccountAddress.ofNat p.irm.toNat).isLt
  rw [← htarget] at hcall
  cases z
  · exact ExecStmt.externalCallFailure (accrue_eval_call_receiver p imms elapsed evm)
      (by simp only [evalExpr?, pure]) (accrue_eval_call_args p imms elapsed evm) hcall
  · exact ExecStmt.externalCallReturnDecodeRevert (accrue_eval_call_receiver p imms elapsed evm)
      (by simp only [evalExpr?, pure]) (accrue_eval_call_args p imms elapsed evm) hcall
      (decodeBorrowRate_short (by simp only [true_and] at hbad; omega))

theorem accrueAfterCall_eval_rate (p : MarketParamsWords) (imms : Store) (elapsed rate : UInt256)
    (evm evm' : EVM.State) :
    evalExpr? config (accrueAfterCall p imms elapsed evm rate) evm' (.var "borrowRate") =
      .ok (.int (Int.ofNat rate.toNat)) := by
  simp only [evalExpr?, accrueAfterCall, store_get_self, EvalResult.ofOption]

theorem accrueAfterCall_eval_elapsed (p : MarketParamsWords) (imms : Store) (elapsed rate : UInt256)
    (evm evm' : EVM.State) :
    evalExpr? config (accrueAfterCall p imms elapsed evm rate) evm' (.var "elapsed") =
      .ok (.int (Int.ofNat elapsed.toNat)) := by
  simp only [evalExpr?, accrueAfterCall, accrueBeforeCall, accrueAfterElapsed,
    store_get_ne (k := "borrowRate") (a := "elapsed") _ _ (by decide),
    store_get_ne (k := "marketState") (a := "elapsed") _ _ (by decide),
    store_get_ne (k := "irm") (a := "elapsed") _ _ (by decide), store_get_self, EvalResult.ofOption]

end Benchmarks.Morpho.MorphoBlue
