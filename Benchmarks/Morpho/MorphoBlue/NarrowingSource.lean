import Benchmarks.Morpho.MorphoBlue.MarketStorageCommon

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

-- LIBRARY CANDIDATE: canonical uint128 values survive explicit narrowing.
theorem halfWord_low_clean (x : UInt256) (h : x.toNat < 2 ^ 128) : halfWord false x = x :=
  u256LandMaskCleanOfToNat x uint128Mask (by decide) h

abbrev toUint128Function : FunctionDecl := contract.functions[5]!

def toUint128Frame (x : UInt256) (imms : Store) : Frame :=
  { contract := contract, locals := (∅ : Store).insert "x" (.int (Int.ofNat x.toNat)), immutables := imms }

theorem toUint128_eval_x (x : UInt256) (imms : Store) (evm : EVM.State) :
    evalExpr? config (toUint128Frame x imms) evm (.var "x") = .ok (.int (Int.ofNat x.toNat)) := by
  simp only [evalExpr?, toUint128Frame, store_get_self, EvalResult.ofOption]

theorem toUint128_eval_guard (x : UInt256) (imms : Store) (evm : EVM.State) :
    evalExpr? config (toUint128Frame x imms) evm
      (.binary .le (.var "x") (.intLit 340282366920938463463374607431768211455)) =
      .ok (.bool (decide (x.toNat < 2 ^ 128))) := by
  simp only [evalExpr?, toUint128_eval_x, bind, EvalResult.bind, pure, evalBinaryOp?]
  congr 2
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  change Int.ofNat x.toNat ≤ Int.ofNat (2 ^ 128 - 1) ↔ x.toNat < 2 ^ 128
  simp only [Int.ofNat_eq_natCast, Int.ofNat_le]
  omega

theorem morphoToUint128BodyOk (x : UInt256) (evm : EVM.State) (imms : Store)
    (hfit : x.toNat < 2 ^ 128) :
    ExecFuncBody config (toUint128Frame x imms) evm toUint128Function.body
      (.returned (toUint128Frame x imms) evm (some [.int (Int.ofNat x.toNat)])) := by
  apply ExecFuncBody.execBlockRet
  apply (ABlock.start.requireStep (by simpa only [decide_eq_true hfit] using (toUint128_eval_guard x imms evm))).returns
  simpa only [halfWord_low_clean x hfit] using evalCastUint128 (toUint128_eval_x x imms evm)

theorem morphoToUint128BodyReverts (x : UInt256) (evm : EVM.State) (imms : Store)
    (hover : 2 ^ 128 ≤ x.toNat) :
    ExecFuncBody config (toUint128Frame x imms) evm toUint128Function.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  exact ABlock.start.requireRevert (by simpa only [decide_eq_false (Nat.not_lt_of_ge hover)] using (toUint128_eval_guard x imms evm))

theorem morphoToUint128CallOk (x : UInt256) (evm : EVM.State) (locals imms : Store)
    (ex : Expr) (retVar : Ident)
    (hx : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm ex =
      .ok (.int (Int.ofNat x.toNat))) (hfit : x.toNat < 2 ^ 128) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "UtilsLib_toUint128" [ex] retVar)
      (.ok { contract := contract, locals := locals.insert retVar (.int (Int.ofNat x.toNat)), immutables := imms } evm) := by
  exact internalCallFunctionReturn (callee := toUint128Function)
    (value := some [.int (Int.ofNat x.toNat)]) (evalExprs?_singleton hx) rfl rfl
    (morphoToUint128BodyOk x evm imms hfit)

theorem morphoToUint128CallReverts (x : UInt256) (evm : EVM.State) (locals imms : Store)
    (ex : Expr) (retVar : Ident)
    (hx : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm ex =
      .ok (.int (Int.ofNat x.toNat))) (hover : 2 ^ 128 ≤ x.toNat) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "UtilsLib_toUint128" [ex] retVar) .reverted := by
  exact internalCallFunctionRevert (callee := toUint128Function) (evalExprs?_singleton hx) rfl rfl
    (morphoToUint128BodyReverts x evm imms hover)

end Benchmarks.Morpho.MorphoBlue
