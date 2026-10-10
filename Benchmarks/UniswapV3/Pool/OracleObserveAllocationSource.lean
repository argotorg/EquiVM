import Benchmarks.UniswapV3.Pool.OracleObserveModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem evalOracleObserveLengthBound {cfg : Config} {frame : Frame} {evm : EVM.State}
    (n : Nat) (hb : n ≤ 2 ^ 64 - 1)
    (he : evalExpr? cfg frame evm (.arrayLength .localVar ⟨"secondsAgos", []⟩) =
      .ok (.int (Int.ofNat n))) :
    evalExpr? cfg frame evm (.binary .le (.arrayLength .localVar ⟨"secondsAgos", []⟩)
      (.intLit (2 ^ 64 - 1))) = .ok (.bool true) := by
  have hn : Int.ofNat n ≤ (2 ^ 64 - 1 : Int) := Int.ofNat_le.mpr hb
  simp only [evalExpr?, he, bind, EvalResult.bind, pure, evalBinaryOp?, decide_eq_true hn]

theorem oracleObserveAllocatePrefix (imms : Store) (evm : EVM.State) (time : UInt256)
    (secondsAgos : List UInt256) (tick : Int) (index liquidity card : UInt256)
    (hn : card.toNat ≠ 0) (hb : secondsAgos.length ≤ 2 ^ 64 - 1) :
    ExecBlock config (oracleObserveFrame imms time secondsAgos tick index liquidity card) evm
      (oracleObserveFunction.body.take 7)
      (.ok (oracleObserveAllocatedFrame imms time secondsAgos tick index liquidity card) evm) := by
  let f0 := oracleObserveZeroFrame imms time secondsAgos tick index liquidity card
  let f1 := oracleObserveTicksFrame imms time secondsAgos tick index liquidity card
  have e0 : evalExpr? config f0 evm (.arrayLength .localVar ⟨"secondsAgos", []⟩) =
      .ok (.int (Int.ofNat secondsAgos.length)) := by
    simpa only [oracleSecondsAgoValues, List.length_map] using
      evalExpr_localArrayLength (cfg := config) (frame := f0) (evm := evm)
        (values := oracleSecondsAgoValues secondsAgos)
        (by simp [f0, oracleObserveZeroFrame, oracleObserveLocals, Std.HashMap.getElem_insert])
  have e1 : evalExpr? config f1 evm (.arrayLength .localVar ⟨"secondsAgos", []⟩) =
      .ok (.int (Int.ofNat secondsAgos.length)) := by
    simpa only [oracleSecondsAgoValues, List.length_map] using
      evalExpr_localArrayLength (cfg := config) (frame := f1) (evm := evm)
        (values := oracleSecondsAgoValues secondsAgos)
        (by simp [f1, oracleObserveTicksFrame, oracleObserveZeroFrame, oracleObserveLocals,
          Std.HashMap.getElem_insert])
  have ep : evalExpr? config f0 evm (.binary .gt (.var "cardinality") (.intLit 0)) =
      .ok (.bool true) := by
    simpa only [decide_eq_true (Nat.pos_of_ne_zero hn)] using
      evalExpr_uint256_var_positive (cfg := config) (frame := f0) evm "cardinality" card
        (by simp [f0, oracleObserveZeroFrame, oracleObserveLocals, Std.HashMap.getElem_insert])
  have st : ExecStmt config f0 evm oracleObserveFunction.body[4]!
      (.ok f1 evm) := by
    exact ExecStmt.assign (evalExpr_newIntArray (.sint ⟨56, by decide⟩) _ e0)
      (assignLocalVarBase_frame (old := .array []) (by
        simp [f0, oracleObserveZeroFrame, Std.HashMap.getElem_insert]))
  have ss : ExecStmt config f1 evm oracleObserveFunction.body[6]!
      (.ok (oracleObserveAllocatedFrame imms time secondsAgos tick index liquidity card) evm) := by
    exact ExecStmt.assign (evalExpr_newIntArray (.uint ⟨160, by decide⟩) _ e1)
      (assignLocalVarBase_frame (old := .array []) (by
        simp [f1, oracleObserveTicksFrame, oracleObserveZeroFrame, Std.HashMap.getElem_insert]))
  exact execBlock_append_ok (oracleObserveZeroPrefix imms evm time secondsAgos tick index liquidity card)
    (ExecBlock.consNormal (ExecStmt.requireTrue ep)
      (ExecBlock.consNormal (ExecStmt.requireTrue (evalOracleObserveLengthBound _ hb e0))
        (ExecBlock.consNormal st
          (ExecBlock.consNormal (ExecStmt.requireTrue (evalOracleObserveLengthBound _ hb e1))
            (ExecBlock.consNormal ss ExecBlock.nil)))))

theorem oracleObserveRevertsZero (imms : Store) (evm : EVM.State) (time : UInt256)
    (secondsAgos : List UInt256) (tick : Int) (index liquidity : UInt256) :
    ExecFuncBody config (oracleObserveFrame imms time secondsAgos tick index liquidity ⟨0⟩) evm
      oracleObserveFunction.body .reverted := by
  have ep : evalExpr? config
      (oracleObserveZeroFrame imms time secondsAgos tick index liquidity ⟨0⟩) evm
      (.binary .gt (.var "cardinality") (.intLit 0)) = .ok (.bool false) := by
    simpa only [show (⟨0⟩ : UInt256).toNat = 0 from rfl, Nat.lt_irrefl, decide_false] using
      evalExpr_uint256_var_positive (cfg := config)
        (frame := oracleObserveZeroFrame imms time secondsAgos tick index liquidity ⟨0⟩)
        evm "cardinality" ⟨0⟩
        (by simp [oracleObserveZeroFrame, oracleObserveLocals, Std.HashMap.getElem_insert])
  apply ExecFuncBody.execBlockRevert
  rw [← List.take_append_drop 2 oracleObserveFunction.body]
  exact execBlock_append_ok (oracleObserveZeroPrefix imms evm time secondsAgos tick index liquidity ⟨0⟩)
    (ExecBlock.consRevert (ExecStmt.requireFalse ep))

end Benchmarks.UniswapV3.Pool
