import Benchmarks.CompoundIII.Comet.TotalsStorage
import Benchmarks.CompoundIII.Comet.NarrowArithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

def timestampWord (env : ExecutionEnv) : UInt256 := UInt256.ofNat env.header.timestamp

def lastAccrualWord (w : UInt256) : UInt256 := packedUint w 26 5

theorem lastAccrualWord_lt (w : UInt256) : (lastAccrualWord w).toNat < 2^40 :=
  packedUint_lt w _ (by decide)

theorem lastAccrualWord_eq (w : UInt256) :
    lastAccrualWord w = UInt256.land (UInt256.shiftRight w ⟨208⟩) ⟨1099511627775⟩ := by
  change UInt256.land (UInt256.div w (UInt256.ofNat (256 ^ (26 : Fin 32).val))) _ = _
  rw [divBytePow_eq_shift]
  rfl

theorem evalLastAccrual (evm : EVM.State) (locals imms : Store)
    (hlocal : locals.get? "lastAccrualTime" = none) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm (.storage ⟨"lastAccrualTime", []⟩) =
      .ok (.int (lastAccrualWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)).toNat) := by
  apply evalExpr_storage_scalar_value (hbackend := rfl)
    (loc := { slot := ⟨1⟩, offset := 26, size := 5, hbound := by decide,
              type := .int (.uint ⟨40, by decide⟩) })
    (er := ⟨"lastAccrualTime", []⟩) (t := .int (.uint ⟨40, by decide⟩)) hlocal
  · simp only [evalStorageRef, evalStorageRefSteps, pure, bind, EvalResult.bind]
  · rfl
  · rfl
  · exact packedUint_load evm ⟨1⟩ 26 5 ⟨40, by decide⟩ rfl

def nowCallable : CallableDecl :=
  { params := [], returnType := [.elem (.int (.uint ⟨40, by decide⟩))]
    body := [.require (.binary .lt (.env .timestamp) (.intLit 1099511627776)),
      .return [.cast (.env .timestamp) (.elem (.int (.uint ⟨40, by decide⟩)))]] }

theorem nowCallable_lookup : lookupCallable? contract "getNowInternal" = some nowCallable := rfl

theorem nowCallable_result (evm : EVM.State) (imms : Store) :
    let frame : Frame := { contract := contract, locals := ∅, immutables := imms }
    if (timestampWord evm.executionEnv).toNat < 2^40 then
      ExecFuncBody config frame evm nowCallable.body
        (.returned frame evm (some [.int (timestampWord evm.executionEnv).toNat]))
    else ExecFuncBody config frame evm nowCallable.body .reverted := by
  dsimp only
  let frame : Frame := { contract := contract, locals := ∅, immutables := imms }
  let t := timestampWord evm.executionEnv
  have he : evalExpr? config frame evm (.env .timestamp) = .ok (.int (Int.ofNat t.toNat)) := by
    simp only [evalExpr?, envValue, t, timestampWord, pure]
  have hcond : evalExpr? config frame evm
      (.binary .lt (.env .timestamp) (.intLit 1099511627776)) =
      .ok (.bool (decide (t.toNat < 2^40))) := by
    simp only [evalExpr?, he, pure, bind, EvalResult.bind, evalBinaryOp?, Int.ofNat_eq_natCast]
    simp
  split_ifs with ht
  · apply ExecFuncBody.execBlockRet
    apply (ABlock.start.requireStep (hcond.trans (by rw [decide_eq_true ht]))).returns
    have hcast := evalExpr_cast_int (intType := .uint ⟨40, by decide⟩) he
    have hn : normalizeInt (.uint ⟨40, by decide⟩) (Int.ofNat t.toNat) = Int.ofNat t.toNat :=
      normalizeInt_uint_eq_self _ _ (Int.natCast_nonneg _) (by
        change (t.toNat : Int) < (2^40 : Nat)
        exact_mod_cast ht)
    rw [hn] at hcast
    exact hcast
  · apply ExecFuncBody.execBlockRevert
    exact ABlock.start.requireRevert (hcond.trans (by rw [decide_eq_false ht]))

theorem now_call_ok (frame : Frame) (evm : EVM.State) (ret : Ident)
    (hc : frame.contract = contract) (ht : (timestampWord evm.executionEnv).toNat < 2^40) :
    ExecStmt config frame evm (.internalCall "getNowInternal" [] ret)
      (.ok { frame with
        locals := frame.locals.insert ret (.int (timestampWord evm.executionEnv).toNat) } evm) := by
  have hb := nowCallable_result evm frame.immutables
  dsimp only at hb
  rw [if_pos ht] at hb
  exact ExecStmt.internalCallReturn (callee := nowCallable) (locals := ∅)
    (cfg := config) (solm := frame) (evm := evm) (args := []) (argVals := []) rfl
    (by rw [hc]; exact nowCallable_lookup) rfl (by simpa only [hc] using hb)

theorem now_call_revert (frame : Frame) (evm : EVM.State) (ret : Ident)
    (hc : frame.contract = contract) (ht : ¬ (timestampWord evm.executionEnv).toNat < 2^40) :
    ExecStmt config frame evm (.internalCall "getNowInternal" [] ret) .reverted := by
  have hb := nowCallable_result evm frame.immutables
  dsimp only at hb
  rw [if_neg ht] at hb
  exact ExecStmt.internalCallRevert (callee := nowCallable) (locals := ∅)
    (cfg := config) (solm := frame) (evm := evm) (args := []) (argVals := []) rfl
    (by rw [hc]; exact nowCallable_lookup) rfl (by simpa only [hc] using hb)

end Benchmarks.CompoundIII.Comet
