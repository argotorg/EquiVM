import Benchmarks.EAS.EAS.Dispatch

variable {fork : Ethereum.Fork}

/-!
# Shared EAS entry guards

The specification initializes its allocation counter before checking call value and
Solidity's signed calldata-size condition. These lemmas preserve that order.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS

def easCalldataGuard : Expr :=
  .binary .lt (.cast (.binary .sub (.arrayLength .localVar { base := "__calldata" })
    (.intLit 4)) (.elem (.int (.uint ⟨256, by decide⟩)))) (.intLit (2^255))

-- LIBRARY CANDIDATE: signed-size guard after binding a calldata byte array.
theorem evalCalldataSizeGuard {cfg : Config} {frame : Frame} {evm : EVM.State}
    {cd : ByteArray} {name : Ident} (hcd : frame.locals.get? name = some (.bytes cd))
    (hsz : 4 ≤ cd.size) (hsize : cd.size < UInt256.size) :
    evalExpr? cfg frame evm
      (.binary .lt (.cast (.binary .sub (.arrayLength .localVar {base := name}) (.intLit 4))
        (.elem (.int (.uint ⟨256, by decide⟩)))) (.intLit (2^255))) =
      .ok (.bool (decide (cd.size - 4 < 2^255))) := by
  have hsub : (cd.size : ℤ) - 4 = ((cd.size - 4 : Nat) : ℤ) := by omega
  simp only [evalExpr?, hcd, readLocalPath?, EvalResult.bind,
    bind, pure, evalBinaryOp?, castValue?, normalizeInt, EvalResult.ofOption]
  change EvalResult.ok (Value.bool (decide (((cd.size : ℤ) - 4) % (2^256) < 2^255))) = _
  rw [hsub, Int.emod_eq_of_lt (Int.natCast_nonneg _)
    (by exact_mod_cast (show cd.size - 4 < 2^256 by change cd.size < 2^256 at hsize; omega))]
  have hlt : (((cd.size - 4 : Nat) : ℤ) < (2:ℤ)^255) = (cd.size - 4 < 2^255) := by
    norm_cast
  simp only [hlt]

def easEntryPrefix : Body := [
  .letDecl "$EAS.freeMemory" none (.intLit 224),
  .require (.binary .eq (.env .callvalue) (.intLit 0)),
  .letDecl "__calldata" (some .bytes) (.env .msgData),
  .require easCalldataGuard]

def easEntryLocals (locals : Store) (cd : ByteArray) : Store :=
  (locals.insert "$EAS.freeMemory" (.int 224)).insert "__calldata" (.bytes cd)

theorem easEntryPrefix_ok {cfg : Config} {frame : Frame} {evm : EVM.State}
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hsz : 4 ≤ evm.executionEnv.calldata.size)
    (hsize : evm.executionEnv.calldata.size < UInt256.size)
    (hguard : evm.executionEnv.calldata.size - 4 < 2^255) :
    ExecBlock fork cfg frame evm easEntryPrefix
      (.ok {frame with locals := easEntryLocals frame.locals evm.executionEnv.calldata} evm) := by
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := .int 224) (by simp only [evalExpr?, pure])) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hvalue)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := .bytes evm.executionEnv.calldata) (by simp only [evalExpr?, pure, envValue])) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ExecBlock.nil
  simpa only [hguard, decide_true] using evalCalldataSizeGuard
    (cfg := cfg) (evm := evm) (store_get_self _ _ _) hsz hsize

theorem easEntryPrefix_value_revert {cfg : Config} {frame : Frame} {evm : EVM.State}
    (hvalue : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecBlock fork cfg frame evm easEntryPrefix .reverted := by
  exact ExecBlock.consNormal (ExecStmt.letDecl (value := .int 224) (by simp only [evalExpr?, pure])) (blockReverts_nonPayable hvalue)

theorem easEntryPrefix_size_revert {cfg : Config} {frame : Frame} {evm : EVM.State}
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hsz : 4 ≤ evm.executionEnv.calldata.size)
    (hsize : evm.executionEnv.calldata.size < UInt256.size)
    (hguard : ¬ evm.executionEnv.calldata.size - 4 < 2^255) :
    ExecBlock fork cfg frame evm easEntryPrefix .reverted := by
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := .int 224) (by simp only [evalExpr?, pure])) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hvalue)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := .bytes evm.executionEnv.calldata) (by simp only [evalExpr?, pure, envValue])) ?_
  refine ExecBlock.consRevert (ExecStmt.requireFalse ?_)
  simpa only [hguard, decide_false] using evalCalldataSizeGuard
    (cfg := cfg) (evm := evm) (store_get_self _ _ _) hsz hsize

theorem easCalldataRemainder {cd : ByteArray} (hsz : 4 ≤ cd.size)
    (hsize : cd.size < UInt256.size) :
    UInt256.ofNat cd.size + UInt256.ofNat (UInt256.size - 4) =
      UInt256.ofNat (cd.size - 4) := by
  rw [u256_add_comm]
  exact lnot3_add_returnSize hsz hsize

theorem easCalldataSizeCheck_ok {cd : ByteArray} (hsz : 4 ≤ cd.size)
    (hsize : cd.size < UInt256.size) (hguard : cd.size - 4 < 2^255) :
    UInt256.slt (UInt256.ofNat cd.size + UInt256.ofNat (UInt256.size - 4)) ⟨0⟩ = ⟨0⟩ := by
  rw [easCalldataRemainder hsz hsize]
  exact slt_ofNat_lit_zero (by decide) (Nat.zero_le _) hguard

theorem easCalldataSizeCheck_revert {cd : ByteArray} (hsz : 4 ≤ cd.size)
    (hsize : cd.size < UInt256.size) (hguard : ¬ cd.size - 4 < 2^255) :
    UInt256.slt (UInt256.ofNat cd.size + UInt256.ofNat (UInt256.size - 4)) ⟨0⟩ ≠ ⟨0⟩ := by
  rw [easCalldataRemainder hsz hsize]
  apply u256_slt_zero_ne_zero_of_high
  rw [ulit_toNat' _ (lt_of_le_of_lt (Nat.sub_le _ _) hsize)]
  exact Nat.le_of_not_gt hguard

theorem easEntryBody_returns {cfg : Config} {C : ContractDecl} {evm : EVM.State}
    {locals imms : Store} {expr : Expr} {value : Value}
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hsz : 4 ≤ evm.executionEnv.calldata.size)
    (hsize : evm.executionEnv.calldata.size < UInt256.size)
    (hguard : evm.executionEnv.calldata.size - 4 < 2^255)
    (heval : evalExpr? cfg
      { contract := C
        locals := easEntryLocals locals evm.executionEnv.calldata
        immutables := imms } evm expr = .ok value) :
    ExecTransitionBody fork cfg C evm locals (easEntryPrefix ++ [.return [expr]])
      (.returned
        { contract := C
          locals := easEntryLocals locals evm.executionEnv.calldata
          immutables := imms } evm (some [value])) imms := by
  exact ExecFuncBody.execBlockRet (execBlock_append
    (easEntryPrefix_ok hvalue hsz hsize hguard)
    (ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton heval))))

theorem easEntryBody_value_revert {cfg : Config} {C : ContractDecl} {evm : EVM.State}
    {locals imms : Store} {rest : Body} (hvalue : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody fork cfg C evm locals (easEntryPrefix ++ rest) .reverted imms :=
  ExecFuncBody.execBlockRevert (execBlockAppendReverted (easEntryPrefix_value_revert hvalue))

theorem easEntryBody_size_revert {cfg : Config} {C : ContractDecl} {evm : EVM.State}
    {locals imms : Store} {rest : Body}
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hsz : 4 ≤ evm.executionEnv.calldata.size)
    (hsize : evm.executionEnv.calldata.size < UInt256.size)
    (hguard : ¬ evm.executionEnv.calldata.size - 4 < 2^255) :
    ExecTransitionBody fork cfg C evm locals (easEntryPrefix ++ rest) .reverted imms :=
  ExecFuncBody.execBlockRevert
    (execBlockAppendReverted (easEntryPrefix_size_revert hvalue hsz hsize hguard))

end Benchmarks.EAS.EAS
