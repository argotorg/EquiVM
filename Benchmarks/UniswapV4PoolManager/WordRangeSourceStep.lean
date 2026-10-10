import Benchmarks.UniswapV4PoolManager.WordArraySource
import Benchmarks.UniswapV4PoolManager.WordRangeABI

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 3000

-- LIBRARY CANDIDATE: normalize an unsigned sum modulo the EVM word size.
theorem normalizeUint256WordAddNat (word : UInt256) (i : Nat) :
    normalizeInt (.uint ⟨256, by decide⟩) (Int.ofNat (word.toNat+i)) =
      Int.ofNat (word + UInt256.ofNat i).toNat := by
  change Int.ofNat (word.toNat+i) % Int.ofNat UInt256.size = _
  simp only [Int.ofNat_eq_natCast, Int.natCast_emod, uadd_toNat, ofNat_toNat_mod, Nat.add_mod_mod]

def wordRangeSlot (start : UInt256) (i : Nat) : UInt256 := start + UInt256.ofNat i
def wordRangeValue (evm : EVM.State) (start : UInt256) (i : Nat) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (wordRangeSlot start i)

theorem wordRangeValue_zero (evm : EVM.State) (start : UInt256) :
    wordRangeValue evm start 0 = Solm.EVM.storageLoad evm evm.executionEnv.codeOwner start := by
  unfold wordRangeValue wordRangeSlot
  rw [show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl, uadd_zero_r]

def wordRangeSlotExpr : Expr := .cast (.binary .add
  (.cast (.var "startSlot") (.elem (.int (.uint ⟨256, by decide⟩)))) (.var "i"))
  (.elem (.int (.uint ⟨256, by decide⟩)))
def wordRangeCond : Expr := .binary .lt (.var "i") (.var "nSlots")
def wordRangeLoopBody : List Stmt := [
  .assign .localVar {base := "result", steps := [.aindex (.var "i")]}
    (.cast (.storage {base := "rawSlots", steps := [.aindex wordRangeSlotExpr]}) (.elem (.bytes abiBytes32Width))),
  .assign .localVar {base := "i"} (.binary .add (.var "i") (.intLit 1))]

structure WordRangeLocals (start : UInt256) (n : Nat) (res : List Value) (i : Nat) (locals : Store) : Prop where
  start_eq : locals.get? "startSlot" = some (wordBytes32Value start)
  count_eq : locals.get? "nSlots" = some (.int (Int.ofNat n))
  index_eq : locals.get? "i" = some (.int (Int.ofNat i))
  result_eq : locals.get? "result" = some (.array res)
  raw_eq : locals.get? "rawSlots" = none

theorem wordRangeSlot_eval {f : Frame} {evm : EVM.State} {start : UInt256} {i : Nat}
    (hs : f.locals.get? "startSlot" = some (wordBytes32Value start))
    (hi : f.locals.get? "i" = some (.int (Int.ofNat i))) :
    evalExpr? config f evm wordRangeSlotExpr = .ok (.int (Int.ofNat (wordRangeSlot start i).toNat)) := by
  exact evalCastValue (naturalAddSource (evalCastValue (evalLocalValue hs) (castBytes32ToUint256 start))
    (evalLocalValue hi)) (by rw [castValue_int, normalizeUint256WordAddNat]; rfl)

theorem wordRangeLoopStep (evm : EVM.State) (imms locals : Store) (start : UInt256) (n : Nat)
    (res : List Value) (i : Nat) (hl : WordRangeLocals start n res i locals)
    (hi : i < n) (hres : res.length = n) :
    ∃ locals', ExecBlock config {contract := contract, locals := locals, immutables := imms}
      evm wordRangeLoopBody (.ok {contract := contract, locals := locals', immutables := imms} evm) ∧
      WordRangeLocals start n (res.set i (wordBytes32Value (wordRangeValue evm start i))) (i+1) locals' := by
  let l1 := locals.insert "result" (.array (res.set i (wordBytes32Value (wordRangeValue evm start i))))
  let l2 := l1.insert "i" (.int (Int.ofNat (i+1)))
  have hi1 : l1.get? "i" = some (.int (Int.ofNat i)) :=
    (store_get_ne _ _ (by decide)).trans hl.index_eq
  refine ⟨l2, ?_, ?_⟩
  · refine ExecBlock.consNormal (ExecStmt.assign ?_ (assignLocalArrayIndex hl.result_eq hl.index_eq (by omega)))
      (ExecBlock.consNormal (ExecStmt.assign
        (naturalAddSource (evalLocalValue hi1) (by simp only [evalExpr?, pure]; rfl))
        (assignLocalValue hi1)) ExecBlock.nil)
    exact evalCastValue (rawSlots_read rfl hl.raw_eq (wordRangeSlot_eval hl.start_eq hl.index_eq))
      (castUint256ToBytes32 _)
  · constructor
    · exact (store_get_ne _ _ (by decide)).trans ((store_get_ne _ _ (by decide)).trans hl.start_eq)
    · exact (store_get_ne _ _ (by decide)).trans ((store_get_ne _ _ (by decide)).trans hl.count_eq)
    · exact store_get_self _ _ _
    · exact (store_get_ne _ _ (by decide)).trans (store_get_self _ _ _)
    · exact (store_get_ne _ _ (by decide)).trans ((store_get_ne _ _ (by decide)).trans hl.raw_eq)

theorem wordRangeSourceLoop (evm : EVM.State) (imms : Store) (start : UInt256) (n remaining : Nat) :
    ∀ locals res i, WordRangeLocals start n res i locals → i+remaining = n → res.length = n →
      (∀ j, j < i → res[j]? = some (wordBytes32Value (wordRangeValue evm start j))) →
      ∃ locals', ExecStmt config {contract := contract, locals := locals, immutables := imms}
        evm (.while wordRangeCond wordRangeLoopBody)
        (.ok {contract := contract, locals := locals', immutables := imms} evm) ∧
        locals'.get? "result" = some (.array (wordArrayValues (wordRangeValue evm start) 0 n)) :=
  wordArrayFillLoop
    (fun _ _ _ hl => evalLocalNatLt hl.index_eq hl.count_eq)
    (fun _ _ _ hl => hl.result_eq)
    (fun locals res i hl hi hr => wordRangeLoopStep evm imms locals start n res i hl hi hr) remaining

end Benchmarks.UniswapV4PoolManager
