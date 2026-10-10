import Benchmarks.UniswapV4PoolManager.Storage
import Benchmarks.UniswapV4PoolManager.LocalArray
import Benchmarks.UniswapV4PoolManager.WordArrayDecode
import Benchmarks.UniswapV4PoolManager.WordArrayFillLoop

/-! Shared source loop for storage and transient word arrays. -/
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 2000

-- LIBRARY CANDIDATE: comparison of natural-valued expressions.
theorem evalNatLt {cfg : Config} {f : Frame} {evm : EVM.State} {lhs rhs : Expr} {a b : Nat}
    (ha : evalExpr? cfg f evm lhs = .ok (.int (Int.ofNat a)))
    (hb : evalExpr? cfg f evm rhs = .ok (.int (Int.ofNat b))) :
    evalExpr? cfg f evm (.binary .lt lhs rhs) = .ok (.bool (decide (a < b))) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide), ha, hb]
  simp only [bind, EvalResult.bind, evalBinaryOp?, Int.ofNat_eq_natCast, Nat.cast_lt]

def wordArrayCond : Expr := .binary .lt (.var "i") (.arrayLength .localVar {base := "slots"})
def wordArrayRead (transient : Bool) (index : Expr) : Expr :=
  if transient then .transient {base := "rawTransient", steps := [.aindex index]}
  else .storage {base := "rawSlots", steps := [.aindex index]}
def wordArrayLoad (transient : Bool) (evm : EVM.State) (slot : UInt256) : UInt256 :=
  if transient then Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot
  else Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot

theorem wordArrayRead_eval (transient : Bool) {f : Frame} {evm : EVM.State} {index : Expr} {slot : UInt256}
    (hf : f.contract = contract) (hraw : f.locals.get? "rawSlots" = none)
    (he : evalExpr? config f evm index = .ok (.int (Int.ofNat slot.toNat))) :
    evalExpr? config f evm (wordArrayRead transient index) =
      .ok (.int (Int.ofNat (wordArrayLoad transient evm slot).toNat)) := by
  cases transient
  · exact rawSlots_read hf hraw he
  · exact rawTransient_read hf he

def wordArrayLoopBody (transient : Bool) : List Stmt := [
  .assign .localVar {base := "result", steps := [.aindex (.var "i")]}
    (.cast (wordArrayRead transient
      (.cast (.index (.var "slots") (.var "i")) (.elem (.int (.uint ⟨256, by decide⟩)))))
      (.elem (.bytes abiBytes32Width))),
  .assign .localVar {base := "i"} (.binary .add (.var "i") (.intLit 1))]

def wordArraySlot (I : ExecutionEnv) (i : Nat) : UInt256 :=
  calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat + 32 + 32 * i)
def wordArrayValue (transient : Bool) (evm : EVM.State) (i : Nat) : UInt256 :=
  wordArrayLoad transient evm (wordArraySlot evm.executionEnv i)

structure WordArrayLocals (slots res : List Value) (i : Nat) (locals : Store) : Prop where
  slots_eq : locals.get? "slots" = some (.array slots)
  index_eq : locals.get? "i" = some (.int (Int.ofNat i))
  result_eq : locals.get? "result" = some (.array res)
  raw_eq : locals.get? "rawSlots" = none

theorem wordArrayLoopStep (transient : Bool) (evm : EVM.State) (locals imms : Store) (slots res : List Value) (i : Nat)
    (hl : WordArrayLocals slots res i locals) (hi : i < slots.length)
    (hres : res.length = slots.length) (hd : WordArrayDecoded evm.executionEnv.calldata slots) :
    ∃ locals', ExecBlock config {contract := contract, locals := locals, immutables := imms}
      evm (wordArrayLoopBody transient) (.ok {contract := contract, locals := locals', immutables := imms} evm) ∧
      WordArrayLocals slots (res.set i (wordBytes32Value (wordArrayValue transient evm i))) (i+1) locals' := by
  let l1 := locals.insert "result" (.array (res.set i (wordBytes32Value (wordArrayValue transient evm i))))
  let l2 := l1.insert "i" (.int (Int.ofNat (i+1)))
  have hi1 : l1.get? "i" = some (.int (Int.ofNat i)) :=
    (store_get_ne _ _ (by decide)).trans hl.index_eq
  have hlookup : slots[i]? = some (wordBytes32Value (wordArraySlot evm.executionEnv i)) := by
    simpa only [← lookupNth_eq_getElem, wordArraySlot] using hd.lookup hi
  refine ⟨l2, ?_, ?_⟩
  · refine ExecBlock.consNormal (ExecStmt.assign ?_ (assignLocalArrayIndex hl.result_eq hl.index_eq
      (by omega))) (ExecBlock.consNormal (ExecStmt.assign
        (naturalAddSource (evalLocalValue hi1) (by simp only [evalExpr?, pure]; rfl))
        (assignLocalValue hi1)) ExecBlock.nil)
    exact evalCastValue (wordArrayRead_eval transient rfl hl.raw_eq (evalCastValue
      (evalLocalArrayIndex hl.slots_eq hl.index_eq hlookup rfl) (castBytes32ToUint256 _)))
      (castUint256ToBytes32 _)
  · constructor
    · exact (store_get_ne _ _ (by decide)).trans ((store_get_ne _ _ (by decide)).trans hl.slots_eq)
    · exact store_get_self _ _ _
    · exact (store_get_ne _ _ (by decide)).trans (store_get_self _ _ _)
    · exact (store_get_ne _ _ (by decide)).trans ((store_get_ne _ _ (by decide)).trans hl.raw_eq)

theorem wordArraySourceLoop (transient : Bool) (evm : EVM.State) (imms : Store) (slots : List Value)
    (hd : WordArrayDecoded evm.executionEnv.calldata slots) (remaining : Nat) :
    ∀ locals res i, WordArrayLocals slots res i locals → i + remaining = slots.length →
      res.length = slots.length →
      (∀ j, j < i → res[j]? = some (wordBytes32Value (wordArrayValue transient evm j))) →
      ∃ locals', ExecStmt config {contract := contract, locals := locals, immutables := imms}
        evm (.while wordArrayCond (wordArrayLoopBody transient))
        (.ok {contract := contract, locals := locals', immutables := imms} evm) ∧
        locals'.get? "result" = some (.array (wordArrayValues (wordArrayValue transient evm) 0 slots.length)) := by
  exact wordArrayFillLoop
    (fun _ _ _ hl => evalNatLt (evalLocalValue hl.index_eq) (evalLocalArrayLength hl.slots_eq))
    (fun _ _ _ hl => hl.result_eq)
    (fun locals res i hl hi hr => wordArrayLoopStep transient evm locals imms slots res i hl hi hr hd)
    remaining

end Benchmarks.UniswapV4PoolManager
