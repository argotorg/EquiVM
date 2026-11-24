import Benchmarks.EAS.EAS.AllocateBlock
import Benchmarks.EAS.Attester.LocalArray

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- LIBRARY CANDIDATE: allocation of a length-prefixed array with a fixed per-element cost.
def arrayAllocationExpr (length : Expr) (width : Nat) : Expr :=
  .binary .add (.intLit 32) (.binary .mul length (.intLit (Int.ofNat width)))

theorem arrayAllocationExpr_eval {cfg : Config} {frame : Frame} {evm : EVM.State} {length : Expr} {n : Nat}
    (h : evalExpr? cfg frame evm length = .ok (.int (Int.ofNat n))) (width : Nat) :
    evalExpr? cfg frame evm (arrayAllocationExpr length width) = .ok (.int (Int.ofNat (32+width*n))) := by
  simp only [arrayAllocationExpr,evalExpr?,h,pure,EvalResult.bind,bind,evalBinaryOp?,Int.ofNat_eq_natCast,
    Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  rw [Int.mul_comm]

def arrayAllocateExprBlock (length : Expr) (width : Nat) : Body :=
  [.require (.binary .le length (.intLit (2^64-1)))] ++ allocateBlock (arrayAllocationExpr length width)

-- GENERALIZES arrayAllocateSource from a local variable to any evaluated length expression.
theorem arrayAllocateExprSource {cfg : Config} {L imms : Store} {evm : EVM.State} {n heap : Nat} {length : Expr}
    (hn : evalExpr? cfg {contract := contract,locals := L,immutables := imms} evm length = .ok (.int (Int.ofNat n)))
    (hh : L.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap))) (width : Nat) :
    if n ≤ 2^64-1 then
      if allocateNext heap (32+width*n) ≤ 2^64-1 ∧ heap ≤ allocateNext heap (32+width*n) then
        ExecBlock fork cfg {contract := contract,locals := L,immutables := imms} evm (arrayAllocateExprBlock length width)
          (.ok {contract := contract,locals := allocateBlockLocals L (allocateNext heap (32+width*n)),immutables := imms} evm)
      else ExecBlock fork cfg {contract := contract,locals := L,immutables := imms} evm (arrayAllocateExprBlock length width) .reverted
    else ExecBlock fork cfg {contract := contract,locals := L,immutables := imms} evm (arrayAllocateExprBlock length width) .reverted := by
  have he := naturalLeSource (cfg := cfg) (evm := evm)
    (frame := {contract := contract,locals := L,immutables := imms}) hn
    (by simp only [evalExpr?,pure]; rfl : evalExpr? cfg _ evm (.intLit (2^64-1)) = .ok (.int (Int.ofNat (2^64-1))))
  have hsize := arrayAllocationExpr_eval hn width
  by_cases hl : n ≤ 2^64-1
  · rw [if_pos hl]
    have hg : ExecStmt fork cfg {contract := contract,locals := L,immutables := imms} evm
        (.require (.binary .le length (.intLit (2^64-1))))
        (.ok {contract := contract,locals := L,immutables := imms} evm) :=
      ExecStmt.requireTrue (by simpa only [decide_eq_true hl] using he)
    by_cases hb : allocateNext heap (32+width*n) ≤ 2^64-1 ∧ heap ≤ allocateNext heap (32+width*n)
    · rw [if_pos hb]
      exact ExecBlock.consNormal hg (allocateBlock_ok hsize hh hb)
    · rw [if_neg hb]
      exact ExecBlock.consNormal hg (allocateBlock_revert hsize hh hb)
  · rw [if_neg hl]
    exact ExecBlock.consRevert (ExecStmt.requireFalse (by simpa only [decide_eq_false hl] using he))


def arrayAllocateBlock (width : Nat) : Body := arrayAllocateExprBlock (.var "length") width

theorem arrayAllocateSource {cfg : Config} {L imms : Store} {evm : EVM.State} {n heap : Nat}
    (hn : L.get? "length" = some (.int (Int.ofNat n)))
    (hh : L.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap))) (width : Nat) :
    if n ≤ 2^64-1 then
      if allocateNext heap (32+width*n) ≤ 2^64-1 ∧ heap ≤ allocateNext heap (32+width*n) then
        ExecBlock fork cfg {contract := contract,locals := L,immutables := imms} evm (arrayAllocateBlock width)
          (.ok {contract := contract,locals := allocateBlockLocals L (allocateNext heap (32+width*n)),immutables := imms} evm)
      else ExecBlock fork cfg {contract := contract,locals := L,immutables := imms} evm (arrayAllocateBlock width) .reverted
    else ExecBlock fork cfg {contract := contract,locals := L,immutables := imms} evm (arrayAllocateBlock width) .reverted :=
  arrayAllocateExprSource (evalLocalValue hn) hh width

end Benchmarks.EAS.EAS
