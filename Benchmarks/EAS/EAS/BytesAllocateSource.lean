import Benchmarks.EAS.EAS.BytesAllocation
import Benchmarks.EAS.EAS.ArrayAllocateSource

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- LIBRARY CANDIDATE: the shared length guard and allocation of a dynamic byte sequence.
def bytesAllocateBlock (length : Expr) : Body :=
  [.require (.binary .le length (.intLit (2^64-1)))] ++ allocateBlock (bytesAllocationExpr length)

theorem bytesAllocateSource {cfg : Config} {L imms : Store} {evm : EVM.State} {length : Expr} {n heap : Nat}
    (hn : evalExpr? cfg {contract := contract,locals := L,immutables := imms} evm length = .ok (.int (Int.ofNat n)))
    (hh : L.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap))) :
    if n ≤ 2^64-1 then
      if allocateNext heap (bytesAllocation n) ≤ 2^64-1 ∧ heap ≤ allocateNext heap (bytesAllocation n) then
        ExecBlock fork cfg {contract := contract,locals := L,immutables := imms} evm (bytesAllocateBlock length)
          (.ok {contract := contract,locals := allocateBlockLocals L (allocateNext heap (bytesAllocation n)),immutables := imms} evm)
      else ExecBlock fork cfg {contract := contract,locals := L,immutables := imms} evm (bytesAllocateBlock length) .reverted
    else ExecBlock fork cfg {contract := contract,locals := L,immutables := imms} evm (bytesAllocateBlock length) .reverted := by
  have he := naturalLeSource (cfg := cfg) (evm := evm)
    (frame := {contract := contract,locals := L,immutables := imms}) hn
    (by simp only [evalExpr?,pure]; rfl : evalExpr? cfg _ evm (.intLit (2^64-1)) = .ok (.int (Int.ofNat (2^64-1))))
  have hsize := bytesAllocationExpr_eval hn
  by_cases hl : n ≤ 2^64-1
  · rw [if_pos hl]
    have hg : ExecStmt fork cfg {contract := contract,locals := L,immutables := imms} evm
        (.require (.binary .le length (.intLit (2^64-1))))
        (.ok {contract := contract,locals := L,immutables := imms} evm) :=
      ExecStmt.requireTrue (by simpa only [decide_eq_true hl] using he)
    by_cases hb : allocateNext heap (bytesAllocation n) ≤ 2^64-1 ∧ heap ≤ allocateNext heap (bytesAllocation n)
    · rw [if_pos hb]
      exact ExecBlock.consNormal hg (allocateBlock_ok hsize hh hb)
    · rw [if_neg hb]
      exact ExecBlock.consNormal hg (allocateBlock_revert hsize hh hb)
  · rw [if_neg hl]
    exact ExecBlock.consRevert (ExecStmt.requireFalse (by simpa only [decide_eq_false hl] using he))

end Benchmarks.EAS.EAS
