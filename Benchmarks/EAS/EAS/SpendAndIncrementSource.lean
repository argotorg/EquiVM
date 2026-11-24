import Benchmarks.EAS.EAS.ArrayLoopSource
import Benchmarks.EAS.EAS.AllocateBlock

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- GENERALIZES multiRevokeUpdateSource to any result local.
def spendAndIncrement (result : Ident) : Body := [
  .assign .localVar {base := "availableValue"} (.inRange abiUInt256Int (.binary .sub (.var "availableValue") (.var result))),
  localCastIncrement "i"]
def spendAndIncrementLocals (L : Store) (available used : UInt256) (i : Nat) : Store :=
  L.insert "availableValue" (.int (Int.ofNat (UInt256.sub available used).toNat)) |>.insert "i" (.int (Int.ofNat (i+1)))

theorem spendAndIncrementSource {cfg : Config} {frame : Frame} {evm : EVM.State} {result : Ident}
    {available used : UInt256} {i : Nat}
    (ha : frame.locals.get? "availableValue"=some (.int (Int.ofNat available.toNat)))
    (hr : frame.locals.get? result=some (.int (Int.ofNat used.toNat)))
    (hi : frame.locals.get? "i"=some (.int (Int.ofNat i)))
    (hb : i+1<UInt256.size) (hu : used.toNat ≤ available.toNat) :
    ExecBlock fork cfg frame evm (spendAndIncrement result)
      (.ok {frame with locals := spendAndIncrementLocals frame.locals available used i} evm) := by
  apply ExecBlock.consNormal (ExecStmt.assign (fork := fork) (hperm := by first | exact Or.inl rfl | assumption | exact Or.inr ‹_›) (evalExpr_uint256_sub (evalLocalValue ha) (evalLocalValue hr) hu) (assignLocalValue ha))
  apply ExecBlock.consNormal (execLocalCastIncrement ?_ hb) ExecBlock.nil
  simpa (disch := decide) only [store_get_ne] using hi

end Benchmarks.EAS.EAS
