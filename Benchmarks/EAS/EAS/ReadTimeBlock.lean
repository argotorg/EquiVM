import Benchmarks.EAS.EAS.HeapResultBlock
import Benchmarks.EAS.EAS.Time

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

def readTimeBlock (tmp result : Ident) : Body :=
  heapResultBlock "_time" [.var "$EAS.freeMemory"] tmp result "$EAS.freeMemory"
def readTimeLocals (L : Store) (tmp result : Ident) (time : UInt256) (heap : Nat) : Store :=
  heapResultLocals L tmp result "$EAS.freeMemory" (.int (Int.ofNat time.toNat)) heap

theorem readTimeBlock_source {cfg : Config} {L imms : Store} {evm : EVM.State} {heap : Nat}
    (tmp result : Ident) (hh : L.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)))
    (ht : (tmp == "$EAS.freeMemory") = false) (htr : (result == tmp) = false)
    (hr : (result == "$EAS.freeMemory") = false) :
    ExecBlock fork cfg {contract := contract,locals := L,immutables := imms} evm (readTimeBlock tmp result)
      (.ok {contract := contract,locals := readTimeLocals L tmp result (easTimeWord evm.executionEnv) heap,immutables := imms} evm) := by
  apply heapResultBlock_ok (timeCall (by simp only [evalExpr?,hh,EvalResult.ofOption])) hh ht htr hr

end Benchmarks.EAS.EAS
