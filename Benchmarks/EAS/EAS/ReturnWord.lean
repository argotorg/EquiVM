import Benchmarks.EAS.EAS.Common
import Benchmarks.EAS.EAS.RuntimeBlocks_005

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS

/-- The runtime's shared return routine, specialized to one ABI word. -/
theorem easReturnWord {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {value : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length + 4 ≤ 1024)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨771⟩ (value :: ⟨32⟩ :: R) mem aw rdata σ k C) :
    RDret fork (deployedRuntime v) g s0 σ value.toByteArray := by
  have hr := easBlocks.eas_block_771 (immWords := wordsOf (immStore v)) hstack rd
  rw [show (⟨32⟩ : UInt256).toNat = 32 from rfl,
    ← Reasoning.Theory.writeWord, writeWord_sparse_read_back] at hr
  exact hr

end Benchmarks.EAS.EAS
