import Benchmarks.UniswapV4PoolManager.EntryTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: a JUMPDEST/SWAP1/SSTORE sequence halts in static mode.
theorem swappedStoreStatic {code : ByteArray} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw pc value slot : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length+2 ≤ 1024) (hp : I.perm = false)
    (hd : decode code pc = some (.JUMPDEST, .none))
    (hs : decode code (pc+⟨1⟩) = some (.SWAP1, .none))
    (hw : decode code (pc+⟨1⟩+⟨1⟩) = some (.SSTORE, .none))
    (h : RD code I g s0 pc (value :: slot :: R) mem aw rdata σ k C) : RDstatic code g s0 := by
  have r1 := h.jumpdest hd (by evm_ov)
  have r2 := r1.swap1 hs (by evm_ov)
  exact RD.sstoreStatic r2 hp hw (by evm_ov)

end Benchmarks.UniswapV4PoolManager
