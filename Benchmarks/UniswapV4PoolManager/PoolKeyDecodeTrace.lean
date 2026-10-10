import Benchmarks.UniswapV4PoolManager.PoolKeyDecodeBounds

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager

theorem poolKeyDecodePrepare {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {aw ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+9 ≤ 1024)
    (hlen : 164 ≤ I.calldata.size) (hhi : I.calldata.size < calldataLimit) (hsize : I.calldata.size < UInt256.size)
    (h : RD (deployedRuntime v) I g s0 ⟨11905⟩ (UInt256.ofNat I.calldata.size :: ret :: R)
      entryMemory aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨11960⟩ (ret :: ⟨160⟩ :: R)
      poolKeyAllocationMemory aw' rdata σ k' C' := by
  obtain ⟨aw', k', C', _, hr⟩ := poolKeyDecodePrepareWords v hstack hlen hhi hsize h
  exact ⟨aw', k', C', hr⟩

theorem decodePoolKeyTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {aw ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+9 ≤ 1024)
    (hlen : 164 ≤ I.calldata.size) (hhi : I.calldata.size < calldataLimit) (hsize : I.calldata.size < UInt256.size)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨11905⟩ (UInt256.ofNat I.calldata.size :: ret :: R)
      entryMemory aw rdata σ k C) :
    (¬PoolKeyCanonical (poolKeyOfCalldata I.calldata) ∧ RDrev (deployedRuntime v) g s0) ∨
    (PoolKeyCanonical (poolKeyOfCalldata I.calldata) ∧ ∃ aw' k' C',
      RD (deployedRuntime v) I g s0 ret (⟨160⟩ :: R) (poolKeyMemory (poolKeyOfCalldata I.calldata))
        aw' rdata σ k' C') := by
  rcases decodePoolKeyTraceWords v hstack hlen hhi hsize hret h with hbad | ⟨hc, aw', k', C', _, hr⟩
  · exact .inl hbad
  · exact .inr ⟨hc, aw', k', C', hr⟩

end Benchmarks.UniswapV4PoolManager
