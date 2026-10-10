import Benchmarks.UniswapV3.Pool.ObservationReadCost
import Benchmarks.UniswapV3.Pool.OracleReadMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem observationReadCursorX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p index : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨13226⟩
      (index :: UInt256.ofNat 8 :: R) mem aw rdata σ k C)
    (hm : MemoryCursor mem aw p) (hb : p.toNat + 128 ≤ 2 ^ 200) (hov : R.length + 9 ≤ 1024) :
    let last := oracleStoredObservation index σ ee
    ∃ k' C', C + 1 + (Cₘ (oracleReadHeadAw mem aw) - Cₘ aw) ≤ C' ∧
      RD (deployedRuntime v) ee g s0 ⟨13311⟩
        ((if last.initialized then ⟨1⟩ else ⟨0⟩) :: UInt256.ofNat 4294967295 :: p :: last.timestamp :: R)
        (observationReadHeadMem mem p last) (oracleReadHeadAw mem aw) rdata σ k' C' := by
  dsimp only
  have hload : memLoad (UInt256.ofNat 64) mem = p := hm.load64
  have hslot : UInt256.ofNat 8 + index = observationSlot index := u256_add_comm _ _
  have ht := oracleStoredTimestamp index σ ee
  have hi := oracleStoredInitialized index σ ee
  simp only [solcSlotWordAt] at ht hi
  have hmem := observationReadHeadMem_eq_cursor index σ ee hm hb
  obtain ⟨kr, Cr, hC, rdRead⟩ := observationReadHeadMonoX (v := v) rd hov
  refine ⟨kr, Cr, hC, ?_⟩
  simpa only [uniswapV3Pool_block_13226_stack, hload, hslot, ← ht, ← hi, hmem] using rdRead

theorem observationReadMonoX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p index : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨13226⟩
      (index :: UInt256.ofNat 8 :: R) mem aw rdata σ k C)
    (hm : HeapMemory mem aw p) (hb : p.toNat + 128 ≤ 2 ^ 200) (hov : R.length + 9 ≤ 1024) :
    let last := oracleStoredObservation index σ ee
    ∃ k' C', C + 1 + (Cₘ (oracleReadHeadAw mem aw) - Cₘ aw) ≤ C' ∧
      RD (deployedRuntime v) ee g s0 ⟨13311⟩
        ((if last.initialized then ⟨1⟩ else ⟨0⟩) :: UInt256.ofNat 4294967295 :: p :: last.timestamp :: R)
        (observationReadHeadMem mem p last) (oracleReadHeadAw mem aw) rdata σ k' C' := by
  exact observationReadCursorX (v := v) rd hm.cursor hb hov

end Benchmarks.UniswapV3.Pool
