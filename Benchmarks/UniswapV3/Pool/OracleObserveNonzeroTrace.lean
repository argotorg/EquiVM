import Benchmarks.UniswapV3.Pool.OracleObservePairTrace
import Benchmarks.UniswapV3.Pool.OracleSurroundingTrace
import Benchmarks.UniswapV3.Pool.OracleDeltaWords
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_044

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem oracleObserveSingleNonzeroCursorX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C allowance : Nat} {aw free card liquidity index : UInt256}
    {tickRaw secondsAgoRaw timeRaw ret time secondsAgo : UInt256} {tick : Int}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨13193⟩
      (card :: liquidity :: index :: tickRaw :: secondsAgoRaw :: timeRaw :: ⟨8⟩ :: ret :: R)
      mem aw rdata σ k C)
    (hi : index.toNat < 2 ^ 16) (hc : card.toNat < 2 ^ 16)
    (htime : UInt256.land (UInt256.ofNat 4294967295) timeRaw = time)
    (hago : UInt256.land (UInt256.ofNat 4294967295) secondsAgoRaw = secondsAgo)
    (hn : secondsAgo ≠ ⟨0⟩)
    (htick : UInt256.signextend (UInt256.ofNat 2) tickRaw = EVM.wordOfInt tick)
    (hliq : liquidity.toNat < 2 ^ 128)
    (hm : MemoryCursor mem aw free) (hbudget : MemoryGasBound aw C allowance)
    (hallowance : allowance ≤ 2 ^ 200) (hcover : free.toNat ≤ aw.toNat * 32 + 32)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 53 ≤ 1024) :
    OracleObserveSingleOutcome v ee g s0 σ rdata ret R time secondsAgo tick index liquidity card
      mem aw free C := by
  have r1 := uniswapV3Pool_block_13193_taken (immWords := wordsOf (immStore v)) (by evm_ov)
    (by rw [u256_land_comm, hago]; exact hn)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [uniswapV3Pool_block_13193_taken_stack] at r1
  have r2 := uniswapV3Pool_block_13360 (immWords := wordsOf (immStore v)) (by evm_ov)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
  simp only [uniswapV3Pool_block_13360_stack] at r2
  have ht := oracleDelta_of_masks htime hago
  rcases oracleSurroundingCursorX (v := v) (time := time) (target := oracleDelta time secondsAgo)
    (tick := tick) r2 hi hc htime ht htick hliq hm (hbudget.mono_cost (by omega))
    hallowance hcover (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest) (by evm_ov)
    with hoog | ⟨hfail, rfail⟩ | ⟨hin, ⟨out⟩⟩
  · exact Or.inl hoog
  · exact Or.inr (Or.inl ⟨.surrounding hn hfail, rfail⟩)
  · have hbout := hbudget.advance (show C + (Cₘ out.aw - Cₘ aw) ≤ out.cost by
      have h := out.cost_bound
      omega)
    rcases memoryGasCapacityOrOOG out.rd hbout hallowance out.cover with hoog | hb
    · exact Or.inl hoog
    · rcases oracleObservePairX (v := v) out.rd hn hin out.run out.heap (by omega)
        out.before_mem out.after_mem out.before_end out.after_end out.cover ht hret (by omega)
        with hoog | (hfail | result)
      · exact Or.inl hoog
      · exact Or.inr (Or.inl hfail)
      · obtain ⟨result⟩ := result
        exact Or.inr (Or.inr ⟨result.lift (by have h := out.cost_bound; omega)
          out.free_mono out.memory_prefix⟩)

theorem oracleObserveSingleNonzeroX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C allowance : Nat} {aw free card liquidity index : UInt256}
    {tickRaw secondsAgoRaw timeRaw ret time secondsAgo : UInt256} {tick : Int}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨13193⟩
      (card :: liquidity :: index :: tickRaw :: secondsAgoRaw :: timeRaw :: ⟨8⟩ :: ret :: R)
      mem aw rdata σ k C)
    (hi : index.toNat < 2 ^ 16) (hc : card.toNat < 2 ^ 16)
    (htime : UInt256.land (UInt256.ofNat 4294967295) timeRaw = time)
    (hago : UInt256.land (UInt256.ofNat 4294967295) secondsAgoRaw = secondsAgo)
    (hn : secondsAgo ≠ ⟨0⟩)
    (htick : UInt256.signextend (UInt256.ofNat 2) tickRaw = EVM.wordOfInt tick)
    (hliq : liquidity.toNat < 2 ^ 128)
    (hm : HeapMemory mem aw free) (hbudget : MemoryGasBound aw C allowance)
    (hallowance : allowance ≤ 2 ^ 200) (hcover : free.toNat ≤ aw.toNat * 32 + 32)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 53 ≤ 1024) :
    OracleObserveSingleOutcome v ee g s0 σ rdata ret R time secondsAgo tick index liquidity card
      mem aw free C := by
  exact oracleObserveSingleNonzeroCursorX (v := v) rd hi hc htime hago hn htick hliq hm.cursor hbudget hallowance hcover hret hov

end Benchmarks.UniswapV3.Pool
