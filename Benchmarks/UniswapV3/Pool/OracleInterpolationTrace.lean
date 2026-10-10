import Benchmarks.UniswapV3.Pool.OracleInterpolationWords
import Benchmarks.UniswapV3.Pool.ObservationCoverage
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_045
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_046

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem oracleInterpolationX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw free beforePtr afterPtr targetRaw target z0 z1 : UInt256}
    {before after : OracleObservation} {mem rdata : ByteArray} {R : List UInt256}
    {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨13471⟩
      (afterPtr :: beforePtr :: targetRaw :: z0 :: z1 :: R) mem aw rdata σ k C)
    (hm : HeapMemory mem aw free) (hb : free.toNat ≤ 2 ^ 200)
    (hbefore : ObservationMemory mem beforePtr before) (hafter : ObservationMemory mem afterPtr after)
    (hbe : beforePtr.toNat + 128 ≤ free.toNat) (hae : afterPtr.toNat + 128 ≤ free.toNat)
    (hcover : free.toNat ≤ aw.toNat * 32 + 32)
    (htarget : UInt256.land targetRaw (UInt256.ofNat (2 ^ 32 - 1)) = target)
    (hov : R.length + 16 ≤ 1024) :
    ((oracleDelta after.timestamp before.timestamp).toNat = 0 ∧
      RDinvalid (deployedRuntime v) g s0) ∨
    ((oracleDelta after.timestamp before.timestamp).toNat ≠ 0 ∧
      ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) ee g s0 ⟨13584⟩
        (oracleInterpolationSecondsRaw before after target ::
          oracleInterpolationTickRaw before after target :: R) mem aw rdata σ k' C') := by
  have hbb : beforePtr.toNat + 128 < UInt256.size := by change _ < 2 ^ 256; omega
  have hab : afterPtr.toNat + 128 < UInt256.size := by change _ < 2 ^ 256; omega
  have hb0 := hbefore.load_timestamp hbb
  have hb32 := hbefore.load_tick hbb
  have hb64 := hbefore.load_seconds hbb
  have ha0 := hafter.load_timestamp hab
  have ha32 := hafter.load_tick hab
  have ha64 := hafter.load_seconds hab
  obtain ⟨eb0, eb32, eb64⟩ := observationLoadExpansion hm.active hb hbe hcover
  obtain ⟨ea0, ea32, ea64⟩ := observationLoadExpansion hm.active hb hae hcover
  have ht : oracleDelta targetRaw before.timestamp = oracleDelta target before.timestamp := by
    rw [← oracleDelta_mask_time targetRaw before.timestamp, htarget]
  by_cases hd : (oracleDelta after.timestamp before.timestamp).toNat = 0
  · have hz : oracleDelta after.timestamp before.timestamp = UInt256.ofNat 0 := u256_inj hd
    have r1 := uniswapV3Pool_block_13471_fallthrough (immWords := wordsOf (immStore v))
      (by evm_ov) (by simpa only [ha0, hb0] using hz) rd
    exact Or.inl ⟨hd, uniswapV3Pool_block_13516 (immWords := wordsOf (immStore v)) r1⟩
  · have hn : oracleDelta after.timestamp before.timestamp ≠ UInt256.ofNat 0 :=
      fun h ↦ hd (congrArg UInt256.toNat h)
    have r1 := uniswapV3Pool_block_13471_taken (immWords := wordsOf (immStore v))
      (by evm_ov) (by simpa only [ha0, hb0] using hn)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    simp only [uniswapV3Pool_block_13471_taken_stack, hb0, hb32, ha0, ha32,
      eb0, eb32, ea0, ea32, memExpansionCost, Nat.sub_self, Nat.add_zero] at r1
    have r2 := uniswapV3Pool_block_13517_taken (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [u256_land_comm]; exact hn)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
    have hmask : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 160 - 1) := by decide
    simp only [uniswapV3Pool_block_13517_taken_stack, hmask,
      u256_add_comm (UInt256.ofNat 32) beforePtr, u256_add_comm (UInt256.ofNat 64) beforePtr,
      u256_add_comm (UInt256.ofNat 64) afterPtr, hb32, hb64, ha64, eb32, eb64, ea64,
      memExpansionCost, Nat.sub_self, Nat.add_zero] at r2
    have r3 := uniswapV3Pool_block_13567 (immWords := wordsOf (immStore v)) (by evm_ov) r2
    simp only [uniswapV3Pool_block_13567_stack, u256_add_comm (UInt256.ofNat 64) beforePtr,
      hb64, eb64, memExpansionCost, Nat.sub_self, Nat.add_zero] at r3
    simp only [u256_land_comm (UInt256.ofNat (2 ^ 160 - 1)),
      u256_land_comm (UInt256.ofNat 4294967295)] at r3
    change UInt256.land (UInt256.sub targetRaw before.timestamp) (UInt256.ofNat 4294967295) =
      UInt256.land (UInt256.sub target before.timestamp) (UInt256.ofNat 4294967295) at ht
    rw [ht] at r3
    refine Or.inr ⟨hd, k + 37 + 33 + 16, C + 118 + 110 + 41, by omega, ?_⟩
    simpa only [oracleInterpolationSecondsRaw, oracleInterpolationTickRaw, oracleDelta] using r3

end Benchmarks.UniswapV3.Pool
