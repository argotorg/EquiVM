import Benchmarks.UniswapV3.Pool.ObservationCoverage
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_045

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem oracleObserveCompareBeforeX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw free beforePtr afterPtr targetRaw target t0 t1 : UInt256}
    {before : OracleObservation} {mem rdata : ByteArray} {R : List UInt256}
    {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨13381⟩
      (afterPtr :: beforePtr :: t0 :: t1 :: targetRaw :: R) mem aw rdata σ k C)
    (hm : HeapMemory mem aw free) (hb : free.toNat ≤ 2 ^ 200)
    (hbefore : ObservationMemory mem beforePtr before) (hbe : beforePtr.toNat + 128 ≤ free.toNat)
    (hcover : free.toNat ≤ aw.toNat * 32 + 32) (hts : before.timestamp.toNat < 2 ^ 32)
    (htarget : UInt256.land (UInt256.ofNat 4294967295) targetRaw = target)
    (hov : R.length + 6 ≤ 1024) :
    RD (deployedRuntime v) ee g s0 (if target = before.timestamp then ⟨13410⟩ else ⟨13431⟩)
      (afterPtr :: beforePtr :: targetRaw :: R) mem aw rdata σ (k + 18) (C + 57) := by
  have hl := hbefore.load_timestamp (by change _ < 2 ^ 256; omega)
  have he := (observationLoadExpansion hm.active hb hbe hcover).1
  have hz : UInt256.ofNat 0 + beforePtr = beforePtr := u256_zero_add _
  have hmask : UInt256.land (UInt256.ofNat 4294967295) before.timestamp = before.timestamp := by
    rw [u256_land_comm]
    exact u256LandMaskCleanOfToNat (bits := 32) _ _ (by decide) hts
  by_cases ht : target = before.timestamp
  · have r := uniswapV3Pool_block_13381_fallthrough (immWords := wordsOf (immStore v)) hov
      (by rw [hz, hl, hmask, htarget, ht, uInt256_eq_self]; decide) rd
    simpa only [if_pos ht, uniswapV3Pool_block_13381_fallthrough_stack, hz, he,
      memExpansionCost, Nat.sub_self, Nat.add_zero] using r
  · have hne : UInt256.eq target before.timestamp = ⟨0⟩ :=
      uInt256_eq_zero_of_ne (fun h ↦ ht (uInt256_eq_one_eq h))
    have r := uniswapV3Pool_block_13381_taken (immWords := wordsOf (immStore v)) hov
      (by rw [hz, hl, hmask, htarget, hne]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    simpa only [if_neg ht, uniswapV3Pool_block_13381_taken_stack, hz, he,
      memExpansionCost, Nat.sub_self, Nat.add_zero] using r

theorem oracleObserveCompareAfterX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw free beforePtr afterPtr targetRaw target : UInt256}
    {after : OracleObservation} {mem rdata : ByteArray} {R : List UInt256}
    {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨13431⟩
      (afterPtr :: beforePtr :: targetRaw :: R) mem aw rdata σ k C)
    (hm : HeapMemory mem aw free) (hb : free.toNat ≤ 2 ^ 200)
    (hafter : ObservationMemory mem afterPtr after) (hae : afterPtr.toNat + 128 ≤ free.toNat)
    (hcover : free.toNat ≤ aw.toNat * 32 + 32) (hts : after.timestamp.toNat < 2 ^ 32)
    (htarget : UInt256.land (UInt256.ofNat 4294967295) targetRaw = target)
    (hov : R.length + 7 ≤ 1024) :
    RD (deployedRuntime v) ee g s0 (if target = after.timestamp then ⟨13450⟩ else ⟨13471⟩)
      (afterPtr :: beforePtr :: targetRaw :: R) mem aw rdata σ (k + 13) (C + 44) := by
  have hl := hafter.load_timestamp (by change _ < 2 ^ 256; omega)
  have he := (observationLoadExpansion hm.active hb hae hcover).1
  have hmask : UInt256.land after.timestamp (UInt256.ofNat 4294967295) = after.timestamp :=
    u256LandMaskCleanOfToNat (bits := 32) _ _ (by decide) hts
  by_cases ht : target = after.timestamp
  · have r := uniswapV3Pool_block_13431_fallthrough (immWords := wordsOf (immStore v)) hov
      (by rw [hl, hmask, htarget, ht, uInt256_eq_self]; decide) rd
    simpa only [if_pos ht, he, memExpansionCost, Nat.sub_self, Nat.add_zero] using r
  · have hne : UInt256.eq after.timestamp target = ⟨0⟩ :=
      uInt256_eq_zero_of_ne (fun h ↦ ht (uInt256_eq_one_eq h).symm)
    have r := uniswapV3Pool_block_13431_taken (immWords := wordsOf (immStore v)) hov
      (by rw [hl, hmask, htarget, hne]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    simpa only [if_neg ht, he, memExpansionCost, Nat.sub_self, Nat.add_zero] using r

end Benchmarks.UniswapV3.Pool
