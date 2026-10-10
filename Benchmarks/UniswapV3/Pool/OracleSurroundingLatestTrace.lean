import Benchmarks.UniswapV3.Pool.OracleSurroundingFirst
import Benchmarks.UniswapV3.Pool.OracleSurroundingResult
import Benchmarks.UniswapV3.Pool.OracleTransform
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_046

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem oracleSurroundingLatestX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p afterPtr beforePtr card liquidity index : UInt256}
    {tickRaw targetRaw timeRaw ret time target : UInt256} {tick : Int} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨18782⟩
      (oracleSurroundingStack afterPtr beforePtr card liquidity index tickRaw targetRaw timeRaw ret R)
      mem aw rdata σ k C)
    (hf : oracleSurroundingFirst time target index σ ee = true)
    (htarget : UInt256.land (UInt256.ofNat 4294967295) targetRaw = target)
    (htick : UInt256.signextend (UInt256.ofNat 2) tickRaw = EVM.wordOfInt tick)
    (hliq : liquidity.toNat < 2 ^ 128)
    (hm : HeapMemory mem aw p) (hb : p.toNat + 256 ≤ 2 ^ 200)
    (hbefore : ObservationMemory mem beforePtr (oracleStoredObservation index σ ee))
    (hafter : ObservationMemory mem afterPtr oracleZeroObservation)
    (hbl : 128 ≤ beforePtr.toNat) (hbe : beforePtr.toNat + 128 ≤ p.toNat)
    (hal : 128 ≤ afterPtr.toNat) (hae : afterPtr.toNat + 128 ≤ p.toNat)
    (hcover : p.toNat ≤ aw.toNat * 32 + 32)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 40 ≤ 1024) :
    Nonempty (OracleSurroundingExit v ee g s0 σ rdata ret R time target tick index liquidity card
      mem aw p C) := by
  let last := oracleStoredObservation index σ ee
  have hrun : OracleSurroundingRun time target tick index liquidity card σ ee last
      (oracleSurroundingLatestAfter last target tick liquidity) := .latest hf
  have hload : memLoad beforePtr mem = last.timestamp :=
    hbefore.load_timestamp (by change _ < 2 ^ 256; omega)
  have hloadAw : M aw beforePtr ⟨32⟩ = aw :=
    expandedWords32_eq_of_cover hm.active (by omega) (by omega)
  have hmask : UInt256.land (UInt256.ofNat 4294967295) last.timestamp = last.timestamp := by
    rw [u256_land_comm]
    exact u256LandMaskCleanOfToNat (bits := 32) _ _ (by decide)
      (oracleStoredTimestamp_lt index σ ee)
  have hzero : UInt256.ofNat 0 + beforePtr = beforePtr := u256_zero_add _
  by_cases heq : last.timestamp = target
  · have r1 := uniswapV3Pool_block_18782_fallthrough (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [hzero, hload, hmask, htarget, heq, uInt256_eq_self]; decide) rd
    simp only [hzero, hloadAw] at r1
    have r2 := uniswapV3Pool_block_18806 (immWords := wordsOf (immStore v)) (by evm_ov)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
    have r3 := uniswapV3Pool_block_13584 (immWords := wordsOf (immStore v)) (by evm_ov) hret r2
    exact ⟨{ mem := mem
             aw := aw
             free := p
             beforePtr := beforePtr
             afterPtr := afterPtr
             before := last
             after := oracleZeroObservation
             k := _
             cost := _
             rd := r3
             run := by simpa only [oracleSurroundingLatestAfter, if_pos heq] using hrun
             heap := hm
             before_mem := hbefore
             after_mem := hafter
             before_lower := hbl
             before_end := hbe
             after_lower := hal
             after_end := hae
             free_mono := le_refl _
             memory_prefix := .refl _ _
             cover := hcover
             cost_bound := by omega }⟩
  · have hne : UInt256.eq last.timestamp target = UInt256.ofNat 0 := by
      apply uInt256_eq_zero_of_ne
      intro h
      exact heq (uInt256_eq_one_eq h)
    have r1 := uniswapV3Pool_block_18782_taken (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [hzero, hload, hmask, htarget, hne]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    simp only [hzero, hloadAw] at r1
    have r2 := uniswapV3Pool_block_18810 (immWords := wordsOf (immStore v)) (by evm_ov)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
    obtain ⟨aw3, k3, C3, hC3, r3, hm3, ha3, hpre3, hcover3⟩ := oracleTransformMonoX (v := v) (time := target) (tick := tick) (last := last)
      r2 hm hbefore (by omega) hbe hb
      (by rw [u256_land_comm]; exact htarget) htick hliq
      (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest) (by evm_ov)
    have r4 := uniswapV3Pool_block_18823 (immWords := wordsOf (immStore v)) (by evm_ov)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r3
    have r5 := uniswapV3Pool_block_13584 (immWords := wordsOf (immStore v)) (by evm_ov) hret r4
    simp only [uniswapV3Pool_block_13584_stack] at r5
    have hp128 : (p + (⟨128⟩ : UInt256)).toNat = p.toNat + 128 :=
      uadd_word_ofNat_toNat p 128 (by change _ < 2 ^ 256; omega)
    have hp256 : (p + (⟨256⟩ : UInt256)).toNat = p.toNat + 256 :=
      uadd_word_ofNat_toNat p 256 (by change _ < 2 ^ 256; omega)
    exact ⟨{ mem := oracleTransformMem mem p last target tick liquidity
             aw := aw3
             free := p + (⟨256⟩ : UInt256)
             beforePtr := beforePtr
             afterPtr := p + (⟨128⟩ : UInt256)
             before := last
             after := oracleTransformed last target tick liquidity
             k := k3 + 7 + 12
             cost := C3 + 22 + 32
             rd := r5
             run := by simpa only [oracleSurroundingLatestAfter, if_neg heq] using hrun
             heap := hm3
             before_mem := MemoryPrefix.wordArray hpre3 hbefore (by omega) hbe
             after_mem := ha3
             before_lower := hbl
             before_end := by rw [hp256]; omega
             after_lower := by rw [hp128]; omega
             after_end := by rw [hp128, hp256]
             free_mono := by rw [hp256]; omega
             memory_prefix := hpre3
             cover := hcover3
             cost_bound := by omega }⟩

end Benchmarks.UniswapV3.Pool
