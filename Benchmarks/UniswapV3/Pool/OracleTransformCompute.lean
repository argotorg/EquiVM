import Benchmarks.UniswapV3.Pool.OracleTransformMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem oracleTransformComputeMonoX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret p lastPtr zeroPtr time timeRaw tickRaw liquidity : UInt256}
    {last : OracleObservation} {tick : Int} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨18474⟩
      (zeroPtr :: liquidity :: tickRaw :: timeRaw :: lastPtr :: ret :: R) mem aw rdata σ k C)
    (hh : HeapMemory mem aw p) (hm : ObservationMemory mem lastPtr last)
    (hp : 96 ≤ lastPtr.toNat) (hl : lastPtr.toNat + 128 ≤ p.toNat)
    (hb : p.toNat + 128 ≤ 2 ^ 200)
    (htime : UInt256.land timeRaw (UInt256.ofNat (2 ^ 32 - 1)) = time)
    (htick : UInt256.signextend (UInt256.ofNat 2) tickRaw = EVM.wordOfInt tick)
    (hliq : liquidity.toNat < 2 ^ 128)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 16 ≤ 1024) :
    ∃ aw' k' C', C + (Cₘ aw' - Cₘ aw) ≤ C' ∧ RD (deployedRuntime v) ee g s0 ret (p :: R)
      (wordArrayAllocMem mem p (oracleTransformed last time tick liquidity).words)
      aw' rdata σ k' C' ∧
      HeapMemory (wordArrayAllocMem mem p (oracleTransformed last time tick liquidity).words)
        aw' (p + ⟨128⟩) ∧ (p + ⟨128⟩).toNat ≤ aw'.toNat * 32 + 32 := by
  have hload : memLoad (UInt256.ofNat 64) mem = p := hh.load64
  have hzero : UInt256.ofNat 0 + lastPtr = lastPtr := u256_zero_add lastPtr
  have hl0 := hm.load_timestamp (by change _ < 2 ^ 256; omega)
  have hl32 : (lastPtr + UInt256.ofNat 32).toNat = lastPtr.toNat + 32 :=
    uadd_word_ofNat_toNat lastPtr 32 (by change _ < 2 ^ 256; omega)
  have hl64 : (lastPtr + UInt256.ofNat 64).toNat = lastPtr.toNat + 64 :=
    uadd_word_ofNat_toNat lastPtr 64 (by change _ < 2 ^ 256; omega)
  have hp32 : (p + UInt256.ofNat 32).toNat = p.toNat + 32 :=
    uadd_word_ofNat_toNat p 32 (by change _ < 2 ^ 256; omega)
  have hp64 : (p + UInt256.ofNat 64).toNat = p.toNat + 64 :=
    uadd_word_ofNat_toNat p 64 (by change _ < 2 ^ 256; omega)
  have hp96 : (p + UInt256.ofNat 96).toNat = p.toNat + 96 :=
    uadd_word_ofNat_toNat p 96 (by change _ < 2 ^ 256; omega)
  have hadd64 : UInt256.ofNat 32 + (p + UInt256.ofNat 32) = p + UInt256.ofNat 64 := by
    rw [u256_add_comm (UInt256.ofNat 32), uadd_assoc]; rfl
  have hadd96 : UInt256.ofNat 32 + (p + UInt256.ofNat 64) = p + UInt256.ofNat 96 := by
    rw [u256_add_comm (UInt256.ofNat 32), uadd_assoc]; rfl
  have hmask : UInt256.land (UInt256.ofNat (2 ^ 128 - 1)) liquidity = liquidity := by
    rw [u256_land_comm]
    exact u256LandMaskCleanOfToNat liquidity _ (by decide) hliq
  have hmem := oracleTransformHeadMem_eq hh hm hp hl hb htime htick (liquidity := liquidity)
  have hmemf : uniswapV3Pool_block_18474_fallthrough_memory
      (mem := mem) (x2 := tickRaw) (x3 := timeRaw) (x4 := lastPtr) =
      oracleTransformHeadMem mem p last time tick liquidity := hmem
  let ah := M (M (M (M (M (M aw lastPtr ⟨32⟩) (UInt256.ofNat 64) ⟨32⟩)
    (UInt256.ofNat 64) ⟨32⟩) p ⟨32⟩) (lastPtr + UInt256.ofNat 32) ⟨32⟩)
    (p + UInt256.ofNat 32) ⟨32⟩
  have ha : ActiveWords ah := by
    apply activeWords_expand32
    · apply activeWords_expand32
      · apply activeWords_expand32
        · apply activeWords_expand32
          · apply activeWords_expand32
            · exact activeWords_expand32 hh.active (by omega)
            · decide
          · decide
        · omega
      · rw [hl32]; omega
    · rw [hp32]; omega
  obtain ⟨kD, CD, hCD, rdDenom⟩ : ∃ kD CD,
      C + (Cₘ ah - Cₘ aw) ≤ CD ∧ RD (deployedRuntime v) ee g s0 ⟨18560⟩
        (oracleLiquidityDenominator liquidity :: (p + UInt256.ofNat 64) :: p ::
          UInt256.sub timeRaw last.timestamp :: zeroPtr :: liquidity :: tickRaw ::
          timeRaw :: lastPtr :: ret :: R)
        (oracleTransformHeadMem mem p last time tick liquidity) ah rdata σ kD CD := by
    by_cases hlq : 0 < liquidity.toNat
    · have rdHead := uniswapV3Pool_block_18474_taken (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [solcMask128, hmask, ugt_one (a := liquidity) (b := UInt256.ofNat 0) hlq]; decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
      simp only [uniswapV3Pool_block_18474_taken_stack, hload, hzero, hl0, hadd64,
        u256_add_comm (UInt256.ofNat 32) lastPtr, u256_add_comm (UInt256.ofNat 32) p,
        hmem] at rdHead
      have rdPush := uniswapV3Pool_block_18558 (immWords := wordsOf (immStore v)) (by evm_ov) rdHead
      simp only [uniswapV3Pool_block_18558_stack] at rdPush
      rw [oracleLiquidityDenominator, if_pos hlq]
      refine ⟨_, _, ?_, rdPush⟩
      dsimp only [ah]
      simp only [memExpansionCost]
      omega
    · have rdHead := uniswapV3Pool_block_18474_fallthrough (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [solcMask128, hmask]; exact ugt_zero (by change liquidity.toNat ≤ 0; omega)) rd
      simp only [uniswapV3Pool_block_18474_fallthrough_stack, hload, hzero, hl0, hadd64,
        u256_add_comm (UInt256.ofNat 32) lastPtr, u256_add_comm (UInt256.ofNat 32) p,
        hmemf] at rdHead
      have rdPush := uniswapV3Pool_block_18552 (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdHead
      simp only [uniswapV3Pool_block_18552_stack] at rdPush
      rw [oracleLiquidityDenominator, if_neg hlq]
      refine ⟨_, _, ?_, rdPush⟩
      dsimp only [ah]
      simp only [memExpansionCost]
      omega
  have hdmask : UInt256.land (UInt256.ofNat (2 ^ 128 - 1))
      (oracleLiquidityDenominator liquidity) = oracleLiquidityDenominator liquidity := by
    rw [u256_land_comm]
    apply u256LandMaskCleanOfToNat (bits := 128) _ _ (by decide)
    unfold oracleLiquidityDenominator
    split
    · exact hliq
    · decide
  have hdnz : oracleLiquidityDenominator liquidity ≠ UInt256.ofNat 0 := by
    intro hz
    have hd := oracleLiquidityDenominator_pos liquidity
    rw [hz] at hd
    contradiction
  have rdDivide := uniswapV3Pool_block_18560_taken (immWords := wordsOf (immStore v))
    (by evm_ov) (by rw [solcMask128, hdmask]; exact hdnz)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdDenom
  have hd : oracleDelta timeRaw last.timestamp = oracleDelta time last.timestamp := by
    rw [← oracleDelta_mask_time, htime]
  simp only [uniswapV3Pool_block_18560_taken_stack, solcMask128, hdmask, shiftLeft_mask32_128]
    at rdDivide
  change RD _ _ _ _ _ (UInt256.shiftLeft (oracleDelta timeRaw last.timestamp) ⟨128⟩ :: _) _ _ _ _ _ _ at rdDivide
  rw [hd] at rdDivide
  have rdReturn := uniswapV3Pool_block_18603 (immWords := wordsOf (immStore v))
    (by evm_ov) hret rdDivide
  have htail := oracleTransformTailMem_eq hm hp hl hb (time := time) (tick := tick) (liquidity := liquidity)
  simp only [uniswapV3Pool_block_18603_stack, htail,
    u256_add_comm (UInt256.ofNat 64) lastPtr, hadd96] at rdReturn
  have ha' := activeWords_expand32
    (activeWords_expand32
      (activeWords_expand32 ha (show (lastPtr + UInt256.ofNat 64).toNat + 32 ≤ 2 ^ 200 by rw [hl64]; omega))
      (show (p + UInt256.ofNat 64).toNat + 32 ≤ 2 ^ 200 by rw [hp64]; omega))
    (show (p + UInt256.ofNat 96).toNat + 32 ≤ 2 ^ 200 by rw [hp96]; omega)
  refine ⟨_, _, _, ?_, rdReturn,
    wordArrayAllocMem_heap mem p _ _ hh.lower (by simp [OracleObservation.words]) hb ha', ?_⟩
  · simp only [memExpansionCost]
    omega
  · have hcap := expandedWords32_cover
      (activeWords_expand32
        (activeWords_expand32 ha
          (show (lastPtr + UInt256.ofNat 64).toNat + 32 ≤ 2 ^ 200 by rw [hl64]; omega))
        (show (p + UInt256.ofNat 64).toNat + 32 ≤ 2 ^ 200 by rw [hp64]; omega))
      (show (p + UInt256.ofNat 96).toNat + 32 ≤ 2 ^ 200 by rw [hp96]; omega)
    have hp128 : (p + (⟨128⟩ : UInt256)).toNat = p.toNat + 128 :=
      uadd_word_ofNat_toNat p 128 (by change _ < 2 ^ 256; omega)
    rw [hp96] at hcap
    dsimp only [M]
    dsimp only [expandedWords] at hcap
    rw [hp128]
    omega


theorem oracleTransformComputeX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret p lastPtr zeroPtr time timeRaw tickRaw liquidity : UInt256}
    {last : OracleObservation} {tick : Int} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨18474⟩
      (zeroPtr :: liquidity :: tickRaw :: timeRaw :: lastPtr :: ret :: R) mem aw rdata σ k C)
    (hh : HeapMemory mem aw p) (hm : ObservationMemory mem lastPtr last)
    (hp : 96 ≤ lastPtr.toNat) (hl : lastPtr.toNat + 128 ≤ p.toNat)
    (hb : p.toNat + 128 ≤ 2 ^ 200)
    (htime : UInt256.land timeRaw (UInt256.ofNat (2 ^ 32 - 1)) = time)
    (htick : UInt256.signextend (UInt256.ofNat 2) tickRaw = EVM.wordOfInt tick)
    (hliq : liquidity.toNat < 2 ^ 128)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 16 ≤ 1024) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ret (p :: R)
      (wordArrayAllocMem mem p (oracleTransformed last time tick liquidity).words)
      aw' rdata σ k' C' ∧
      HeapMemory (wordArrayAllocMem mem p (oracleTransformed last time tick liquidity).words)
        aw' (p + ⟨128⟩) := by
  obtain ⟨aw', k', C', _, hout, hheap, _⟩ := oracleTransformComputeMonoX (v := v)
    rd hh hm hp hl hb htime htick hliq hret hov
  exact ⟨aw', k', C', hout, hheap⟩

end Benchmarks.UniswapV3.Pool
