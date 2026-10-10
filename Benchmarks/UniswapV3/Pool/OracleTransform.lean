import Benchmarks.UniswapV3.Pool.OracleTransformCompute

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def oracleTransformMem (mem : ByteArray) (p : UInt256) (last : OracleObservation)
    (time : UInt256) (tick : Int) (liquidity : UInt256) : ByteArray :=
  wordArrayAllocMem (wordArrayAllocMem mem p [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩])
    (p + ⟨128⟩) (oracleTransformed last time tick liquidity).words

theorem oracleTransformMonoX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret p lastPtr time timeRaw tickRaw liquidity : UInt256}
    {last : OracleObservation} {tick : Int} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨18466⟩
      (liquidity :: tickRaw :: timeRaw :: lastPtr :: ret :: R) mem aw rdata σ k C)
    (hh : HeapMemory mem aw p) (hm : ObservationMemory mem lastPtr last)
    (hp : 96 ≤ lastPtr.toNat) (hl : lastPtr.toNat + 128 ≤ p.toNat)
    (hb : p.toNat + 256 ≤ 2 ^ 200)
    (htime : UInt256.land timeRaw (UInt256.ofNat (2 ^ 32 - 1)) = time)
    (htick : UInt256.signextend (UInt256.ofNat 2) tickRaw = EVM.wordOfInt tick)
    (hliq : liquidity.toNat < 2 ^ 128)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 16 ≤ 1024) :
    ∃ aw' k' C', C + (Cₘ aw' - Cₘ aw) ≤ C' ∧ RD (deployedRuntime v) ee g s0 ret ((p + ⟨128⟩) :: R)
      (oracleTransformMem mem p last time tick liquidity) aw' rdata σ k' C' ∧
      HeapMemory (oracleTransformMem mem p last time tick liquidity) aw' (p + ⟨256⟩) ∧
      ObservationMemory (oracleTransformMem mem p last time tick liquidity)
        (p + ⟨128⟩) (oracleTransformed last time tick liquidity) ∧
      MemoryPrefix mem (oracleTransformMem mem p last time tick liquidity) p.toNat ∧
      (p + ⟨256⟩).toNat ≤ aw'.toNat * 32 + 32 := by
  dsimp only [oracleTransformMem]
  have hpn : (p + (⟨128⟩ : UInt256)).toNat = p.toNat + 128 :=
    uadd_word_ofNat_toNat p 128 (by change _ < 2 ^ 256; omega)
  have hpnext : (p + (⟨128⟩ : UInt256)) + ⟨128⟩ = p + ⟨256⟩ := by rw [uadd_assoc]; rfl
  have rdZero := uniswapV3Pool_block_18466 (immWords := wordsOf (immStore v))
    (by evm_ov) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) rd
  simp only [uniswapV3Pool_block_18466_stack] at rdZero
  obtain ⟨az, kz, Cz, hCz, rdCompute, hhCompute, _⟩ := observationZeroMonoX (v := v) rdZero hh (by omega)
    (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest) (by evm_ov)
  have hpre := wordArrayAllocMem_prefix mem p [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩]
  have hmCompute : ObservationMemory (wordArrayAllocMem mem p [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩])
      lastPtr last := MemoryPrefix.wordArray hpre hm hp hl
  obtain ⟨ar, kr, Cr, hCr, rdReturn, hhReturn, hcover⟩ := oracleTransformComputeMonoX (v := v) rdCompute hhCompute hmCompute hp
    (by rw [hpn]; omega) (by rw [hpn]; omega) htime htick hliq hret hov
  refine ⟨ar, kr, Cr, by omega, rdReturn, ?_, ?_, ?_, ?_⟩
  · change HeapMemory _ _ ((p + (⟨128⟩ : UInt256)) + ⟨128⟩) at hhReturn
    rw [hpnext] at hhReturn
    exact hhReturn
  · exact wordArrayAllocMem_region _ _ _ hhCompute.lower (by simp [OracleObservation.words])
  · have hpre2 := wordArrayAllocMem_prefix
      (wordArrayAllocMem mem p [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩]) (p + ⟨128⟩)
      (oracleTransformed last time tick liquidity).words
    have hpre2' := hpre2.mono (show p.toNat ≤ (p + (⟨128⟩ : UInt256)).toNat by rw [hpn]; omega)
    exact hpre.trans hpre2'
  · simpa only [hpnext] using hcover 

theorem oracleTransformX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret p lastPtr time timeRaw tickRaw liquidity : UInt256}
    {last : OracleObservation} {tick : Int} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨18466⟩
      (liquidity :: tickRaw :: timeRaw :: lastPtr :: ret :: R) mem aw rdata σ k C)
    (hh : HeapMemory mem aw p) (hm : ObservationMemory mem lastPtr last)
    (hp : 96 ≤ lastPtr.toNat) (hl : lastPtr.toNat + 128 ≤ p.toNat)
    (hb : p.toNat + 256 ≤ 2 ^ 200)
    (htime : UInt256.land timeRaw (UInt256.ofNat (2 ^ 32 - 1)) = time)
    (htick : UInt256.signextend (UInt256.ofNat 2) tickRaw = EVM.wordOfInt tick)
    (hliq : liquidity.toNat < 2 ^ 128)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 16 ≤ 1024) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ret ((p + ⟨128⟩) :: R)
      (oracleTransformMem mem p last time tick liquidity) aw' rdata σ k' C' ∧
      HeapMemory (oracleTransformMem mem p last time tick liquidity) aw' (p + ⟨256⟩) ∧
      ObservationMemory (oracleTransformMem mem p last time tick liquidity)
        (p + ⟨128⟩) (oracleTransformed last time tick liquidity) ∧
      MemoryPrefix mem (oracleTransformMem mem p last time tick liquidity) p.toNat := by
  obtain ⟨aw', k', C', _, hout, hheap, hmem, hpre, _⟩ := oracleTransformMonoX (v := v)
    rd hh hm hp hl hb htime htick hliq hret hov
  exact ⟨aw', k', C', hout, hheap, hmem, hpre⟩

end Benchmarks.UniswapV3.Pool

