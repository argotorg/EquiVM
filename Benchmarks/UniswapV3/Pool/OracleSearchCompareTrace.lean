import Benchmarks.UniswapV3.Pool.OracleSearchAfter

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem oracleSearchPairCompareX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p left right beforePtr afterPtr : UInt256}
    {cardRaw indexRaw targetRaw timeRaw ret time target : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (before after : OracleObservation)
    (rd : RD (deployedRuntime v) ee g s0 ⟨20184⟩
      (targetRaw :: before.timestamp :: timeRaw :: ⟨20717⟩ :: ⟨0⟩ ::
        oracleSearchStack (oracleSearchMiddle left right) left right beforePtr afterPtr
          cardRaw indexRaw targetRaw timeRaw ret R) mem aw rdata σ k C)
    (htime : UInt256.land (UInt256.ofNat 4294967295) timeRaw = time)
    (htarget : UInt256.land (UInt256.ofNat 4294967295) targetRaw = target)
    (hb32 : before.timestamp.toNat < 2 ^ 32) (ha32 : after.timestamp.toNat < 2 ^ 32)
    (hm : HeapMemory mem aw p) (hb : p.toNat + 128 ≤ 2 ^ 200)
    (hafter : ObservationMemory mem afterPtr after) (hend : afterPtr.toNat + 128 ≤ p.toNat)
    (hcover : p.toNat ≤ aw.toNat * 32 + 32) (hov : R.length + 26 ≤ 1024) :
    let first := oracleLte time before.timestamp target
    let second := oracleLte time target after.timestamp
    ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) ee g s0 ⟨20742⟩
      ((if first && second then ⟨1⟩ else ⟨0⟩) :: (if first then ⟨1⟩ else ⟨0⟩) ::
        oracleSearchStack (oracleSearchMiddle left right) left right beforePtr afterPtr
          cardRaw indexRaw targetRaw timeRaw ret R) mem aw rdata σ k' C' := by
  dsimp only
  have hbeforeMask : UInt256.land (UInt256.ofNat 4294967295) before.timestamp =
      before.timestamp := by
    rw [u256_land_comm]
    exact u256LandMaskCleanOfToNat (bits := 32) _ _ (by decide) hb32
  have hafterMask : UInt256.land (UInt256.ofNat 4294967295) after.timestamp =
      after.timestamp := by
    rw [u256_land_comm]
    exact u256LandMaskCleanOfToNat (bits := 32) _ _ (by decide) ha32
  obtain ⟨k1, C1, hC1, r1⟩ := oracleLteMonoX (v := v) time before.timestamp target rd
    htime hbeforeMask htarget
    (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest)
    (by first | omega | (dsimp only [oracleSearchStack, List.length]; omega))
  by_cases hf : oracleLte time before.timestamp target = true
  · rw [if_pos hf] at r1
    have r2 := uniswapV3Pool_block_20717_fallthrough (immWords := wordsOf (immStore v))
      (by first | omega | (dsimp only [oracleSearchStack, List.length]; omega)) (by decide) r1
    have r3 := uniswapV3Pool_block_20727 (immWords := wordsOf (immStore v))
      (by first | omega | (dsimp only [oracleSearchStack, List.length]; omega))
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r2
    have hload : memLoad afterPtr mem = after.timestamp := by
      simpa only [OracleObservation.words, Nat.mul_zero,
        show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl, u256_add_zero,
        List.getElem_cons_zero] using hafter.load 0 (by simp [OracleObservation.words])
          (by simp only [OracleObservation.words, List.length_cons, List.length_nil]
              change _ < 2 ^ 256
              omega)
    have hloadAw : M aw afterPtr ⟨32⟩ = aw :=
      expandedWords32_eq_of_cover hm.active (by omega) (by omega)
    simp only [uniswapV3Pool_block_20727_stack,
      show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl, u256_zero_add, hload, hloadAw] at r3
    obtain ⟨k2, C2, hC2, r4⟩ := oracleLteMonoX (v := v) time target after.timestamp r3
      htime htarget hafterMask
      (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest)
      (by first | omega | (dsimp only [oracleSearchStack, List.length]; omega))
    refine ⟨k2, C2, by omega, ?_⟩
    simpa only [hf, Bool.true_and, ↓reduceIte] using r4
  · have r2 := uniswapV3Pool_block_20717_taken (immWords := wordsOf (immStore v))
      (by first | omega | (dsimp only [oracleSearchStack, List.length]; omega))
      (by rw [if_neg hf]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
    refine ⟨k1 + 8, C1 + 28, by omega, ?_⟩
    have hfz : oracleLte time before.timestamp target = false := by
      exact Bool.eq_false_of_not_eq_true hf
    simpa only [uniswapV3Pool_block_20717_taken_stack, hfz, Bool.false_and,
      Bool.false_eq_true, ↓reduceIte] using r2

end Benchmarks.UniswapV3.Pool
