import Benchmarks.UniswapV3.Pool.BitmapNextAdjustTrace
import Benchmarks.UniswapV3.Pool.SignedWordZero
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_034

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem bitmapNextPrefixRawX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw lteRaw spacingRaw tickRaw base ret : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables} (tick spacing : Int)
    (rd : RD (deployedRuntime v) ee g s0 ⟨11307⟩
      (lteRaw :: spacingRaw :: tickRaw :: base :: ret :: R) mem aw rdata σ k C)
    (htlo : -(2 ^ 23 : Int) ≤ tick) (hthi : tick < 2 ^ 23)
    (hslo : -(2 ^ 23 : Int) ≤ spacing) (hshi : spacing < 2 ^ 23)
    (ht : UInt256.signextend (UInt256.ofNat 2) tickRaw = EVM.wordOfInt tick)
    (hs : UInt256.signextend (UInt256.ofNat 2) spacingRaw = EVM.wordOfInt spacing)
    (hov : R.length + 12 ≤ 1024) :
    (spacing = 0 ∧ RDinvalid (deployedRuntime v) g s0) ∨
      (spacing ≠ 0 ∧ ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨11376⟩
        (EVM.wordOfInt (bitmapNextCompressed tick spacing) :: ⟨0⟩ :: ⟨0⟩ ::
          lteRaw :: spacingRaw :: tickRaw :: base :: ret :: R) mem aw rdata σ k' C') := by
  by_cases hn : spacing = 0
  · have r0 := uniswapV3Pool_block_11307_fallthrough (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [hs, hn]; rfl) rd
    exact Or.inl ⟨hn, uniswapV3Pool_block_11326 (immWords := wordsOf (immStore v)) r0⟩
  have hsn : EVM.wordOfInt spacing ≠ (UInt256.ofNat 0) := by
    intro he
    exact hn ((wordOfInt_zero_iff_signed spacing (by omega) (by omega)).mp he)
  have r0 := uniswapV3Pool_block_11307_taken (immWords := wordsOf (immStore v))
    (by evm_ov) (by rw [hs]; exact hsn)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
  have hq : UInt256.sdiv (UInt256.signextend (UInt256.ofNat 2) tickRaw)
      (UInt256.signextend (UInt256.ofNat 2) spacingRaw) = EVM.wordOfInt (tick.tdiv spacing) := by
    rw [ht, hs]
    exact wordOfInt_sdiv tick spacing (by omega) (by omega) (by omega) (by omega)
  have hlt : UInt256.slt (UInt256.signextend (UInt256.ofNat 2) tickRaw) (UInt256.ofNat 0) =
      if tick < 0 then ⟨1⟩ else ⟨0⟩ := by
    rw [ht]
    exact slt_wordOfInt tick 0 (by omega) (by omega) (by decide) (by decide)
  have hg : ∃ kg Cg, RD (deployedRuntime v) ee g s0 ⟨11366⟩
      ((if bitmapNextAdjust tick spacing then ⟨1⟩ else ⟨0⟩) :: EVM.wordOfInt (tick.tdiv spacing) ::
        ⟨0⟩ :: ⟨0⟩ :: lteRaw :: spacingRaw :: tickRaw :: base :: ret :: R)
        mem aw rdata σ kg Cg := by
    by_cases htneg : tick < 0
    · have r1 := uniswapV3Pool_block_11327_fallthrough (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [hlt, if_pos htneg]; decide) r0
      have r2 := uniswapV3Pool_block_11344_taken (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [hs]; exact hsn)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
      have r3 := uniswapV3Pool_block_11359 (immWords := wordsOf (immStore v))
        (by simp only [uniswapV3Pool_block_11344_taken_stack]; evm_ov) r2
      simp only [uniswapV3Pool_block_11344_taken_stack, ht, hs,
        wordOfInt_sdiv tick spacing (by omega) (by omega) (by omega) (by omega)] at r3
      have r4 := RD.smod r3
        (by immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore v),
          (⟨11360⟩ : UInt256), UInt8.ofNat 7, .SMOD, none,
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      rw [wordOfInt_smod tick spacing (by omega) (by omega) (by omega) (by omega) hn] at r4
      have r5 := uniswapV3Pool_block_11361 (immWords := wordsOf (immStore v)) (by evm_ov) r4
      have hrabs : (tick.tmod spacing).natAbs < 2 ^ 23 := by
        rw [Int.natAbs_tmod]
        exact lt_of_lt_of_le (Nat.mod_lt _ (Int.natAbs_pos.mpr hn)) (by omega)
      have hrClean : UInt256.signextend (UInt256.ofNat 2) (EVM.wordOfInt (tick.tmod spacing)) =
          EVM.wordOfInt (tick.tmod spacing) := by
        rw [signextend_wordOfInt ⟨24, by decide⟩ _ _ (by decide) (by decide),
          normalizeSint_eq_self ⟨24, by decide⟩ _ (by change -(2 ^ 23 : Int) ≤ _; omega)
            (by change _ < (2 ^ 23 : Int); omega)]
      have hflag : UInt256.isZero (UInt256.isZero
          (UInt256.signextend (UInt256.ofNat 2) (EVM.wordOfInt (tick.tmod spacing)))) =
          if bitmapNextAdjust tick spacing then ⟨1⟩ else ⟨0⟩ := by
        rw [hrClean]
        by_cases hr : tick.tmod spacing = 0
        · have ha : ¬bitmapNextAdjust tick spacing := fun h ↦ h.2 hr
          rw [if_neg ha, hr]
          rfl
        · have hrn : EVM.wordOfInt (tick.tmod spacing) ≠ (⟨0⟩ : UInt256) := by
            intro he
            exact hr ((wordOfInt_zero_iff_signed _ (by omega) (by omega)).mp he)
          rw [if_pos (show bitmapNextAdjust tick spacing from ⟨htneg, hr⟩),
            isZero_eq_zero_of_ne hrn]
          rfl
      simpa only [uniswapV3Pool_block_11361_stack, hflag] using RD.pack r5
    · have r1 := uniswapV3Pool_block_11327_taken (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [hlt, if_neg htneg]; decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r0
      have ha : ¬bitmapNextAdjust tick spacing := fun h ↦ htneg h.1
      simpa only [uniswapV3Pool_block_11327_taken_stack, uniswapV3Pool_block_11307_taken_stack,
        hq, hlt, if_neg htneg, if_neg ha] using RD.pack r1
  obtain ⟨kg, Cg, rg⟩ := hg
  exact Or.inr ⟨hn, bitmapNextAdjustX (v := v) tick spacing htlo hthi hn rg (by evm_ov)⟩

end Benchmarks.UniswapV3.Pool
