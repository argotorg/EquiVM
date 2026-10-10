import Benchmarks.UniswapV3.Pool.BitmapPositionTrace
import Benchmarks.UniswapV3.Pool.BitmapFlipPrefix
import Benchmarks.UniswapV3.Pool.SignedDivisionGeneral
import Benchmarks.UniswapV3.Pool.SignedWordZero
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_071
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_072

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

theorem bitmapFlipBeforeStoreRawX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw base ret spacingRaw : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (tick spacing : Int)
    (rd : RD (deployedRuntime v) ee g s0 ⟨21285⟩
      (spacingRaw :: EVM.wordOfInt tick :: base :: ret :: R) mem aw rdata σ k C)
    (htlo : -(2 ^ 23 : Int) ≤ tick) (hthi : tick < 2 ^ 23)
    (hslo : -(2 ^ 23 : Int) ≤ spacing) (hshi : spacing < 2 ^ 23)
    (hs : UInt256.signextend (UInt256.ofNat 2) spacingRaw = EVM.wordOfInt spacing)
    (hov : R.length + 11 ≤ 1024) :
    (RDinvalid (deployedRuntime v) g s0 ∧ spacing = 0) ∨
    (RDrev (deployedRuntime v) g s0 ∧ spacing ≠ 0 ∧ tick.tmod spacing ≠ 0) ∨
    (spacing ≠ 0 ∧ tick.tmod spacing = 0 ∧ ∃ k' C',
      RD (deployedRuntime v) ee g s0 ⟨21341⟩
        (bitmapPositionBitRaw (tick.tdiv spacing) :: EVM.wordOfInt (bitmapWordPos (tick.tdiv spacing)) ::
          ⟨0⟩ :: ⟨0⟩ :: spacingRaw :: EVM.wordOfInt tick :: base :: ret :: R)
        mem aw rdata σ k' C') := by
  have ht : UInt256.signextend (UInt256.ofNat 2) (EVM.wordOfInt tick) = EVM.wordOfInt tick := by
    rw [signextend_wordOfInt ⟨24, by decide⟩ _ tick (by decide) (by decide),
      normalizeSint_eq_self ⟨24, by decide⟩ _ htlo hthi]
  by_cases hn : spacing = 0
  · have rz := uniswapV3Pool_block_21285_fallthrough (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [hs, hn]; rfl) rd
    exact Or.inl ⟨uniswapV3Pool_block_21299 (immWords := wordsOf (immStore v)) rz, hn⟩
  · have hsn : EVM.wordOfInt spacing ≠ (UInt256.ofNat 0) := by
      intro he
      exact hn ((wordOfInt_zero_iff_signed spacing (by omega) (by omega)).mp he)
    have rn := uniswapV3Pool_block_21285_taken (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [hs]; exact hsn)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) rd
    have rp := uniswapV3Pool_block_21300 (immWords := wordsOf (immStore v))
      (by change R.length + 6 + 0 ≤ 1024; omega) rn
    have rm := RD.smod rp
      (by immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore v),
        (⟨21301⟩ : UInt256), UInt8.ofNat 7, .SMOD, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
    have hm : UInt256.smod (UInt256.signextend (UInt256.ofNat 2) (EVM.wordOfInt tick))
        (UInt256.signextend (UInt256.ofNat 2) spacingRaw) =
        EVM.wordOfInt (tick.tmod spacing) := by
      rw [ht, hs]
      exact wordOfInt_smod tick spacing (by omega) (by omega) (by omega) (by omega) hn
    rw [hm] at rm
    have hb : -(2 ^ 23 : Int) < tick.tmod spacing ∧ tick.tmod spacing < 2 ^ 23 := by
      have hnabs : 0 < spacing.natAbs := by omega
      have hmabs := Nat.mod_lt tick.natAbs hnabs
      have habs := Int.natAbs_tmod tick spacing
      omega
    have hc : UInt256.signextend (UInt256.ofNat 2) (EVM.wordOfInt (tick.tmod spacing)) =
        EVM.wordOfInt (tick.tmod spacing) := by
      rw [signextend_wordOfInt ⟨24, by decide⟩ _ _ (by decide) (by decide),
        normalizeSint_eq_self ⟨24, by decide⟩ _ (by change -(2 ^ 23 : Int) ≤ _; omega) hb.2]
    by_cases hr : tick.tmod spacing = 0
    · have rg := uniswapV3Pool_block_21302_taken (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [hc, hr]; decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) rm
      have rc := uniswapV3Pool_block_21314_taken (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [hs]; exact hsn)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) rg
      have rq := uniswapV3Pool_block_21335 (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) rc
      have hq : UInt256.sdiv (UInt256.signextend (UInt256.ofNat 2) (EVM.wordOfInt tick))
          (UInt256.signextend (UInt256.ofNat 2) spacingRaw) =
          EVM.wordOfInt (tick.tdiv spacing) := by
        rw [ht, hs]
        exact wordOfInt_sdiv tick spacing (by omega) (by omega) (by omega) (by omega)
      simp only [uniswapV3Pool_block_21335_stack, hq] at rq
      obtain ⟨k', C', rout⟩ := bitmapPositionX (v := v) (tick.tdiv spacing) rq
        (by rw [uniswapV3PoolPatchedValidJumps v]; native_decide) (by evm_ov)
      exact Or.inr (Or.inr ⟨hn, hr, k', C', rout⟩)
    · have hrn : EVM.wordOfInt (tick.tmod spacing) ≠ (⟨0⟩ : UInt256) := by
        intro he
        exact hr ((wordOfInt_zero_iff_signed _ (by omega) (by omega)).mp he)
      have rb := uniswapV3Pool_block_21302_fallthrough (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [hc]; exact isZero_eq_zero_of_ne hrn) rm
      exact Or.inr (Or.inl ⟨uniswapV3Pool_block_21310 (immWords := wordsOf (immStore v))
        (by change R.length + 4 + 2 ≤ 1024; omega) rb, hn, hr⟩)


theorem bitmapFlipBeforeStoreX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw base ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (tick spacing : Int)
    (rd : RD (deployedRuntime v) ee g s0 ⟨21285⟩
      (EVM.wordOfInt spacing :: EVM.wordOfInt tick :: base :: ret :: R) mem aw rdata σ k C)
    (htlo : -(2 ^ 23 : Int) ≤ tick) (hthi : tick < 2 ^ 23)
    (hslo : -(2 ^ 23 : Int) ≤ spacing) (hshi : spacing < 2 ^ 23)
    (hov : R.length + 11 ≤ 1024) :
    (RDinvalid (deployedRuntime v) g s0 ∧ spacing = 0) ∨
    (RDrev (deployedRuntime v) g s0 ∧ spacing ≠ 0 ∧ tick.tmod spacing ≠ 0) ∨
    (spacing ≠ 0 ∧ tick.tmod spacing = 0 ∧ ∃ k' C',
      RD (deployedRuntime v) ee g s0 ⟨21341⟩
        (bitmapPositionBitRaw (tick.tdiv spacing) :: EVM.wordOfInt (bitmapWordPos (tick.tdiv spacing)) ::
          ⟨0⟩ :: ⟨0⟩ :: EVM.wordOfInt spacing :: EVM.wordOfInt tick :: base :: ret :: R)
        mem aw rdata σ k' C') := by
  apply bitmapFlipBeforeStoreRawX (v := v) tick spacing rd htlo hthi hslo hshi ?_ hov
  rw [signextend_wordOfInt ⟨24, by decide⟩ _ spacing (by decide) (by decide),
    normalizeSint_eq_self ⟨24, by decide⟩ _ hslo hshi]

end Benchmarks.UniswapV3.Pool
