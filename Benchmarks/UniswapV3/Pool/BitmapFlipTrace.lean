import Benchmarks.UniswapV3.Pool.BitmapFlipFinishTrace
import Benchmarks.UniswapV3.Pool.BitmapFlipStaticTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

theorem bitmapFlipRawX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret spacingRaw : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (tick spacing : Int)
    (rd : RD (deployedRuntime v) ee g s0 ⟨21285⟩
      (spacingRaw :: EVM.wordOfInt tick :: ⟨6⟩ :: ret :: R) mem aw rdata σ k C)
    (htlo : -(2 ^ 23 : Int) ≤ tick) (hthi : tick < 2 ^ 23)
    (hslo : -(2 ^ 23 : Int) ≤ spacing) (hshi : spacing < 2 ^ 23)
    (hs : UInt256.signextend (UInt256.ofNat 2) spacingRaw = EVM.wordOfInt spacing)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (hov : R.length + 11 ≤ 1024) :
    (RDinvalid (deployedRuntime v) g s0 ∧ spacing = 0) ∨
    (RDrev (deployedRuntime v) g s0 ∧ spacing ≠ 0 ∧ tick.tmod spacing ≠ 0) ∨
    (spacing ≠ 0 ∧ tick.tmod spacing = 0 ∧
      ((RDstatic (deployedRuntime v) g s0 ∧ ee.perm = false) ∨
       (ee.perm = true ∧ ∃ k' C',
         RD (deployedRuntime v) ee g s0 ret R (bitmapFlipMemory mem tick spacing)
           (M (M (M aw ⟨0⟩ ⟨32⟩) ⟨32⟩ ⟨32⟩) ⟨0⟩ ⟨64⟩) rdata
           (bitmapFlippedMap σ ee (bitmapWordPos (tick.tdiv spacing)) (bitmapFlipMask tick spacing))
           k' C'))) := by
  rcases bitmapFlipBeforeStoreRawX (v := v) tick spacing rd htlo hthi hslo hshi hs hov with
    hz | hb | ⟨hn, hr, k', C', rout⟩
  · exact Or.inl hz
  · exact Or.inr (Or.inl hb)
  · refine Or.inr (Or.inr ⟨hn, hr, ?_⟩)
    cases hp : ee.perm
    · exact Or.inl ⟨bitmapFlipStoreStaticX (v := v) rout hp hov, rfl⟩
    · exact Or.inr ⟨rfl, bitmapFlipFinishRawX (v := v) tick spacing rout hp hret hov⟩


theorem bitmapFlipX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (tick spacing : Int)
    (rd : RD (deployedRuntime v) ee g s0 ⟨21285⟩
      (EVM.wordOfInt spacing :: EVM.wordOfInt tick :: ⟨6⟩ :: ret :: R) mem aw rdata σ k C)
    (htlo : -(2 ^ 23 : Int) ≤ tick) (hthi : tick < 2 ^ 23)
    (hslo : -(2 ^ 23 : Int) ≤ spacing) (hshi : spacing < 2 ^ 23)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (hov : R.length + 11 ≤ 1024) :
    (RDinvalid (deployedRuntime v) g s0 ∧ spacing = 0) ∨
    (RDrev (deployedRuntime v) g s0 ∧ spacing ≠ 0 ∧ tick.tmod spacing ≠ 0) ∨
    (spacing ≠ 0 ∧ tick.tmod spacing = 0 ∧
      ((RDstatic (deployedRuntime v) g s0 ∧ ee.perm = false) ∨
       (ee.perm = true ∧ ∃ k' C' aw',
         RD (deployedRuntime v) ee g s0 ret R (bitmapFlipMemory mem tick spacing) aw' rdata
           (bitmapFlippedMap σ ee (bitmapWordPos (tick.tdiv spacing)) (bitmapFlipMask tick spacing))
           k' C'))) := by
  have hs : UInt256.signextend (UInt256.ofNat 2) (EVM.wordOfInt spacing) =
      EVM.wordOfInt spacing := by
    rw [signextend_wordOfInt ⟨24, by decide⟩ _ spacing (by decide) (by decide),
      normalizeSint_eq_self ⟨24, by decide⟩ _ hslo hshi]
  rcases bitmapFlipRawX (v := v) tick spacing rd htlo hthi hslo hshi hs hret hov with
    hz | hb | ⟨hn, hr, h⟩
  · exact Or.inl hz
  · exact Or.inr (Or.inl hb)
  · refine Or.inr (Or.inr ⟨hn, hr, ?_⟩)
    rcases h with hb | ⟨hp, k', C', r'⟩
    · exact Or.inl hb
    · exact Or.inr ⟨hp, k', C', _, r'⟩

end Benchmarks.UniswapV3.Pool
