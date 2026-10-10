import Benchmarks.UniswapV4PoolManager.SafeCast128Trace
import Benchmarks.UniswapV4PoolManager.ModifyLiquidityParams
import Benchmarks.UniswapV4PoolManager.PoolKeyView
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_017

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
open poolManagerBlocks
set_option maxRecDepth 5000

/-- The public caller checks the signed delta and allocates the pool parameter record. -/
theorem modifyLiquidityPoolPrepareTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw free keyPtr paramsPtr src len id junk x0 x1 : UInt256}
    {key : PoolKeyWords} {p : ModifyLiquidityWords} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+16 ≤ 1024)
    (hc : int24Canonical key.tickSpacing) (hl : int24Canonical p.lower) (hu : int24Canonical p.upper)
    (hkey : PoolKeyView mem keyPtr key)
    (hparams : MemorySlice mem paramsPtr.toNat (wordBytes (modifyLiquidityWords p)))
    (hpb : paramsPtr.toNat+128 ≤ free.toNat) (hfb : free.toNat+320 ≤ solcMaxU64)
    (hfree : memLoad (UInt256.ofNat 64) mem = free) (hpaid : Cₘ aw ≤ C)
    (h : RD (deployedRuntime v) I g s0 ⟨5511⟩
      (x0 :: x1 :: src :: paramsPtr :: len :: keyPtr :: id :: junk :: R) mem aw rdata σ k C) :
    if signedFits ⟨128, by decide⟩ (EVM.signed p.delta) then
      ∃ aw' k' C', Cₘ aw' ≤ C' ∧ RD (deployedRuntime v) I g s0 ⟨5584⟩
        ((free+UInt256.ofNat 192) :: key.tickSpacing :: p.salt :: id :: paramsPtr :: src :: len ::
          p.upper :: p.delta :: p.lower :: keyPtr :: free :: junk :: R) mem aw' rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have hfit : free.toNat+320 < UInt256.size := by
    change _ ≤ 2^64-1 at hfb
    change _ < 2^256
    omega
  have hload {i : Nat} {w : UInt256} (hi : (modifyLiquidityWords p)[i]? = some w) :
      memLoad (paramsPtr+UInt256.ofNat (32*i)) mem = w := by
    have hib : i < 4 := by
      have hh := (List.getElem?_eq_some_iff.mp hi).1
      simpa only [modifyLiquidityWords, List.length_cons, List.length_nil] using hh
    exact hparams.word_load hi (uadd_word_ofNat_toNat paramsPtr (32*i) (by omega))
  have hlo : memLoad paramsPtr mem = p.lower := by
    have hh := hload (i := 0) rfl
    have hz : paramsPtr+UInt256.ofNat (32*0) = paramsPtr := uint256_add_zero_right paramsPtr
    simpa only [hz] using hh
  have hup := hload (i := 1) rfl
  have hdelta := hload (i := 2) rfl
  have hsalt := hload (i := 3) rfl
  have hspacing := hkey.load (i := 3) rfl
  have rd1 := poolManager_block_5511 (by change R.length+11 ≤ 1024; omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  have hcl : UInt256.signextend (UInt256.ofNat 2) p.lower = p.lower := (signextend24_eq_iff _).mpr hl
  have hcu : UInt256.signextend (UInt256.ofNat 2) p.upper = p.upper := (signextend24_eq_iff _).mpr hu
  have hcs : UInt256.signextend (UInt256.ofNat 2) key.tickSpacing = key.tickSpacing :=
    (signextend24_eq_iff _).mpr hc
  simp only [poolManager_block_5511_stack, hdelta, hup, hlo, hcl, hcu] at rd1
  have hp1 : Cₘ (M (M (M aw paramsPtr ⟨32⟩) (paramsPtr+UInt256.ofNat 32) ⟨32⟩)
      (paramsPtr+UInt256.ofNat 64) ⟨32⟩) ≤ C+(71+memExpansionCost aw paramsPtr ⟨32⟩+
        memExpansionCost (M aw paramsPtr ⟨32⟩) (paramsPtr+UInt256.ofNat 32) ⟨32⟩+
        memExpansionCost (M (M aw paramsPtr ⟨32⟩) (paramsPtr+UInt256.ofNat 32) ⟨32⟩)
          (paramsPtr+UInt256.ofNat 64) ⟨32⟩) := by
    dsimp only [memExpansionCost]
    omega
  have hword := wordOfInt_signed p.delta
  rw [← hword] at rd1
  have hcast := signedToInt128CostTrace v (by change R.length+12 ≤ 1024; omega)
    (signedWord_fits p.delta) (by rw [deployedRuntime_jumps]; jump_dest) rd1
  by_cases hd : signedFits ⟨128, by decide⟩ (EVM.signed p.delta)
  · rw [if_pos hd] at hcast ⊢
    obtain ⟨k2, C2, hcost2, rd2⟩ := hcast
    rw [hword] at rd2
    have h192 := uadd_word_ofNat_toNat free 192 (by omega)
    have hguard : UInt256.lor
        (UInt256.gt (free+UInt256.ofNat 192) (UInt256.ofNat solcMaxU64))
        (UInt256.lt (free+UInt256.ofNat 192) free) = ⟨0⟩ := by
      rw [ugt_zero (by change (free+UInt256.ofNat 192).toNat ≤ solcMaxU64; rw [h192]; omega),
        ult_zero (by rw [h192]; omega)]
      rfl
    have rd3 := poolManager_block_5541_fallthrough (by change R.length+16 ≤ 1024; exact hstack)
      (by rw [hfree]; exact hguard) rd2
    simp only [poolManager_block_5541_fallthrough_stack, hfree, hspacing, hsalt, hcs] at rd3
    refine ⟨_, _, _, ?_, rd3⟩
    dsimp only [memExpansionCost] at hp1 hcost2 ⊢
    omega
  · rw [if_neg hd] at hcast ⊢
    exact hcast

end Benchmarks.UniswapV4PoolManager
