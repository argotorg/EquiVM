import Benchmarks.UniswapV4PoolManager.PoolModifyInsideTrace
import Benchmarks.UniswapV4PoolManager.PoolModifyOutsideTrace
import Benchmarks.UniswapV4PoolManager.PoolModifyAmountEntryTrace
import Benchmarks.UniswapV4PoolManager.PoolModifyAmountResult

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolModifyRegionActiveWords (aw : UInt256) (p : PoolModifyParams) (tick : Int) : UInt256 :=
  if tick < EVM.signed p.lower then aw else if tick < EVM.signed p.upper then M aw (UInt256.ofNat 128) ⟨32⟩ else aw

theorem poolModifyRegionExactTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id tick sqrtPrice : UInt256} {p : PoolModifyParams}
    {k C : Nat} {R : List UInt256} (f : Frame)
    (v : PoolManagerImmutables) (hstack : R.length+23 ≤ 1024) (hI : evm.executionEnv = I)
    (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id)
    (hl : int24Canonical p.lower) (hu : int24Canonical p.upper) (ht : poolTicksValid p.lower p.upper)
    (hp : sqrtPrice.toNat < 2^160) (hd : signedFits ⟨128, by decide⟩ p.delta)
    (h : RD (deployedRuntime v) I g s0
      (if EVM.signed tick < EVM.signed p.lower then ⟨6344⟩ else ⟨6398⟩)
      (tick :: sqrtPrice :: p.lower :: p.upper :: EVM.wordOfInt p.delta :: R)
      mem aw rdata evm.accountMap k C) :
    blockResultTrace (deployedRuntime v) g s0 (fun _ post =>
      post.executionEnv = I ∧ post.σ₀ = evm.σ₀ ∧ ∃ k' C',
        RD (deployedRuntime v) I g s0 ⟨6390⟩ (poolModifyRegionDeltaWord p (EVM.signed tick) sqrtPrice :: R)
          mem (poolModifyRegionActiveWords aw p (EVM.signed tick)) rdata post.accountMap k' C') (fun _ _ => False)
      (poolModifyRegionResult f evm id p (EVM.signed tick) sqrtPrice) := by
  by_cases hb : EVM.signed tick < EVM.signed p.lower
  · rw [if_pos hb] at h
    simp only [poolModifyRegionActiveWords, poolModifyRegionResult, poolModifyRegionDeltaWord, if_pos hb]
    have hr := poolModifyOutsideTrace f false v (by omega) hl hu ht hd h
    apply blockResultTrace_mono hr
    intro f1 post _ ht1
    obtain ⟨rfl, k1, C1, rd1⟩ := ht1
    exact ⟨hI, rfl, k1, C1, rd1⟩
  · rw [if_neg hb] at h
    simp only [poolModifyRegionActiveWords, poolModifyRegionResult, poolModifyRegionDeltaWord, if_neg hb]
    obtain ⟨k1, C1, rd1⟩ := poolModifyUpperRegionTrace v (by simp only [List.length_cons]; omega) h
    by_cases hub : EVM.signed tick < EVM.signed p.upper
    · rw [if_pos hub] at rd1
      simp only [if_pos hub]
      exact poolModifyInsideExactTrace f v hstack hI hm hl hu ht hp hd rd1
    · rw [if_neg hub] at rd1
      simp only [if_neg hub]
      have hr := poolModifyOutsideTrace (tick := tick) f true v (by omega) hl hu ht hd rd1
      apply blockResultTrace_mono hr
      intro f1 post _ ht1
      obtain ⟨rfl, k2, C2, rd2⟩ := ht1
      exact ⟨hI, rfl, k2, C2, rd2⟩

theorem poolModifyRegionTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id tick sqrtPrice : UInt256} {p : PoolModifyParams}
    {k C : Nat} {R : List UInt256} (f : Frame)
    (v : PoolManagerImmutables) (hstack : R.length+23 ≤ 1024) (hI : evm.executionEnv = I)
    (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id)
    (hl : int24Canonical p.lower) (hu : int24Canonical p.upper) (ht : poolTicksValid p.lower p.upper)
    (hp : sqrtPrice.toNat < 2^160) (hd : signedFits ⟨128, by decide⟩ p.delta)
    (h : RD (deployedRuntime v) I g s0
      (if EVM.signed tick < EVM.signed p.lower then ⟨6344⟩ else ⟨6398⟩)
      (tick :: sqrtPrice :: p.lower :: p.upper :: EVM.wordOfInt p.delta :: R)
      mem aw rdata evm.accountMap k C) :
    blockResultTrace (deployedRuntime v) g s0 (fun _ post =>
      post.executionEnv = I ∧ post.σ₀ = evm.σ₀ ∧ ∃ aw' k' C',
        RD (deployedRuntime v) I g s0 ⟨6390⟩ (poolModifyRegionDeltaWord p (EVM.signed tick) sqrtPrice :: R)
          mem aw' rdata post.accountMap k' C') (fun _ _ => False)
      (poolModifyRegionResult f evm id p (EVM.signed tick) sqrtPrice) := by
  have hr := poolModifyRegionExactTrace f v hstack hI hm hl hu ht hp hd h
  apply blockResultTrace_mono hr
  intro f' post _ ht'
  exact ⟨ht'.1, ht'.2.1, _, ht'.2.2⟩

end Benchmarks.UniswapV4PoolManager
