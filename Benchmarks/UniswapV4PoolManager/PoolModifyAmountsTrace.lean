import Benchmarks.UniswapV4PoolManager.PoolModifyRegionTrace
import Benchmarks.UniswapV4PoolManager.MemoryGas

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolModifyAmountRest (fees x1 x2 x4 x5 x9 extra : UInt256) (R : List UInt256) : List UInt256 :=
  x1 :: x2 :: fees :: x4 :: x5 :: ⟨6222⟩ :: ⟨6240⟩ :: fees :: x9 :: ⟨64⟩ :: extra :: R

def poolModifyAmountsNormal (v : PoolManagerImmutables) (I : ExecutionEnv) (g : Sat256) (s0 evm : State)
    (mem rdata : ByteArray) (id fees x1 x2 x4 x5 x9 extra : UInt256) (p : PoolModifyParams)
    (R : List UInt256) (_ : Frame) (post : State) : Prop :=
  post.executionEnv = I ∧ post.σ₀ = evm.σ₀ ∧ ∃ j0 j1 j2 aw k C,
    RD (deployedRuntime v) I g s0 ⟨6046⟩
      (j0 :: j1 :: j2 :: poolModifyAmountsDeltaWord evm id p :: poolModifyAmountRest fees x1 x2 x4 x5 x9 extra R)
      mem aw rdata post.accountMap k C

def poolModifyAmountsNormalAtAW (v : PoolManagerImmutables) (I : ExecutionEnv) (g : Sat256) (s0 evm : State)
    (mem rdata : ByteArray) (id fees x1 x2 x4 x5 x9 extra : UInt256) (p : PoolModifyParams)
    (R : List UInt256) (aw : UInt256) (_ : Frame) (post : State) : Prop :=
  post.executionEnv = I ∧ post.σ₀ = evm.σ₀ ∧ ∃ j0 j1 j2 k C,
    RD (deployedRuntime v) I g s0 ⟨6046⟩
      (j0 :: j1 :: j2 :: poolModifyAmountsDeltaWord evm id p :: poolModifyAmountRest fees x1 x2 x4 x5 x9 extra R)
      mem aw rdata post.accountMap k C

theorem poolModifyAmountsExactTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw junk id fees x1 x2 x4 x5 x9 extra : UInt256} {p : PoolModifyParams}
    {k C : Nat} {R : List UInt256} (f : Frame)
    (v : PoolManagerImmutables) (hstack : R.length+34 ≤ 1024) (hI : evm.executionEnv = I)
    (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id)
    (hl : int24Canonical p.lower) (hu : int24Canonical p.upper) (ht : poolTicksValid p.lower p.upper)
    (hd : signedFits ⟨128, by decide⟩ p.delta)
    (h : RD (deployedRuntime v) I g s0 ⟨6036⟩
      (junk :: p.lower :: p.upper :: EVM.wordOfInt p.delta :: ⟨0⟩ :: poolModifyAmountRest fees x1 x2 x4 x5 x9 extra R)
      mem aw rdata evm.accountMap k C) :
    blockResultTrace (deployedRuntime v) g s0
      (poolModifyAmountsNormalAtAW v I g s0 evm mem rdata id fees x1 x2 x4 x5 x9 extra p R (if p.delta ≠ 0 then M aw (UInt256.ofNat 128) ⟨32⟩ else aw))
      (fun _ _ => False) (poolModifyAmountsResult f evm id p) := by
  obtain ⟨k1, C1, rd1⟩ := poolModifyAmountGuardTrace v
    (by simp only [poolModifyAmountRest, List.length_cons]; omega) hd h
  by_cases hz : p.delta ≠ 0
  · rw [if_pos hz] at rd1
    simp only [poolModifyAmountsResult, if_pos hz]
    obtain ⟨k2, C2, rd2⟩ := poolModifyPriceExactTrace v
      (by simp only [poolModifyAmountRest, List.length_cons]; omega) hI hm rd1
    have hregion := poolModifyRegionExactTrace (poolModifyPricePreludeFrame f evm id) v
      (by simp only [poolModifyAmountRest, List.length_cons]; omega) hI hm hl hu ht
      (poolSqrtPrice_bound evm id) hd rd2
    simp only [poolModifyRegionActiveWords, memoryWords_idem, ite_self] at hregion
    apply blockResultTrace_mono hregion
    intro f1 post _ ht1
    obtain ⟨hIpost, hσpost, k3, C3, rd3⟩ := ht1
    have rd4 := poolManagerBlocks.poolManager_block_6390 (by omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd3
    unfold poolModifyAmountsNormalAtAW
    rw [poolModifyAmountsDeltaWord, if_pos hz]
    exact ⟨hIpost, hσpost, extra, extra, extra, _, _, rd4⟩
  · rw [if_neg hz] at rd1
    simp only [poolModifyAmountsResult, if_neg hz]
    dsimp only [blockResultTrace]
    unfold poolModifyAmountsNormalAtAW
    rw [poolModifyAmountsDeltaWord, if_neg hz]
    exact ⟨hI, rfl, p.lower, p.upper, EVM.wordOfInt p.delta, k1, C1, rd1⟩

theorem poolModifyAmountsTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw junk id fees x1 x2 x4 x5 x9 extra : UInt256} {p : PoolModifyParams}
    {k C : Nat} {R : List UInt256} (f : Frame)
    (v : PoolManagerImmutables) (hstack : R.length+34 ≤ 1024) (hI : evm.executionEnv = I)
    (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id)
    (hl : int24Canonical p.lower) (hu : int24Canonical p.upper) (ht : poolTicksValid p.lower p.upper)
    (hd : signedFits ⟨128, by decide⟩ p.delta)
    (h : RD (deployedRuntime v) I g s0 ⟨6036⟩
      (junk :: p.lower :: p.upper :: EVM.wordOfInt p.delta :: ⟨0⟩ :: poolModifyAmountRest fees x1 x2 x4 x5 x9 extra R)
      mem aw rdata evm.accountMap k C) :
    blockResultTrace (deployedRuntime v) g s0
      (poolModifyAmountsNormal v I g s0 evm mem rdata id fees x1 x2 x4 x5 x9 extra p R)
      (fun _ _ => False) (poolModifyAmountsResult f evm id p) := by
  have hr := poolModifyAmountsExactTrace f v hstack hI hm hl hu ht hd h
  apply blockResultTrace_mono hr
  intro f' post _ ht'
  obtain ⟨hIpost, hσpost, j0, j1, j2, k', C', rd⟩ := ht'
  exact ⟨hIpost, hσpost, j0, j1, j2, _, k', C', rd⟩

end Benchmarks.UniswapV4PoolManager
