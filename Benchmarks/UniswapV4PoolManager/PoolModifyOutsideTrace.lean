import Benchmarks.UniswapV4PoolManager.PoolModifyOutsidePricesTrace
import Benchmarks.UniswapV4PoolManager.PoolModifyCheckedAmountTrace
import Benchmarks.UniswapV4PoolManager.PoolModifyAmountFrames
import Benchmarks.UniswapV4PoolManager.BalanceDeltaWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem poolModifyOutsidePackTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw word : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (one : Bool) (v : PoolManagerImmutables) (hstack : R.length+2 ≤ 1024)
    (h : RD (deployedRuntime v) I g s0 (poolModifyOutsideCastPC one) (word :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨6390⟩
      (balanceDeltaWord (if one then ⟨0⟩ else word) (if one then word else ⟨0⟩) :: R)
      mem aw rdata σ k' C' := by
  cases one with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, balanceDeltaWord_zero_right]
    exact ⟨_, _, poolManagerBlocks.poolManager_block_6386 hstack h⟩
  | true =>
    simp only [↓reduceIte, balanceDeltaWord_zero_left]
    exact ⟨_, _, poolManagerBlocks.poolManager_block_6597 hstack
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h⟩

theorem poolModifyOutsideTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw tick sqrtPrice : UInt256} {p : PoolModifyParams}
    {k C : Nat} {R : List UInt256} (f : Frame)
    (one : Bool) (v : PoolManagerImmutables) (hstack : R.length+18 ≤ 1024)
    (hl : int24Canonical p.lower) (hu : int24Canonical p.upper) (ht : poolTicksValid p.lower p.upper)
    (hd : signedFits ⟨128, by decide⟩ p.delta)
    (h : RD (deployedRuntime v) I g s0 (poolModifyOutsideStartPC one)
      (poolModifyOutsideInputStack one tick sqrtPrice p R) mem aw rdata evm.accountMap k C) :
    blockResultTrace (deployedRuntime v) g s0 (fun _ post => post = evm ∧ ∃ k' C',
      RD (deployedRuntime v) I g s0 ⟨6390⟩ (poolModifyOutsideDeltaWord one p :: R)
        mem aw rdata post.accountMap k' C') (fun _ _ => False)
      (poolModifyOutsideResult f evm one p) := by
  obtain ⟨k1, C1, rd1⟩ := poolModifyOutsidePricesTrace one v (by omega) hl hu ht hd h
  have hchecked := poolModifyCheckedAmountTrace (poolModifyOutsidePricesFrame f one p)
    (poolModifyOutsideAmountRet one) (poolModifyOutsideCastRet one) one v hstack
    (tickSqrtPrice_lt_160 (poolTicksValid_bounds ht).1) (tickSqrtPrice_lt_160 (poolTicksValid_bounds ht).2)
    hd (by cases one <;> rw [deployedRuntime_jumps] <;> jump_dest) rd1
  apply blockResultTrace_continueBlock hchecked
  intro f1 post _ ht1
  obtain ⟨rfl, k2, C2, rd2⟩ := ht1
  exact ⟨rfl, poolModifyOutsidePackTrace one v (by omega) rd2⟩

end Benchmarks.UniswapV4PoolManager
