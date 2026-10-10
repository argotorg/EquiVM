import Benchmarks.UniswapV4PoolManager.PoolModifyRegionAmountTrace
import Benchmarks.UniswapV4PoolManager.PoolModifyLiquidityTrace
import Benchmarks.UniswapV4PoolManager.PoolModifyAmountFrames

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem poolModifyInsideExactTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id sqrtPrice : UInt256} {p : PoolModifyParams}
    {k C : Nat} {R : List UInt256} (f : Frame)
    (v : PoolManagerImmutables) (hstack : R.length+23 ≤ 1024) (hI : evm.executionEnv = I)
    (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id)
    (hl : int24Canonical p.lower) (hu : int24Canonical p.upper) (ht : poolTicksValid p.lower p.upper)
    (hp : sqrtPrice.toNat < 2^160) (hd : signedFits ⟨128, by decide⟩ p.delta)
    (h : RD (deployedRuntime v) I g s0 ⟨6410⟩
      (p.upper :: p.lower :: sqrtPrice :: EVM.wordOfInt p.delta :: R) mem aw rdata evm.accountMap k C) :
    blockResultTrace (deployedRuntime v) g s0 (fun _ post =>
      post.executionEnv = I ∧ post.σ₀ = evm.σ₀ ∧ ∃ k' C',
        RD (deployedRuntime v) I g s0 ⟨6390⟩ (poolModifyInsideDeltaWord p sqrtPrice :: R)
          mem (M aw (UInt256.ofNat 128) ⟨32⟩) rdata post.accountMap k' C') (fun _ _ => False)
      (poolModifyInsideResult f evm id p sqrtPrice) := by
  have hfirst := poolModifyRegionAmount0Trace f v hstack hu ht hp hd h
  apply blockResultTrace_continueBlock hfirst
  intro f1 mid1 _ ht1
  obtain ⟨rfl, k1, C1, rd1⟩ := ht1
  have hsecond := poolModifyRegionAmount1Trace f1 v (by omega) hl ht hp hd rd1
  apply blockResultTrace_continueBlock hsecond
  intro f2 mid2 _ ht2
  obtain ⟨rfl, k2, C2, rd2⟩ := ht2
  exact poolModifyLiquidityExactTrace (poolModifyInsidePackFrame f2 p sqrtPrice) v (by omega) hI hm hd rd2

theorem poolModifyInsideTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id sqrtPrice : UInt256} {p : PoolModifyParams}
    {k C : Nat} {R : List UInt256} (f : Frame)
    (v : PoolManagerImmutables) (hstack : R.length+23 ≤ 1024) (hI : evm.executionEnv = I)
    (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id)
    (hl : int24Canonical p.lower) (hu : int24Canonical p.upper) (ht : poolTicksValid p.lower p.upper)
    (hp : sqrtPrice.toNat < 2^160) (hd : signedFits ⟨128, by decide⟩ p.delta)
    (h : RD (deployedRuntime v) I g s0 ⟨6410⟩
      (p.upper :: p.lower :: sqrtPrice :: EVM.wordOfInt p.delta :: R) mem aw rdata evm.accountMap k C) :
    blockResultTrace (deployedRuntime v) g s0 (fun _ post =>
      post.executionEnv = I ∧ post.σ₀ = evm.σ₀ ∧ ∃ aw' k' C',
        RD (deployedRuntime v) I g s0 ⟨6390⟩ (poolModifyInsideDeltaWord p sqrtPrice :: R)
          mem aw' rdata post.accountMap k' C') (fun _ _ => False)
      (poolModifyInsideResult f evm id p sqrtPrice) := by
  have hr := poolModifyInsideExactTrace f v hstack hI hm hl hu ht hp hd h
  apply blockResultTrace_mono hr
  intro f' post _ ht'
  exact ⟨ht'.1, ht'.2.1, _, ht'.2.2⟩

end Benchmarks.UniswapV4PoolManager
