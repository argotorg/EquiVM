import Benchmarks.UniswapV4PoolManager.PoolModifyFinishPaidTrace
import Benchmarks.UniswapV4PoolManager.PoolModifyClearsPaidTrace
import Benchmarks.UniswapV4PoolManager.PoolModifyAccountingMemory
import Benchmarks.UniswapV4PoolManager.PoolModifyAccounting

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem poolModifyAfterFeesPaidTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State} {σ₀ : AccountMap}
    {mem rdata : ByteArray} {aw id fees ptr x1 x2 x4 x5 x9 extra : UInt256} {p : PoolModifyParams}
    {fl fu : Bool} {k C : Nat} {R : List UInt256} (f : Frame)
    (v : PoolManagerImmutables) (hstack : R.length+34 ≤ 1024) (hI : evm.executionEnv = I) (hσ : evm.σ₀ = σ₀)
    (hl : int24Canonical p.lower) (hu : int24Canonical p.upper) (ht : poolTicksValid p.lower p.upper)
    (hd : signedFits ⟨128, by decide⟩ p.delta)
    (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id) (hmem : 160 ≤ mem.size)
    (hptr : 64 ≤ ptr.toNat) (hspan : ptr.toNat+96 ≤ mem.size) (hfit : ptr.toNat+128 < UInt256.size)
    (hfl : memLoad ptr mem = UInt256.fromBool fl)
    (hfu : memLoad (ptr+UInt256.ofNat 64) mem = UInt256.fromBool fu)
    (h5 : 5 ≤ aw.toNat) (hactive : ptr.toNat+128 ≤ aw.toNat*32) (hpaid : Cₘ aw ≤ C)
    (h : RD (deployedRuntime v) I g s0 (if p.delta < 0 then ⟨6620⟩ else ⟨6036⟩)
      (poolModifyFeesOutputStack fees ptr ⟨0⟩ x1 x2 x4 x5 x9 p (extra :: R)) mem aw rdata evm.accountMap k C) :
    functionResultTrace (deployedRuntime v) g s0
      (poolModifyReturnPaidTrace v I g s0 σ₀ (poolModifyClearsMemory mem id p fl fu) rdata x1 x2 x4 x5 x9 extra R)
      (poolModifyAfterFeesResult f evm id p fl fu fees) := by
  have hr := poolModifyClearsPaidTrace f v (by omega) hI hl hu hm hmem hptr hspan hfit hfl hfu h5 hactive hpaid h
  apply functionResultTrace_continueBlock hr
  intro f1 post _ ht1
  obtain ⟨hIpost, hσpost, junk, k1, C1, hpaid1, rd1⟩ := ht1
  have hm1 := (poolModifyClearsMemory_loadWord mem id p fl fu (UInt256.ofNat 128) (by decide) hmem).trans hm
  exact poolModifyFinishPaidTrace f1 v hstack hIpost (hσpost.trans hσ) hm1 hl hu ht hd h5 hpaid1 rd1

end Benchmarks.UniswapV4PoolManager
