import Benchmarks.UniswapV4PoolManager.PoolModifyFinishTrace
import Benchmarks.UniswapV4PoolManager.PoolModifyAmountsPaidTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolModifyReturnPaidTrace (v : PoolManagerImmutables) (I : ExecutionEnv) (g : Sat256) (s0 : State)
    (σ₀ : AccountMap) (mem rdata : ByteArray) (x1 x2 x4 x5 x9 extra : UInt256)
    (R : List UInt256) (post : State) (values : Option (List Value)) : Prop :=
  post.executionEnv = I ∧ post.σ₀ = σ₀ ∧ ∃ principal fees,
    values = some [.int (EVM.signed principal), .int (EVM.signed fees)] ∧ ∃ j0 j1 j2 aw k C, Cₘ aw ≤ C ∧
      RD (deployedRuntime v) I g s0 ⟨6046⟩
        (j0 :: j1 :: j2 :: principal :: poolModifyAmountRest fees x1 x2 x4 x5 x9 extra R)
        mem aw rdata post.accountMap k C

theorem poolModifyFinishPaidTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State} {σ₀ : AccountMap}
    {mem rdata : ByteArray} {aw junk id fees x1 x2 x4 x5 x9 extra : UInt256} {p : PoolModifyParams}
    {k C : Nat} {R : List UInt256} (f : Frame)
    (v : PoolManagerImmutables) (hstack : R.length+34 ≤ 1024) (hI : evm.executionEnv = I) (hσ : evm.σ₀ = σ₀)
    (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id)
    (hl : int24Canonical p.lower) (hu : int24Canonical p.upper) (ht : poolTicksValid p.lower p.upper)
    (hd : signedFits ⟨128, by decide⟩ p.delta)
    (h5 : 5 ≤ aw.toNat) (hpaid : Cₘ aw ≤ C)
    (h : RD (deployedRuntime v) I g s0 ⟨6036⟩
      (junk :: p.lower :: p.upper :: EVM.wordOfInt p.delta :: ⟨0⟩ :: poolModifyAmountRest fees x1 x2 x4 x5 x9 extra R)
      mem aw rdata evm.accountMap k C) :
    functionResultTrace (deployedRuntime v) g s0
      (poolModifyReturnPaidTrace v I g s0 σ₀ mem rdata x1 x2 x4 x5 x9 extra R)
      (poolModifyFinishResult f evm id p fees) := by
  have hr := poolModifyAmountsPaidTrace f v hstack hI hm hl hu ht hd h5 hpaid h
  apply functionResultTrace_continueBlock hr
  intro f1 post _ ht1
  obtain ⟨hIpost, hσpost, j0, j1, j2, k1, C1, hpaid1, rd1⟩ := ht1
  exact ⟨hIpost, hσpost.trans hσ, poolModifyAmountsDeltaWord evm id p, fees, rfl,
    j0, j1, j2, aw, k1, C1, hpaid1, rd1⟩

end Benchmarks.UniswapV4PoolManager
