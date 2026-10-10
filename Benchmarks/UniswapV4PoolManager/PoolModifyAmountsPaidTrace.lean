import Benchmarks.UniswapV4PoolManager.PoolModifyAmountsTrace
import Benchmarks.UniswapV4PoolManager.ResultTraceCostExists

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem poolModifyAmountsPaidTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw junk id fees x1 x2 x4 x5 x9 extra : UInt256} {p : PoolModifyParams}
    {k C : Nat} {R : List UInt256} (f : Frame)
    (v : PoolManagerImmutables) (hstack : R.length+34 ≤ 1024) (hI : evm.executionEnv = I)
    (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id)
    (hl : int24Canonical p.lower) (hu : int24Canonical p.upper) (ht : poolTicksValid p.lower p.upper)
    (hd : signedFits ⟨128, by decide⟩ p.delta)
    (h5 : 5 ≤ aw.toNat) (hpaid : Cₘ aw ≤ C)
    (h : RD (deployedRuntime v) I g s0 ⟨6036⟩
      (junk :: p.lower :: p.upper :: EVM.wordOfInt p.delta :: ⟨0⟩ :: poolModifyAmountRest fees x1 x2 x4 x5 x9 extra R)
      mem aw rdata evm.accountMap k C) :
    blockResultTrace (deployedRuntime v) g s0
      (fun _ post => post.executionEnv = I ∧ post.σ₀ = evm.σ₀ ∧ ∃ j0 j1 j2 kr Cr, Cₘ aw ≤ Cr ∧
        RD (deployedRuntime v) I g s0 ⟨6046⟩
          (j0 :: j1 :: j2 :: poolModifyAmountsDeltaWord evm id p :: poolModifyAmountRest fees x1 x2 x4 x5 x9 extra R)
          mem aw rdata post.accountMap kr Cr)
      (fun _ _ => False) (poolModifyAmountsResult f evm id p) := by
  have he : M aw (UInt256.ofNat 128) ⟨32⟩ = aw := memoryWords_eq_self (by change 128+32 ≤ _*32; omega)
  have hcost := blockResultTrace_retainCost_exists (α := UInt256 × UInt256 × UInt256)
    (facts := fun _ post _ => post.executionEnv = I ∧ post.σ₀ = evm.σ₀)
    (entry := ⟨⟨6036⟩,
      junk :: p.lower :: p.upper :: EVM.wordOfInt p.delta :: ⟨0⟩ :: poolModifyAmountRest fees x1 x2 x4 x5 x9 extra R,
      mem, aw, rdata, evm.accountMap⟩)
    (next := fun _ post js => ⟨⟨6046⟩,
      js.1 :: js.2.1 :: js.2.2 :: poolModifyAmountsDeltaWord evm id p :: poolModifyAmountRest fees x1 x2 x4 x5 x9 extra R,
      mem, aw, rdata, post.accountMap⟩)
    (fun budget start ki Ci hin => by
      have hr := poolModifyAmountsExactTrace f v hstack hI hm hl hu ht hd hin
      simp only [he, ite_self] at hr
      apply blockResultTrace_mono hr
      intro f' post _ ht'
      obtain ⟨hIpost, hσpost, j0, j1, j2, kr, Cr, rd⟩ := ht'
      exact ⟨⟨j0, j1, j2⟩, kr, Cr, ⟨hIpost, hσpost⟩, rd⟩) h
  apply blockResultTrace_mono hcost
  intro f' post _ ht'
  obtain ⟨⟨j0, j1, j2⟩, kr, Cr, ⟨hIpost, hσpost⟩, hle, rd⟩ := ht'
  exact ⟨hIpost, hσpost, j0, j1, j2, kr, Cr, hpaid.trans hle, rd⟩

end Benchmarks.UniswapV4PoolManager
