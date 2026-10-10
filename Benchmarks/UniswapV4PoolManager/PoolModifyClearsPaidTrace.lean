import Benchmarks.UniswapV4PoolManager.PoolModifyClearActiveWords
import Benchmarks.UniswapV4PoolManager.ResultTraceCostExists

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem poolModifyClearsPaidTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id fees ptr x0 x1 x2 x4 x5 x9 extra : UInt256} {p : PoolModifyParams}
    {fl fu : Bool} {k C : Nat} {R : List UInt256} (f : Frame)
    (v : PoolManagerImmutables) (hstack : R.length+24 ≤ 1024) (hI : evm.executionEnv = I)
    (hl : int24Canonical p.lower) (hu : int24Canonical p.upper)
    (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id) (hmem : 160 ≤ mem.size)
    (hptr : 64 ≤ ptr.toNat) (hspan : ptr.toNat+96 ≤ mem.size) (hfit : ptr.toNat+128 < UInt256.size)
    (hfl : memLoad ptr mem = UInt256.fromBool fl)
    (hfu : memLoad (ptr+UInt256.ofNat 64) mem = UInt256.fromBool fu)
    (h5 : 5 ≤ aw.toNat) (hactive : ptr.toNat+128 ≤ aw.toNat*32) (hpaid : Cₘ aw ≤ C)
    (h : RD (deployedRuntime v) I g s0 (if p.delta < 0 then ⟨6620⟩ else ⟨6036⟩)
      (poolModifyFeesOutputStack fees ptr x0 x1 x2 x4 x5 x9 p (extra :: R)) mem aw rdata evm.accountMap k C) :
    blockResultTrace (deployedRuntime v) g s0
      (fun _ post => post.executionEnv = I ∧ post.σ₀ = evm.σ₀ ∧ ∃ junk kr Cr, Cₘ aw ≤ Cr ∧
        RD (deployedRuntime v) I g s0 ⟨6036⟩
          (junk :: (poolModifyFeesOutputStack fees ptr x0 x1 x2 x4 x5 x9 p (extra :: R)).tail)
          (poolModifyClearsMemory mem id p fl fu) aw rdata post.accountMap kr Cr)
      (fun _ _ => False) (poolModifyClearsResult f evm id p fl fu) := by
  have he := poolModifyClearsActiveWords_eq_self p.delta fl fu h5 hfit hactive
  have hcost := blockResultTrace_retainCost_exists (α := UInt256)
    (facts := fun _ post _ => post.executionEnv = I ∧ post.σ₀ = evm.σ₀)
    (entry := ⟨if p.delta < 0 then ⟨6620⟩ else ⟨6036⟩,
      poolModifyFeesOutputStack fees ptr x0 x1 x2 x4 x5 x9 p (extra :: R), mem, aw, rdata, evm.accountMap⟩)
    (next := fun _ post junk => ⟨⟨6036⟩,
      junk :: (poolModifyFeesOutputStack fees ptr x0 x1 x2 x4 x5 x9 p (extra :: R)).tail,
      poolModifyClearsMemory mem id p fl fu, aw, rdata, post.accountMap⟩)
    (fun budget start ki Ci hin => by
      have hr := poolModifyClearsExactTrace f v hstack hI hl hu hm hmem hptr hspan hfit hfl hfu hin
      rw [he] at hr
      apply blockResultTrace_mono hr
      intro f' post _ ht'
      obtain ⟨hIpost, hσpost, junk, kr, Cr, rd⟩ := ht'
      exact ⟨junk, kr, Cr, ⟨hIpost, hσpost⟩, rd⟩) h
  apply blockResultTrace_mono hcost
  intro f' post _ ht'
  obtain ⟨junk, kr, Cr, ⟨hIpost, hσpost⟩, hle, rd⟩ := ht'
  exact ⟨hIpost, hσpost, junk, kr, Cr, hpaid.trans hle, rd⟩

end Benchmarks.UniswapV4PoolManager
