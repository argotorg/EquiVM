import Benchmarks.UniswapV4PoolManager.PoolModifyBitmapActiveWords
import Benchmarks.UniswapV4PoolManager.BlockTraceCost

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem poolModifyBitmapsPaidTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id ptr x0 x1 x2 x4 x5 x9 params : UInt256} {p : PoolModifyParams}
    {fl fu : Bool} {k C : Nat} {R : List UInt256} (f : Frame)
    (v : PoolManagerImmutables) (hstack : R.length+20 ≤ 1024) (hI : evm.executionEnv = I)
    (hc : int24Canonical p.spacing) (hl : int24Canonical p.lower) (hu : int24Canonical p.upper)
    (ht : poolTicksValid p.lower p.upper)
    (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id) (hmem : 160 ≤ mem.size)
    (hs : memLoad (params+UInt256.ofNat 128) mem = p.spacing)
    (hp : 64 ≤ (params+UInt256.ofNat 128).toNat)
    (hps : (params+UInt256.ofNat 128).toNat+32 ≤ mem.size)
    (hptr : 64 ≤ ptr.toNat) (hspan : ptr.toNat+96 ≤ mem.size) (hfit : ptr.toNat+128 < UInt256.size)
    (hfl : memLoad ptr mem = UInt256.fromBool fl)
    (hfu : memLoad (ptr+UInt256.ofNat 64) mem = UInt256.fromBool fu)
    (h5 : 5 ≤ aw.toNat) (hactive : ptr.toNat+128 ≤ aw.toNat*32)
    (hpa : (params+UInt256.ofNat 128).toNat+32 ≤ aw.toNat*32) (hpaid : Cₘ aw ≤ C)
    (h : RD (deployedRuntime v) I g s0 ⟨7256⟩
      (x0 :: x1 :: x2 :: ptr :: x4 :: x5 :: p.upper :: EVM.wordOfInt p.delta :: p.lower :: x9 :: params :: R)
      mem aw rdata evm.accountMap k C) :
    blockResultTrace (deployedRuntime v) g s0
      (fun _ post => post.executionEnv = I ∧ post.σ₀ = evm.σ₀ ∧ ∃ kr Cr, Cₘ aw ≤ Cr ∧
        RD (deployedRuntime v) I g s0 ⟨5722⟩
          (x0 :: x1 :: x2 :: ptr :: x4 :: x5 :: p.upper :: EVM.wordOfInt p.delta :: p.lower :: x9 :: params :: R)
          (poolModifyBitmapsMemory mem id p fl fu) aw rdata post.accountMap kr Cr)
      (fun _ _ => False) (poolModifyBitmapsResult f evm id p fl fu) := by
  have he := poolModifyBitmapsActiveWords_eq_self fl fu h5 hfit hactive hpa
  have hcost := blockResultTrace_retainCost
    (facts := fun _ post => post.executionEnv = I ∧ post.σ₀ = evm.σ₀)
    (next := fun _ post => ⟨⟨5722⟩,
      x0 :: x1 :: x2 :: ptr :: x4 :: x5 :: p.upper :: EVM.wordOfInt p.delta :: p.lower :: x9 :: params :: R,
      poolModifyBitmapsMemory mem id p fl fu, aw, rdata, post.accountMap⟩)
    (entry := ⟨⟨7256⟩,
      x0 :: x1 :: x2 :: ptr :: x4 :: x5 :: p.upper :: EVM.wordOfInt p.delta :: p.lower :: x9 :: params :: R,
      mem, aw, rdata, evm.accountMap⟩)
    (fun budget start ki Ci hin => by
      have hr := poolModifyBitmapsExactTrace f v hstack hI hc hl hu ht hm hmem hs hp hps hptr hspan hfit hfl hfu hin
      rw [he] at hr
      apply blockResultTrace_mono hr
      intro f' post _ ht'
      exact ⟨⟨ht'.1, ht'.2.1⟩, ht'.2.2⟩) h
  apply blockResultTrace_mono hcost
  intro f' post _ ht'
  obtain ⟨⟨hIpost, hσpost⟩, kr, Cr, hle, rd⟩ := ht'
  exact ⟨hIpost, hσpost, kr, Cr, hpaid.trans hle, rd⟩

end Benchmarks.UniswapV4PoolManager
