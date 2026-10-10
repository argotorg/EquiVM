import Benchmarks.UniswapV4PoolManager.PoolModifyTickActiveWords
import Benchmarks.UniswapV4PoolManager.BlockTraceCost

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolModifyTwoTicksFacts (I : ExecutionEnv) (evm : State) (id : UInt256)
    (p : PoolModifyParams) (_ : Frame) (post : State) : Prop :=
  post.executionEnv = I ∧ post.σ₀ = evm.σ₀ ∧
  (EVM.wordOfInt (tickGrossAfterInt (poolModifyLowerPacked evm id p) p.delta)).toNat < 2^128 ∧
  (EVM.wordOfInt (tickGrossAfterInt (poolModifyUpperPacked evm id p) p.delta)).toNat < 2^128

def poolModifyTwoTicksCursor (mem rdata : ByteArray) (aw id ptr x0 x1 x2 x4 x5 : UInt256)
    (p : PoolModifyParams) (evm : State) (R : List UInt256) (_ : Frame) (post : State) : Cursor :=
  ⟨if 0 ≤ p.delta then ⟨7329⟩ else ⟨7256⟩,
   x0 :: x1 :: x2 :: ptr :: x4 :: x5 :: p.upper :: EVM.wordOfInt p.delta :: p.lower :: R,
   poolModifyTwoTicksMemory mem ptr id p evm, aw, rdata, post.accountMap⟩

/-- Updating both ticks keeps paid memory when their result record is already active. -/
theorem poolModifyTwoTicksPaidTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id ptr x0 x1 x2 x4 x5 : UInt256} {p : PoolModifyParams}
    {k C : Nat} {R : List UInt256} (f : Frame)
    (v : PoolManagerImmutables) (hstack : R.length+21 ≤ 1024) (hI : evm.executionEnv = I)
    (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id) (hmem : 160 ≤ mem.size)
    (hptr : 160 ≤ ptr.toNat) (hfit : ptr.toNat+128 < UInt256.size)
    (hl : int24Canonical p.lower) (hu : int24Canonical p.upper)
    (hd : signedFits ⟨128, by decide⟩ p.delta)
    (hactive : ptr.toNat+128 ≤ aw.toNat*32) (hpaid : Cₘ aw ≤ C)
    (h : RD (deployedRuntime v) I g s0 ⟨6949⟩
      (x0 :: x1 :: x2 :: ptr :: x4 :: x5 :: p.upper :: EVM.wordOfInt p.delta :: p.lower :: R)
      mem aw rdata evm.accountMap k C) :
    blockResultTrace (deployedRuntime v) g s0 (fun f' post =>
      poolModifyTwoTicksFacts I evm id p f' post ∧ ∃ kr Cr, Cₘ aw ≤ Cr ∧
        RDc (deployedRuntime v) I g s0
          (poolModifyTwoTicksCursor mem rdata aw id ptr x0 x1 x2 x4 x5 p evm R f' post) kr Cr)
      (fun _ _ => False) (poolModifyTwoTicksResult f evm id p) := by
  have he := poolModifyTwoTicksActiveWords_eq_self id p evm (by omega) hfit hactive
  have hcost := blockResultTrace_retainCost
    (facts := poolModifyTwoTicksFacts I evm id p)
    (next := poolModifyTwoTicksCursor mem rdata aw id ptr x0 x1 x2 x4 x5 p evm R)
    (entry := ⟨⟨6949⟩,
      x0 :: x1 :: x2 :: ptr :: x4 :: x5 :: p.upper :: EVM.wordOfInt p.delta :: p.lower :: R,
      mem, aw, rdata, evm.accountMap⟩)
    (fun budget start ki Ci hin => by
      have hr := poolModifyTwoTicksExactTrace f v hstack hI hm hmem hptr (by omega) hl hu hd hin
      rw [he] at hr
      apply blockResultTrace_mono hr
      intro f' post _ ht
      exact ⟨⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1⟩, ht.2.2.2.2⟩) h
  apply blockResultTrace_mono hcost
  intro f' post _ ht
  obtain ⟨facts, kr, Cr, hle, rd⟩ := ht
  exact ⟨facts, kr, Cr, hpaid.trans hle, rd⟩

end Benchmarks.UniswapV4PoolManager
