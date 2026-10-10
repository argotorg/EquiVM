import Benchmarks.UniswapV4PoolManager.PoolModifyLimitsTrace
import Benchmarks.UniswapV4PoolManager.BlockTraceCost
import Benchmarks.UniswapV4PoolManager.MemoryGas

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem poolModifyLimitsActiveWords_eq_self {aw params ptr : UInt256} (delta : Int)
    (hf : ptr.toNat+128 < UInt256.size) (hc : ptr.toNat+128 ≤ aw.toNat*32)
    (hp : (params+UInt256.ofNat 128).toNat+32 ≤ aw.toNat*32) :
    poolModifyLimitsActiveWords aw params ptr delta = aw := by
  have h32 := uadd_word_ofNat_toNat ptr 32 (by omega)
  have h96 := uadd_word_ofNat_toNat ptr 96 (by omega)
  have hparams : M aw (params+UInt256.ofNat 128) ⟨32⟩ = aw := memoryWords_eq_self hp
  have hp32 : M aw (ptr+UInt256.ofNat 32) ⟨32⟩ = aw :=
    memoryWords_eq_self (by change (ptr+UInt256.ofNat 32).toNat+32 ≤ _*32; rw [h32]; omega)
  have hp96 : M aw (ptr+UInt256.ofNat 96) ⟨32⟩ = aw :=
    memoryWords_eq_self (by change (ptr+UInt256.ofNat 96).toNat+32 ≤ _*32; rw [h96]; omega)
  simp only [poolModifyLimitsActiveWords, hparams, hp32, hp96, ite_self]

theorem poolModifyLimitsPaidTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw spacing gl gu x0 x1 x2 ptr x4 x5 x6 x7 x8 x9 params : UInt256}
    {delta : Int} {k C : Nat} {R : List UInt256} (f : Frame)
    (v : PoolManagerImmutables) (hstack : R.length+18 ≤ 1024) (hc : int24Canonical spacing)
    (hs : memLoad (params+UInt256.ofNat 128) mem = spacing)
    (hl : memLoad (ptr+UInt256.ofNat 32) mem = gl)
    (hu : memLoad (ptr+UInt256.ofNat 96) mem = gu)
    (hgl : gl.toNat < 2^128) (hgu : gu.toNat < 2^128)
    (hfit : ptr.toNat+128 < UInt256.size) (hactive : ptr.toNat+128 ≤ aw.toNat*32)
    (hpa : (params+UInt256.ofNat 128).toNat+32 ≤ aw.toNat*32) (hpaid : Cₘ aw ≤ C)
    (h : RD (deployedRuntime v) I g s0 (if 0 ≤ delta then ⟨7329⟩ else ⟨7256⟩)
      (x0 :: x1 :: x2 :: ptr :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: params :: R)
      mem aw rdata evm.accountMap k C) :
    blockResultTrace (deployedRuntime v) g s0 (fun _ post => post = evm ∧ ∃ kr Cr, Cₘ aw ≤ Cr ∧
      RD (deployedRuntime v) I g s0 ⟨7256⟩
        (x0 :: x1 :: x2 :: ptr :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: params :: R)
        mem aw rdata post.accountMap kr Cr) (fun _ _ => False)
      (poolModifyLimitsResult f evm delta (EVM.signed spacing) gl gu) := by
  have he := poolModifyLimitsActiveWords_eq_self delta hfit hactive hpa
  have hcost := blockResultTrace_retainCost
    (facts := fun _ post => post = evm)
    (next := fun _ post => ⟨⟨7256⟩,
      x0 :: x1 :: x2 :: ptr :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: params :: R,
      mem, aw, rdata, post.accountMap⟩)
    (entry := ⟨if 0 ≤ delta then ⟨7329⟩ else ⟨7256⟩,
      x0 :: x1 :: x2 :: ptr :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: params :: R,
      mem, aw, rdata, evm.accountMap⟩)
    (fun budget start ki Ci hin => by
      have hr := poolModifyLimitsExactTrace f v hstack hc hs hl hu hgl hgu hin
      rw [he] at hr
      exact hr) h
  apply blockResultTrace_mono hcost
  intro f' post _ ht
  obtain ⟨hpost, kr, Cr, hle, rd⟩ := ht
  exact ⟨hpost, kr, Cr, hpaid.trans hle, rd⟩

end Benchmarks.UniswapV4PoolManager
