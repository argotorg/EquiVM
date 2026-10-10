import Benchmarks.UniswapV4PoolManager.PoolModifyLimitsTrace
import Benchmarks.UniswapV4PoolManager.PoolModifyBitmapsTrace
import Benchmarks.UniswapV4PoolManager.PoolModifyTickFinish

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem poolModifyTickFinishTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id ptr x0 x1 x2 x4 x5 x9 params gl gu : UInt256} {p : PoolModifyParams}
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
    (hgl : memLoad (ptr+UInt256.ofNat 32) mem = gl)
    (hgu : memLoad (ptr+UInt256.ofNat 96) mem = gu)
    (hbgl : gl.toNat < 2^128) (hbgu : gu.toNat < 2^128)
    (h : RD (deployedRuntime v) I g s0 (if 0 ≤ p.delta then ⟨7329⟩ else ⟨7256⟩)
      (x0 :: x1 :: x2 :: ptr :: x4 :: x5 :: p.upper :: EVM.wordOfInt p.delta :: p.lower :: x9 :: params :: R)
      mem aw rdata evm.accountMap k C) :
    blockResultTrace (deployedRuntime v) g s0
      (poolModifyBitmapsNormal v I g s0 evm.σ₀ mem rdata id ptr x0 x1 x2 x4 x5 x9 params p R fl fu)
      (fun _ _ => False) (poolModifyTickFinishResult f evm id p fl gl fu gu) := by
  have hr := poolModifyLimitsTrace f v (by omega) hc hs hgl hgu hbgl hbgu h
  apply blockResultTrace_continueBlock hr
  intro f1 post _ ht1
  obtain ⟨rfl, aw1, k1, C1, rd1⟩ := ht1
  exact poolModifyBitmapsTrace f1 v hstack hI hc hl hu ht hm hmem hs hp hps hptr hspan hfit hfl hfu rd1

end Benchmarks.UniswapV4PoolManager
