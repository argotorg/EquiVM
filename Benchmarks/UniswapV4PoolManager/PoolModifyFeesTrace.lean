import Benchmarks.UniswapV4PoolManager.PoolModifyFeesPreludeTrace
import Benchmarks.UniswapV4PoolManager.PoolModifyPositionTrace
import Benchmarks.UniswapV4PoolManager.PoolModifyFeeDeltaTrace
import Benchmarks.UniswapV4PoolManager.PoolModifyFeeFrames

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolModifyFeesOutputStack (fees ptr x0 x1 x2 x4 x5 x9 : UInt256) (p : PoolModifyParams)
    (R : List UInt256) : List UInt256 :=
  ptr :: p.lower :: p.upper :: EVM.wordOfInt p.delta :: x0 :: x1 :: x2 :: fees :: x4 :: x5 ::
    ⟨6222⟩ :: ⟨6240⟩ :: fees :: x9 :: ⟨64⟩ :: R

def poolModifyFeesNormal (v : PoolManagerImmutables) (I : ExecutionEnv) (g : Sat256) (s0 evm : State)
    (mem rdata : ByteArray) (free id ptr x0 x1 x2 x4 x5 x9 : UInt256)
    (p : PoolModifyParams) (R : List UInt256) (_ : Frame) (post : State) : Prop :=
  post.executionEnv = I ∧ post.σ₀ = evm.σ₀ ∧ ∃ aw k C,
    RD (deployedRuntime v) I g s0 (if p.delta < 0 then ⟨6620⟩ else ⟨6036⟩)
      (poolModifyFeesOutputStack (poolModifyFeeDeltaWord evm id p) ptr x0 x1 x2 x4 x5 x9 p R)
      (poolModifyFeesMemory mem free id p) aw rdata post.accountMap k C

theorem poolModifyFeesTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw free id params x0 x1 x2 ptr x4 x5 x9 : UInt256} {p : PoolModifyParams}
    {k C : Nat} {R : List UInt256} (f : Frame)
    (v : PoolManagerImmutables) (hstack : R.length+31 ≤ 1024) (hI : evm.executionEnv = I)
    (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id) (hmem : 160 ≤ mem.size)
    (hl : int24Canonical p.lower) (hu : int24Canonical p.upper)
    (hdlo : -(2^127 : Int) ≤ p.delta) (hdhi : p.delta < 2^127)
    (hfree : memLoad (UInt256.ofNat 64) mem = free) (hfl : 160 ≤ free.toNat)
    (hfh : free.toNat+64 < UInt256.size)
    (ha : UInt256.land (memLoad params mem) solcAddrMask = accountWord p.owner)
    (hs : memLoad (params+UInt256.ofNat 160) mem = p.salt)
    (hp : 64 ≤ params.toNat) (hps : params.toNat+192 ≤ mem.size) (hpf : params.toNat+160 < UInt256.size)
    (h : RD (deployedRuntime v) I g s0 ⟨5722⟩
      (x0 :: x1 :: x2 :: ptr :: x4 :: x5 :: p.upper :: EVM.wordOfInt p.delta :: p.lower :: x9 :: params :: R)
      mem aw rdata evm.accountMap k C) :
    blockResultTrace (deployedRuntime v) g s0
      (poolModifyFeesNormal v I g s0 evm mem rdata free id ptr x0 x1 x2 x4 x5 x9 p R)
      (fun _ _ => False) (poolModifyFeesResult f evm id p) := by
  obtain ⟨aw1, k1, C1, rd1⟩ := poolModifyFeesPreludeTrace v (by omega) hI hm hmem hl hu
    hfree hfl hfh ha hs hp hps hpf h
  have hpos := poolModifyPositionTrace (poolModifyFeesPreludeFrame f evm id p) v hstack hI hdlo hdhi rd1
  apply blockResultTrace_continueBlock hpos
  intro f1 mid _ ht1
  obtain ⟨hImid, hσmid, k2, C2, rd2⟩ := ht1
  dsimp only [positionUpdateContinuation] at rd2
  have hfee := poolModifyFeeDeltaTrace f1 v (by simp only [List.length_cons]; omega) hdlo hdhi rd2
  apply blockResultTrace_mono hfee
  intro f2 post _ ht2
  obtain ⟨rfl, k3, C3, rd3⟩ := ht2
  exact ⟨hImid, hσmid, aw1, k3, C3, rd3⟩

end Benchmarks.UniswapV4PoolManager
