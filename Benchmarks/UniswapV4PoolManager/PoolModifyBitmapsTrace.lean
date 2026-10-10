import Benchmarks.UniswapV4PoolManager.PoolModifyFlipTrace
import Benchmarks.UniswapV4PoolManager.PoolModifyBitmaps
import Benchmarks.UniswapV4PoolManager.MappingScratchMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem poolModifyFlipMemory_size (mem : ByteArray) (id tick spacing : UInt256) (flipped : Bool)
    (hm : 64 ≤ mem.size) : (poolModifyFlipMemory mem id tick spacing flipped).size = mem.size :=
  conditionalHashMemory_size _ _ _ _ hm

theorem poolModifyFlipMemory_loadWord (mem : ByteArray) (id tick spacing read : UInt256) (flipped : Bool)
    (hoff : 64 ≤ read.toNat) (hin : read.toNat+32 ≤ mem.size) :
    memLoad read (poolModifyFlipMemory mem id tick spacing flipped) = memLoad read mem :=
  conditionalHashMemory_loadWord _ _ _ _ _ hoff hin

def poolModifyBitmapsMemory (mem : ByteArray) (id : UInt256) (p : PoolModifyParams) (fl fu : Bool) : ByteArray :=
  poolModifyFlipMemory (poolModifyFlipMemory mem id p.lower p.spacing fl) id p.upper p.spacing fu

def poolModifyBitmapsNormal (v : PoolManagerImmutables) (I : ExecutionEnv) (g : Sat256) (s0 : State)
    (σ₀ : AccountMap) (mem rdata : ByteArray) (id ptr x0 x1 x2 x4 x5 x9 params : UInt256)
    (p : PoolModifyParams) (R : List UInt256) (fl fu : Bool) (_ : Frame) (post : State) : Prop :=
  post.executionEnv = I ∧ post.σ₀ = σ₀ ∧ ∃ aw k C,
    RD (deployedRuntime v) I g s0 ⟨5722⟩
      (x0 :: x1 :: x2 :: ptr :: x4 :: x5 :: p.upper :: EVM.wordOfInt p.delta :: p.lower :: x9 :: params :: R)
      (poolModifyBitmapsMemory mem id p fl fu) aw rdata post.accountMap k C

def poolModifyBitmapsActiveWords (aw params ptr : UInt256) (fl fu : Bool) : UInt256 :=
  poolModifyFlipActiveWords (poolModifyFlipActiveWords aw params ptr false fl) params ptr true fu

def poolModifyBitmapsNormalAtAW (v : PoolManagerImmutables) (I : ExecutionEnv) (g : Sat256) (s0 : State)
    (σ₀ : AccountMap) (mem rdata : ByteArray) (id ptr x0 x1 x2 x4 x5 x9 params : UInt256)
    (p : PoolModifyParams) (R : List UInt256) (fl fu : Bool) (aw : UInt256) (_ : Frame) (post : State) : Prop :=
  post.executionEnv = I ∧ post.σ₀ = σ₀ ∧ ∃ k C,
    RD (deployedRuntime v) I g s0 ⟨5722⟩
      (x0 :: x1 :: x2 :: ptr :: x4 :: x5 :: p.upper :: EVM.wordOfInt p.delta :: p.lower :: x9 :: params :: R)
      (poolModifyBitmapsMemory mem id p fl fu) aw rdata post.accountMap k C

theorem poolModifyBitmapsExactTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
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
    (h : RD (deployedRuntime v) I g s0 ⟨7256⟩
      (x0 :: x1 :: x2 :: ptr :: x4 :: x5 :: p.upper :: EVM.wordOfInt p.delta :: p.lower :: x9 :: params :: R)
      mem aw rdata evm.accountMap k C) :
    blockResultTrace (deployedRuntime v) g s0
      (poolModifyBitmapsNormalAtAW v I g s0 evm.σ₀ mem rdata id ptr x0 x1 x2 x4 x5 x9 params p R fl fu (poolModifyBitmapsActiveWords aw params ptr fl fu))
      (fun _ _ => False) (poolModifyBitmapsResult f evm id p fl fu) := by
  have hlo := poolModifyFlipExactTrace f false fl v hstack hI hc hl (poolTicksValid_bounds ht).1 hm hs hfl h
  apply blockResultTrace_continueBlock hlo
  intro f1 mid _ ht1
  obtain ⟨hImid, hσmid, k1, C1, rd1⟩ := ht1
  have hm1 := (poolModifyFlipMemory_loadWord mem id p.lower p.spacing (UInt256.ofNat 128) fl (by decide) hmem).trans hm
  have hs1 := (poolModifyFlipMemory_loadWord mem id p.lower p.spacing _ fl hp hps).trans hs
  have h64 := uadd_word_ofNat_toNat ptr 64 (by omega)
  have hf1 := (poolModifyFlipMemory_loadWord mem id p.lower p.spacing (ptr+UInt256.ofNat 64) fl
    (by omega) (by omega)).trans hfu
  have hup := poolModifyFlipExactTrace f1 true fu v hstack hImid hc hu (poolTicksValid_bounds ht).2 hm1 hs1 hf1 rd1
  apply blockResultTrace_mono hup
  intro f2 post _ ht2
  obtain ⟨hIpost, hσpost, hr⟩ := ht2
  exact ⟨hIpost, hσpost.trans hσmid, hr⟩

theorem poolModifyBitmapsTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
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
    (h : RD (deployedRuntime v) I g s0 ⟨7256⟩
      (x0 :: x1 :: x2 :: ptr :: x4 :: x5 :: p.upper :: EVM.wordOfInt p.delta :: p.lower :: x9 :: params :: R)
      mem aw rdata evm.accountMap k C) :
    blockResultTrace (deployedRuntime v) g s0
      (poolModifyBitmapsNormal v I g s0 evm.σ₀ mem rdata id ptr x0 x1 x2 x4 x5 x9 params p R fl fu)
      (fun _ _ => False) (poolModifyBitmapsResult f evm id p fl fu) := by
  have hr := poolModifyBitmapsExactTrace f v hstack hI hc hl hu ht hm hmem hs hp hps hptr hspan hfit hfl hfu h
  apply blockResultTrace_mono hr
  intro f' post _ ht'
  exact ⟨ht'.1, ht'.2.1, _, ht'.2.2⟩

end Benchmarks.UniswapV4PoolManager
