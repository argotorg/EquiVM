import Benchmarks.UniswapV4PoolManager.PoolModifyTwoTicksTrace
import Benchmarks.UniswapV4PoolManager.PoolModifyTickFinishTrace
import Benchmarks.UniswapV4PoolManager.PoolModifyTickMemoryFields
import Benchmarks.UniswapV4PoolManager.PoolModifyTicks

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolModifyTicksActiveMemory (mem : ByteArray) (ptr id : UInt256) (p : PoolModifyParams) (evm : State) : ByteArray :=
  poolModifyBitmapsMemory (poolModifyTwoTicksMemory mem ptr id p evm) id p
    (tickFlipped (poolModifyLowerPacked evm id p) p.delta)
    (tickFlipped (poolModifyUpperPacked evm id p) p.delta)
def poolModifyTicksMemory (mem : ByteArray) (ptr id : UInt256) (p : PoolModifyParams) (evm : State) : ByteArray :=
  if p.delta ≠ 0 then poolModifyTicksActiveMemory mem ptr id p evm else mem

def poolModifyTicksNormal (v : PoolManagerImmutables) (I : ExecutionEnv) (g : Sat256) (s0 evm : State)
    (mem rdata : ByteArray) (id ptr x0 x1 x2 x4 x5 x9 params : UInt256)
    (p : PoolModifyParams) (R : List UInt256) (_ : Frame) (post : State) : Prop :=
  post.executionEnv = I ∧ post.σ₀ = evm.σ₀ ∧ ∃ aw k C,
    RD (deployedRuntime v) I g s0 ⟨5722⟩
      (x0 :: x1 :: x2 :: ptr :: x4 :: x5 :: p.upper :: EVM.wordOfInt p.delta :: p.lower :: x9 :: params :: R)
      (poolModifyTicksMemory mem ptr id p evm) aw rdata post.accountMap k C

theorem poolModifyTicksActiveTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id ptr x0 x1 x2 x4 x5 x9 params : UInt256} {p : PoolModifyParams}
    {k C : Nat} {R : List UInt256} (f : Frame)
    (v : PoolManagerImmutables) (hstack : R.length+23 ≤ 1024) (hI : evm.executionEnv = I)
    (hc : int24Canonical p.spacing) (hl : int24Canonical p.lower) (hu : int24Canonical p.upper)
    (ht : poolTicksValid p.lower p.upper) (hd : signedFits ⟨128, by decide⟩ p.delta)
    (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id) (hmem : 160 ≤ mem.size)
    (hs : memLoad (params+UInt256.ofNat 128) mem = p.spacing)
    (hp : 64 ≤ (params+UInt256.ofNat 128).toNat)
    (hps : (params+UInt256.ofNat 128).toNat+32 ≤ mem.size)
    (hpb : (params+UInt256.ofNat 128).toNat+32 ≤ ptr.toNat)
    (hptr : 160 ≤ ptr.toNat) (hfit : ptr.toNat+128 < UInt256.size)
    (h : RD (deployedRuntime v) I g s0 ⟨6949⟩
      (x0 :: x1 :: x2 :: ptr :: x4 :: x5 :: p.upper :: EVM.wordOfInt p.delta :: p.lower :: x9 :: params :: R)
      mem aw rdata evm.accountMap k C) :
    blockResultTrace (deployedRuntime v) g s0 (fun _ post => post.executionEnv = I ∧ post.σ₀ = evm.σ₀ ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨5722⟩
        (x0 :: x1 :: x2 :: ptr :: x4 :: x5 :: p.upper :: EVM.wordOfInt p.delta :: p.lower :: x9 :: params :: R)
        (poolModifyTicksActiveMemory mem ptr id p evm) aw' rdata post.accountMap k' C')
      (fun _ _ => False) (poolModifyTicksActiveResult f evm id p) := by
  have htwo := poolModifyTwoTicksTrace f v (by simp only [List.length_cons]; omega) hI hm hmem hptr
    (by omega) hl hu hd h
  apply blockResultTrace_continueBlock htwo
  intro f1 mid _ hnormal
  obtain ⟨hImid, hσmid, hgl, hgu, aw1, k1, C1, rd1⟩ := hnormal
  have hsize := poolModifyTwoTicksMemory_size_ge mem ptr id p evm (by omega)
  have hspan := tickUpperResultMemory_span (poolModifyLowerMemory mem ptr id p evm) ptr
    (EVM.wordOfInt (tickGrossAfterInt (poolModifyUpperPacked evm id p) p.delta))
    (UInt256.fromBool (tickFlipped (poolModifyUpperPacked evm id p) p.delta)) (by omega)
  have hm1 := (poolModifyTwoTicksMemory_loadWord mem ptr id p evm (UInt256.ofNat 128)
    (by decide) hmem hptr hfit).trans hm
  have hs1 := (poolModifyTwoTicksMemory_loadWord mem ptr id p evm _ hp hps hpb hfit).trans hs
  have hfinish := poolModifyTickFinishTrace f1 v (by omega) hImid hc hl hu ht hm1 (by omega) hs1 hp
    (by omega) (by omega) (by change ptr.toNat+96 ≤ (tickUpperResultMemory _ _ _ _).size; omega) hfit
    (poolModifyTwoTicksMemory_lowerFlipped mem ptr id p evm (by omega) hfit)
    (poolModifyTwoTicksMemory_upperFlipped mem ptr id p evm)
    (poolModifyTwoTicksMemory_lowerGross mem ptr id p evm (by omega) hfit)
    (poolModifyTwoTicksMemory_upperGross mem ptr id p evm hfit) hgl hgu rd1
  apply blockResultTrace_mono hfinish
  intro f2 post _ hpost
  obtain ⟨hIpost, hσpost, hr⟩ := hpost
  exact ⟨hIpost, hσpost.trans hσmid, hr⟩

theorem poolModifyTicksTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id ptr x0 x1 x2 x4 x5 x9 params : UInt256} {p : PoolModifyParams}
    {k C : Nat} {R : List UInt256} (f : Frame)
    (v : PoolManagerImmutables) (hstack : R.length+23 ≤ 1024) (hI : evm.executionEnv = I)
    (hc : int24Canonical p.spacing) (hl : int24Canonical p.lower) (hu : int24Canonical p.upper)
    (ht : poolTicksValid p.lower p.upper) (hd : signedFits ⟨128, by decide⟩ p.delta)
    (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id) (hmem : 160 ≤ mem.size)
    (hs : memLoad (params+UInt256.ofNat 128) mem = p.spacing)
    (hp : 64 ≤ (params+UInt256.ofNat 128).toNat)
    (hps : (params+UInt256.ofNat 128).toNat+32 ≤ mem.size)
    (hpb : (params+UInt256.ofNat 128).toNat+32 ≤ ptr.toNat)
    (hptr : 160 ≤ ptr.toNat) (hfit : ptr.toNat+128 < UInt256.size)
    (h : RD (deployedRuntime v) I g s0 (if p.delta ≠ 0 then ⟨6949⟩ else ⟨5722⟩)
      (x0 :: x1 :: x2 :: ptr :: x4 :: x5 :: p.upper :: EVM.wordOfInt p.delta :: p.lower :: x9 :: params :: R)
      mem aw rdata evm.accountMap k C) :
    blockResultTrace (deployedRuntime v) g s0
      (poolModifyTicksNormal v I g s0 evm mem rdata id ptr x0 x1 x2 x4 x5 x9 params p R)
      (fun _ _ => False) (poolModifyTicksResult f evm id p) := by
  by_cases hz : p.delta ≠ 0
  · rw [if_pos hz] at h
    rw [poolModifyTicksResult, if_pos hz]
    apply blockResultTrace_mono (poolModifyTicksActiveTrace f v hstack hI hc hl hu ht hd hm hmem hs hp hps hpb hptr hfit h)
    intro f1 post _ ht1
    unfold poolModifyTicksNormal
    rw [poolModifyTicksMemory, if_pos hz]
    exact ht1
  · rw [if_neg hz] at h
    rw [poolModifyTicksResult, if_neg hz]
    change evm.executionEnv = I ∧ evm.σ₀ = evm.σ₀ ∧ _
    refine ⟨hI, rfl, aw, k, C, ?_⟩
    rw [poolModifyTicksMemory, if_neg hz]
    exact h

end Benchmarks.UniswapV4PoolManager
