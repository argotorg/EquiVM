import Benchmarks.UniswapV4PoolManager.PoolModifyClearTrace
import Benchmarks.UniswapV4PoolManager.PoolModifyClears

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolModifyClearsMemory (mem : ByteArray) (id : UInt256) (p : PoolModifyParams) (fl fu : Bool) : ByteArray :=
  if p.delta < 0 then poolModifyClearMemory (poolModifyClearMemory mem id p.lower fl) id p.upper fu else mem

def poolModifyClearsNormal (v : PoolManagerImmutables) (I : ExecutionEnv) (g : Sat256) (s0 : State)
    (σ₀ : AccountMap) (mem rdata : ByteArray) (id fees ptr x0 x1 x2 x4 x5 x9 : UInt256)
    (p : PoolModifyParams) (R : List UInt256) (fl fu : Bool) (_ : Frame) (post : State) : Prop :=
  post.executionEnv = I ∧ post.σ₀ = σ₀ ∧ ∃ junk aw k C,
    RD (deployedRuntime v) I g s0 ⟨6036⟩
      (junk :: (poolModifyFeesOutputStack fees ptr x0 x1 x2 x4 x5 x9 p R).tail)
      (poolModifyClearsMemory mem id p fl fu) aw rdata post.accountMap k C

def poolModifyClearsActiveWords (aw ptr : UInt256) (delta : Int) (fl fu : Bool) : UInt256 :=
  if delta < 0 then poolModifyClearActiveWords (poolModifyClearActiveWords aw ptr false fl) ptr true fu else aw

def poolModifyClearsNormalAtAW (v : PoolManagerImmutables) (I : ExecutionEnv) (g : Sat256) (s0 : State)
    (σ₀ : AccountMap) (mem rdata : ByteArray) (id fees ptr x0 x1 x2 x4 x5 x9 : UInt256)
    (p : PoolModifyParams) (R : List UInt256) (fl fu : Bool) (aw : UInt256) (_ : Frame) (post : State) : Prop :=
  post.executionEnv = I ∧ post.σ₀ = σ₀ ∧ ∃ junk k C,
    RD (deployedRuntime v) I g s0 ⟨6036⟩
      (junk :: (poolModifyFeesOutputStack fees ptr x0 x1 x2 x4 x5 x9 p R).tail)
      (poolModifyClearsMemory mem id p fl fu) aw rdata post.accountMap k C

theorem poolModifyClearsExactTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id fees ptr x0 x1 x2 x4 x5 x9 extra : UInt256} {p : PoolModifyParams}
    {fl fu : Bool} {k C : Nat} {R : List UInt256} (f : Frame)
    (v : PoolManagerImmutables) (hstack : R.length+24 ≤ 1024) (hI : evm.executionEnv = I)
    (hl : int24Canonical p.lower) (hu : int24Canonical p.upper)
    (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id) (hmem : 160 ≤ mem.size)
    (hptr : 64 ≤ ptr.toNat) (hspan : ptr.toNat+96 ≤ mem.size) (hfit : ptr.toNat+128 < UInt256.size)
    (hfl : memLoad ptr mem = UInt256.fromBool fl)
    (hfu : memLoad (ptr+UInt256.ofNat 64) mem = UInt256.fromBool fu)
    (h : RD (deployedRuntime v) I g s0 (if p.delta < 0 then ⟨6620⟩ else ⟨6036⟩)
      (poolModifyFeesOutputStack fees ptr x0 x1 x2 x4 x5 x9 p (extra :: R)) mem aw rdata evm.accountMap k C) :
    blockResultTrace (deployedRuntime v) g s0
      (poolModifyClearsNormalAtAW v I g s0 evm.σ₀ mem rdata id fees ptr x0 x1 x2 x4 x5 x9 p (extra :: R) fl fu (poolModifyClearsActiveWords aw ptr p.delta fl fu))
      (fun _ _ => False) (poolModifyClearsResult f evm id p fl fu) := by
  by_cases hd : p.delta < 0
  · rw [if_pos hd] at h
    rw [poolModifyClearsResult, if_pos hd]
    have hlo := poolModifyClearLowerExactTrace f v (by simp only [List.length_cons]; omega) hI hl hm hfl h
    apply blockResultTrace_continueBlock hlo
    intro f1 mid _ ht1
    obtain ⟨hImid, hσmid, k1, C1, rd1⟩ := ht1
    have hm1 : memLoad (UInt256.ofNat 128) (poolModifyClearMemory mem id p.lower fl) = poolSlot id :=
      (conditionalHashMemory_loadWord mem _ _ (UInt256.ofNat 128) fl (by decide) hmem).trans hm
    have h64 := uadd_word_ofNat_toNat ptr 64 (by omega)
    have hfu1 : memLoad (ptr+UInt256.ofNat 64) (poolModifyClearMemory mem id p.lower fl) = UInt256.fromBool fu :=
      (conditionalHashMemory_loadWord mem _ _ (ptr+UInt256.ofNat 64) fl (by omega) (by omega)).trans hfu
    have hup := poolModifyClearUpperExactTrace f1 v (by simp only [List.length_cons]; omega) hImid hu hm1 hfu1 rd1
    apply blockResultTrace_mono hup
    intro f2 post _ ht2
    obtain ⟨hIpost, hσpost, k2, C2, rd2⟩ := ht2
    have rd3 := poolManagerBlocks.poolManager_block_6636 (by omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd2
    unfold poolModifyClearsNormalAtAW
    rw [poolModifyClearsMemory, if_pos hd, poolModifyClearsActiveWords, if_pos hd]
    exact ⟨hIpost, hσpost.trans hσmid, extra, _, _, rd3⟩
  · rw [if_neg hd] at h
    rw [poolModifyClearsResult, if_neg hd]
    dsimp only [blockResultTrace]
    unfold poolModifyClearsNormalAtAW
    rw [poolModifyClearsMemory, if_neg hd, poolModifyClearsActiveWords, if_neg hd]
    exact ⟨hI, rfl, ptr, k, C, h⟩

theorem poolModifyClearsTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id fees ptr x0 x1 x2 x4 x5 x9 extra : UInt256} {p : PoolModifyParams}
    {fl fu : Bool} {k C : Nat} {R : List UInt256} (f : Frame)
    (v : PoolManagerImmutables) (hstack : R.length+24 ≤ 1024) (hI : evm.executionEnv = I)
    (hl : int24Canonical p.lower) (hu : int24Canonical p.upper)
    (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id) (hmem : 160 ≤ mem.size)
    (hptr : 64 ≤ ptr.toNat) (hspan : ptr.toNat+96 ≤ mem.size) (hfit : ptr.toNat+128 < UInt256.size)
    (hfl : memLoad ptr mem = UInt256.fromBool fl)
    (hfu : memLoad (ptr+UInt256.ofNat 64) mem = UInt256.fromBool fu)
    (h : RD (deployedRuntime v) I g s0 (if p.delta < 0 then ⟨6620⟩ else ⟨6036⟩)
      (poolModifyFeesOutputStack fees ptr x0 x1 x2 x4 x5 x9 p (extra :: R)) mem aw rdata evm.accountMap k C) :
    blockResultTrace (deployedRuntime v) g s0
      (poolModifyClearsNormal v I g s0 evm.σ₀ mem rdata id fees ptr x0 x1 x2 x4 x5 x9 p (extra :: R) fl fu)
      (fun _ _ => False) (poolModifyClearsResult f evm id p fl fu) := by
  have hr := poolModifyClearsExactTrace f v hstack hI hl hu hm hmem hptr hspan hfit hfl hfu h
  apply blockResultTrace_mono hr
  intro f' post _ ht
  obtain ⟨hIpost, hσpost, junk, k', C', rd⟩ := ht
  exact ⟨hIpost, hσpost, junk, _, k', C', rd⟩

end Benchmarks.UniswapV4PoolManager
