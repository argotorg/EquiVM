import Benchmarks.UniswapV4PoolManager.PoolModifyClear
import Benchmarks.UniswapV4PoolManager.PoolModifyFeesTrace
import Benchmarks.UniswapV4PoolManager.TickClearCorrect
import Benchmarks.UniswapV4PoolManager.ConditionalMappingMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolModifyClearMemory (mem : ByteArray) (id tick : UInt256) (flipped : Bool) : ByteArray :=
  conditionalHashMemory mem tick (poolSlot id+⟨4⟩) flipped

def poolModifyClearMiddleStack (fees ptr x0 x1 x2 x4 x5 x9 : UInt256) (p : PoolModifyParams)
    (R : List UInt256) : List UInt256 :=
  ptr :: ⟨64⟩ :: (poolModifyFeesOutputStack fees ptr x0 x1 x2 x4 x5 x9 p R).tail

def poolModifyClearActiveWords (aw ptr : UInt256) (upper flipped : Bool) : UInt256 :=
  let flagAW := M aw (if upper then ptr+UInt256.ofNat 64 else ptr) ⟨32⟩
  if flipped then tickClearActiveWords flagAW else flagAW

theorem poolModifyClearLowerExactTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id fees ptr x0 x1 x2 x4 x5 x9 : UInt256} {p : PoolModifyParams}
    {fl : Bool} {k C : Nat} {R : List UInt256} (f : Frame)
    (v : PoolManagerImmutables) (hstack : R.length+23 ≤ 1024) (hI : evm.executionEnv = I)
    (hl : int24Canonical p.lower) (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id)
    (hfl : memLoad ptr mem = UInt256.fromBool fl)
    (h : RD (deployedRuntime v) I g s0 ⟨6620⟩
      (poolModifyFeesOutputStack fees ptr x0 x1 x2 x4 x5 x9 p R) mem aw rdata evm.accountMap k C) :
    blockResultTrace (deployedRuntime v) g s0 (fun _ post => post.executionEnv = I ∧ post.σ₀ = evm.σ₀ ∧
      ∃ k' C', RD (deployedRuntime v) I g s0 ⟨6629⟩
        (poolModifyClearMiddleStack fees ptr x0 x1 x2 x4 x5 x9 p R)
        (poolModifyClearMemory mem id p.lower fl) (poolModifyClearActiveWords aw ptr false fl) rdata post.accountMap k' C') (fun _ _ => False)
      (poolModifyClearResult f evm id (EVM.signed p.lower) false fl) := by
  cases fl with
  | false =>
    have rd1 := poolManagerBlocks.poolManager_block_6620_fallthrough (by omega) hfl h
    exact ⟨hI, rfl, _, _, rd1⟩
  | true =>
    have rd1 := poolManagerBlocks.poolManager_block_6620_taken (by omega) (by rw [hfl]; decide)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    simp only [poolManagerBlocks.poolManager_block_6620_taken_stack] at rd1
    have hc := tickClearLowerExactResultTrace (poolModifyClearAliasFrame f id false) v
      (by simp only [List.length_cons]; omega) hI hm hl rd1
    apply blockResultTrace_resumeCall hc
    intro cf post values _ ht
    cases values with
    | some values => exact False.elim ht
    | none =>
      obtain ⟨hIpost, hσpost, k2, C2, rd2⟩ := ht
      have rd3 := poolManagerBlocks.poolManager_block_6725 (by simp only [List.length_cons]; omega)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd2
      exact ⟨hIpost, hσpost, _, _, rd3⟩

theorem poolModifyClearLowerTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id fees ptr x0 x1 x2 x4 x5 x9 : UInt256} {p : PoolModifyParams}
    {fl : Bool} {k C : Nat} {R : List UInt256} (f : Frame)
    (v : PoolManagerImmutables) (hstack : R.length+23 ≤ 1024) (hI : evm.executionEnv = I)
    (hl : int24Canonical p.lower) (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id)
    (hfl : memLoad ptr mem = UInt256.fromBool fl)
    (h : RD (deployedRuntime v) I g s0 ⟨6620⟩
      (poolModifyFeesOutputStack fees ptr x0 x1 x2 x4 x5 x9 p R) mem aw rdata evm.accountMap k C) :
    blockResultTrace (deployedRuntime v) g s0 (fun _ post => post.executionEnv = I ∧ post.σ₀ = evm.σ₀ ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨6629⟩
        (poolModifyClearMiddleStack fees ptr x0 x1 x2 x4 x5 x9 p R)
        (poolModifyClearMemory mem id p.lower fl) aw' rdata post.accountMap k' C') (fun _ _ => False)
      (poolModifyClearResult f evm id (EVM.signed p.lower) false fl) := by
  have hr := poolModifyClearLowerExactTrace f v hstack hI hl hm hfl h
  apply blockResultTrace_mono hr
  intro f' post _ ht
  exact ⟨ht.1, ht.2.1, _, ht.2.2⟩

theorem poolModifyClearUpperExactTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id fees ptr x0 x1 x2 x4 x5 x9 : UInt256} {p : PoolModifyParams}
    {fu : Bool} {k C : Nat} {R : List UInt256} (f : Frame)
    (v : PoolManagerImmutables) (hstack : R.length+21 ≤ 1024) (hI : evm.executionEnv = I)
    (hu : int24Canonical p.upper) (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id)
    (hfu : memLoad (ptr+UInt256.ofNat 64) mem = UInt256.fromBool fu)
    (h : RD (deployedRuntime v) I g s0 ⟨6629⟩
      (poolModifyClearMiddleStack fees ptr x0 x1 x2 x4 x5 x9 p R) mem aw rdata evm.accountMap k C) :
    blockResultTrace (deployedRuntime v) g s0 (fun _ post => post.executionEnv = I ∧ post.σ₀ = evm.σ₀ ∧
      ∃ k' C', RD (deployedRuntime v) I g s0 ⟨6636⟩
        (poolModifyFeesOutputStack fees ptr x0 x1 x2 x4 x5 x9 p R).tail
        (poolModifyClearMemory mem id p.upper fu) (poolModifyClearActiveWords aw ptr true fu) rdata post.accountMap k' C') (fun _ _ => False)
      (poolModifyClearResult f evm id (EVM.signed p.upper) true fu) := by
  cases fu with
  | false =>
    have rd1 := poolManagerBlocks.poolManager_block_6629_fallthrough
      (by simp only [poolModifyClearMiddleStack, poolModifyFeesOutputStack, List.tail_cons, List.length_cons]; omega) hfu h
    exact ⟨hI, rfl, _, _, rd1⟩
  | true =>
    have rd1 := poolManagerBlocks.poolManager_block_6629_taken
      (by simp only [poolModifyClearMiddleStack, poolModifyFeesOutputStack, List.tail_cons, List.length_cons]; omega)
      (by change memLoad (ptr+UInt256.ofNat 64) mem ≠ UInt256.ofNat 0; rw [hfu]; decide)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    simp only [poolManagerBlocks.poolManager_block_6629_taken_stack] at rd1
    have hc := tickClearUpperExactResultTrace (poolModifyClearAliasFrame f id true) v
      (by simp only [List.length_cons]; omega) hI hm hu rd1
    apply blockResultTrace_resumeCall hc
    intro cf post values _ ht
    cases values with
    | some values => exact False.elim ht
    | none =>
      obtain ⟨hIpost, hσpost, k2, C2, rd2⟩ := ht
      have rd3 := poolManagerBlocks.poolManager_block_6681 (by simp only [List.length_cons]; omega)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd2
      exact ⟨hIpost, hσpost, _, _, rd3⟩

theorem poolModifyClearUpperTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id fees ptr x0 x1 x2 x4 x5 x9 : UInt256} {p : PoolModifyParams}
    {fu : Bool} {k C : Nat} {R : List UInt256} (f : Frame)
    (v : PoolManagerImmutables) (hstack : R.length+21 ≤ 1024) (hI : evm.executionEnv = I)
    (hu : int24Canonical p.upper) (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id)
    (hfu : memLoad (ptr+UInt256.ofNat 64) mem = UInt256.fromBool fu)
    (h : RD (deployedRuntime v) I g s0 ⟨6629⟩
      (poolModifyClearMiddleStack fees ptr x0 x1 x2 x4 x5 x9 p R) mem aw rdata evm.accountMap k C) :
    blockResultTrace (deployedRuntime v) g s0 (fun _ post => post.executionEnv = I ∧ post.σ₀ = evm.σ₀ ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨6636⟩
        (poolModifyFeesOutputStack fees ptr x0 x1 x2 x4 x5 x9 p R).tail
        (poolModifyClearMemory mem id p.upper fu) aw' rdata post.accountMap k' C') (fun _ _ => False)
      (poolModifyClearResult f evm id (EVM.signed p.upper) true fu) := by
  have hr := poolModifyClearUpperExactTrace f v hstack hI hu hm hfu h
  apply blockResultTrace_mono hr
  intro f' post _ ht
  exact ⟨ht.1, ht.2.1, _, ht.2.2⟩

end Benchmarks.UniswapV4PoolManager
