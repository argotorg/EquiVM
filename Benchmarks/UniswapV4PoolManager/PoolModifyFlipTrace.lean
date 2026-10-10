import Benchmarks.UniswapV4PoolManager.PoolModifyFlipEntry
import Benchmarks.UniswapV4PoolManager.TickBitmapCorrect
import Benchmarks.UniswapV4PoolManager.BlockResultTrace
import Benchmarks.UniswapV4PoolManager.ConditionalMappingMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolModifyFlipMemory (mem : ByteArray) (id tick spacing : UInt256) (flipped : Bool) : ByteArray :=
  conditionalHashMemory mem (EVM.wordOfInt (tickBitmapPosition (EVM.signed tick) (EVM.signed spacing)))
    (poolSlot id+⟨5⟩) flipped

def poolModifyFlipNormal (v : PoolManagerImmutables) (I : ExecutionEnv) (g : Sat256) (s0 : State)
    (σ₀ : AccountMap) (mem rdata : ByteArray) (id ptr x0 x1 x2 x4 x5 x9 params : UInt256)
    (p : PoolModifyParams) (R : List UInt256) (upper flipped : Bool) (_ : Frame) (post : State) : Prop :=
  post.executionEnv = I ∧ post.σ₀ = σ₀ ∧ ∃ aw k C,
    RD (deployedRuntime v) I g s0 (poolModifyFlipNext upper)
      (x0 :: x1 :: x2 :: ptr :: x4 :: x5 :: p.upper :: EVM.wordOfInt p.delta :: p.lower :: x9 :: params :: R)
      (poolModifyFlipMemory mem id (if upper then p.upper else p.lower) p.spacing flipped)
      aw rdata post.accountMap k C

def poolModifyFlipActiveWords (aw params ptr : UInt256) (upper flipped : Bool) : UInt256 :=
  let entryAW := poolModifyFlipEnterActiveWords aw params ptr upper flipped
  if flipped then tickBitmapActiveWords entryAW else entryAW

def poolModifyFlipNormalAtAW (v : PoolManagerImmutables) (I : ExecutionEnv) (g : Sat256) (s0 : State)
    (σ₀ : AccountMap) (mem rdata : ByteArray) (id ptr x0 x1 x2 x4 x5 x9 params : UInt256)
    (p : PoolModifyParams) (R : List UInt256) (upper flipped : Bool) (aw : UInt256) (_ : Frame) (post : State) : Prop :=
  post.executionEnv = I ∧ post.σ₀ = σ₀ ∧ ∃ k C,
    RD (deployedRuntime v) I g s0 (poolModifyFlipNext upper)
      (x0 :: x1 :: x2 :: ptr :: x4 :: x5 :: p.upper :: EVM.wordOfInt p.delta :: p.lower :: x9 :: params :: R)
      (poolModifyFlipMemory mem id (if upper then p.upper else p.lower) p.spacing flipped)
      aw rdata post.accountMap k C

theorem poolModifyFlipExactTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id ptr x0 x1 x2 x4 x5 x9 params : UInt256} {p : PoolModifyParams}
    {k C : Nat} {R : List UInt256} (f : Frame) (upper flipped : Bool)
    (v : PoolManagerImmutables) (hstack : R.length+20 ≤ 1024) (hI : evm.executionEnv = I)
    (hc : int24Canonical p.spacing) (ht : int24Canonical (if upper then p.upper else p.lower))
    (hb : (EVM.signed (if upper then p.upper else p.lower)).natAbs ≤ 887272)
    (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id)
    (hs : memLoad (params+UInt256.ofNat 128) mem = p.spacing)
    (hf : memLoad (if upper then ptr+UInt256.ofNat 64 else ptr) mem = UInt256.fromBool flipped)
    (h : RD (deployedRuntime v) I g s0 (poolModifyFlipStart upper)
      (x0 :: x1 :: x2 :: ptr :: x4 :: x5 :: p.upper :: EVM.wordOfInt p.delta :: p.lower :: x9 :: params :: R)
      mem aw rdata evm.accountMap k C) :
    blockResultTrace (deployedRuntime v) g s0
      (poolModifyFlipNormalAtAW v I g s0 evm.σ₀ mem rdata id ptr x0 x1 x2 x4 x5 x9 params p R upper flipped (poolModifyFlipActiveWords aw params ptr upper flipped))
      (fun _ _ => False)
      (poolModifyFlipResult f evm id (EVM.signed (if upper then p.upper else p.lower))
        (EVM.signed p.spacing) upper flipped) := by
  have he := poolModifyFlipEnterExactTrace upper flipped v (by omega) hc hm hs hf h
  cases flipped with
  | false =>
    exact ⟨hI, rfl, he⟩
  | true =>
    obtain ⟨k1, C1, rd1⟩ := he
    have hc := tickBitmapExactResultTrace (poolModifyFlipAliasFrame f id upper) v
      (by simp only [List.length_cons]; omega) hI ht hc hb
      (by cases upper <;> rw [deployedRuntime_jumps] <;> jump_dest) rd1
    apply blockResultTrace_resumeCall hc
    intro cf post values _ hv
    cases values with
    | some values => exact False.elim hv
    | none =>
      obtain ⟨hIpost, hσpost, k2, C2, rd2⟩ := hv
      exact ⟨hIpost, hσpost, poolModifyFlipReturnExactTrace upper v
        (by simp only [List.length_cons]; omega) rd2⟩

theorem poolModifyFlipTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id ptr x0 x1 x2 x4 x5 x9 params : UInt256} {p : PoolModifyParams}
    {k C : Nat} {R : List UInt256} (f : Frame) (upper flipped : Bool)
    (v : PoolManagerImmutables) (hstack : R.length+20 ≤ 1024) (hI : evm.executionEnv = I)
    (hc : int24Canonical p.spacing) (ht : int24Canonical (if upper then p.upper else p.lower))
    (hb : (EVM.signed (if upper then p.upper else p.lower)).natAbs ≤ 887272)
    (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id)
    (hs : memLoad (params+UInt256.ofNat 128) mem = p.spacing)
    (hf : memLoad (if upper then ptr+UInt256.ofNat 64 else ptr) mem = UInt256.fromBool flipped)
    (h : RD (deployedRuntime v) I g s0 (poolModifyFlipStart upper)
      (x0 :: x1 :: x2 :: ptr :: x4 :: x5 :: p.upper :: EVM.wordOfInt p.delta :: p.lower :: x9 :: params :: R)
      mem aw rdata evm.accountMap k C) :
    blockResultTrace (deployedRuntime v) g s0
      (poolModifyFlipNormal v I g s0 evm.σ₀ mem rdata id ptr x0 x1 x2 x4 x5 x9 params p R upper flipped)
      (fun _ _ => False)
      (poolModifyFlipResult f evm id (EVM.signed (if upper then p.upper else p.lower))
        (EVM.signed p.spacing) upper flipped) := by
  have hr := poolModifyFlipExactTrace f upper flipped v hstack hI hc ht hb hm hs hf h
  apply blockResultTrace_mono hr
  intro f' post _ ht'
  exact ⟨ht'.1, ht'.2.1, _, ht'.2.2⟩

end Benchmarks.UniswapV4PoolManager
