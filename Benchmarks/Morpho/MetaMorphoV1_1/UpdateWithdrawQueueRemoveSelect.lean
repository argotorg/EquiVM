import Benchmarks.Morpho.MetaMorphoV1_1.UpdateWithdrawQueueHeap
import Benchmarks.Morpho.MetaMorphoV1_1.UpdateWithdrawQueueReady
import Benchmarks.Morpho.MetaMorphoV1_1.LocalArrayBoolSource
import Benchmarks.Morpho.MetaMorphoV1_1.WordArrayIndexRuntime
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_042

/-! Select retained and omitted entries in the second withdrawal-queue loop. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem updateWithdrawQueueUnseenSource {frame : Frame} {imms : Store} {evm : State}
    {indexes : List Value} {curr i : Nat} {seen : List Bool} {queue : List UInt256}
    {cursor : UInt256} {b : Bool}
    (h : UpdateWithdrawQueueReady frame imms indexes curr i seen queue cursor)
    (hb : seen[i]? = some b) :
    evalExpr? config frame evm updateWithdrawQueueUnseenCondition = .ok (.bool (!b)) :=
  evalLocalArrayBoolNot h.seen h.index hb

theorem updateWithdrawQueueRetainedSource {frame : Frame} {imms : Store} {evm : State}
    {indexes : List Value} {curr i : Nat} {seen : List Bool} {queue : List UInt256}
    {cursor : UInt256}
    (h : UpdateWithdrawQueueReady frame imms indexes curr i seen queue cursor)
    (hb : seen[i]? = some true) :
    ExecBlock config frame evm updateWithdrawQueueRemoveBody (.ok frame evm) :=
  ExecBlock.consNormal
    (ExecStmt.iteFalse (updateWithdrawQueueUnseenSource h hb) ExecBlock.nil) ExecBlock.nil

theorem updateWithdrawQueueRemoveSelect {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C curr len i : Nat}
    {seen : List Bool} {queue : List UInt256} {cursor : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 7 ≤ 1024)
    (hm : UpdateWithdrawQueueHeap mem curr len seen queue cursor) (hi : i < curr)
    (rd : RD (deployedRuntime v) I g s0 ⟨8435⟩
      (UInt256.ofNat i :: ⟨128⟩ :: R) mem aw out σ k C) :
    (seen[i]? = some true ∧ ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨8452⟩
      (UInt256.ofNat i :: ⟨128⟩ :: R) mem aw' out σ k' C') ∨
    (seen[i]? = some false ∧ ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨8460⟩
      (UInt256.ofNat i :: ⟨128⟩ :: R) mem aw' out σ k' C') := by
  have hf := hm.seen.fit
  simp only [seenWords, List.length_map, hm.seenLength] at hf
  have hseen : memLoad ⟨128⟩ mem = UInt256.ofNat curr := by
    simpa only [seenWords, List.length_map, hm.seenLength] using hm.seen.length
  have r1 := metaMorphoV1_1_block_8435 (immWords := wordsOf (immStore v))
    (by omega) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  obtain ⟨aw2, k2, C2, r2⟩ := memoryWordArrayIndex v
    (by simp only [List.length_cons]; omega)
    (by rw [hseen, ulit_toNat' _ (by omega), ulit_toNat' _ (by omega)]; exact hi)
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) r1
  have haddr := memoryWordArrayIndex_address 128 i (by omega)
  change UInt256.shiftLeft (UInt256.ofNat i) ⟨5⟩ + ⟨128⟩ + ⟨32⟩ =
    UInt256.ofNat (160 + 32 * i) at haddr
  rw [haddr] at r2
  have hib : i < seen.length := by rw [hm.seenLength]; exact hi
  have hb := List.getElem?_eq_getElem hib
  have hload : memLoad (UInt256.ofNat (160 + 32 * i)) mem =
      if seen[i] then ⟨1⟩ else ⟨0⟩ := by
    simpa only [seenWords, List.getElem_map] using hm.seen.data i hi
  cases he : seen[i] with
  | true =>
      obtain ⟨aw3, k3, C3, r3⟩ := metaMorphoV1_1_block_8445_fallthrough_packed
        (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
        (by rw [hload, he]; rfl) r2
      exact .inl ⟨by simpa only [he] using hb, aw3, k3, C3, r3⟩
  | false =>
      obtain ⟨aw3, k3, C3, r3⟩ := metaMorphoV1_1_block_8445_taken_packed
        (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
        (by rw [hload, he]; decide)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r2
      exact .inr ⟨by simpa only [he] using hb, aw3, k3, C3, r3⟩

theorem updateWithdrawQueueRemoveIncrement {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C i : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 2 ≤ 1024)
    (rd : RD (deployedRuntime v) I g s0 ⟨8452⟩ (UInt256.ofNat i :: R) mem aw out σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨8175⟩
      (UInt256.ofNat (i + 1) :: R) mem aw out σ k' C' := by
  have r1 := metaMorphoV1_1_block_8452 (immWords := wordsOf (immStore v)) hstack
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  have hadd : UInt256.ofNat 1 + UInt256.ofNat i = UInt256.ofNat (i + 1) :=
    u256_one_add_ofNat i
  simpa only [metaMorphoV1_1_block_8452_stack, hadd] using RD.pack r1

end Benchmarks.Morpho.MetaMorphoV1_1
