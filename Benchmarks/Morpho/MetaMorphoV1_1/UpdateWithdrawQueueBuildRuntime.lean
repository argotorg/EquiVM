import Benchmarks.Morpho.MetaMorphoV1_1.UpdateWithdrawQueueMemory
import Benchmarks.Morpho.MetaMorphoV1_1.CalldataArrayIndexRuntime
import Benchmarks.Morpho.MetaMorphoV1_1.WordArrayIndexRuntime
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_043
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_044

/-! One bytecode iteration of withdrawal-queue construction. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem updateWithdrawQueueBuildRuntime {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C curr len i : Nat}
    {seen : List Bool} {queue : List UInt256} {data newData : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 15 ≤ 1024)
    (hm : UpdateWithdrawQueueMemory mem curr len i seen queue) (hi : i < len)
    (hc : (codeOwnerStorageWord I σ ⟨21⟩).toNat = curr)
    (rd : RD (deployedRuntime v) I g s0 ⟨8690⟩
      ([UInt256.ofNat i, UInt256.ofNat len, data, ⟨128⟩, UInt256.ofNat curr,
        UInt256.ofNat (160 + 32 * curr), newData] ++ R) mem aw out σ k C) :
    let prev := calldataWord I.calldata (UInt256.shiftLeft (UInt256.ofNat i) ⟨5⟩ + data).toNat
    let id := codeOwnerStorageWord I σ
      (uInt256OfByteArray (KEC (UInt256.toByteArray ⟨21⟩)) + prev)
    (curr ≤ prev.toNat ∧ RDrev (deployedRuntime v) g s0) ∨
    (prev.toNat < curr ∧ seen[prev.toNat]? = some true ∧ RDrev (deployedRuntime v) g s0) ∨
    (prev.toNat < curr ∧ seen[prev.toNat]? = some false ∧ ∃ aw' k' C',
      RD (deployedRuntime v) I g s0 ⟨8163⟩
        ([UInt256.ofNat (i + 1), UInt256.ofNat len, data, ⟨128⟩, UInt256.ofNat curr,
          UInt256.ofNat (160 + 32 * curr), newData] ++ R)
        (updateWithdrawQueueBuildMem (wordAt0Mem ⟨21⟩ mem) curr prev.toNat i id)
        aw' out σ k' C') := by
  dsimp only
  let prev := calldataWord I.calldata (UInt256.shiftLeft (UInt256.ofNat i) ⟨5⟩ + data).toNat
  let id := codeOwnerStorageWord I σ
    (uInt256OfByteArray (KEC (UInt256.toByteArray ⟨21⟩)) + prev)
  have hf := hm.queue.fit
  rw [hm.queueLength] at hf
  have hlen : len < UInt256.size := by omega
  have hcur : curr < UInt256.size := by omega
  change RD (deployedRuntime v) I g s0 ⟨8690⟩
    (UInt256.ofNat i :: UInt256.ofNat len :: data :: ⟨128⟩ :: UInt256.ofNat curr ::
      UInt256.ofNat (160 + 32 * curr) :: newData :: R) mem aw out σ k C at rd
  have r1 := metaMorphoV1_1_block_8690 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  obtain ⟨k2, C2, r2⟩ := calldataArrayIndex v
    (by simp only [List.length_cons]; omega)
    (by rw [ulit_toNat' _ (by omega), ulit_toNat' _ hlen]; exact hi)
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) r1
  have r3 := metaMorphoV1_1_block_8701 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r2
  by_cases hp : prev.toNat < curr
  · obtain ⟨k4, C4, r4⟩ := withdrawQueueIndex v
      (by simp only [List.length_cons]; omega)
      (by change prev.toNat < _; rw [hc]; exact hp)
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) r3
    obtain ⟨k5, C5, r5⟩ := metaMorphoV1_1_block_8711 (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r4
    have hm' := hm.scratch ⟨21⟩
    have hseen : memLoad ⟨128⟩ (wordAt0Mem ⟨21⟩ mem) = UInt256.ofNat curr := by
      simpa only [seenWords, List.length_map, hm.seenLength] using hm'.seen.length
    have hshift : UInt256.shiftLeft (⟨0⟩ : UInt256) (UInt256.ofNat 3) = ⟨0⟩ := rfl
    simp only [metaMorphoV1_1_block_8711_stack, hshift, wordShiftRight_zero] at r5
    obtain ⟨aw6, k6, C6, r6⟩ := memoryWordArrayIndex v
      (by simp only [List.length_cons]; omega)
      (by rw [hseen, ulit_toNat' _ hcur]; exact hp)
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) r5
    have haddr : UInt256.shiftLeft prev ⟨5⟩ + ⟨128⟩ + ⟨32⟩ =
        UInt256.ofNat (160 + 32 * prev.toNat) := by
      simpa only [u256_ofNat_toNat] using
        memoryWordArrayIndex_address 128 prev.toNat (by omega)
    change RD (deployedRuntime v) I g s0 ⟨8729⟩
      ((UInt256.shiftLeft prev ⟨5⟩ + ⟨128⟩ + ⟨32⟩) :: prev :: id ::
        UInt256.ofNat i :: UInt256.ofNat len :: data :: ⟨128⟩ :: UInt256.ofNat curr ::
        UInt256.ofNat (160 + 32 * curr) :: newData :: R)
      (wordAt0Mem ⟨21⟩ mem) aw6 out σ k6 C6 at r6
    rw [haddr] at r6
    have hps : prev.toNat < seen.length := by rw [hm.seenLength]; exact hp
    have hb := List.getElem?_eq_getElem hps
    have hload : memLoad (UInt256.ofNat (160 + 32 * prev.toNat)) (wordAt0Mem ⟨21⟩ mem) =
        if seen[prev.toNat] then ⟨1⟩ else ⟨0⟩ := by
      simpa only [seenWords, List.getElem_map] using hm'.seen.data prev.toNat hp
    cases he : seen[prev.toNat] with
    | true =>
        have r7 := metaMorphoV1_1_block_8729_taken (immWords := wordsOf (immStore v))
          (by simp only [List.length_cons]; omega)
          (by rw [hload, he]; decide)
          (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r6
        exact .inr (.inl ⟨hp, by simpa only [he] using hb,
          metaMorphoV1_1_block_8767 (immWords := wordsOf (immStore v))
            (by simp only [List.length_cons]; omega) r7⟩)
    | false =>
        have r7 := metaMorphoV1_1_block_8729_fallthrough (immWords := wordsOf (immStore v))
          (by simp only [List.length_cons]; omega) (by rw [hload, he]; rfl) r6
        have r8 := metaMorphoV1_1_block_8735 (immWords := wordsOf (immStore v))
          (by simp only [List.length_cons]; omega)
          (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r7
        obtain ⟨aw9, k9, C9, r9⟩ := memoryWordArrayIndex v
          (by simp only [List.length_cons]; omega)
          (by rw [hseen, ulit_toNat' _ hcur]; exact hp)
          (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) r8
        change RD (deployedRuntime v) I g s0 ⟨8749⟩
          ((UInt256.shiftLeft prev ⟨5⟩ + ⟨128⟩ + ⟨32⟩) :: ⟨1⟩ :: id ::
            UInt256.ofNat i :: ⟨1⟩ :: UInt256.ofNat len :: data :: ⟨128⟩ ::
            UInt256.ofNat curr :: UInt256.ofNat (160 + 32 * curr) :: newData :: R)
          (wordAt0Mem ⟨21⟩ mem) aw9 out σ k9 C9 at r9
        rw [haddr] at r9
        have r10 := metaMorphoV1_1_block_8749 (immWords := wordsOf (immStore v))
          (by simp only [List.length_cons]; omega)
          (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r9
        simp only [metaMorphoV1_1_block_8749_memory,
          ulit_toNat' (160 + 32 * prev.toNat) (by omega)] at r10
        have hq := hm'.queue.write_disjoint (off := 160 + 32 * prev.toNat)
          ⟨1⟩ (.inr (by omega))
        have hnew : memLoad (UInt256.ofNat (160 + 32 * curr))
            (writeWord (wordAt0Mem ⟨21⟩ mem) (160 + 32 * prev.toNat) ⟨1⟩) =
            UInt256.ofNat len := by simpa only [hm.queueLength] using hq.length
        dsimp only [Reasoning.Theory.writeWord] at hnew
        obtain ⟨aw11, k11, C11, r11⟩ := memoryWordArrayIndex v
          (by simp only [List.length_cons]; omega)
          (by rw [hnew, ulit_toNat' _ (by omega), ulit_toNat' _ hlen]; exact hi)
          (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) r10
        have hnewaddr := memoryWordArrayIndex_address (160 + 32 * curr) i (by omega)
        have hnewaddr' : 160 + 32 * curr + 32 + 32 * i = 192 + 32 * curr + 32 * i := by
          omega
        simp only [hnewaddr, hnewaddr'] at r11
        obtain ⟨aw12, k12, C12, r12⟩ := metaMorphoV1_1_block_8760_packed
          (immWords := wordsOf (immStore v))
          (by simp only [List.length_cons]; omega)
          (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r11
        refine .inr (.inr ⟨hp, by simpa only [he] using hb, aw12, k12, C12, ?_⟩)
        simpa only [metaMorphoV1_1_block_8760_stack, metaMorphoV1_1_block_8760_memory,
          metaMorphoV1_1_block_8749_memory, updateWithdrawQueueBuildMem, Reasoning.Theory.writeWord,
          show UInt256.ofNat i + ⟨1⟩ = UInt256.ofNat (i + 1) from ofNat_add_words _ _,
          ulit_toNat' (160 + 32 * prev.toNat) (by omega),
          ulit_toNat' (192 + 32 * curr + 32 * i) (by omega)] using r12
  · exact .inl ⟨by change curr ≤ prev.toNat; omega, withdrawQueueIndexRevert v
      (by simp only [List.length_cons]; omega)
      (by change (codeOwnerStorageWord I σ ⟨21⟩).toNat ≤ prev.toNat; rw [hc]; omega) r3⟩

end Benchmarks.Morpho.MetaMorphoV1_1
