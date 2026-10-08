import Benchmarks.EAS.Attester.MultiRevokeInnerTrace
import Benchmarks.EAS.Attester.MultiRevokeMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.EAS.Attester.Immutables attesterRuntimeBlocks

namespace Benchmarks.EAS.Attester

theorem multiRevokeOuterStore {words : String → UInt256} {I g s0 σ mem aw out k C R}
    {free base n i schemaPtr : Nat} {innerIndex dataBase innerN uidData secondData : UInt256}
    (h : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨672⟩
      ([innerIndex, dataBase, innerN, innerN, uidData, UInt256.ofNat i,
        UInt256.ofNat base, UInt256.ofNat n, UInt256.ofNat n, secondData,
        UInt256.ofNat n, UInt256.ofNat schemaPtr] ++ R) mem aw out σ k C)
    (hstack : R.length + 18 ≤ 1024) (hbase : 96 ≤ base)
    (hin : base + 32 ≤ mem.size) (hspan : base + 32 + 32 * n ≤ free)
    (hlen : memLoad (UInt256.ofNat base) mem = UInt256.ofNat n)
    (hptr : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat free)
    (hi : i < n) (hf : free + 64 < UInt256.size)
    (hcd : schemaPtr + 32 * n < UInt256.size) :
    ∃ aw' k' C', RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨367⟩
      ([UInt256.ofNat (i + 1), UInt256.ofNat base, UInt256.ofNat n, UInt256.ofNat n,
        secondData, UInt256.ofNat n, UInt256.ofNat schemaPtr] ++ R)
      (pairSlotMemory mem free (base + 32 + 32 * i)
        (calldataWord I.calldata (schemaPtr + 32 * i)) dataBase) aw' out σ k' C' := by
  have hnfit : n < UInt256.size := by omega
  have hifit : i < UInt256.size := by omega
  have hffit : free < UInt256.size := by omega
  have hbfit : base < UInt256.size := by omega
  have hf32 : 32 + free < UInt256.size := by omega
  have hdifit : 32 * i + schemaPtr < UInt256.size := by omega
  have hbifit : 32 + 32 * i + base < UInt256.size := by omega
  have hlt : UInt256.lt (UInt256.ofNat i) (UInt256.ofNat n) = ⟨1⟩ :=
    ult_one (by rw [ulit_toNat' _ hifit, ulit_toNat' _ hnfit]; exact hi)
  obtain ⟨aw', k', C', h'⟩ := attesterRuntime_block_672_taken_packed (R := R) hstack
    (by rw [hlt]; decide) (by rw [attesterRuntime_validJumps]; native_decide) h
  simp only [attesterRuntime_block_672_taken_stack, attesterRuntime_block_672_taken_memory,
    hptr, ofNat_add_words] at h'
  have hfields : attesterRuntime_block_702_taken_memory (ee := I)
      (mem := (UInt256.ofNat (64 + free)).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)
      (x0 := UInt256.ofNat i) (x2 := UInt256.ofNat schemaPtr)
      (x3 := UInt256.ofNat free) (x5 := dataBase) =
      pairStructMemory mem free (calldataWord I.calldata (schemaPtr + 32 * i)) dataBase := by
    simp only [attesterRuntime_block_702_taken_memory, ofNat_mul_words, ofNat_add_words,
      ulit_toNat' _ hffit, ulit_toNat' _ hf32, ulit_toNat' _ hdifit,
      pairStructMemory, writeCascade, Reasoning.Theory.writeWord]
    simp only [Nat.add_comm]
    rfl
  have hload : memLoad (UInt256.ofNat base)
      (pairStructMemory mem free (calldataWord I.calldata (schemaPtr + 32 * i)) dataBase) =
      UInt256.ofNat n :=
    ((pairStructMemory_prefix _ _ _ _).load_preserved hbase (by omega) hin hbfit).trans hlen
  obtain ⟨aw'', k'', C'', h''⟩ := attesterRuntime_block_702_taken_packed
    (x0 := UInt256.ofNat i) (x1 := UInt256.ofNat n) (x2 := UInt256.ofNat schemaPtr)
    (x3 := UInt256.ofNat free) (x4 := UInt256.ofNat free) (x5 := dataBase)
    (x9 := UInt256.ofNat i) (x10 := UInt256.ofNat base)
    (by simp only [List.length_cons]; omega)
    (by change UInt256.lt (UInt256.ofNat i)
          (memLoad (UInt256.ofNat base) (attesterRuntime_block_702_taken_memory
            (ee := I) (mem := (UInt256.ofNat (64 + free)).toByteArray.write 0 mem
              (UInt256.ofNat 64).toNat 32) (x0 := UInt256.ofNat i)
            (x2 := UInt256.ofNat schemaPtr) (x3 := UInt256.ofNat free) (x5 := dataBase))) ≠ _
        rw [hfields, hload, hlt]; decide)
    (by rw [attesterRuntime_validJumps]; native_decide) h'
  simp only [attesterRuntime_block_702_taken_stack, hfields] at h''
  obtain ⟨awf, kf, Cf, hf'⟩ := attesterRuntime_block_736_packed
    (by simp only [List.length_cons]; omega)
    (by rw [attesterRuntime_validJumps]; native_decide) h''
  simp only [attesterRuntime_block_736_stack, attesterRuntime_block_736_memory,
    ofNat_mul_words, ofNat_add_words, ulit_toNat' _ hbifit] at hf'
  refine ⟨awf, kf, Cf, ?_⟩
  simpa only [pairStructMemory, pairSlotMemory, writeCascade, Reasoning.Theory.writeWord,
    Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hf'

theorem multiRevokeRowBuild {words : String → UInt256} {I g s0 σ mem aw out k C R}
    {free base n i schemaPtr uidPtr m : Nat} {secondData : UInt256}
    (h : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨479⟩
      ([UInt256.ofNat m, UInt256.ofNat m, UInt256.ofNat uidPtr, UInt256.ofNat i,
        UInt256.ofNat base, UInt256.ofNat n, UInt256.ofNat n, secondData,
        UInt256.ofNat n, UInt256.ofNat schemaPtr] ++ R) mem aw out σ k C)
    (hstack : R.length + 19 ≤ 1024) (hbase : 96 ≤ base)
    (hin : base + 32 ≤ mem.size) (hspan : base + 32 + 32 * n ≤ free)
    (hlen : memLoad (UInt256.ofNat base) mem = UInt256.ofNat n)
    (hptr : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat free)
    (hi : i < n) (hm : 0 < m) (hm64 : m ≤ solcMaxU64)
    (hf : free + 96 + 160 * m < UInt256.size)
    (hcd : schemaPtr + 32 * n < UInt256.size) (huid : uidPtr + 32 * m < UInt256.size) :
    ∃ aw' k' C', RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨367⟩
      ([UInt256.ofNat (i + 1), UInt256.ofNat base, UInt256.ofNat n, UInt256.ofNat n,
        secondData, UInt256.ofNat n, UInt256.ofNat schemaPtr] ++ R)
      (multiRevokeRowMemory mem I.calldata free base i schemaPtr uidPtr m) aw' out σ k' C' := by
  have hfree : 96 ≤ free := by omega
  have hfreefit : free < UInt256.size := by omega
  obtain ⟨aw', k', C', h'⟩ := pairArrayAllocate479
    (R := UInt256.ofNat m :: UInt256.ofNat uidPtr :: UInt256.ofNat i :: UInt256.ofNat base ::
      UInt256.ofNat n :: UInt256.ofNat n :: secondData :: UInt256.ofNat n ::
      UInt256.ofNat schemaPtr :: R) h
    (by simp only [List.length_cons]; omega)
    hfree hptr hm hm64 (by omega)
  obtain ⟨aw'', k'', C'', h''⟩ := multiRevokeInnerRun
    (R := UInt256.ofNat i :: UInt256.ofNat base :: UInt256.ofNat n :: UInt256.ofNat n ::
      secondData :: UInt256.ofNat n :: UInt256.ofNat schemaPtr :: R) h'
    (by simp only [List.length_cons]; omega)
    hfree (by rw [pairArrayMemory_size hfree]; omega) (by omega)
    (pairArrayMemory_length hfree hfreefit) (pairArrayMemory_freePtr hfree)
    (show 0 + m = m from Nat.zero_add _) (by omega) huid
  change RD _ _ _ _ _ _ (revokeDataMemory mem I.calldata free uidPtr m) _ _ _ _ _ at h''
  have hp := revokeDataMemory_prefix mem I.calldata free uidPtr m
  have hsize := hp.size
  have hl := (hp.load_preserved hbase (by omega) hin (by omega)).trans hlen
  obtain ⟨awf, kf, Cf, hf'⟩ := multiRevokeOuterStore h'' (by omega) hbase
    (by omega) (by omega) hl (revokeDataMemory_freePtr hfree) hi (by omega) hcd
  exact ⟨awf, kf, Cf, hf'⟩

end Benchmarks.EAS.Attester
