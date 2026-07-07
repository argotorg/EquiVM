import Benchmarks.EAS.Attester.MultiRevokeMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.EAS.Attester.Immutables

namespace Benchmarks.EAS.Attester

def attesterMultiRevokeOuterInitFreeInv
    (I : ExecutionEnv) (n : Nat) (a : AttesterMultiOuterArrayInitState) : Prop :=
  a.remaining = UInt256.ofNat (n + 1) ∧
  n + 1 < UInt256.size ∧
  n + 1 ≤ (attesterFirstArrayLengthWord I).toNat ∧
  3 ≤ a.aw.toNat ∧
  a.aw.toNat * 32 < UInt256.size ∧
  64 + 32 ≤ (attesterMultiOuterArrayInitFreeWord a.mem a.aw).toNat ∧
  128 + 32 ≤ (attesterMultiOuterArrayInitFreeWord a.mem a.aw).toNat ∧
  (attesterMultiOuterArrayInitFreeWord a.mem a.aw).toNat + 64 * (n + 1) <
    UInt256.size ∧
  (attesterMultiOuterArrayInitFreeWord a.mem a.aw).toNat + 64 * (n + 1) +
      160 + 160 * solcMaxU64 < UInt256.size ∧
  64 + 32 ≤ a.slot.toNat ∧
  128 + 32 ≤ a.slot.toNat ∧
  a.slot.toNat + 32 * (n + 1) < UInt256.size ∧
  a.slot.toNat + 32 * (n + 1) + 32 < UInt256.size ∧
  a.mem.readWithPadding 128 32 =
    UInt256.toByteArray (attesterFirstArrayLengthWord I) ∧
  128 + 32 ≤ a.mem.size ∧
  (attesterMultiOuterArrayInitFreeWord a.mem a.aw).toNat =
    160 + 32 * (attesterFirstArrayLengthWord I).toNat +
      64 * ((attesterFirstArrayLengthWord I).toNat - (n + 1))

theorem attesterMultiRevokeOuterInitFreeInv_remaining
    {I : ExecutionEnv} {n : Nat} {a : AttesterMultiOuterArrayInitState}
    (hInv : attesterMultiRevokeOuterInitFreeInv I n a) :
    a.remaining = UInt256.ofNat (n + 1) :=
  hInv.1

theorem attesterMultiRevokeOuterInitFreeInv_bound
    {I : ExecutionEnv} {n : Nat} {a : AttesterMultiOuterArrayInitState}
    (hInv : attesterMultiRevokeOuterInitFreeInv I n a) :
    n + 1 < UInt256.size :=
  hInv.2.1

theorem attesterMultiRevokeOuterInitFreeInv_init
    {I : ExecutionEnv}
    (hlenNe : (attesterFirstArrayLengthWord I).toNat ≠ 0)
    (hlenMax : (attesterFirstArrayLengthWord I).toNat ≤ solcMaxU64) :
    attesterMultiRevokeOuterInitFreeInv I
      ((attesterFirstArrayLengthWord I).toNat - 1)
      { slot := ((⟨32⟩ : UInt256) + ⟨128⟩),
        remaining := attesterFirstArrayLengthWord I,
        mem := attesterMultiOuterArrayAllocMem I,
        aw := UInt256.ofNat 5 } := by
  let len := attesterFirstArrayLengthWord I
  have hsucc : len.toNat - 1 + 1 = len.toNat := by
    unfold len
    omega
  have hfreeToNat :
      (attesterMultiOuterArrayInitFreeWord
        (attesterMultiOuterArrayAllocMem I) (UInt256.ofNat 5)).toNat =
        160 + 32 * len.toNat := by
    unfold attesterMultiOuterArrayInitFreeWord len
    rw [attesterMultiOuterArrayAllocMem_mload64 I]
    rw [attesterMultiOuterArrayAllocEndWord_toNat (I := I) hlenMax]
  have hslotToNat : (((⟨32⟩ : UInt256) + ⟨128⟩).toNat) = 160 := by
    decide
  have hbound96 : 96 * len.toNat ≤ 96 * solcMaxU64 := by
    unfold len
    exact Nat.mul_le_mul_left 96 hlenMax
  have hbound32 : 32 * len.toNat ≤ 32 * solcMaxU64 := by
    unfold len
    exact Nat.mul_le_mul_left 32 hlenMax
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [len, hsucc] using (u256_ofNat_toNat len).symm
  · rw [hsucc]
    exact len.val.isLt
  · rw [hsucc]
  · change 3 ≤ (UInt256.ofNat 5).toNat
    decide
  · change (UInt256.ofNat 5).toNat * 32 < UInt256.size
    decide
  · rw [hfreeToNat]
    omega
  · rw [hfreeToNat]
    omega
  · rw [hfreeToNat, hsucc]
    norm_num [solcMaxU64, UInt256.size] at hbound96 ⊢
    omega
  · rw [hfreeToNat, hsucc]
    norm_num [solcMaxU64, UInt256.size] at hbound96 ⊢
    omega
  · rw [hslotToNat]
    omega
  · rw [hslotToNat]
  · rw [hslotToNat, hsucc]
    norm_num [solcMaxU64, UInt256.size] at hbound32 ⊢
    omega
  · rw [hslotToNat, hsucc]
    norm_num [solcMaxU64, UInt256.size] at hbound32 ⊢
    omega
  · exact attesterMultiOuterArrayAllocMem_read128 I
  · rw [attesterMultiOuterArrayAllocMem_size I]
  · rw [hfreeToNat, hsucc]
    unfold len
    omega

set_option maxHeartbeats 1000000 in
theorem attesterMultiRevokeOuterInitFreeInv_step
    {I : ExecutionEnv} {n : Nat} {a : AttesterMultiOuterArrayInitState}
    (hInv : attesterMultiRevokeOuterInitFreeInv I (n + 1) a) :
    attesterMultiRevokeOuterInitFreeInv I n
      (attesterMultiOuterArrayInitStepState a) := by
  rcases hInv with
    ⟨hrem, hbound, hleOld, hawGe, hawMul, hfreeGe, hfree160, hfreeBound, hfreeSpare,
      hslotGe, hslot160, hslotBound, hslotSpare, hread128, hmem128, hfreeExact⟩
  have hfree95 :
      (attesterMultiOuterArrayInitFreeWord a.mem a.aw).toNat + 95 < UInt256.size := by
    have hpos : 2 ≤ (n + 1) + 1 := by omega
    have hmul : 95 ≤ 64 * ((n + 1) + 1) := by nlinarith
    omega
  have hslot63 : a.slot.toNat + 63 < UInt256.size := by
    have hpos : 2 ≤ (n + 1) + 1 := by omega
    have hmul : 63 ≤ 32 * ((n + 1) + 1) := by nlinarith
    omega
  have hawStep :=
    attesterMultiOuterArrayInitStepAw_bounds
      (slot := a.slot) (mem := a.mem) (aw := a.aw)
      hawGe hawMul hfree95 hslot63
  have hfree32 :
      (attesterMultiOuterArrayInitFreeWord a.mem a.aw).toNat + 32 <
        UInt256.size := by
    omega
  have hoffsetToNat :
      (attesterMultiOuterArrayInitOffsetWord a.mem a.aw).toNat =
        (attesterMultiOuterArrayInitFreeWord a.mem a.aw).toNat + 32 := by
    unfold attesterMultiOuterArrayInitOffsetWord
    exact uadd_word_lit32_toNat
      (attesterMultiOuterArrayInitFreeWord a.mem a.aw) hfree32
  have hoffsetGe :
      64 + 32 ≤ (attesterMultiOuterArrayInitOffsetWord a.mem a.aw).toNat := by
    rw [hoffsetToNat]
    omega
  have hfree64 :
      (attesterMultiOuterArrayInitFreeWord a.mem a.aw).toNat + 64 <
        UInt256.size := by
    omega
  have hfreeStep :
      (attesterMultiOuterArrayInitFreeWord
          (attesterMultiOuterArrayInitStepMem a.slot a.mem a.aw)
          (attesterMultiOuterArrayInitStepAw a.slot a.mem a.aw)).toNat =
        (attesterMultiOuterArrayInitFreeWord a.mem a.aw).toNat + 64 :=
    attesterMultiOuterArrayInitStep_freeWord_toNat
      (slot := a.slot) (mem := a.mem) (aw := a.aw)
      hfreeGe hoffsetGe hslotGe hawStep.2 hawStep.1 hfree64
  have hslot32 : a.slot.toNat + 32 < UInt256.size := by
    omega
  have hslotStep :
      (((⟨32⟩ : UInt256) + a.slot).toNat) = a.slot.toNat + 32 :=
    uadd_lit32_toNat a.slot hslot32
  have hoffset160 :
      128 + 32 ≤ (attesterMultiOuterArrayInitOffsetWord a.mem a.aw).toNat := by
    rw [hoffsetToNat]
    omega
  have hread128Step :
      (attesterMultiOuterArrayInitStepMem a.slot a.mem a.aw).readWithPadding
          128 32 =
        UInt256.toByteArray (attesterFirstArrayLengthWord I) := by
    simpa using
      (attesterMultiOuterArrayInitStep_readWithPadding_nat
        (base := (⟨128⟩ : UInt256)) (slot := a.slot)
        (len := attesterFirstArrayLengthWord I) (mem := a.mem) (aw := a.aw)
        (by simpa using hmem128)
        (by simpa using hread128)
        (by decide)
        (by simpa using hfree160)
        (by simpa using hoffset160)
        (by simpa using hslot160))
  have hmem128Step :
      128 + 32 ≤ (attesterMultiOuterArrayInitStepMem a.slot a.mem a.aw).size :=
    le_trans hmem128 attesterMultiOuterArrayInitStep_size_ge
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change UInt256.sub a.remaining (⟨1⟩ : UInt256) = UInt256.ofNat (n + 1)
    rw [hrem]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      attester_u256_ofNat_succ_sub_one (n := n + 1) hbound
  · omega
  · omega
  · simpa [attesterMultiOuterArrayInitStepState] using hawStep.1
  · simpa [attesterMultiOuterArrayInitStepState] using hawStep.2
  · change 64 + 32 ≤
      (attesterMultiOuterArrayInitFreeWord
        (attesterMultiOuterArrayInitStepMem a.slot a.mem a.aw)
        (attesterMultiOuterArrayInitStepAw a.slot a.mem a.aw)).toNat
    rw [hfreeStep]
    omega
  · change 128 + 32 ≤
      (attesterMultiOuterArrayInitFreeWord
        (attesterMultiOuterArrayInitStepMem a.slot a.mem a.aw)
        (attesterMultiOuterArrayInitStepAw a.slot a.mem a.aw)).toNat
    rw [hfreeStep]
    omega
  · change
      (attesterMultiOuterArrayInitFreeWord
          (attesterMultiOuterArrayInitStepMem a.slot a.mem a.aw)
          (attesterMultiOuterArrayInitStepAw a.slot a.mem a.aw)).toNat +
          64 * (n + 1) <
        UInt256.size
    rw [hfreeStep]
    omega
  · change
      (attesterMultiOuterArrayInitFreeWord
          (attesterMultiOuterArrayInitStepMem a.slot a.mem a.aw)
          (attesterMultiOuterArrayInitStepAw a.slot a.mem a.aw)).toNat +
          64 * (n + 1) + 160 + 160 * solcMaxU64 <
        UInt256.size
    rw [hfreeStep]
    omega
  · change 64 + 32 ≤ (((⟨32⟩ : UInt256) + a.slot).toNat)
    rw [hslotStep]
    omega
  · change 128 + 32 ≤ (((⟨32⟩ : UInt256) + a.slot).toNat)
    rw [hslotStep]
    omega
  · change (((⟨32⟩ : UInt256) + a.slot).toNat) + 32 * (n + 1) <
      UInt256.size
    rw [hslotStep]
    omega
  · change (((⟨32⟩ : UInt256) + a.slot).toNat) + 32 * (n + 1) + 32 <
      UInt256.size
    rw [hslotStep]
    omega
  · simpa [attesterMultiOuterArrayInitStepState] using hread128Step
  · simpa [attesterMultiOuterArrayInitStepState] using hmem128Step
  · change
      (attesterMultiOuterArrayInitFreeWord
          (attesterMultiOuterArrayInitStepMem a.slot a.mem a.aw)
          (attesterMultiOuterArrayInitStepAw a.slot a.mem a.aw)).toNat =
        160 + 32 * (attesterFirstArrayLengthWord I).toNat +
          64 * ((attesterFirstArrayLengthWord I).toNat - (n + 1))
    rw [hfreeStep, hfreeExact]
    have hsub :
        (attesterFirstArrayLengthWord I).toNat - (n + 1) =
          (attesterFirstArrayLengthWord I).toNat - (n + 2) + 1 := by
      omega
    rw [hsub]
    nlinarith

theorem attesterX_multiRevokeOuterArrayInitProgressWithStateInvariant
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    (hprogress :
      ∃ k C, RD (patchedRuntime v) I g
        (initState cA gh bl σ σ₀ g A I) (⟨291⟩ : UInt256)
        [((⟨32⟩ : UInt256) + ⟨128⟩),
          attesterFirstArrayLengthWord I, ⟨128⟩, ⟨0⟩,
          attesterFirstArrayLengthWord I,
          attesterSecondArrayLengthWord I,
          (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
          attesterFirstArrayLengthWord I,
          (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
          ⟨97⟩, solcSelectorWord I]
        (attesterMultiOuterArrayAllocMem I) (UInt256.ofNat 5)
        ByteArray.empty (cA, σ) k C)
    (Inv : Nat → AttesterMultiOuterArrayInitState → Prop)
    (hremaining :
      ∀ n a, Inv n a → a.remaining = UInt256.ofNat (n + 1))
    (hbound : ∀ n a, Inv n a → n + 1 < UInt256.size)
    (hstep :
      ∀ n a, Inv (n + 1) a → Inv n (attesterMultiOuterArrayInitStepState a))
    (hinit :
      Inv ((attesterFirstArrayLengthWord I).toNat - 1)
        { slot := ((⟨32⟩ : UInt256) + ⟨128⟩),
          remaining := attesterFirstArrayLengthWord I,
          mem := attesterMultiOuterArrayAllocMem I,
          aw := UInt256.ofNat 5 }) :
    ∃ a' k C,
      a'.remaining = (⟨1⟩ : UInt256) ∧
      Inv 0 a' ∧
      RD (patchedRuntime v) I g
        (initState cA gh bl σ σ₀ g A I) (⟨335⟩ : UInt256)
        (attesterMultiRevokeOuterArrayInitExitStack I ⟨128⟩
          (attesterFirstArrayLengthWord I) a')
        (attesterMultiOuterArrayInitFinalMem a')
        (attesterMultiOuterArrayInitFinalAw a')
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k0, C0, rd0⟩ := hprogress
  exact attesterX_multiRevokeOuterArrayInitLoopWithStateInvariant
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) v
    (slot := ((⟨32⟩ : UInt256) + ⟨128⟩))
    (base := ⟨128⟩)
    (len := attesterFirstArrayLengthWord I)
    (mem := attesterMultiOuterArrayAllocMem I)
    (aw := UInt256.ofNat 5) (k := k0) (C := C0)
    Inv hremaining hbound hstep hinit rd0

theorem attesterX_multiRevokeOuterArrayInitProgressWithFreeInvariant
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    (hlenNe : (attesterFirstArrayLengthWord I).toNat ≠ 0)
    (hlenMax : (attesterFirstArrayLengthWord I).toNat ≤ solcMaxU64)
    (hprogress :
      ∃ k C, RD (patchedRuntime v) I g
        (initState cA gh bl σ σ₀ g A I) (⟨291⟩ : UInt256)
        [((⟨32⟩ : UInt256) + ⟨128⟩),
          attesterFirstArrayLengthWord I, ⟨128⟩, ⟨0⟩,
          attesterFirstArrayLengthWord I,
          attesterSecondArrayLengthWord I,
          (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
          attesterFirstArrayLengthWord I,
          (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
          ⟨97⟩, solcSelectorWord I]
        (attesterMultiOuterArrayAllocMem I) (UInt256.ofNat 5)
        ByteArray.empty (cA, σ) k C) :
    ∃ a' k C,
      a'.remaining = (⟨1⟩ : UInt256) ∧
      attesterMultiRevokeOuterInitFreeInv I 0 a' ∧
      RD (patchedRuntime v) I g
        (initState cA gh bl σ σ₀ g A I) (⟨335⟩ : UInt256)
        (attesterMultiRevokeOuterArrayInitExitStack I ⟨128⟩
          (attesterFirstArrayLengthWord I) a')
        (attesterMultiOuterArrayInitFinalMem a')
        (attesterMultiOuterArrayInitFinalAw a')
        ByteArray.empty (cA, σ) k C := by
  exact attesterX_multiRevokeOuterArrayInitProgressWithStateInvariant
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) v
    hprogress
    (Inv := attesterMultiRevokeOuterInitFreeInv I)
    (fun n a hInv => attesterMultiRevokeOuterInitFreeInv_remaining hInv)
    (fun n a hInv => attesterMultiRevokeOuterInitFreeInv_bound hInv)
    (fun n a hInv => attesterMultiRevokeOuterInitFreeInv_step hInv)
    (attesterMultiRevokeOuterInitFreeInv_init
      (I := I) hlenNe hlenMax)

theorem attesterX_multiRevokeOuterSourceLoopFirstGuardWithInvariant
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    (Inv : AttesterMultiOuterArrayInitState → Prop)
    (hlenNe : (attesterFirstArrayLengthWord I).toNat ≠ 0)
    (hprogress :
      ∃ a' k C,
        a'.remaining = (⟨1⟩ : UInt256) ∧
        Inv a' ∧
        RD (patchedRuntime v) I g
          (initState cA gh bl σ σ₀ g A I) (⟨335⟩ : UInt256)
          (attesterMultiRevokeOuterArrayInitExitStack I ⟨128⟩
            (attesterFirstArrayLengthWord I) a')
          (attesterMultiOuterArrayInitFinalMem a')
          (attesterMultiOuterArrayInitFinalAw a')
          ByteArray.empty (cA, σ) k C) :
    ∃ a' k C,
      a'.remaining = (⟨1⟩ : UInt256) ∧
      Inv a' ∧
      RD (patchedRuntime v) I g
        (initState cA gh bl σ σ₀ g A I) (⟨344⟩ : UInt256)
        (attesterMultiRevokeOuterArrayInitExitStack I ⟨128⟩
          (attesterFirstArrayLengthWord I) a')
        (attesterMultiOuterArrayInitFinalMem a')
        (attesterMultiOuterArrayInitFinalAw a')
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨a', k0, C0, hrem, hInv, rd0⟩ := hprogress
  obtain ⟨k1, C1, rd1⟩ :=
    attesterX_multiRevokeOuterSourceLoopFirstGuard
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (base := ⟨128⟩)
      (len := attesterFirstArrayLengthWord I)
      (mem := attesterMultiOuterArrayInitFinalMem a')
      (aw := attesterMultiOuterArrayInitFinalAw a')
      (k := k0) (C := C0) hlenNe
      (by
        simpa [attesterMultiRevokeOuterArrayInitExitStack] using rd0)
  exact ⟨a', k1, C1, hrem, hInv, by
    simpa [attesterMultiRevokeOuterArrayInitExitStack] using rd1⟩

theorem attesterX_multiRevokeOuterSecondArrayAccessOkWithInvariant
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    (Inv : AttesterMultiOuterArrayInitState → Prop)
    (hsecondLenNe : (attesterSecondArrayLengthWord I).toNat ≠ 0)
    (hprogress :
      ∃ a' k C,
        a'.remaining = (⟨1⟩ : UInt256) ∧
        Inv a' ∧
        RD (patchedRuntime v) I g
          (initState cA gh bl σ σ₀ g A I) (⟨344⟩ : UInt256)
          (attesterMultiRevokeOuterArrayInitExitStack I ⟨128⟩
            (attesterFirstArrayLengthWord I) a')
          (attesterMultiOuterArrayInitFinalMem a')
          (attesterMultiOuterArrayInitFinalAw a')
          ByteArray.empty (cA, σ) k C) :
    ∃ a' k C,
      a'.remaining = (⟨1⟩ : UInt256) ∧
      Inv a' ∧
      RD (patchedRuntime v) I g
        (initState cA gh bl σ σ₀ g A I) (⟨363⟩ : UInt256)
        [⟨0⟩, attesterSecondArrayLengthWord I,
          (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
          ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨0⟩, ⟨128⟩,
          attesterFirstArrayLengthWord I,
          attesterSecondArrayLengthWord I,
          (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
          attesterFirstArrayLengthWord I,
          (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
          ⟨97⟩, solcSelectorWord I]
        (attesterMultiOuterArrayInitFinalMem a')
        (attesterMultiOuterArrayInitFinalAw a')
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨a', k0, C0, hrem, hInv, rd0⟩ := hprogress
  obtain ⟨k1, C1, rd1⟩ :=
    attesterX_multiRevokeOuterSecondArrayAccessOk
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (base := ⟨128⟩)
      (len := attesterFirstArrayLengthWord I)
      (mem := attesterMultiOuterArrayInitFinalMem a')
      (aw := attesterMultiOuterArrayInitFinalAw a')
      (k := k0) (C := C0) hsecondLenNe
      (by
        simpa [attesterMultiRevokeOuterArrayInitExitStack] using rd0)
  exact ⟨a', k1, C1, hrem, hInv, rd1⟩

theorem attesterX_multiRevokeFirstInnerArrayDecoderEntryWithInvariant
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    (Inv : AttesterMultiOuterArrayInitState → Prop)
    (hprogress :
      ∃ a' k C,
        a'.remaining = (⟨1⟩ : UInt256) ∧
        Inv a' ∧
        RD (patchedRuntime v) I g
          (initState cA gh bl σ σ₀ g A I) (⟨363⟩ : UInt256)
          [⟨0⟩, attesterSecondArrayLengthWord I,
            (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
            ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨0⟩, ⟨128⟩,
            attesterFirstArrayLengthWord I,
            attesterSecondArrayLengthWord I,
            (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
            attesterFirstArrayLengthWord I,
            (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
            ⟨97⟩, solcSelectorWord I]
          (attesterMultiOuterArrayInitFinalMem a')
          (attesterMultiOuterArrayInitFinalAw a')
          ByteArray.empty (cA, σ) k C) :
    ∃ a' k C,
      a'.remaining = (⟨1⟩ : UInt256) ∧
      Inv a' ∧
      RD (patchedRuntime v) I g
        (initState cA gh bl σ σ₀ g A I) (⟨2353⟩ : UInt256)
        [(UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
          (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
          ⟨381⟩, ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨0⟩, ⟨128⟩,
          attesterFirstArrayLengthWord I,
          attesterSecondArrayLengthWord I,
          (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
          attesterFirstArrayLengthWord I,
          (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
          ⟨97⟩, solcSelectorWord I]
        (attesterMultiOuterArrayInitFinalMem a')
        (attesterMultiOuterArrayInitFinalAw a')
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨a', k0, C0, hrem, hInv, rd0⟩ := hprogress
  obtain ⟨k1, C1, rd1⟩ :=
    attesterX_multiRevokeFirstInnerArrayDecoderEntryFromOuterSecond
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (mem := attesterMultiOuterArrayInitFinalMem a')
      (aw := attesterMultiOuterArrayInitFinalAw a')
      (k := k0) (C := C0) rd0
  exact ⟨a', k1, C1, hrem, hInv, rd1⟩

theorem attesterX_multiRevokeFirstInnerArrayDecoderReturnWithInvariant
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    (Inv : AttesterMultiOuterArrayInitState → Prop)
    (hoffsetOk :
      UInt256.slt (attesterFirstInnerArrayOffsetWord I)
        (UInt256.add
          (UInt256.sub (UInt256.ofNat I.calldata.size)
            (attesterSecondArrayPayloadStartWord I))
          (UInt256.lnot (⟨30⟩ : UInt256))) = ⟨1⟩)
    (hlenOk :
      UInt256.gt (attesterFirstInnerArrayLengthWord I)
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩) = ⟨0⟩)
    (hpayloadOk :
      UInt256.sgt (attesterFirstInnerArrayStartWord I + ⟨32⟩)
        (UInt256.sub (UInt256.ofNat I.calldata.size)
          (UInt256.shiftLeft (attesterFirstInnerArrayLengthWord I) ⟨5⟩)) = ⟨0⟩)
    (hprogress :
      ∃ a' k C,
        a'.remaining = (⟨1⟩ : UInt256) ∧
        Inv a' ∧
        RD (patchedRuntime v) I g
          (initState cA gh bl σ σ₀ g A I) (⟨2353⟩ : UInt256)
          [(UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
            (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
            ⟨381⟩, ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨0⟩, ⟨128⟩,
            attesterFirstArrayLengthWord I,
            attesterSecondArrayLengthWord I,
            (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
            attesterFirstArrayLengthWord I,
            (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
            ⟨97⟩, solcSelectorWord I]
          (attesterMultiOuterArrayInitFinalMem a')
          (attesterMultiOuterArrayInitFinalAw a')
          ByteArray.empty (cA, σ) k C) :
    ∃ a' k C,
      a'.remaining = (⟨1⟩ : UInt256) ∧
      Inv a' ∧
      RD (patchedRuntime v) I g
        (initState cA gh bl σ σ₀ g A I) (⟨381⟩ : UInt256)
        [attesterFirstInnerArrayLengthWord I,
          attesterFirstInnerArrayStartWord I + ⟨32⟩,
          ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨0⟩, ⟨128⟩,
          attesterFirstArrayLengthWord I,
          attesterSecondArrayLengthWord I,
          attesterSecondArrayPayloadStartWord I,
          attesterFirstArrayLengthWord I,
          (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
          ⟨97⟩, solcSelectorWord I]
        (attesterMultiOuterArrayInitFinalMem a')
        (attesterMultiOuterArrayInitFinalAw a')
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨a', k0, C0, hrem, hInv, rd0⟩ := hprogress
  obtain ⟨k1, C1, rd1⟩ :=
    attesterX_multiRevokeFirstInnerArrayOffsetOk
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v hoffsetOk
      (mem := attesterMultiOuterArrayInitFinalMem a')
      (aw := attesterMultiOuterArrayInitFinalAw a')
      (k := k0) (C := C0)
      (by simpa [attesterSecondArrayPayloadStartWord] using rd0)
  obtain ⟨k2, C2, rd2⟩ :=
    attesterX_multiRevokeFirstInnerArrayLengthMaxOk
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v hlenOk
      (mem := attesterMultiOuterArrayInitFinalMem a')
      (aw := attesterMultiOuterArrayInitFinalAw a')
      (k := k1) (C := C1) rd1
  obtain ⟨k3, C3, rd3⟩ :=
    attesterX_multiRevokeFirstInnerArrayPayloadOkToReturn
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v hpayloadOk
      (mem := attesterMultiOuterArrayInitFinalMem a')
      (aw := attesterMultiOuterArrayInitFinalAw a')
      (k := k2) (C := C2) rd2
  exact ⟨a', k3, C3, hrem, hInv, rd3⟩

theorem attesterX_multiRevokeFirstInnerArrayNonemptyProgressWithInvariant
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    (Inv : AttesterMultiOuterArrayInitState → Prop)
    (hlenNe : attesterFirstInnerArrayLengthWord I ≠ ⟨0⟩)
    (hlenOk :
      UInt256.gt (attesterFirstInnerArrayLengthWord I)
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩) = ⟨0⟩)
    (hprogress :
      ∃ a' k C,
        a'.remaining = (⟨1⟩ : UInt256) ∧
        Inv a' ∧
        RD (patchedRuntime v) I g
          (initState cA gh bl σ σ₀ g A I) (⟨381⟩ : UInt256)
          [attesterFirstInnerArrayLengthWord I,
            attesterFirstInnerArrayStartWord I + ⟨32⟩,
            ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨0⟩, ⟨128⟩,
            attesterFirstArrayLengthWord I,
            attesterSecondArrayLengthWord I,
            attesterSecondArrayPayloadStartWord I,
            attesterFirstArrayLengthWord I,
            (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
            ⟨97⟩, solcSelectorWord I]
          (attesterMultiOuterArrayInitFinalMem a')
          (attesterMultiOuterArrayInitFinalAw a')
          ByteArray.empty (cA, σ) k C) :
    ∃ a' k C,
      a'.remaining = (⟨1⟩ : UInt256) ∧
      Inv a' ∧
      RD (patchedRuntime v) I g
        (initState cA gh bl σ σ₀ g A I) (⟨445⟩ : UInt256)
        [attesterFirstInnerArrayLengthWord I, ⟨0⟩,
          attesterFirstInnerArrayLengthWord I,
          attesterFirstInnerArrayLengthWord I,
          attesterFirstInnerArrayStartWord I + ⟨32⟩,
          ⟨0⟩, ⟨128⟩,
          attesterFirstArrayLengthWord I,
          attesterSecondArrayLengthWord I,
          attesterSecondArrayPayloadStartWord I,
          attesterFirstArrayLengthWord I,
          (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
          ⟨97⟩, solcSelectorWord I]
        (attesterMultiOuterArrayInitFinalMem a')
        (attesterMultiOuterArrayInitFinalAw a')
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨a', k0, C0, hrem, hInv, rd0⟩ := hprogress
  obtain ⟨k1, C1, rd1⟩ :=
    attesterX_multiRevokeFirstInnerArrayNonemptyOk
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v hlenNe
      (mem := attesterMultiOuterArrayInitFinalMem a')
      (aw := attesterMultiOuterArrayInitFinalAw a')
      (k := k0) (C := C0) rd0
  obtain ⟨k2, C2, rd2⟩ :=
    attesterX_multiRevokeFirstInnerArrayLengthAllocMaxOk
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v hlenOk
      (mem := attesterMultiOuterArrayInitFinalMem a')
      (aw := attesterMultiOuterArrayInitFinalAw a')
      (k := k1) (C := C1) rd1
  exact ⟨a', k2, C2, hrem, hInv, rd2⟩

theorem attesterX_multiRevokeFirstInnerArrayAllocProgressWithInvariant
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    (Inv : AttesterMultiOuterArrayInitState → Prop)
    (hlenNe : attesterFirstInnerArrayLengthWord I ≠ ⟨0⟩)
    (hprogress :
      ∃ a' k C,
        a'.remaining = (⟨1⟩ : UInt256) ∧
        Inv a' ∧
        RD (patchedRuntime v) I g
          (initState cA gh bl σ σ₀ g A I) (⟨445⟩ : UInt256)
          [attesterFirstInnerArrayLengthWord I, ⟨0⟩,
            attesterFirstInnerArrayLengthWord I,
            attesterFirstInnerArrayLengthWord I,
            attesterFirstInnerArrayStartWord I + ⟨32⟩,
            ⟨0⟩, ⟨128⟩,
            attesterFirstArrayLengthWord I,
            attesterSecondArrayLengthWord I,
            attesterSecondArrayPayloadStartWord I,
            attesterFirstArrayLengthWord I,
            (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
            ⟨97⟩, solcSelectorWord I]
          (attesterMultiOuterArrayInitFinalMem a')
          (attesterMultiOuterArrayInitFinalAw a')
          ByteArray.empty (cA, σ) k C) :
    ∃ a' k C,
      a'.remaining = (⟨1⟩ : UInt256) ∧
      Inv a' ∧
      RD (patchedRuntime v) I g
        (initState cA gh bl σ σ₀ g A I) (⟨475⟩ : UInt256)
        (((⟨32⟩ : UInt256) +
            attesterInnerArrayAllocFreeWord
              (attesterMultiOuterArrayInitFinalMem a')
              (attesterMultiOuterArrayInitFinalAw a')) ::
          attesterFirstInnerArrayLengthWord I ::
          attesterInnerArrayAllocFreeWord
            (attesterMultiOuterArrayInitFinalMem a')
            (attesterMultiOuterArrayInitFinalAw a') ::
          ⟨0⟩ ::
          attesterFirstInnerArrayLengthWord I ::
          attesterFirstInnerArrayLengthWord I ::
          (attesterFirstInnerArrayStartWord I + ⟨32⟩) ::
          [⟨0⟩, ⟨128⟩,
            attesterFirstArrayLengthWord I,
            attesterSecondArrayLengthWord I,
            attesterSecondArrayPayloadStartWord I,
            attesterFirstArrayLengthWord I,
            (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
            ⟨97⟩, solcSelectorWord I])
        (attesterInnerArrayAllocMem
          (attesterFirstInnerArrayLengthWord I)
          (attesterMultiOuterArrayInitFinalMem a')
          (attesterMultiOuterArrayInitFinalAw a'))
        (attesterInnerArrayAllocAw
          (attesterFirstInnerArrayLengthWord I)
          (attesterMultiOuterArrayInitFinalMem a')
          (attesterMultiOuterArrayInitFinalAw a'))
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨a', k0, C0, hrem, hInv, rd0⟩ := hprogress
  obtain ⟨k1, C1, rd1⟩ :=
    attesterX_multiRevokeFirstInnerArrayAllocToInitLoop
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (len := attesterFirstInnerArrayLengthWord I)
      (payload := attesterFirstInnerArrayStartWord I + ⟨32⟩)
      (tail := [⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I,
        attesterSecondArrayLengthWord I,
        attesterSecondArrayPayloadStartWord I,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨97⟩, solcSelectorWord I])
      (mem := attesterMultiOuterArrayInitFinalMem a')
      (aw := attesterMultiOuterArrayInitFinalAw a')
      (k := k0) (C := C0)
      (by simp) hlenNe (by simpa using rd0)
  exact ⟨a', k1, C1, hrem, hInv, rd1⟩

def attesterMultiRevokeInnerInitReadInv
    (I : ExecutionEnv) (a : AttesterMultiOuterArrayInitState)
    (n : Nat) (b : AttesterMultiRevokeInnerArrayInitState) : Prop :=
  let base :=
    attesterInnerArrayAllocFreeWord
      (attesterMultiOuterArrayInitFinalMem a)
      (attesterMultiOuterArrayInitFinalAw a)
  let len := attesterFirstInnerArrayLengthWord I
  attesterMultiRevokeOuterInitFreeInv I 0 a ∧
  b.remaining = UInt256.ofNat (n + 1) ∧
  n + 1 < UInt256.size ∧
  3 ≤ b.aw.toNat ∧
  b.aw.toNat * 32 < UInt256.size ∧
  b.mem.readWithPadding base.toNat 32 = UInt256.toByteArray len ∧
  base.toNat + 32 ≤ b.mem.size ∧
  64 + 32 ≤ base.toNat ∧
  base.toNat + 32 ≤ (attesterMultiOuterArrayInitFreeWord b.mem b.aw).toNat ∧
  (attesterMultiOuterArrayInitFreeWord b.mem b.aw).toNat +
      64 * (n + 1) < UInt256.size ∧
  (attesterMultiOuterArrayInitFreeWord b.mem b.aw).toNat +
      64 * (n + 1) + 64 * len.toNat + 96 < UInt256.size ∧
  base.toNat + 32 ≤ b.slot.toNat ∧
  b.slot.toNat + 32 * (n + 1) + 63 < UInt256.size ∧
  base.toNat + 32 + 32 * len.toNat + 63 < UInt256.size ∧
  b.mem.readWithPadding 128 32 =
    UInt256.toByteArray (attesterFirstArrayLengthWord I) ∧
  128 + 32 ≤ b.mem.size ∧
  128 + 32 ≤ base.toNat

theorem attesterMultiRevokeInnerInitReadInv_outer
    {I : ExecutionEnv} {a : AttesterMultiOuterArrayInitState}
    {n : Nat} {b : AttesterMultiRevokeInnerArrayInitState}
    (hInv : attesterMultiRevokeInnerInitReadInv I a n b) :
    attesterMultiRevokeOuterInitFreeInv I 0 a :=
  hInv.1

theorem attesterMultiRevokeInnerInitReadInv_remaining
    {I : ExecutionEnv} {a : AttesterMultiOuterArrayInitState}
    {n : Nat} {b : AttesterMultiRevokeInnerArrayInitState}
    (hInv : attesterMultiRevokeInnerInitReadInv I a n b) :
    b.remaining = UInt256.ofNat (n + 1) :=
  hInv.2.1

theorem attesterMultiRevokeInnerInitReadInv_bound
    {I : ExecutionEnv} {a : AttesterMultiOuterArrayInitState}
    {n : Nat} {b : AttesterMultiRevokeInnerArrayInitState}
    (hInv : attesterMultiRevokeInnerInitReadInv I a n b) :
    n + 1 < UInt256.size :=
  hInv.2.2.1

set_option maxHeartbeats 1000000 in
theorem attesterMultiRevokeInnerInitReadInv_init
    {I : ExecutionEnv} {a : AttesterMultiOuterArrayInitState}
    (hOuter : attesterMultiRevokeOuterInitFreeInv I 0 a)
    (hlenNe : (attesterFirstInnerArrayLengthWord I).toNat ≠ 0)
    (hlenMax : (attesterFirstInnerArrayLengthWord I).toNat ≤ solcMaxU64) :
    attesterMultiRevokeInnerInitReadInv I a
      ((attesterFirstInnerArrayLengthWord I).toNat - 1)
      { slot :=
          ((⟨32⟩ : UInt256) +
            attesterInnerArrayAllocFreeWord
              (attesterMultiOuterArrayInitFinalMem a)
              (attesterMultiOuterArrayInitFinalAw a)),
        remaining := attesterFirstInnerArrayLengthWord I,
        mem :=
          attesterInnerArrayAllocMem
            (attesterFirstInnerArrayLengthWord I)
            (attesterMultiOuterArrayInitFinalMem a)
            (attesterMultiOuterArrayInitFinalAw a),
        aw :=
          attesterInnerArrayAllocAw
            (attesterFirstInnerArrayLengthWord I)
            (attesterMultiOuterArrayInitFinalMem a)
            (attesterMultiOuterArrayInitFinalAw a) } := by
  let base :=
    attesterInnerArrayAllocFreeWord
      (attesterMultiOuterArrayInitFinalMem a)
      (attesterMultiOuterArrayInitFinalAw a)
  let len := attesterFirstInnerArrayLengthWord I
  rcases hOuter with
    ⟨harem, habound, hale, hawGe, hawMul, hbaseGe, hbase160, hbaseBound, hbaseSpare,
      hslotGe, hslot160, hslotBound, hslotSpare, houterRead128, houterMem128,
      _houterFreeExact⟩
  let oldFree := attesterMultiOuterArrayInitFreeWord a.mem a.aw
  have holdFreeGe : 64 + 32 ≤ oldFree.toNat := by
    simpa [oldFree] using hbaseGe
  have holdFree160 : 128 + 32 ≤ oldFree.toNat := by
    simpa [oldFree] using hbase160
  have holdFreeBound : oldFree.toNat + 64 < UInt256.size := by
    simpa [oldFree] using hbaseBound
  have holdFreeSpare : oldFree.toNat + 64 + 160 + 160 * solcMaxU64 <
      UInt256.size := by
    simpa [oldFree] using hbaseSpare
  have houterFree95 : oldFree.toNat + 95 < UInt256.size := by
    omega
  have houterSlot63 : a.slot.toNat + 63 < UInt256.size := by
    omega
  have houterStepAw :=
    attesterMultiOuterArrayInitStepAw_bounds
      (slot := a.slot) (mem := a.mem) (aw := a.aw)
      hawGe hawMul houterFree95 houterSlot63
  have holdFree32 : oldFree.toNat + 32 < UInt256.size := by
    omega
  have hoffsetToNat :
      (attesterMultiOuterArrayInitOffsetWord a.mem a.aw).toNat =
        oldFree.toNat + 32 := by
    unfold attesterMultiOuterArrayInitOffsetWord oldFree
    exact uadd_word_lit32_toNat
      (attesterMultiOuterArrayInitFreeWord a.mem a.aw) holdFree32
  have hoffsetGe :
      64 + 32 ≤ (attesterMultiOuterArrayInitOffsetWord a.mem a.aw).toNat := by
    rw [hoffsetToNat]
    omega
  have hfinalFreeToNat :
      (attesterMultiOuterArrayInitFreeWord
          (attesterMultiOuterArrayInitFinalMem a)
          (attesterMultiOuterArrayInitFinalAw a)).toNat =
        oldFree.toNat + 64 := by
    change
      (attesterMultiOuterArrayInitFreeWord
          (attesterMultiOuterArrayInitStepMem a.slot a.mem a.aw)
          (attesterMultiOuterArrayInitStepAw a.slot a.mem a.aw)).toNat =
        oldFree.toNat + 64
    exact attesterMultiOuterArrayInitStep_freeWord_toNat
      (slot := a.slot) (mem := a.mem) (aw := a.aw)
      holdFreeGe hoffsetGe hslotGe
      houterStepAw.2 houterStepAw.1 holdFreeBound
  have hbase63 : base.toNat + 63 < UInt256.size := by
    unfold base attesterInnerArrayAllocFreeWord
    rw [hfinalFreeToNat]
    omega
  have hbaseFinalGe : 64 + 32 ≤ base.toNat := by
    unfold base attesterInnerArrayAllocFreeWord
    rw [hfinalFreeToNat]
    omega
  have hbaseFinal160 : 128 + 32 ≤ base.toNat := by
    unfold base attesterInnerArrayAllocFreeWord
    rw [hfinalFreeToNat]
    omega
  have hoffset160 :
      128 + 32 ≤ (attesterMultiOuterArrayInitOffsetWord a.mem a.aw).toNat := by
    rw [hoffsetToNat]
    omega
  have houterFinalRead128 :
      (attesterMultiOuterArrayInitFinalMem a).readWithPadding 128 32 =
        UInt256.toByteArray (attesterFirstArrayLengthWord I) := by
    change
      (attesterMultiOuterArrayInitStepMem a.slot a.mem a.aw).readWithPadding
          128 32 =
        UInt256.toByteArray (attesterFirstArrayLengthWord I)
    simpa using
      (attesterMultiOuterArrayInitStep_readWithPadding_nat
        (base := (⟨128⟩ : UInt256)) (slot := a.slot)
        (len := attesterFirstArrayLengthWord I) (mem := a.mem) (aw := a.aw)
        (by simpa using houterMem128)
        (by simpa using houterRead128)
        (by decide)
        (by simpa using hbase160)
        (by simpa using hoffset160)
        (by simpa using hslot160))
  have houterFinalMem128 :
      128 + 32 ≤ (attesterMultiOuterArrayInitFinalMem a).size := by
    change 128 + 32 ≤
      (attesterMultiOuterArrayInitStepMem a.slot a.mem a.aw).size
    exact le_trans houterMem128 attesterMultiOuterArrayInitStep_size_ge
  have hallocAw :=
    attesterInnerArrayAllocAw_bounds
      (len := len)
      (mem := attesterMultiOuterArrayInitFinalMem a)
      (aw := attesterMultiOuterArrayInitFinalAw a)
      (by
        simpa [attesterMultiOuterArrayInitFinalAw] using houterStepAw.1)
      (by
        simpa [attesterMultiOuterArrayInitFinalAw] using houterStepAw.2)
      hbase63
  have hallocBound : base.toNat + 32 + 32 * len.toNat < UInt256.size := by
    unfold base len attesterInnerArrayAllocFreeWord
    rw [hfinalFreeToNat]
    have hmul : 32 * (attesterFirstInnerArrayLengthWord I).toNat ≤
        160 * solcMaxU64 := by
      have h32 : 32 * (attesterFirstInnerArrayLengthWord I).toNat ≤
          32 * solcMaxU64 := Nat.mul_le_mul_left 32 hlenMax
      nlinarith
    norm_num [solcMaxU64, UInt256.size] at hmul holdFreeSpare ⊢
    omega
  have hallocFreeToNat :
      (attesterInnerArrayAllocFreeWord
          (attesterInnerArrayAllocMem len
            (attesterMultiOuterArrayInitFinalMem a)
            (attesterMultiOuterArrayInitFinalAw a))
          (attesterInnerArrayAllocAw len
            (attesterMultiOuterArrayInitFinalMem a)
            (attesterMultiOuterArrayInitFinalAw a))).toNat =
        base.toNat + 32 + 32 * len.toNat := by
    unfold base
    exact attesterInnerArrayAllocMem_freeWord_toNat
      (len := len)
      (mem := attesterMultiOuterArrayInitFinalMem a)
      (aw := attesterMultiOuterArrayInitFinalAw a)
      hallocAw.2 hallocAw.1 hallocBound
  have hslotToNat :
      (((⟨32⟩ : UInt256) + base).toNat) = base.toNat + 32 := by
    exact uadd_lit32_toNat base (by omega)
  have hallocRead128 :
      (attesterInnerArrayAllocMem len
          (attesterMultiOuterArrayInitFinalMem a)
          (attesterMultiOuterArrayInitFinalAw a)).readWithPadding 128 32 =
        UInt256.toByteArray (attesterFirstArrayLengthWord I) := by
    simpa using
      (attesterInnerArrayAllocMem_readWithPadding_at_nat
        (readBase := (⟨128⟩ : UInt256)) (len := len)
        (readLen := attesterFirstArrayLengthWord I)
        (mem := attesterMultiOuterArrayInitFinalMem a)
        (aw := attesterMultiOuterArrayInitFinalAw a)
        (by simpa using houterFinalMem128)
        (by simpa using houterFinalRead128)
        (by decide)
        (by simpa [base] using hbaseFinal160))
  have hallocMem128 :
      128 + 32 ≤
        (attesterInnerArrayAllocMem len
          (attesterMultiOuterArrayInitFinalMem a)
          (attesterMultiOuterArrayInitFinalAw a)).size :=
    le_trans houterFinalMem128 attesterInnerArrayAllocMem_size_ge
  have hlenSucc : len.toNat - 1 + 1 = len.toNat := by
    unfold len
    omega
  unfold attesterMultiRevokeInnerInitReadInv
  simp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨harem, habound, hale, hawGe, hawMul, hbaseGe, hbase160, hbaseBound, hbaseSpare,
      hslotGe, hslot160, hslotBound, hslotSpare, houterRead128, houterMem128,
      _houterFreeExact⟩
  · simpa [len, hlenSucc] using (u256_ofNat_toNat len).symm
  · rw [hlenSucc]
    exact len.val.isLt
  · simpa [len] using hallocAw.1
  · simpa [len] using hallocAw.2
  · exact attesterInnerArrayAllocMem_readWithPadding_len_nat
      (len := len)
      (mem := attesterMultiOuterArrayInitFinalMem a)
      (aw := attesterMultiOuterArrayInitFinalAw a)
      hbaseFinalGe
  · exact attesterInnerArrayAllocMem_base_size
      (len := len)
      (mem := attesterMultiOuterArrayInitFinalMem a)
      (aw := attesterMultiOuterArrayInitFinalAw a)
  · exact hbaseFinalGe
  · rw [hallocFreeToNat]
    exact Nat.le_add_right _ _
  · change
      (attesterInnerArrayAllocFreeWord
          (attesterInnerArrayAllocMem len
            (attesterMultiOuterArrayInitFinalMem a)
            (attesterMultiOuterArrayInitFinalAw a))
          (attesterInnerArrayAllocAw len
            (attesterMultiOuterArrayInitFinalMem a)
            (attesterMultiOuterArrayInitFinalAw a))).toNat +
          64 * (len.toNat - 1 + 1) <
        UInt256.size
    rw [hallocFreeToNat, hlenSucc]
    unfold base len attesterInnerArrayAllocFreeWord
    rw [hfinalFreeToNat]
    have hmul : 96 * (attesterFirstInnerArrayLengthWord I).toNat ≤
        160 * solcMaxU64 := by
      have h96 : 96 * (attesterFirstInnerArrayLengthWord I).toNat ≤
          96 * solcMaxU64 := Nat.mul_le_mul_left 96 hlenMax
      exact le_trans h96
        (Nat.mul_le_mul_right solcMaxU64 (by norm_num : 96 ≤ 160))
    norm_num [solcMaxU64, UInt256.size] at hmul holdFreeSpare ⊢
    omega
  · change
      (attesterInnerArrayAllocFreeWord
          (attesterInnerArrayAllocMem len
            (attesterMultiOuterArrayInitFinalMem a)
            (attesterMultiOuterArrayInitFinalAw a))
          (attesterInnerArrayAllocAw len
            (attesterMultiOuterArrayInitFinalMem a)
            (attesterMultiOuterArrayInitFinalAw a))).toNat +
          64 * (len.toNat - 1 + 1) + 64 * len.toNat + 96 <
        UInt256.size
    rw [hallocFreeToNat, hlenSucc]
    unfold base len attesterInnerArrayAllocFreeWord
    rw [hfinalFreeToNat]
    have hmul : 160 * (attesterFirstInnerArrayLengthWord I).toNat ≤
        160 * solcMaxU64 :=
      Nat.mul_le_mul_left 160 hlenMax
    norm_num [solcMaxU64, UInt256.size] at hmul holdFreeSpare ⊢
    omega
  · rw [hslotToNat]
  · change (((⟨32⟩ : UInt256) + base).toNat) +
      32 * (len.toNat - 1 + 1) + 63 < UInt256.size
    rw [hslotToNat, hlenSucc]
    unfold base len attesterInnerArrayAllocFreeWord
    rw [hfinalFreeToNat]
    have hmul : 32 * (attesterFirstInnerArrayLengthWord I).toNat ≤
        160 * solcMaxU64 := by
      have h32 : 32 * (attesterFirstInnerArrayLengthWord I).toNat ≤
          32 * solcMaxU64 := Nat.mul_le_mul_left 32 hlenMax
      exact le_trans h32
        (Nat.mul_le_mul_right solcMaxU64 (by norm_num : 32 ≤ 160))
    norm_num [solcMaxU64, UInt256.size] at hmul holdFreeSpare ⊢
    omega
  · rw [hfinalFreeToNat]
    have hmul : 32 * (attesterFirstInnerArrayLengthWord I).toNat ≤
        160 * solcMaxU64 := by
      have h32 : 32 * (attesterFirstInnerArrayLengthWord I).toNat ≤
          32 * solcMaxU64 := Nat.mul_le_mul_left 32 hlenMax
      exact le_trans h32
        (Nat.mul_le_mul_right solcMaxU64 (by norm_num : 32 ≤ 160))
    norm_num [solcMaxU64, UInt256.size] at hmul holdFreeSpare ⊢
    omega
  · exact hallocRead128
  · exact hallocMem128
  · exact hbaseFinal160

theorem attesterMultiRevokeInnerInitReadInv_step
    {I : ExecutionEnv} {a : AttesterMultiOuterArrayInitState}
    {n : Nat} {b : AttesterMultiRevokeInnerArrayInitState}
    (hInv : attesterMultiRevokeInnerInitReadInv I a (n + 1) b) :
    attesterMultiRevokeInnerInitReadInv I a n
      (attesterMultiRevokeInnerArrayInitStepState b) := by
  let base :=
    attesterInnerArrayAllocFreeWord
      (attesterMultiOuterArrayInitFinalMem a)
      (attesterMultiOuterArrayInitFinalAw a)
  let len := attesterFirstInnerArrayLengthWord I
  rcases hInv with
    ⟨hOuter, hrem, hbound, hawGe, hawMul, hread, hmem, hbaseGe, hfreeGe,
      hfreeBound, hfreeSpare, hslotGe, hslotBound, hbaseSlot63, hread128,
      hmem128, hbase160⟩
  have hfree63 :
      (attesterMultiOuterArrayInitFreeWord b.mem b.aw).toNat + 63 < UInt256.size := by
    have hmul : 63 ≤ 64 * ((n + 1) + 1) := by nlinarith
    omega
  have hfree32 :
      (attesterMultiOuterArrayInitFreeWord b.mem b.aw).toNat + 32 < UInt256.size := by
    omega
  have hsecondToNat :
      (attesterMultiRevokeInnerArrayInitSecondZeroWord b.mem b.aw).toNat =
        (attesterMultiOuterArrayInitFreeWord b.mem b.aw).toNat + 32 :=
    attesterMultiRevokeInnerArrayInitSecondZeroWord_toNat
      (mem := b.mem) (aw := b.aw) hfree32
  have hsecondGe :
      base.toNat + 32 ≤
        (attesterMultiRevokeInnerArrayInitSecondZeroWord b.mem b.aw).toNat := by
    rw [hsecondToNat]
    exact le_trans hfreeGe (Nat.le_add_right _ _)
  have hfree160 :
      128 + 32 ≤ (attesterMultiOuterArrayInitFreeWord b.mem b.aw).toNat := by
    omega
  have hsecond160 :
      128 + 32 ≤
        (attesterMultiRevokeInnerArrayInitSecondZeroWord b.mem b.aw).toNat := by
    rw [hsecondToNat]
    omega
  have hslot160 : 128 + 32 ≤ b.slot.toNat := by
    omega
  have hfree160 :
      128 + 32 ≤ (attesterMultiOuterArrayInitFreeWord b.mem b.aw).toNat := by
    omega
  have hsecond160 :
      128 + 32 ≤
        (attesterMultiRevokeInnerArrayInitSecondZeroWord b.mem b.aw).toNat := by
    rw [hsecondToNat]
    omega
  have hslot160 : 128 + 32 ≤ b.slot.toNat := by
    omega
  have hsecond63 :
      (attesterMultiRevokeInnerArrayInitSecondZeroWord b.mem b.aw).toNat + 63 <
        UInt256.size := by
    rw [hsecondToNat]
    have hmul : 95 ≤ 64 * ((n + 1) + 1) := by nlinarith
    omega
  have hslot63 : b.slot.toNat + 63 < UInt256.size := by
    have hmul : 63 ≤ 32 * ((n + 1) + 1) := by nlinarith
    omega
  have hawStep :=
    attesterMultiRevokeInnerArrayInitStepAw_bounds
      (slot := b.slot) (mem := b.mem) (aw := b.aw)
      hawGe hawMul hfree63 hsecond63 hslot63
  have hreadStep :
      (attesterMultiRevokeInnerArrayInitStepMem b.slot b.mem b.aw).readWithPadding
          base.toNat 32 =
        UInt256.toByteArray len :=
    attesterMultiRevokeInnerArrayInitStep_readWithPadding_nat
      (base := base) (slot := b.slot) (len := len) (mem := b.mem) (aw := b.aw)
      hmem hread hbaseGe hfreeGe hsecondGe hslotGe
  have hmemStep :
      base.toNat + 32 ≤
        (attesterMultiRevokeInnerArrayInitStepMem b.slot b.mem b.aw).size :=
    attesterMultiRevokeInnerArrayInitStep_base_size
      (base := base) (slot := b.slot) (len := len) (mem := b.mem) (aw := b.aw)
      hmem
  have hread128Step :
      (attesterMultiRevokeInnerArrayInitStepMem b.slot b.mem b.aw).readWithPadding
          128 32 =
        UInt256.toByteArray (attesterFirstArrayLengthWord I) := by
    simpa using
      (attesterMultiRevokeInnerArrayInitStep_readWithPadding_nat
        (base := (⟨128⟩ : UInt256)) (slot := b.slot)
        (len := attesterFirstArrayLengthWord I) (mem := b.mem) (aw := b.aw)
        (by simpa using hmem128)
        (by simpa using hread128)
        (by decide)
        (by simpa using hfree160)
        (by simpa using hsecond160)
        (by simpa using hslot160))
  have hmem128Step :
      128 + 32 ≤ (attesterMultiRevokeInnerArrayInitStepMem b.slot b.mem b.aw).size :=
    le_trans hmem128 attesterMultiRevokeInnerArrayInitStep_size_ge
  have hfree96 :
      64 + 32 ≤ (attesterMultiOuterArrayInitFreeWord b.mem b.aw).toNat := by
    omega
  have hsecond96 :
      64 + 32 ≤ (attesterMultiRevokeInnerArrayInitSecondZeroWord b.mem b.aw).toNat := by
    omega
  have hslot96 : 64 + 32 ≤ b.slot.toNat := by
    omega
  have hfree64 :
      (attesterMultiOuterArrayInitFreeWord b.mem b.aw).toNat + 64 <
        UInt256.size := by
    omega
  have hfreeStepToNat :
      (attesterMultiOuterArrayInitFreeWord
          (attesterMultiRevokeInnerArrayInitStepMem b.slot b.mem b.aw)
          (attesterMultiRevokeInnerArrayInitStepAw b.slot b.mem b.aw)).toNat =
        (attesterMultiOuterArrayInitFreeWord b.mem b.aw).toNat + 64 :=
    attesterMultiRevokeInnerArrayInitStep_freeWord_toNat
      (slot := b.slot) (mem := b.mem) (aw := b.aw)
      hfree96 hsecond96 hslot96 hawStep.2 hawStep.1 hfree64
  have hslot32 : b.slot.toNat + 32 < UInt256.size := by
    omega
  have hslotStepToNat : (((⟨32⟩ : UInt256) + b.slot).toNat) =
      b.slot.toNat + 32 :=
    uadd_lit32_toNat b.slot hslot32
  unfold attesterMultiRevokeInnerInitReadInv
  simp only
  constructor
  · exact hOuter
  · constructor
    · change UInt256.sub b.remaining (⟨1⟩ : UInt256) = UInt256.ofNat (n + 1)
      rw [hrem]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        attester_u256_ofNat_succ_sub_one (n := n + 1) hbound
    · constructor
      · omega
      · constructor
        · simpa [attesterMultiRevokeInnerArrayInitStepState] using hawStep.1
        · constructor
          · simpa [attesterMultiRevokeInnerArrayInitStepState] using hawStep.2
          · constructor
            · simpa [base, len, attesterMultiRevokeInnerArrayInitStepState] using hreadStep
            · constructor
              · simpa [base, attesterMultiRevokeInnerArrayInitStepState] using hmemStep
              · constructor
                · exact hbaseGe
                · constructor
                  · change base.toNat + 32 ≤
                      (attesterMultiOuterArrayInitFreeWord
                        (attesterMultiRevokeInnerArrayInitStepMem b.slot b.mem b.aw)
                        (attesterMultiRevokeInnerArrayInitStepAw b.slot b.mem b.aw)).toNat
                    rw [hfreeStepToNat]
                    omega
                  · constructor
                    · change
                        (attesterMultiOuterArrayInitFreeWord
                          (attesterMultiRevokeInnerArrayInitStepMem b.slot b.mem b.aw)
                          (attesterMultiRevokeInnerArrayInitStepAw b.slot b.mem b.aw)).toNat +
                            64 * (n + 1) <
                          UInt256.size
                      rw [hfreeStepToNat]
                      omega
                    · constructor
                      · change
                          (attesterMultiOuterArrayInitFreeWord
                            (attesterMultiRevokeInnerArrayInitStepMem b.slot b.mem b.aw)
                            (attesterMultiRevokeInnerArrayInitStepAw b.slot b.mem b.aw)).toNat +
                              64 * (n + 1) + 64 * len.toNat + 96 <
                            UInt256.size
                        rw [hfreeStepToNat]
                        have hfreeSpareLen :
                            (attesterMultiOuterArrayInitFreeWord b.mem b.aw).toNat +
                                64 * ((n + 1) + 1) + 64 * len.toNat + 96 <
                              UInt256.size := by
                          simpa [len] using hfreeSpare
                        omega
                      · constructor
                        · change base.toNat + 32 ≤ (((⟨32⟩ : UInt256) + b.slot).toNat)
                          rw [hslotStepToNat]
                          exact le_trans hslotGe (Nat.le_add_right _ _)
                        · constructor
                          · change (((⟨32⟩ : UInt256) + b.slot).toNat) +
                              32 * (n + 1) + 63 <
                              UInt256.size
                            rw [hslotStepToNat]
                            omega
                          · constructor
                            · exact hbaseSlot63
                            · constructor
                              · simpa [attesterMultiRevokeInnerArrayInitStepState]
                                  using hread128Step
                              · constructor
                                · simpa [attesterMultiRevokeInnerArrayInitStepState]
                                    using hmem128Step
                                · exact hbase160

theorem attesterX_multiRevokeFirstInnerArrayInitProgressWithReadInvariant
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    (hlenNe : attesterFirstInnerArrayLengthWord I ≠ ⟨0⟩)
    (hlenMax : (attesterFirstInnerArrayLengthWord I).toNat ≤ solcMaxU64)
    (hprogress :
      ∃ a' k C,
        a'.remaining = (⟨1⟩ : UInt256) ∧
        attesterMultiRevokeOuterInitFreeInv I 0 a' ∧
        RD (patchedRuntime v) I g
          (initState cA gh bl σ σ₀ g A I) (⟨475⟩ : UInt256)
          (((⟨32⟩ : UInt256) +
              attesterInnerArrayAllocFreeWord
                (attesterMultiOuterArrayInitFinalMem a')
                (attesterMultiOuterArrayInitFinalAw a')) ::
            attesterFirstInnerArrayLengthWord I ::
            attesterInnerArrayAllocFreeWord
              (attesterMultiOuterArrayInitFinalMem a')
              (attesterMultiOuterArrayInitFinalAw a') ::
            ⟨0⟩ ::
            attesterFirstInnerArrayLengthWord I ::
            attesterFirstInnerArrayLengthWord I ::
            (attesterFirstInnerArrayStartWord I + ⟨32⟩) ::
            [⟨0⟩, ⟨128⟩,
              attesterFirstArrayLengthWord I,
              attesterSecondArrayLengthWord I,
              attesterSecondArrayPayloadStartWord I,
              attesterFirstArrayLengthWord I,
              (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
              ⟨97⟩, solcSelectorWord I])
          (attesterInnerArrayAllocMem
            (attesterFirstInnerArrayLengthWord I)
            (attesterMultiOuterArrayInitFinalMem a')
            (attesterMultiOuterArrayInitFinalAw a'))
          (attesterInnerArrayAllocAw
            (attesterFirstInnerArrayLengthWord I)
            (attesterMultiOuterArrayInitFinalMem a')
            (attesterMultiOuterArrayInitFinalAw a'))
          ByteArray.empty (cA, σ) k C) :
    ∃ a' b' k C,
      a'.remaining = (⟨1⟩ : UInt256) ∧
      attesterMultiRevokeOuterInitFreeInv I 0 a' ∧
      b'.remaining = (⟨1⟩ : UInt256) ∧
      attesterMultiRevokeInnerInitReadInv I a' 0 b' ∧
      RD (patchedRuntime v) I g
        (initState cA gh bl σ σ₀ g A I) (⟨518⟩ : UInt256)
        (attesterMultiRevokeInnerArrayInitExitStack I
          (attesterInnerArrayAllocFreeWord
            (attesterMultiOuterArrayInitFinalMem a')
            (attesterMultiOuterArrayInitFinalAw a'))
          (attesterFirstInnerArrayLengthWord I)
          (attesterFirstInnerArrayStartWord I + ⟨32⟩)
          b')
        (attesterMultiRevokeInnerArrayInitFinalMem b')
        (attesterMultiRevokeInnerArrayInitFinalAw b')
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨a', k0, C0, hrem, hOuter, rd0⟩ := hprogress
  have hlenNatNe : (attesterFirstInnerArrayLengthWord I).toNat ≠ 0 := by
    intro hzero
    apply hlenNe
    apply u256_inj
    simpa using hzero
  obtain ⟨b', k1, C1, hbrem, hInv, rd1⟩ :=
    attesterX_multiRevokeInnerArrayInitLoopWithStateInvariant
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (Inv := attesterMultiRevokeInnerInitReadInv I a')
      (slot :=
        ((⟨32⟩ : UInt256) +
          attesterInnerArrayAllocFreeWord
            (attesterMultiOuterArrayInitFinalMem a')
            (attesterMultiOuterArrayInitFinalAw a')))
      (base :=
        attesterInnerArrayAllocFreeWord
          (attesterMultiOuterArrayInitFinalMem a')
          (attesterMultiOuterArrayInitFinalAw a'))
      (len := attesterFirstInnerArrayLengthWord I)
      (payload := attesterFirstInnerArrayStartWord I + ⟨32⟩)
      (mem :=
        attesterInnerArrayAllocMem
          (attesterFirstInnerArrayLengthWord I)
          (attesterMultiOuterArrayInitFinalMem a')
          (attesterMultiOuterArrayInitFinalAw a'))
      (aw :=
        attesterInnerArrayAllocAw
          (attesterFirstInnerArrayLengthWord I)
          (attesterMultiOuterArrayInitFinalMem a')
          (attesterMultiOuterArrayInitFinalAw a'))
      (k := k0) (C := C0)
      (fun n b hInv => attesterMultiRevokeInnerInitReadInv_remaining hInv)
      (fun n b hInv => attesterMultiRevokeInnerInitReadInv_bound hInv)
      (fun n b hInv => attesterMultiRevokeInnerInitReadInv_step hInv)
      (attesterMultiRevokeInnerInitReadInv_init
        (I := I) (a := a') hOuter hlenNatNe hlenMax)
      (by simpa using rd0)
  exact ⟨a', b', k1, C1, hrem, hOuter, hbrem, hInv, rd1⟩

structure attesterMultiRevokeInnerCopyReadInv
    (I : ExecutionEnv) (a : AttesterMultiOuterArrayInitState)
    (b : AttesterMultiRevokeInnerArrayInitState)
    (n : Nat) (s : AttesterMultiRevokeInnerArrayCopyState) : Prop where
  init : attesterMultiRevokeInnerInitReadInv I a 0 b
  idx :
    s.idx =
      UInt256.ofNat ((attesterFirstInnerArrayLengthWord I).toNat - n)
  le : n ≤ (attesterFirstInnerArrayLengthWord I).toNat
  awGe : 3 ≤ s.aw.toNat
  awMul : s.aw.toNat * 32 < UInt256.size
  read :
    s.mem.readWithPadding
        (attesterInnerArrayAllocFreeWord
          (attesterMultiOuterArrayInitFinalMem a)
          (attesterMultiOuterArrayInitFinalAw a)).toNat 32 =
      UInt256.toByteArray (attesterFirstInnerArrayLengthWord I)
  memSize :
    (attesterInnerArrayAllocFreeWord
      (attesterMultiOuterArrayInitFinalMem a)
      (attesterMultiOuterArrayInitFinalAw a)).toNat + 32 ≤ s.mem.size
  baseGe :
    64 + 32 ≤
      (attesterInnerArrayAllocFreeWord
        (attesterMultiOuterArrayInitFinalMem a)
        (attesterMultiOuterArrayInitFinalAw a)).toNat
  base63 :
    (attesterInnerArrayAllocFreeWord
      (attesterMultiOuterArrayInitFinalMem a)
      (attesterMultiOuterArrayInitFinalAw a)).toNat + 63 < UInt256.size
  freeGe :
    (attesterInnerArrayAllocFreeWord
      (attesterMultiOuterArrayInitFinalMem a)
      (attesterMultiOuterArrayInitFinalAw a)).toNat + 32 ≤
      (attesterMultiRevokeInnerArrayCopyFreeWord s.mem s.aw).toNat
  freeSpare :
    (attesterMultiRevokeInnerArrayCopyFreeWord s.mem s.aw).toNat +
        64 * n + 96 < UInt256.size
  zeroGe :
    (attesterInnerArrayAllocFreeWord
      (attesterMultiOuterArrayInitFinalMem a)
      (attesterMultiOuterArrayInitFinalAw a)).toNat + 32 ≤
      (attesterMultiRevokeInnerArrayCopyZeroWord s.mem s.aw).toNat
  slotGe :
    (attesterInnerArrayAllocFreeWord
      (attesterMultiOuterArrayInitFinalMem a)
      (attesterMultiOuterArrayInitFinalAw a)).toNat + 32 ≤
      (attesterMultiRevokeInnerArrayCopySlotWord
        (attesterInnerArrayAllocFreeWord
          (attesterMultiOuterArrayInitFinalMem a)
          (attesterMultiOuterArrayInitFinalAw a)) s.idx).toNat
  slot63 :
    (attesterMultiRevokeInnerArrayCopySlotWord
      (attesterInnerArrayAllocFreeWord
        (attesterMultiOuterArrayInitFinalMem a)
        (attesterMultiOuterArrayInitFinalAw a)) s.idx).toNat + 63 <
      UInt256.size
  outerRead :
    s.mem.readWithPadding 128 32 =
      UInt256.toByteArray (attesterFirstArrayLengthWord I)
  outerMemSize : 128 + 32 ≤ s.mem.size
  base160 :
    128 + 32 ≤
      (attesterInnerArrayAllocFreeWord
        (attesterMultiOuterArrayInitFinalMem a)
        (attesterMultiOuterArrayInitFinalAw a)).toNat

theorem attesterMultiRevokeInnerCopyReadInv_idx
    {I : ExecutionEnv} {a : AttesterMultiOuterArrayInitState}
    {b : AttesterMultiRevokeInnerArrayInitState}
    {n : Nat} {s : AttesterMultiRevokeInnerArrayCopyState}
    (hInv : attesterMultiRevokeInnerCopyReadInv I a b n s) :
    s.idx =
      UInt256.ofNat ((attesterFirstInnerArrayLengthWord I).toNat - n) := by
  exact hInv.idx

theorem attesterMultiRevokeInnerCopyReadInv_le
    {I : ExecutionEnv} {a : AttesterMultiOuterArrayInitState}
    {b : AttesterMultiRevokeInnerArrayInitState}
    {n : Nat} {s : AttesterMultiRevokeInnerArrayCopyState}
    (hInv : attesterMultiRevokeInnerCopyReadInv I a b n s) :
    n ≤ (attesterFirstInnerArrayLengthWord I).toNat := by
  exact hInv.le

theorem attesterMultiRevokeInnerArrayCopyNextIdx_ofNat_progress
    {len n : Nat}
    (hle : n + 1 ≤ len) (hlen : len < UInt256.size) :
    attesterMultiRevokeInnerArrayCopyNextIdx
        (UInt256.ofNat (len - (n + 1))) =
      UInt256.ofNat (len - n) := by
  apply u256_inj
  unfold attesterMultiRevokeInnerArrayCopyNextIdx
  rw [uadd_toNat]
  rw [show (⟨1⟩ : UInt256).toNat = 1 by decide]
  rw [ulit_toNat' (len - (n + 1)) (by omega)]
  rw [ulit_toNat' (len - n) (by omega)]
  have hsum : 1 + (len - (n + 1)) = len - n := by omega
  rw [hsum]
  exact Nat.mod_eq_of_lt (by omega)

def attesterMultiRevokeInnerCopyInitState
    (b : AttesterMultiRevokeInnerArrayInitState) :
    AttesterMultiRevokeInnerArrayCopyState :=
  { idx := (⟨0⟩ : UInt256),
    mem := attesterMultiRevokeInnerArrayInitFinalMem b,
    aw := attesterMultiRevokeInnerArrayInitFinalAw b }

set_option maxHeartbeats 1000000 in
theorem attesterMultiRevokeInnerCopyReadInv_init
    {I : ExecutionEnv} {a : AttesterMultiOuterArrayInitState}
    {b : AttesterMultiRevokeInnerArrayInitState}
    (hInv : attesterMultiRevokeInnerInitReadInv I a 0 b) :
    attesterMultiRevokeInnerCopyReadInv I a b
      (attesterFirstInnerArrayLengthWord I).toNat
      (attesterMultiRevokeInnerCopyInitState b) := by
  let base :=
    attesterInnerArrayAllocFreeWord
      (attesterMultiOuterArrayInitFinalMem a)
      (attesterMultiOuterArrayInitFinalAw a)
  let len := attesterFirstInnerArrayLengthWord I
  have hInvOrig := hInv
  rcases hInv with
    ⟨hOuter, hrem, hbound, hawGe, hawMul, hread, hmem, hbaseGe, hfreeGe,
      hfreeBound, hfreeSpare, hslotGe, hslotBound, hbaseSlot63, hread128,
      hmem128, hbase160⟩
  have hfree63 :
      (attesterMultiOuterArrayInitFreeWord b.mem b.aw).toNat + 63 <
        UInt256.size := by
    omega
  have hfree32 :
      (attesterMultiOuterArrayInitFreeWord b.mem b.aw).toNat + 32 <
        UInt256.size := by
    omega
  have hsecondToNat :
      (attesterMultiRevokeInnerArrayInitSecondZeroWord b.mem b.aw).toNat =
        (attesterMultiOuterArrayInitFreeWord b.mem b.aw).toNat + 32 :=
    attesterMultiRevokeInnerArrayInitSecondZeroWord_toNat
      (mem := b.mem) (aw := b.aw) hfree32
  have hsecondGe :
      base.toNat + 32 ≤
        (attesterMultiRevokeInnerArrayInitSecondZeroWord b.mem b.aw).toNat := by
    rw [hsecondToNat]
    exact le_trans hfreeGe (Nat.le_add_right _ _)
  have hfree160 :
      128 + 32 ≤ (attesterMultiOuterArrayInitFreeWord b.mem b.aw).toNat := by
    omega
  have hsecond160 :
      128 + 32 ≤
        (attesterMultiRevokeInnerArrayInitSecondZeroWord b.mem b.aw).toNat := by
    rw [hsecondToNat]
    omega
  have hslot160 : 128 + 32 ≤ b.slot.toNat := by
    omega
  have hsecond63 :
      (attesterMultiRevokeInnerArrayInitSecondZeroWord b.mem b.aw).toNat + 63 <
        UInt256.size := by
    rw [hsecondToNat]
    omega
  have hslot63 : b.slot.toNat + 63 < UInt256.size := by
    omega
  have hawStep :=
    attesterMultiRevokeInnerArrayInitStepAw_bounds
      (slot := b.slot) (mem := b.mem) (aw := b.aw)
      hawGe hawMul hfree63 hsecond63 hslot63
  have hreadStep :
      (attesterMultiRevokeInnerArrayInitFinalMem b).readWithPadding
          base.toNat 32 =
        UInt256.toByteArray len := by
    change
      (attesterMultiRevokeInnerArrayInitStepMem b.slot b.mem b.aw).readWithPadding
          base.toNat 32 =
        UInt256.toByteArray len
    exact attesterMultiRevokeInnerArrayInitStep_readWithPadding_nat
      (base := base) (slot := b.slot) (len := len) (mem := b.mem) (aw := b.aw)
      hmem hread hbaseGe hfreeGe hsecondGe hslotGe
  have hmemStep :
      base.toNat + 32 ≤ (attesterMultiRevokeInnerArrayInitFinalMem b).size := by
    change base.toNat + 32 ≤
      (attesterMultiRevokeInnerArrayInitStepMem b.slot b.mem b.aw).size
    exact attesterMultiRevokeInnerArrayInitStep_base_size
      (base := base) (slot := b.slot) (len := len) (mem := b.mem) (aw := b.aw)
      hmem
  have hread128Step :
      (attesterMultiRevokeInnerArrayInitFinalMem b).readWithPadding 128 32 =
        UInt256.toByteArray (attesterFirstArrayLengthWord I) := by
    change
      (attesterMultiRevokeInnerArrayInitStepMem b.slot b.mem b.aw).readWithPadding
          128 32 =
        UInt256.toByteArray (attesterFirstArrayLengthWord I)
    simpa using
      (attesterMultiRevokeInnerArrayInitStep_readWithPadding_nat
        (base := (⟨128⟩ : UInt256)) (slot := b.slot)
        (len := attesterFirstArrayLengthWord I) (mem := b.mem) (aw := b.aw)
        (by simpa using hmem128)
        (by simpa using hread128)
        (by decide)
        (by simpa using hfree160)
        (by simpa using hsecond160)
        (by simpa using hslot160))
  have hmem128Step :
      128 + 32 ≤ (attesterMultiRevokeInnerArrayInitFinalMem b).size := by
    change 128 + 32 ≤
      (attesterMultiRevokeInnerArrayInitStepMem b.slot b.mem b.aw).size
    exact le_trans hmem128 attesterMultiRevokeInnerArrayInitStep_size_ge
  have hfree96 :
      64 + 32 ≤ (attesterMultiOuterArrayInitFreeWord b.mem b.aw).toNat := by
    omega
  have hsecond96 :
      64 + 32 ≤ (attesterMultiRevokeInnerArrayInitSecondZeroWord b.mem b.aw).toNat := by
    omega
  have hslot96 : 64 + 32 ≤ b.slot.toNat := by
    omega
  have hfree64 :
      (attesterMultiOuterArrayInitFreeWord b.mem b.aw).toNat + 64 <
        UInt256.size := by
    omega
  have hfreeStepToNat :
      (attesterMultiRevokeInnerArrayCopyFreeWord
          (attesterMultiRevokeInnerArrayInitFinalMem b)
          (attesterMultiRevokeInnerArrayInitFinalAw b)).toNat =
        (attesterMultiOuterArrayInitFreeWord b.mem b.aw).toNat + 64 := by
    change
      (attesterMultiOuterArrayInitFreeWord
          (attesterMultiRevokeInnerArrayInitStepMem b.slot b.mem b.aw)
          (attesterMultiRevokeInnerArrayInitStepAw b.slot b.mem b.aw)).toNat =
        (attesterMultiOuterArrayInitFreeWord b.mem b.aw).toNat + 64
    exact attesterMultiRevokeInnerArrayInitStep_freeWord_toNat
      (slot := b.slot) (mem := b.mem) (aw := b.aw)
      hfree96 hsecond96 hslot96 hawStep.2 hawStep.1 hfree64
  have hfreeFinalGe :
      base.toNat + 32 ≤
        (attesterMultiRevokeInnerArrayCopyFreeWord
          (attesterMultiRevokeInnerArrayInitFinalMem b)
          (attesterMultiRevokeInnerArrayInitFinalAw b)).toNat := by
    rw [hfreeStepToNat]
    omega
  have hfreeFinalSpare :
      (attesterMultiRevokeInnerArrayCopyFreeWord
          (attesterMultiRevokeInnerArrayInitFinalMem b)
          (attesterMultiRevokeInnerArrayInitFinalAw b)).toNat +
          64 * len.toNat + 96 < UInt256.size := by
    rw [hfreeStepToNat]
    have hfreeSpareLen :
        (attesterMultiOuterArrayInitFreeWord b.mem b.aw).toNat +
            64 * (0 + 1) + 64 * len.toNat + 96 <
          UInt256.size := by
      simpa [len] using hfreeSpare
    omega
  have hfreeFinal63 :
      (attesterMultiRevokeInnerArrayCopyFreeWord
          (attesterMultiRevokeInnerArrayInitFinalMem b)
          (attesterMultiRevokeInnerArrayInitFinalAw b)).toNat + 63 <
        UInt256.size := by
    omega
  have hfreeFinal32 :
      (attesterMultiRevokeInnerArrayCopyFreeWord
          (attesterMultiRevokeInnerArrayInitFinalMem b)
          (attesterMultiRevokeInnerArrayInitFinalAw b)).toNat + 32 <
        UInt256.size := by
    omega
  have hzeroToNat :
      (attesterMultiRevokeInnerArrayCopyZeroWord
          (attesterMultiRevokeInnerArrayInitFinalMem b)
          (attesterMultiRevokeInnerArrayInitFinalAw b)).toNat =
        (attesterMultiRevokeInnerArrayCopyFreeWord
          (attesterMultiRevokeInnerArrayInitFinalMem b)
          (attesterMultiRevokeInnerArrayInitFinalAw b)).toNat + 32 :=
    attesterMultiRevokeInnerArrayCopyZeroWord_toNat hfreeFinal32
  have hzeroGe :
      base.toNat + 32 ≤
        (attesterMultiRevokeInnerArrayCopyZeroWord
          (attesterMultiRevokeInnerArrayInitFinalMem b)
          (attesterMultiRevokeInnerArrayInitFinalAw b)).toNat := by
    rw [hzeroToNat]
    exact le_trans hfreeFinalGe (Nat.le_add_right _ _)
  have hzero63 :
      (attesterMultiRevokeInnerArrayCopyZeroWord
          (attesterMultiRevokeInnerArrayInitFinalMem b)
          (attesterMultiRevokeInnerArrayInitFinalAw b)).toNat + 63 <
        UInt256.size := by
    rw [hzeroToNat]
    omega
  have hbase63 : base.toNat + 63 < UInt256.size := by
    omega
  have hslot0Bound :
      base.toNat + 32 + 32 * (⟨0⟩ : UInt256).toNat + 63 < UInt256.size := by
    change base.toNat + 32 + 32 * 0 + 63 < UInt256.size
    omega
  have hslot0ToNat :
      (attesterMultiRevokeInnerArrayCopySlotWord base (⟨0⟩ : UInt256)).toNat =
        base.toNat + 32 + 32 * (⟨0⟩ : UInt256).toNat :=
    attesterMultiRevokeInnerArrayCopySlotWord_toNat (by omega)
  have hslot0Ge :
      base.toNat + 32 ≤
        (attesterMultiRevokeInnerArrayCopySlotWord base (⟨0⟩ : UInt256)).toNat :=
    attesterMultiRevokeInnerArrayCopySlotWord_above_base (by omega)
  have hslot0_63 :
      (attesterMultiRevokeInnerArrayCopySlotWord base (⟨0⟩ : UInt256)).toNat + 63 <
        UInt256.size := by
    rw [hslot0ToNat]
    omega
  have hidx0 :
      (⟨0⟩ : UInt256) = UInt256.ofNat (len.toNat - len.toNat) := by
    rw [show len.toNat - len.toNat = 0 by omega]
    apply u256_inj
    rfl
  exact
    { init := hInvOrig
      idx := by simpa [len] using hidx0
      le := le_rfl
      awGe := by
        change 3 ≤ (attesterMultiRevokeInnerArrayInitStepAw b.slot b.mem b.aw).toNat
        exact hawStep.1
      awMul := by
        change
          (attesterMultiRevokeInnerArrayInitStepAw b.slot b.mem b.aw).toNat * 32 <
            UInt256.size
        exact hawStep.2
      read := by
        change
          (attesterMultiRevokeInnerArrayInitFinalMem b).readWithPadding
              base.toNat 32 =
            UInt256.toByteArray len
        exact hreadStep
      memSize := by
        change base.toNat + 32 ≤ (attesterMultiRevokeInnerArrayInitFinalMem b).size
        exact hmemStep
      baseGe := by
        change 64 + 32 ≤ base.toNat
        exact hbaseGe
      base63 := by
        change base.toNat + 63 < UInt256.size
        exact hbase63
      freeGe := by
        change base.toNat + 32 ≤
          (attesterMultiRevokeInnerArrayCopyFreeWord
            (attesterMultiRevokeInnerArrayInitFinalMem b)
            (attesterMultiRevokeInnerArrayInitFinalAw b)).toNat
        exact hfreeFinalGe
      freeSpare := by
        change
          (attesterMultiRevokeInnerArrayCopyFreeWord
              (attesterMultiRevokeInnerArrayInitFinalMem b)
              (attesterMultiRevokeInnerArrayInitFinalAw b)).toNat +
              64 * len.toNat + 96 <
            UInt256.size
        exact hfreeFinalSpare
      zeroGe := by
        change base.toNat + 32 ≤
          (attesterMultiRevokeInnerArrayCopyZeroWord
            (attesterMultiRevokeInnerArrayInitFinalMem b)
            (attesterMultiRevokeInnerArrayInitFinalAw b)).toNat
        exact hzeroGe
      slotGe := by
        change base.toNat + 32 ≤
          (attesterMultiRevokeInnerArrayCopySlotWord base (⟨0⟩ : UInt256)).toNat
        exact hslot0Ge
      slot63 := by
        change
          (attesterMultiRevokeInnerArrayCopySlotWord base (⟨0⟩ : UInt256)).toNat + 63 <
            UInt256.size
        exact hslot0_63
      outerRead := by
        change (attesterMultiRevokeInnerArrayInitFinalMem b).readWithPadding 128 32 =
          UInt256.toByteArray (attesterFirstArrayLengthWord I)
        exact hread128Step
      outerMemSize := by
        change 128 + 32 ≤ (attesterMultiRevokeInnerArrayInitFinalMem b).size
        exact hmem128Step
      base160 := by
        change 128 + 32 ≤ base.toNat
        exact hbase160 }

set_option maxHeartbeats 1000000 in
theorem attesterMultiRevokeInnerCopyReadInv_step
    {I : ExecutionEnv} {a : AttesterMultiOuterArrayInitState}
    {b : AttesterMultiRevokeInnerArrayInitState}
    {n : Nat} {s : AttesterMultiRevokeInnerArrayCopyState}
    (hInv : attesterMultiRevokeInnerCopyReadInv I a b (n + 1) s) :
    attesterMultiRevokeInnerCopyReadInv I a b n
      (attesterMultiRevokeInnerArrayCopyStepState I
        (attesterInnerArrayAllocFreeWord
          (attesterMultiOuterArrayInitFinalMem a)
          (attesterMultiOuterArrayInitFinalAw a))
        (attesterFirstInnerArrayStartWord I + ⟨32⟩) s) := by
  let base :=
    attesterInnerArrayAllocFreeWord
      (attesterMultiOuterArrayInitFinalMem a)
      (attesterMultiOuterArrayInitFinalAw a)
  let len := attesterFirstInnerArrayLengthWord I
  let payload := attesterFirstInnerArrayStartWord I + ⟨32⟩
  have hInit := hInv.init
  rcases hInit with
    ⟨_hOuter, _hrem, _hbound, _hawGeInit, _hawMulInit, _hreadInit, _hmemInit,
      _hbaseGeInit, _hfreeGeInit, _hfreeBoundInit, _hfreeSpareInit, _hslotGeInit,
      _hslotBoundInit, hbaseSlot63, _hread128Init, _hmem128Init, _hbase160Init⟩
  have hbaseGe' : 64 + 32 ≤ base.toNat := by
    simpa [base] using hInv.baseGe
  have hbase63' : base.toNat + 63 < UInt256.size := by
    simpa [base] using hInv.base63
  have hfreeGe' :
      base.toNat + 32 ≤
        (attesterMultiRevokeInnerArrayCopyFreeWord s.mem s.aw).toNat := by
    simpa [base] using hInv.freeGe
  have hzeroGe' :
      base.toNat + 32 ≤
        (attesterMultiRevokeInnerArrayCopyZeroWord s.mem s.aw).toNat := by
    simpa [base] using hInv.zeroGe
  have hslotGe' :
      base.toNat + 32 ≤
        (attesterMultiRevokeInnerArrayCopySlotWord base s.idx).toNat := by
    simpa [base] using hInv.slotGe
  have hslot63' :
      (attesterMultiRevokeInnerArrayCopySlotWord base s.idx).toNat + 63 <
        UInt256.size := by
    simpa [base] using hInv.slot63
  have hbase160' : 128 + 32 ≤ base.toNat := by
    simpa [base] using hInv.base160
  have hfree160' :
      128 + 32 ≤ (attesterMultiRevokeInnerArrayCopyFreeWord s.mem s.aw).toNat := by
    omega
  have hzero160' :
      128 + 32 ≤ (attesterMultiRevokeInnerArrayCopyZeroWord s.mem s.aw).toNat := by
    omega
  have hslot160' :
      128 + 32 ≤ (attesterMultiRevokeInnerArrayCopySlotWord base s.idx).toNat := by
    omega
  have hnextIdx :
      attesterMultiRevokeInnerArrayCopyNextIdx s.idx =
        UInt256.ofNat (len.toNat - n) := by
    rw [hInv.idx]
    exact attesterMultiRevokeInnerArrayCopyNextIdx_ofNat_progress
      (len := len.toNat) (n := n) hInv.le len.val.isLt
  have hnextIdxToNat :
      (attesterMultiRevokeInnerArrayCopyNextIdx s.idx).toNat = len.toNat - n := by
    rw [hnextIdx]
    exact ulit_toNat' (len.toNat - n)
      (lt_of_le_of_lt (Nat.sub_le _ _) len.val.isLt)
  have hfree63 :
      (attesterMultiRevokeInnerArrayCopyFreeWord s.mem s.aw).toNat + 63 <
        UInt256.size := by
    have hspare := hInv.freeSpare
    omega
  have hfree32 :
      (attesterMultiRevokeInnerArrayCopyFreeWord s.mem s.aw).toNat + 32 <
        UInt256.size := by
    have hspare := hInv.freeSpare
    omega
  have hzeroToNat :
      (attesterMultiRevokeInnerArrayCopyZeroWord s.mem s.aw).toNat =
        (attesterMultiRevokeInnerArrayCopyFreeWord s.mem s.aw).toNat + 32 :=
    attesterMultiRevokeInnerArrayCopyZeroWord_toNat hfree32
  have hzero63 :
      (attesterMultiRevokeInnerArrayCopyZeroWord s.mem s.aw).toNat + 63 <
        UInt256.size := by
    rw [hzeroToNat]
    have hspare := hInv.freeSpare
    omega
  have hawStep :=
    attesterMultiRevokeInnerArrayCopyStepAw_bounds
      (I := I) (base := base) (payload := payload) (idx := s.idx)
      (mem := s.mem) (aw := s.aw)
      hInv.awGe hInv.awMul hbase63' hfree63 hzero63 hslot63'
  have hreadStep :
      (attesterMultiRevokeInnerArrayCopyStepMem I base payload s.idx s.mem s.aw).readWithPadding
          base.toNat 32 =
        UInt256.toByteArray len :=
    attesterMultiRevokeInnerArrayCopyStep_readWithPadding_nat
      (I := I) (base := base) (payload := payload) (idx := s.idx)
      (len := len) (mem := s.mem) (aw := s.aw)
      (by simpa [base] using hInv.memSize)
      (by simpa [base, len] using hInv.read)
      hbaseGe' hfreeGe' hzeroGe' hslotGe'
  have hmemStep :
      base.toNat + 32 ≤
        (attesterMultiRevokeInnerArrayCopyStepMem I base payload s.idx s.mem s.aw).size :=
    attesterMultiRevokeInnerArrayCopyStep_base_size
      (I := I) (base := base) (payload := payload) (idx := s.idx)
      (mem := s.mem) (aw := s.aw) hInv.memSize
  have hread128Step :
      (attesterMultiRevokeInnerArrayCopyStepMem I base payload s.idx s.mem s.aw).readWithPadding
          128 32 =
        UInt256.toByteArray (attesterFirstArrayLengthWord I) := by
    simpa using
      (attesterMultiRevokeInnerArrayCopyStep_readWithPadding_at_nat
        (I := I) (readBase := (⟨128⟩ : UInt256))
        (base := base) (payload := payload) (idx := s.idx)
        (len := attesterFirstArrayLengthWord I) (mem := s.mem) (aw := s.aw)
        (by simpa using hInv.outerMemSize)
        (by simpa using hInv.outerRead)
        (by decide)
        (by simpa using hfree160')
        (by simpa using hzero160')
        (by simpa using hslot160'))
  have hmem128Step :
      128 + 32 ≤
        (attesterMultiRevokeInnerArrayCopyStepMem I base payload s.idx s.mem s.aw).size :=
    le_trans hInv.outerMemSize attesterMultiRevokeInnerArrayCopyStep_size_ge
  have hfree96 :
      64 + 32 ≤ (attesterMultiRevokeInnerArrayCopyFreeWord s.mem s.aw).toNat := by
    have hbase96 : 64 + 32 ≤ base.toNat + 32 := by omega
    exact le_trans hbase96 hfreeGe'
  have hzero96 :
      64 + 32 ≤ (attesterMultiRevokeInnerArrayCopyZeroWord s.mem s.aw).toNat := by
    have hbase96 : 64 + 32 ≤ base.toNat + 32 := by omega
    exact le_trans hbase96 hzeroGe'
  have hslot96 :
      64 + 32 ≤ (attesterMultiRevokeInnerArrayCopySlotWord base s.idx).toNat := by
    have hbase96 : 64 + 32 ≤ base.toNat + 32 := by omega
    exact le_trans hbase96 hslotGe'
  have hfree64 :
      (attesterMultiRevokeInnerArrayCopyFreeWord s.mem s.aw).toNat + 64 <
        UInt256.size := by
    omega
  have hfreeStepToNat :
      (attesterMultiRevokeInnerArrayCopyFreeWord
          (attesterMultiRevokeInnerArrayCopyStepMem I base payload s.idx s.mem s.aw)
          (attesterMultiRevokeInnerArrayCopyStepAw I base payload s.idx s.mem s.aw)).toNat =
        (attesterMultiRevokeInnerArrayCopyFreeWord s.mem s.aw).toNat + 64 :=
    attesterMultiRevokeInnerArrayCopyStep_freeWord_toNat
      (I := I) (base := base) (payload := payload) (idx := s.idx)
      (mem := s.mem) (aw := s.aw)
      hfree96 hzero96 hslot96 hawStep.2 hawStep.1 hfree64
  have hfreeStepGe :
      base.toNat + 32 ≤
        (attesterMultiRevokeInnerArrayCopyFreeWord
          (attesterMultiRevokeInnerArrayCopyStepMem I base payload s.idx s.mem s.aw)
        (attesterMultiRevokeInnerArrayCopyStepAw I base payload s.idx s.mem s.aw)).toNat := by
    rw [hfreeStepToNat]
    exact le_trans hfreeGe' (Nat.le_add_right _ _)
  have hfreeStepSpare :
      (attesterMultiRevokeInnerArrayCopyFreeWord
          (attesterMultiRevokeInnerArrayCopyStepMem I base payload s.idx s.mem s.aw)
          (attesterMultiRevokeInnerArrayCopyStepAw I base payload s.idx s.mem s.aw)).toNat +
          64 * n + 96 < UInt256.size := by
    rw [hfreeStepToNat]
    have hspare := hInv.freeSpare
    omega
  have hfreeStep32 :
      (attesterMultiRevokeInnerArrayCopyFreeWord
          (attesterMultiRevokeInnerArrayCopyStepMem I base payload s.idx s.mem s.aw)
          (attesterMultiRevokeInnerArrayCopyStepAw I base payload s.idx s.mem s.aw)).toNat +
          32 < UInt256.size := by
    omega
  have hzeroStepToNat :
      (attesterMultiRevokeInnerArrayCopyZeroWord
          (attesterMultiRevokeInnerArrayCopyStepMem I base payload s.idx s.mem s.aw)
          (attesterMultiRevokeInnerArrayCopyStepAw I base payload s.idx s.mem s.aw)).toNat =
        (attesterMultiRevokeInnerArrayCopyFreeWord
          (attesterMultiRevokeInnerArrayCopyStepMem I base payload s.idx s.mem s.aw)
          (attesterMultiRevokeInnerArrayCopyStepAw I base payload s.idx s.mem s.aw)).toNat +
          32 :=
    attesterMultiRevokeInnerArrayCopyZeroWord_toNat hfreeStep32
  have hzeroStepGe :
      base.toNat + 32 ≤
        (attesterMultiRevokeInnerArrayCopyZeroWord
          (attesterMultiRevokeInnerArrayCopyStepMem I base payload s.idx s.mem s.aw)
          (attesterMultiRevokeInnerArrayCopyStepAw I base payload s.idx s.mem s.aw)).toNat := by
    rw [hzeroStepToNat]
    exact le_trans hfreeStepGe (Nat.le_add_right _ _)
  have hslotNextBound :
      base.toNat + 32 +
          32 * (attesterMultiRevokeInnerArrayCopyNextIdx s.idx).toNat + 63 <
        UInt256.size := by
    rw [hnextIdxToNat]
    have hbaseSlot63' :
        base.toNat + 32 + 32 * len.toNat + 63 < UInt256.size := by
      simpa [base, len] using hbaseSlot63
    have hleLen : 32 * (len.toNat - n) ≤ 32 * len.toNat :=
      Nat.mul_le_mul_left 32 (Nat.sub_le _ _)
    omega
  have hslotNextToNat :
      (attesterMultiRevokeInnerArrayCopySlotWord base
          (attesterMultiRevokeInnerArrayCopyNextIdx s.idx)).toNat =
        base.toNat + 32 +
          32 * (attesterMultiRevokeInnerArrayCopyNextIdx s.idx).toNat :=
    attesterMultiRevokeInnerArrayCopySlotWord_toNat (by omega)
  have hslotNextGe :
      base.toNat + 32 ≤
        (attesterMultiRevokeInnerArrayCopySlotWord base
          (attesterMultiRevokeInnerArrayCopyNextIdx s.idx)).toNat :=
    attesterMultiRevokeInnerArrayCopySlotWord_above_base (by omega)
  have hslotNext63 :
      (attesterMultiRevokeInnerArrayCopySlotWord base
          (attesterMultiRevokeInnerArrayCopyNextIdx s.idx)).toNat + 63 <
        UInt256.size := by
    rw [hslotNextToNat]
    exact hslotNextBound
  exact
    { init := hInv.init
      idx := by
        change attesterMultiRevokeInnerArrayCopyNextIdx s.idx =
          UInt256.ofNat ((attesterFirstInnerArrayLengthWord I).toNat - n)
        simpa [len] using hnextIdx
      le := by
        have hle := hInv.le
        omega
      awGe := by
        change 3 ≤ (attesterMultiRevokeInnerArrayCopyStepAw I base payload s.idx s.mem s.aw).toNat
        exact hawStep.1
      awMul := by
        change
          (attesterMultiRevokeInnerArrayCopyStepAw I base payload s.idx s.mem s.aw).toNat *
              32 <
            UInt256.size
        exact hawStep.2
      read := by
        change
          (attesterMultiRevokeInnerArrayCopyStepMem I base payload s.idx s.mem s.aw).readWithPadding
              base.toNat 32 =
            UInt256.toByteArray len
        exact hreadStep
      memSize := by
        change base.toNat + 32 ≤
          (attesterMultiRevokeInnerArrayCopyStepMem I base payload s.idx s.mem s.aw).size
        exact hmemStep
      baseGe := by
        change 64 + 32 ≤ base.toNat
        exact hInv.baseGe
      base63 := by
        change base.toNat + 63 < UInt256.size
        exact hInv.base63
      freeGe := by
        change base.toNat + 32 ≤
          (attesterMultiRevokeInnerArrayCopyFreeWord
            (attesterMultiRevokeInnerArrayCopyStepMem I base payload s.idx s.mem s.aw)
            (attesterMultiRevokeInnerArrayCopyStepAw I base payload s.idx s.mem s.aw)).toNat
        exact hfreeStepGe
      freeSpare := by
        change
          (attesterMultiRevokeInnerArrayCopyFreeWord
            (attesterMultiRevokeInnerArrayCopyStepMem I base payload s.idx s.mem s.aw)
            (attesterMultiRevokeInnerArrayCopyStepAw I base payload s.idx s.mem s.aw)).toNat +
              64 * n + 96 < UInt256.size
        exact hfreeStepSpare
      zeroGe := by
        change base.toNat + 32 ≤
          (attesterMultiRevokeInnerArrayCopyZeroWord
            (attesterMultiRevokeInnerArrayCopyStepMem I base payload s.idx s.mem s.aw)
            (attesterMultiRevokeInnerArrayCopyStepAw I base payload s.idx s.mem s.aw)).toNat
        exact hzeroStepGe
      slotGe := by
        change base.toNat + 32 ≤
          (attesterMultiRevokeInnerArrayCopySlotWord base
            (attesterMultiRevokeInnerArrayCopyNextIdx s.idx)).toNat
        exact hslotNextGe
      slot63 := by
        change
          (attesterMultiRevokeInnerArrayCopySlotWord base
            (attesterMultiRevokeInnerArrayCopyNextIdx s.idx)).toNat + 63 <
            UInt256.size
        exact hslotNext63
      outerRead := by
        change
          (attesterMultiRevokeInnerArrayCopyStepMem I base payload s.idx s.mem s.aw).readWithPadding
              128 32 =
            UInt256.toByteArray (attesterFirstArrayLengthWord I)
        exact hread128Step
      outerMemSize := by
        change 128 + 32 ≤
          (attesterMultiRevokeInnerArrayCopyStepMem I base payload s.idx s.mem s.aw).size
        exact hmem128Step
      base160 := by
        change 128 + 32 ≤ base.toNat
        exact hbase160' }

theorem attesterX_multiRevokeFirstInnerArrayCopyProgressWithStateInvariant
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    (hprogress :
      ∃ (a' : AttesterMultiOuterArrayInitState),
      ∃ (b' : AttesterMultiRevokeInnerArrayInitState),
      ∃ k C,
        a'.remaining = (⟨1⟩ : UInt256) ∧
        b'.remaining = (⟨1⟩ : UInt256) ∧
        RD (patchedRuntime v) I g
          (initState cA gh bl σ σ₀ g A I) (⟨518⟩ : UInt256)
          (attesterMultiRevokeInnerArrayInitExitStack I
            (attesterInnerArrayAllocFreeWord
              (attesterMultiOuterArrayInitFinalMem a')
              (attesterMultiOuterArrayInitFinalAw a'))
            (attesterFirstInnerArrayLengthWord I)
            (attesterFirstInnerArrayStartWord I + ⟨32⟩)
            b')
          (attesterMultiRevokeInnerArrayInitFinalMem b')
          (attesterMultiRevokeInnerArrayInitFinalAw b')
          ByteArray.empty (cA, σ) k C)
    (Inv :
      AttesterMultiOuterArrayInitState →
        AttesterMultiRevokeInnerArrayInitState → Nat →
          AttesterMultiRevokeInnerArrayCopyState → Prop)
    (hidx :
      ∀ a b n s, Inv a b n s →
        s.idx =
          UInt256.ofNat ((attesterFirstInnerArrayLengthWord I).toNat - n))
    (hle :
      ∀ a b n s, Inv a b n s →
        n ≤ (attesterFirstInnerArrayLengthWord I).toNat)
    (hload :
      ∀ a b n s, Inv a b n s →
        attesterMloadWord
          (attesterMultiRevokeInnerArrayCopyZeroMem I
            (attesterFirstInnerArrayStartWord I + ⟨32⟩) s.idx s.mem s.aw)
          (attesterMultiRevokeInnerArrayCopyZeroAw I
            (attesterFirstInnerArrayStartWord I + ⟨32⟩) s.idx s.mem s.aw)
          (attesterInnerArrayAllocFreeWord
            (attesterMultiOuterArrayInitFinalMem a)
            (attesterMultiOuterArrayInitFinalAw a)) =
          attesterFirstInnerArrayLengthWord I)
    (hstep :
      ∀ a b n s, Inv a b (n + 1) s →
        Inv a b n
          (attesterMultiRevokeInnerArrayCopyStepState I
            (attesterInnerArrayAllocFreeWord
              (attesterMultiOuterArrayInitFinalMem a)
              (attesterMultiOuterArrayInitFinalAw a))
            (attesterFirstInnerArrayStartWord I + ⟨32⟩) s))
    (hinit :
      ∀ a b,
        a.remaining = (⟨1⟩ : UInt256) →
        b.remaining = (⟨1⟩ : UInt256) →
        Inv a b (attesterFirstInnerArrayLengthWord I).toNat
          { idx := (⟨0⟩ : UInt256),
            mem := attesterMultiRevokeInnerArrayInitFinalMem b,
            aw := attesterMultiRevokeInnerArrayInitFinalAw b }) :
    ∃ (a' : AttesterMultiOuterArrayInitState),
    ∃ (b' : AttesterMultiRevokeInnerArrayInitState),
    ∃ (c' : AttesterMultiRevokeInnerArrayCopyState),
    ∃ k C,
      a'.remaining = (⟨1⟩ : UInt256) ∧
      b'.remaining = (⟨1⟩ : UInt256) ∧
      c'.idx = attesterFirstInnerArrayLengthWord I ∧
      Inv a' b' 0 c' ∧
      RD (patchedRuntime v) I g
        (initState cA gh bl σ σ₀ g A I) (⟨608⟩ : UInt256)
        (attesterMultiRevokeInnerArrayCopyStack
          (attesterInnerArrayAllocFreeWord
            (attesterMultiOuterArrayInitFinalMem a')
            (attesterMultiOuterArrayInitFinalAw a'))
          (attesterFirstInnerArrayLengthWord I)
          (attesterFirstInnerArrayStartWord I + ⟨32⟩)
          [⟨0⟩, ⟨128⟩,
            attesterFirstArrayLengthWord I,
            attesterSecondArrayLengthWord I,
            attesterSecondArrayPayloadStartWord I,
            attesterFirstArrayLengthWord I,
            (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
            ⟨97⟩, solcSelectorWord I]
          c')
        c'.mem c'.aw ByteArray.empty (cA, σ) k C := by
  obtain ⟨a', b', k0, C0, harem, hbrem, rd0⟩ := hprogress
  obtain ⟨c', k1, C1, hcidx, hInv, rd1⟩ :=
    attesterX_multiRevokeInnerArrayCopyLoopWithStateInvariant
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (base :=
        attesterInnerArrayAllocFreeWord
          (attesterMultiOuterArrayInitFinalMem a')
          (attesterMultiOuterArrayInitFinalAw a'))
      (len := attesterFirstInnerArrayLengthWord I)
      (payload := attesterFirstInnerArrayStartWord I + ⟨32⟩)
      (tail := [⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I,
        attesterSecondArrayLengthWord I,
        attesterSecondArrayPayloadStartWord I,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨97⟩, solcSelectorWord I])
      (mem := attesterMultiRevokeInnerArrayInitFinalMem b')
      (aw := attesterMultiRevokeInnerArrayInitFinalAw b')
      (k := k0) (C := C0) (by simp)
      (Inv := Inv a' b') (hidx a' b') (hle a' b') (hload a' b')
      (hstep a' b') (hinit a' b' harem hbrem)
      (by simpa [attesterMultiRevokeInnerArrayInitExitStack] using rd0)
  exact ⟨a', b', c', k1, C1, harem, hbrem, hcidx, hInv, rd1⟩

set_option maxHeartbeats 1000000 in
theorem attesterX_multiRevokeFirstInnerArrayCopyProgressWithReadStateInvariant
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    (hprogress :
      ∃ (a' : AttesterMultiOuterArrayInitState),
      ∃ (b' : AttesterMultiRevokeInnerArrayInitState),
      ∃ k C,
        a'.remaining = (⟨1⟩ : UInt256) ∧
        attesterMultiRevokeOuterInitFreeInv I 0 a' ∧
        b'.remaining = (⟨1⟩ : UInt256) ∧
        attesterMultiRevokeInnerInitReadInv I a' 0 b' ∧
        RD (patchedRuntime v) I g
          (initState cA gh bl σ σ₀ g A I) (⟨518⟩ : UInt256)
          (attesterMultiRevokeInnerArrayInitExitStack I
            (attesterInnerArrayAllocFreeWord
              (attesterMultiOuterArrayInitFinalMem a')
              (attesterMultiOuterArrayInitFinalAw a'))
            (attesterFirstInnerArrayLengthWord I)
            (attesterFirstInnerArrayStartWord I + ⟨32⟩)
            b')
          (attesterMultiRevokeInnerArrayInitFinalMem b')
          (attesterMultiRevokeInnerArrayInitFinalAw b')
          ByteArray.empty (cA, σ) k C) :
    ∃ (a' : AttesterMultiOuterArrayInitState),
    ∃ (b' : AttesterMultiRevokeInnerArrayInitState),
    ∃ (c' : AttesterMultiRevokeInnerArrayCopyState),
    ∃ k C,
      a'.remaining = (⟨1⟩ : UInt256) ∧
      attesterMultiRevokeOuterInitFreeInv I 0 a' ∧
      b'.remaining = (⟨1⟩ : UInt256) ∧
      attesterMultiRevokeInnerInitReadInv I a' 0 b' ∧
      c'.idx = attesterFirstInnerArrayLengthWord I ∧
      attesterMultiRevokeInnerCopyReadInv I a' b' 0 c' ∧
      RD (patchedRuntime v) I g
        (initState cA gh bl σ σ₀ g A I) (⟨608⟩ : UInt256)
        (attesterMultiRevokeInnerArrayCopyStack
          (attesterInnerArrayAllocFreeWord
            (attesterMultiOuterArrayInitFinalMem a')
            (attesterMultiOuterArrayInitFinalAw a'))
          (attesterFirstInnerArrayLengthWord I)
          (attesterFirstInnerArrayStartWord I + ⟨32⟩)
          [⟨0⟩, ⟨128⟩,
            attesterFirstArrayLengthWord I,
            attesterSecondArrayLengthWord I,
            attesterSecondArrayPayloadStartWord I,
            attesterFirstArrayLengthWord I,
            (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
            ⟨97⟩, solcSelectorWord I]
          c')
        c'.mem c'.aw ByteArray.empty (cA, σ) k C := by
  obtain ⟨a', b', k0, C0, harem, hOuter, hbrem, hInit, rd0⟩ := hprogress
  let base :=
    attesterInnerArrayAllocFreeWord
      (attesterMultiOuterArrayInitFinalMem a')
      (attesterMultiOuterArrayInitFinalAw a')
  let len := attesterFirstInnerArrayLengthWord I
  let payload := attesterFirstInnerArrayStartWord I + ⟨32⟩
  have hload :
      ∀ n s, attesterMultiRevokeInnerCopyReadInv I a' b' n s →
        attesterMloadWord
          (attesterMultiRevokeInnerArrayCopyZeroMem I payload s.idx s.mem s.aw)
          (attesterMultiRevokeInnerArrayCopyZeroAw I payload s.idx s.mem s.aw)
          base = len := by
    intro n s hInv
    have hfree96 :
        (attesterMultiRevokeInnerArrayCopyFreeWord s.mem s.aw).toNat + 96 <
          UInt256.size := by
      have hspare := hInv.freeSpare
      omega
    exact attesterMultiRevokeInnerArrayCopyZero_mloadLen_of_bounds_nat
      (I := I) (base := base) (payload := payload) (idx := s.idx)
      (len := len) (mem := s.mem) (aw := s.aw)
      (by simpa [base] using hInv.memSize)
      (by simpa [base, len] using hInv.read)
      hInv.awGe hInv.awMul hfree96
      (by simpa [base] using hInv.baseGe)
      (by simpa [base] using hInv.freeGe)
      (by simpa [base] using hInv.zeroGe)
  obtain ⟨c', k1, C1, hcidx, hCopyInv, rd1⟩ :=
    attesterX_multiRevokeInnerArrayCopyLoopWithStateInvariant
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (base := base)
      (len := len)
      (payload := payload)
      (tail := [⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I,
        attesterSecondArrayLengthWord I,
        attesterSecondArrayPayloadStartWord I,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨97⟩, solcSelectorWord I])
      (mem := attesterMultiRevokeInnerArrayInitFinalMem b')
      (aw := attesterMultiRevokeInnerArrayInitFinalAw b')
      (k := k0) (C := C0) (by simp)
      (Inv := attesterMultiRevokeInnerCopyReadInv I a' b')
      (fun n s hInv => attesterMultiRevokeInnerCopyReadInv_idx hInv)
      (fun n s hInv => attesterMultiRevokeInnerCopyReadInv_le hInv)
      hload
      (fun n s hInv => attesterMultiRevokeInnerCopyReadInv_step hInv)
      (attesterMultiRevokeInnerCopyReadInv_init hInit)
      (by
        simpa [base, len, payload, attesterMultiRevokeInnerArrayInitExitStack]
          using rd0)
  exact ⟨a', b', c', k1, C1, harem, hOuter, hbrem, hInit, hcidx, hCopyInv, rd1⟩

end Benchmarks.EAS.Attester
