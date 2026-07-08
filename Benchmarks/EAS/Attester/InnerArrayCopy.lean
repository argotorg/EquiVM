import Benchmarks.EAS.Attester.InnerArrayInit

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.EAS.Attester.Immutables

namespace Benchmarks.EAS.Attester

theorem attesterMloadWord_of_readWithPadding
    {mem : ByteArray} {aw base len : UInt256}
    (hmem : base.toNat + 32 ≤ mem.size)
    (haw : ¬ base ≥ aw * ⟨32⟩)
    (hread : mem.readWithPadding base.toNat 32 = UInt256.toByteArray len) :
    attesterMloadWord mem aw base = len := by
  unfold attesterMloadWord
  rw [if_neg (not_or.mpr ⟨by omega, haw⟩), hread,
    fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]

theorem attesterMloadWord_writeWord_preserved
    {mem : ByteArray} {aw base len writeOff writeVal : UInt256}
    (hmem : base.toNat + 32 ≤ mem.size)
    (haw : ¬ base ≥ aw * ⟨32⟩)
    (hread : mem.readWithPadding base.toNat 32 = UInt256.toByteArray len)
    (hgap : writeOff.toNat - mem.size < USize.size)
    (hdisj :
      (base.toNat + 32 ≤ writeOff.toNat ∧ base.toNat + 32 ≤ mem.size) ∨
      (writeOff.toNat + 32 ≤ base.toNat ∧ base.toNat + 32 ≤ mem.size)) :
    attesterMloadWord
        ((UInt256.toByteArray writeVal).write 0 mem writeOff.toNat 32)
        aw base = len := by
  apply attesterMloadWord_of_readWithPadding
  · have hsize := writeWord_size mem writeOff.toNat writeVal hgap
    unfold Reasoning.Theory.writeWord at hsize
    rw [hsize]
    omega
  · exact haw
  · change (Reasoning.Theory.writeWord mem writeOff.toNat writeVal).readWithPadding base.toNat 32 =
      UInt256.toByteArray len
    rw [writeWord_read_preserved_len mem writeOff.toNat base.toNat 32 writeVal
      hgap hdisj (by norm_num) (by norm_num), hread]

theorem attesterReadWithPadding_writeWord_preserved_above
    {mem : ByteArray} {base writeOff : Nat} {len writeVal : UInt256}
    (hmem : base + 32 ≤ mem.size)
    (hgap : writeOff - mem.size < USize.size)
    (habove : base + 32 ≤ writeOff)
    (hread : mem.readWithPadding base 32 = UInt256.toByteArray len) :
    (Reasoning.Theory.writeWord mem writeOff writeVal).readWithPadding base 32 =
      UInt256.toByteArray len := by
  rw [writeWord_read_preserved_len mem writeOff base 32 writeVal hgap
    (Or.inl ⟨habove, hmem⟩) (by norm_num) (by norm_num), hread]

theorem attesterReadWithPadding_writeWord_preserved_below
    {mem : ByteArray} {base writeOff : Nat} {len writeVal : UInt256}
    (hmem : base + 32 ≤ mem.size)
    (hgap : writeOff - mem.size < USize.size)
    (hbelow : writeOff + 32 ≤ base)
    (hread : mem.readWithPadding base 32 = UInt256.toByteArray len) :
    (Reasoning.Theory.writeWord mem writeOff writeVal).readWithPadding base 32 =
      UInt256.toByteArray len := by
  rw [writeWord_read_preserved_len mem writeOff base 32 writeVal hgap
    (Or.inr ⟨hbelow, hmem⟩) (by norm_num) (by norm_num), hread]

theorem attesterMultiOuterArrayLenMem_size (I : ExecutionEnv) :
    (attesterMultiOuterArrayLenMem I).size = 160 := by
  unfold attesterMultiOuterArrayLenMem
  rw [toByteArray_write_eq _ _ _ (by rw [solcFreePtrMem_size]; omega)
    (by rw [solcFreePtrMem_size]; exact lt_usize _ (by norm_num))]
  rw [ByteArray.size_append, ByteArray.size_append, ByteArray_zeroes_size,
    toByteArray_size, solcFreePtrMem_size]

theorem attesterMultiOuterArrayAllocMem_size (I : ExecutionEnv) :
    (attesterMultiOuterArrayAllocMem I).size = 160 := by
  unfold attesterMultiOuterArrayAllocMem
  change (Reasoning.Theory.writeWord (attesterMultiOuterArrayLenMem I) 64
    (attesterMultiOuterArrayAllocEndWord I)).size = 160
  rw [writeWord_size_of_inside _ _ _
    (by rw [attesterMultiOuterArrayLenMem_size I]; omega),
    attesterMultiOuterArrayLenMem_size]

theorem attesterMultiOuterArrayAllocMem_read64 (I : ExecutionEnv) :
    (attesterMultiOuterArrayAllocMem I).readWithPadding 64 32 =
      UInt256.toByteArray (attesterMultiOuterArrayAllocEndWord I) := by
  unfold attesterMultiOuterArrayAllocMem
  change (Reasoning.Theory.writeWord (attesterMultiOuterArrayLenMem I) 64
    (attesterMultiOuterArrayAllocEndWord I)).readWithPadding 64 32 =
      UInt256.toByteArray (attesterMultiOuterArrayAllocEndWord I)
  exact toByteArray_write_read_back_of_gap
    (attesterMultiOuterArrayAllocEndWord I) (attesterMultiOuterArrayLenMem I) 64
    (by
      rw [attesterMultiOuterArrayLenMem_size I]
      exact lt_usize 0 (by norm_num))

theorem attesterMultiOuterArrayAllocMem_mload64 (I : ExecutionEnv) :
    attesterMloadWord (attesterMultiOuterArrayAllocMem I) (UInt256.ofNat 5) ⟨64⟩ =
      attesterMultiOuterArrayAllocEndWord I := by
  unfold attesterMloadWord
  rw [if_neg]
  · rw [show (⟨64⟩ : UInt256).toNat = 64 by decide]
    rw [attesterMultiOuterArrayAllocMem_read64 I, fromByteArrayBigEndian_toByteArray,
      u256_ofNat_toNat]
  · rw [not_or]
    constructor
    · rw [attesterMultiOuterArrayAllocMem_size I]
      decide
    · decide

theorem attesterInnerArrayAllocMem_readWithPadding_len
    {len : UInt256} {mem : ByteArray} {aw : UInt256}
    (hgapLen :
      (attesterInnerArrayAllocFreeWord mem aw).toNat - mem.size < USize.size)
    (hgapFree :
      64 - (attesterInnerArrayAllocLenMem len mem aw).size < USize.size)
    (h64 : 64 + 32 ≤ (attesterInnerArrayAllocFreeWord mem aw).toNat) :
    (attesterInnerArrayAllocMem len mem aw).readWithPadding
        (attesterInnerArrayAllocFreeWord mem aw).toNat 32 =
      UInt256.toByteArray len := by
  let base := attesterInnerArrayAllocFreeWord mem aw
  have hreadLen :
      (attesterInnerArrayAllocLenMem len mem aw).readWithPadding base.toNat 32 =
        UInt256.toByteArray len := by
    change (Reasoning.Theory.writeWord mem base.toNat len).readWithPadding
        base.toNat 32 = UInt256.toByteArray len
    exact toByteArray_write_read_back_of_gap len mem base.toNat hgapLen
  have hmemLen :
      base.toNat + 32 ≤ (attesterInnerArrayAllocLenMem len mem aw).size := by
    have hsize := writeWord_size mem base.toNat len hgapLen
    unfold Reasoning.Theory.writeWord at hsize
    rw [hsize]
    omega
  change (Reasoning.Theory.writeWord
      (attesterInnerArrayAllocLenMem len mem aw) 64
      (attesterInnerArrayAllocEndWord len mem aw)).readWithPadding
        base.toNat 32 =
      UInt256.toByteArray len
  exact attesterReadWithPadding_writeWord_preserved_below
    (mem := attesterInnerArrayAllocLenMem len mem aw)
    (base := base.toNat) (writeOff := 64) (len := len)
    (writeVal := attesterInnerArrayAllocEndWord len mem aw)
    hmemLen hgapFree h64 hreadLen

theorem attesterInnerArrayAllocMem_mloadLen
    {len : UInt256} {mem : ByteArray} {aw : UInt256}
    (hgapLen :
      (attesterInnerArrayAllocFreeWord mem aw).toNat - mem.size < USize.size)
    (hgapFree :
      64 - (attesterInnerArrayAllocLenMem len mem aw).size < USize.size)
    (h64 : 64 + 32 ≤ (attesterInnerArrayAllocFreeWord mem aw).toNat)
    (haw :
      ¬ attesterInnerArrayAllocFreeWord mem aw ≥
        attesterInnerArrayAllocAw len mem aw * (⟨32⟩ : UInt256)) :
    attesterMloadWord
        (attesterInnerArrayAllocMem len mem aw)
      (attesterInnerArrayAllocAw len mem aw)
      (attesterInnerArrayAllocFreeWord mem aw) = len := by
  let base := attesterInnerArrayAllocFreeWord mem aw
  have hread :=
    attesterInnerArrayAllocMem_readWithPadding_len
      (len := len) (mem := mem) (aw := aw) hgapLen hgapFree h64
  have hmem :
      base.toNat + 32 ≤ (attesterInnerArrayAllocMem len mem aw).size := by
    have hsize1 := writeWord_size mem base.toNat len hgapLen
    have hsize2 := writeWord_size (attesterInnerArrayAllocLenMem len mem aw)
      64 (attesterInnerArrayAllocEndWord len mem aw) hgapFree
    unfold Reasoning.Theory.writeWord at hsize1 hsize2
    rw [hsize2, hsize1]
    omega
  exact attesterMloadWord_of_readWithPadding hmem haw (by simpa [base] using hread)

theorem attesterMultiRevokeInnerArrayInitStep_readWithPadding_preserved
    {base slot len : UInt256} {mem : ByteArray} {aw : UInt256}
    (hmem : base.toNat + 32 ≤ mem.size)
    (hread : mem.readWithPadding base.toNat 32 = UInt256.toByteArray len)
    (hgap64 : 64 - mem.size < USize.size)
    (hgapFree :
      (attesterMultiOuterArrayInitFreeWord mem aw).toNat -
        (attesterMultiOuterArrayInitFreeMem mem aw).size < USize.size)
    (hgapSecond :
      (attesterMultiRevokeInnerArrayInitSecondZeroWord mem aw).toNat -
        (attesterMultiOuterArrayInitZeroMem mem aw).size < USize.size)
    (hgapSlot :
      slot.toNat -
        (attesterMultiRevokeInnerArrayInitSecondZeroMem mem aw).size < USize.size)
    (h64 : 64 + 32 ≤ base.toNat)
    (hfree :
      base.toNat + 32 ≤ (attesterMultiOuterArrayInitFreeWord mem aw).toNat)
    (hsecond :
      base.toNat + 32 ≤
        (attesterMultiRevokeInnerArrayInitSecondZeroWord mem aw).toNat)
    (hslot : base.toNat + 32 ≤ slot.toNat) :
    (attesterMultiRevokeInnerArrayInitStepMem slot mem aw).readWithPadding
        base.toNat 32 =
      UInt256.toByteArray len := by
  have hread1 :
      (attesterMultiOuterArrayInitFreeMem mem aw).readWithPadding base.toNat 32 =
        UInt256.toByteArray len := by
    change (Reasoning.Theory.writeWord mem 64
      ((⟨64⟩ : UInt256) + attesterMultiOuterArrayInitFreeWord mem aw)).readWithPadding
        base.toNat 32 = UInt256.toByteArray len
    exact attesterReadWithPadding_writeWord_preserved_below
      (mem := mem) (base := base.toNat) (writeOff := 64)
      (len := len)
      (writeVal :=
        ((⟨64⟩ : UInt256) + attesterMultiOuterArrayInitFreeWord mem aw))
      hmem hgap64 h64 hread
  have hmem1 :
      base.toNat + 32 ≤ (attesterMultiOuterArrayInitFreeMem mem aw).size := by
    have hsize := writeWord_size mem 64
      ((⟨64⟩ : UInt256) + attesterMultiOuterArrayInitFreeWord mem aw) hgap64
    unfold Reasoning.Theory.writeWord at hsize
    rw [hsize]
    omega
  have hread2 :
      (attesterMultiOuterArrayInitZeroMem mem aw).readWithPadding base.toNat 32 =
        UInt256.toByteArray len := by
    change (Reasoning.Theory.writeWord
      (attesterMultiOuterArrayInitFreeMem mem aw)
      (attesterMultiOuterArrayInitFreeWord mem aw).toNat
      (⟨0⟩ : UInt256)).readWithPadding base.toNat 32 =
        UInt256.toByteArray len
    exact attesterReadWithPadding_writeWord_preserved_above
      (mem := attesterMultiOuterArrayInitFreeMem mem aw)
      (base := base.toNat)
      (writeOff := (attesterMultiOuterArrayInitFreeWord mem aw).toNat)
      (len := len) (writeVal := (⟨0⟩ : UInt256))
      hmem1 hgapFree hfree hread1
  have hmem2 :
      base.toNat + 32 ≤ (attesterMultiOuterArrayInitZeroMem mem aw).size := by
    have hsize := writeWord_size
      (attesterMultiOuterArrayInitFreeMem mem aw)
      (attesterMultiOuterArrayInitFreeWord mem aw).toNat
      (⟨0⟩ : UInt256) hgapFree
    unfold Reasoning.Theory.writeWord at hsize
    rw [hsize]
    omega
  have hread3 :
      (attesterMultiRevokeInnerArrayInitSecondZeroMem mem aw).readWithPadding
          base.toNat 32 =
        UInt256.toByteArray len := by
    change (Reasoning.Theory.writeWord
      (attesterMultiOuterArrayInitZeroMem mem aw)
      (attesterMultiRevokeInnerArrayInitSecondZeroWord mem aw).toNat
      (⟨0⟩ : UInt256)).readWithPadding base.toNat 32 =
        UInt256.toByteArray len
    exact attesterReadWithPadding_writeWord_preserved_above
      (mem := attesterMultiOuterArrayInitZeroMem mem aw)
      (base := base.toNat)
      (writeOff := (attesterMultiRevokeInnerArrayInitSecondZeroWord mem aw).toNat)
      (len := len) (writeVal := (⟨0⟩ : UInt256))
      hmem2 hgapSecond hsecond hread2
  have hmem3 :
      base.toNat + 32 ≤
        (attesterMultiRevokeInnerArrayInitSecondZeroMem mem aw).size := by
    have hsize := writeWord_size
      (attesterMultiOuterArrayInitZeroMem mem aw)
      (attesterMultiRevokeInnerArrayInitSecondZeroWord mem aw).toNat
      (⟨0⟩ : UInt256) hgapSecond
    unfold Reasoning.Theory.writeWord at hsize
    rw [hsize]
    omega
  change (Reasoning.Theory.writeWord
    (attesterMultiRevokeInnerArrayInitSecondZeroMem mem aw)
    slot.toNat (attesterMultiOuterArrayInitFreeWord mem aw)).readWithPadding
      base.toNat 32 =
    UInt256.toByteArray len
  exact attesterReadWithPadding_writeWord_preserved_above
    (mem := attesterMultiRevokeInnerArrayInitSecondZeroMem mem aw)
    (base := base.toNat) (writeOff := slot.toNat) (len := len)
    (writeVal := attesterMultiOuterArrayInitFreeWord mem aw)
    hmem3 hgapSlot hslot hread3

theorem attesterMultiRevokeInnerArrayInitStep_mloadLen_of_readWithPadding
    {base slot len : UInt256} {mem : ByteArray} {aw : UInt256}
    (hmem : base.toNat + 32 ≤ mem.size)
    (hread : mem.readWithPadding base.toNat 32 = UInt256.toByteArray len)
    (haw :
      ¬ base ≥
        attesterMultiRevokeInnerArrayInitStepAw slot mem aw * (⟨32⟩ : UInt256))
    (hgap64 : 64 - mem.size < USize.size)
    (hgapFree :
      (attesterMultiOuterArrayInitFreeWord mem aw).toNat -
        (attesterMultiOuterArrayInitFreeMem mem aw).size < USize.size)
    (hgapSecond :
      (attesterMultiRevokeInnerArrayInitSecondZeroWord mem aw).toNat -
        (attesterMultiOuterArrayInitZeroMem mem aw).size < USize.size)
    (hgapSlot :
      slot.toNat -
        (attesterMultiRevokeInnerArrayInitSecondZeroMem mem aw).size < USize.size)
    (h64 : 64 + 32 ≤ base.toNat)
    (hfree :
      base.toNat + 32 ≤ (attesterMultiOuterArrayInitFreeWord mem aw).toNat)
    (hsecond :
      base.toNat + 32 ≤
        (attesterMultiRevokeInnerArrayInitSecondZeroWord mem aw).toNat)
    (hslot : base.toNat + 32 ≤ slot.toNat) :
    attesterMloadWord
      (attesterMultiRevokeInnerArrayInitStepMem slot mem aw)
      (attesterMultiRevokeInnerArrayInitStepAw slot mem aw)
      base = len := by
  have hreadStep :=
    attesterMultiRevokeInnerArrayInitStep_readWithPadding_preserved
      (base := base) (slot := slot) (len := len) (mem := mem) (aw := aw)
      hmem hread hgap64 hgapFree hgapSecond hgapSlot h64 hfree hsecond hslot
  have hmemStep :
      base.toNat + 32 ≤
        (attesterMultiRevokeInnerArrayInitStepMem slot mem aw).size := by
    have hsize1 := writeWord_size mem 64
      ((⟨64⟩ : UInt256) + attesterMultiOuterArrayInitFreeWord mem aw) hgap64
    have hsize2 := writeWord_size
      (attesterMultiOuterArrayInitFreeMem mem aw)
      (attesterMultiOuterArrayInitFreeWord mem aw).toNat
      (⟨0⟩ : UInt256) hgapFree
    have hsize3 := writeWord_size
      (attesterMultiOuterArrayInitZeroMem mem aw)
      (attesterMultiRevokeInnerArrayInitSecondZeroWord mem aw).toNat
      (⟨0⟩ : UInt256) hgapSecond
    have hsize4 := writeWord_size
      (attesterMultiRevokeInnerArrayInitSecondZeroMem mem aw)
      slot.toNat (attesterMultiOuterArrayInitFreeWord mem aw) hgapSlot
    unfold Reasoning.Theory.writeWord at hsize1 hsize2 hsize3 hsize4
    rw [hsize4, hsize3, hsize2, hsize1]
    omega
  exact attesterMloadWord_of_readWithPadding hmemStep haw hreadStep

theorem attesterX_multiRevokeOuterArrayInitLoopWithStateInvariant
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {slot base len : UInt256} {mem : ByteArray} {aw : UInt256} {k C}
    (Inv : Nat → AttesterMultiOuterArrayInitState → Prop)
    (hremaining :
      ∀ n a, Inv n a → a.remaining = UInt256.ofNat (n + 1))
    (hbound :
      ∀ n a, Inv n a → n + 1 < UInt256.size)
    (hstep :
      ∀ n a, Inv (n + 1) a → Inv n (attesterMultiOuterArrayInitStepState a))
    (hinit :
      Inv (len.toNat - 1)
        { slot := slot, remaining := len, mem := mem, aw := aw })
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨291⟩ : UInt256)
      [slot, len, base, ⟨0⟩, len,
        attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        len,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨97⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ a' k' C',
      a'.remaining = (⟨1⟩ : UInt256) ∧
      Inv 0 a' ∧
      RD (patchedRuntime v) I g
        (initState cA gh bl σ σ₀ g A I) (⟨335⟩ : UInt256)
        (attesterMultiRevokeOuterArrayInitExitStack I base len a')
        (attesterMultiOuterArrayInitFinalMem a')
        (attesterMultiOuterArrayInitFinalAw a')
        ByteArray.empty (cA, σ) k' C' := by
  let stk := attesterMultiRevokeOuterArrayInitStack I base len
  let memOf : AttesterMultiOuterArrayInitState → ByteArray := fun a => a.mem
  let awOf : AttesterMultiOuterArrayInitState → UInt256 := fun a => a.aw
  let exitStk := attesterMultiRevokeOuterArrayInitExitStack I base len
  let exitMem := attesterMultiOuterArrayInitFinalMem
  let exitAw := attesterMultiOuterArrayInitFinalAw
  have hexit :
      ∀ a, Inv 0 a → ∀ k C,
        RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
          (⟨291⟩ : UInt256) (stk a) (memOf a) (awOf a)
          ByteArray.empty (cA, σ) k C →
        ∃ k' C',
          RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
            (⟨335⟩ : UInt256) (exitStk a) (exitMem a) (exitAw a)
            ByteArray.empty (cA, σ) k' C' := by
    intro a hInv k C rd
    have hrem : a.remaining = (⟨1⟩ : UInt256) := by
      simpa using hremaining 0 a hInv
    exact attesterX_multiRevokeOuterArrayInitFinalIteration
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) v (slot := a.slot) (base := base) (len := len)
      (mem := a.mem) (aw := a.aw)
      (by
        simpa [stk, memOf, awOf, hrem, attesterMultiRevokeOuterArrayInitStack]
          using rd)
  have hbody :
      ∀ n a, Inv (n + 1) a → ∀ k C,
        RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
          (⟨291⟩ : UInt256) (stk a) (memOf a) (awOf a)
          ByteArray.empty (cA, σ) k C →
        ∃ a' k' C',
          Inv n a' ∧
          RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
            (⟨291⟩ : UInt256) (stk a') (memOf a') (awOf a')
            ByteArray.empty (cA, σ) k' C' := by
    intro n a hInv k C rd
    let a' := attesterMultiOuterArrayInitStepState a
    have hsub :
        UInt256.sub a.remaining (⟨1⟩ : UInt256) = UInt256.ofNat (n + 1) := by
      rw [hremaining (n + 1) a hInv]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        attester_u256_ofNat_succ_sub_one (n := n + 1)
          (hbound (n + 1) a hInv)
    have hnext : UInt256.sub a.remaining (⟨1⟩ : UInt256) ≠ ⟨0⟩ := by
      rw [hsub]
      exact attester_u256_ofNat_pos_ne_zero
        (n := n + 1) (by omega) (by
          have := hbound (n + 1) a hInv
          omega)
    obtain ⟨k', C', rd'⟩ :=
      attesterX_multiRevokeOuterArrayInitNonFinalIteration
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) v (slot := a.slot) (base := base) (len := len)
        (remaining := a.remaining) (mem := a.mem) (aw := a.aw) hnext
        (by
          simpa [stk, memOf, awOf, attesterMultiRevokeOuterArrayInitStack]
            using rd)
    refine ⟨a', k', C', hstep n a hInv, ?_⟩
    simpa [a', stk, memOf, awOf, attesterMultiRevokeOuterArrayInitStack,
      attesterMultiOuterArrayInitStepState] using rd'
  let a0 : AttesterMultiOuterArrayInitState :=
    { slot := slot, remaining := len, mem := mem, aw := aw }
  obtain ⟨a', k', C', hInvFinal, rdFinal⟩ :=
    RD.whileLoopCarryExit
      (code := patchedRuntime v) (ee := I) (g := g)
      (s0 := initState cA gh bl σ σ₀ g A I)
      (rdata := ByteArray.empty) (acc := (cA, σ))
      (header := (⟨291⟩ : UInt256)) (exit := (⟨335⟩ : UInt256))
      Inv stk memOf awOf exitStk exitMem exitAw hexit hbody
      (len.toNat - 1) a0 (by simpa [a0] using hinit) k C
      (by
        simpa [a0, stk, memOf, awOf, attesterMultiRevokeOuterArrayInitStack]
          using hreach)
  exact ⟨a', k', C', by simpa using hremaining 0 a' hInvFinal,
    hInvFinal, rdFinal⟩

theorem attesterX_multiAttestOuterArrayInitLoopWithStateInvariant
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {slot base len : UInt256} {mem : ByteArray} {aw : UInt256} {k C}
    (Inv : Nat → AttesterMultiOuterArrayInitState → Prop)
    (hremaining :
      ∀ n a, Inv n a → a.remaining = UInt256.ofNat (n + 1))
    (hbound :
      ∀ n a, Inv n a → n + 1 < UInt256.size)
    (hstep :
      ∀ n a, Inv (n + 1) a → Inv n (attesterMultiOuterArrayInitStepState a))
    (hinit :
      Inv (len.toNat - 1)
        { slot := slot, remaining := len, mem := mem, aw := aw })
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨929⟩ : UInt256)
      [slot, len, base, ⟨0⟩, len, ⟨96⟩,
        attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        len,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨118⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ a' k' C',
      a'.remaining = (⟨1⟩ : UInt256) ∧
      Inv 0 a' ∧
      RD (patchedRuntime v) I g
        (initState cA gh bl σ σ₀ g A I) (⟨973⟩ : UInt256)
        (attesterMultiAttestOuterArrayInitExitStack I base len a')
        (attesterMultiOuterArrayInitFinalMem a')
        (attesterMultiOuterArrayInitFinalAw a')
        ByteArray.empty (cA, σ) k' C' := by
  let stk := attesterMultiAttestOuterArrayInitStack I base len
  let memOf : AttesterMultiOuterArrayInitState → ByteArray := fun a => a.mem
  let awOf : AttesterMultiOuterArrayInitState → UInt256 := fun a => a.aw
  let exitStk := attesterMultiAttestOuterArrayInitExitStack I base len
  let exitMem := attesterMultiOuterArrayInitFinalMem
  let exitAw := attesterMultiOuterArrayInitFinalAw
  have hexit :
      ∀ a, Inv 0 a → ∀ k C,
        RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
          (⟨929⟩ : UInt256) (stk a) (memOf a) (awOf a)
          ByteArray.empty (cA, σ) k C →
        ∃ k' C',
          RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
            (⟨973⟩ : UInt256) (exitStk a) (exitMem a) (exitAw a)
            ByteArray.empty (cA, σ) k' C' := by
    intro a hInv k C rd
    have hrem : a.remaining = (⟨1⟩ : UInt256) := by
      simpa using hremaining 0 a hInv
    exact attesterX_multiAttestOuterArrayInitFinalIteration
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) v (slot := a.slot) (base := base) (len := len)
      (mem := a.mem) (aw := a.aw)
      (by
        simpa [stk, memOf, awOf, hrem, attesterMultiAttestOuterArrayInitStack]
          using rd)
  have hbody :
      ∀ n a, Inv (n + 1) a → ∀ k C,
        RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
          (⟨929⟩ : UInt256) (stk a) (memOf a) (awOf a)
          ByteArray.empty (cA, σ) k C →
        ∃ a' k' C',
          Inv n a' ∧
          RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
            (⟨929⟩ : UInt256) (stk a') (memOf a') (awOf a')
            ByteArray.empty (cA, σ) k' C' := by
    intro n a hInv k C rd
    let a' := attesterMultiOuterArrayInitStepState a
    have hsub :
        UInt256.sub a.remaining (⟨1⟩ : UInt256) = UInt256.ofNat (n + 1) := by
      rw [hremaining (n + 1) a hInv]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        attester_u256_ofNat_succ_sub_one (n := n + 1)
          (hbound (n + 1) a hInv)
    have hnext : UInt256.sub a.remaining (⟨1⟩ : UInt256) ≠ ⟨0⟩ := by
      rw [hsub]
      exact attester_u256_ofNat_pos_ne_zero
        (n := n + 1) (by omega) (by
          have := hbound (n + 1) a hInv
          omega)
    obtain ⟨k', C', rd'⟩ :=
      attesterX_multiAttestOuterArrayInitNonFinalIteration
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) v (slot := a.slot) (base := base) (len := len)
        (remaining := a.remaining) (mem := a.mem) (aw := a.aw) hnext
        (by
          simpa [stk, memOf, awOf, attesterMultiAttestOuterArrayInitStack]
            using rd)
    refine ⟨a', k', C', hstep n a hInv, ?_⟩
    simpa [a', stk, memOf, awOf, attesterMultiAttestOuterArrayInitStack,
      attesterMultiOuterArrayInitStepState] using rd'
  let a0 : AttesterMultiOuterArrayInitState :=
    { slot := slot, remaining := len, mem := mem, aw := aw }
  obtain ⟨a', k', C', hInvFinal, rdFinal⟩ :=
    RD.whileLoopCarryExit
      (code := patchedRuntime v) (ee := I) (g := g)
      (s0 := initState cA gh bl σ σ₀ g A I)
      (rdata := ByteArray.empty) (acc := (cA, σ))
      (header := (⟨929⟩ : UInt256)) (exit := (⟨973⟩ : UInt256))
      Inv stk memOf awOf exitStk exitMem exitAw hexit hbody
      (len.toNat - 1) a0 (by simpa [a0] using hinit) k C
      (by
        simpa [a0, stk, memOf, awOf, attesterMultiAttestOuterArrayInitStack]
          using hreach)
  exact ⟨a', k', C', by simpa using hremaining 0 a' hInvFinal,
    hInvFinal, rdFinal⟩

theorem attesterX_multiRevokeInnerArrayInitLoopWithStateInvariant
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {slot base len payload : UInt256} {mem : ByteArray} {aw : UInt256} {k C}
    (Inv : Nat → AttesterMultiRevokeInnerArrayInitState → Prop)
    (hremaining :
      ∀ n a, Inv n a → a.remaining = UInt256.ofNat (n + 1))
    (hbound :
      ∀ n a, Inv n a → n + 1 < UInt256.size)
    (hstep :
      ∀ n a, Inv (n + 1) a → Inv n (attesterMultiRevokeInnerArrayInitStepState a))
    (hinit :
      Inv (len.toNat - 1)
        { slot := slot, remaining := len, mem := mem, aw := aw })
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨475⟩ : UInt256)
      [slot, len, base, ⟨0⟩, len, len, payload,
        ⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I,
        attesterSecondArrayLengthWord I,
        attesterSecondArrayPayloadStartWord I,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨97⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ a' k' C',
      a'.remaining = (⟨1⟩ : UInt256) ∧
      Inv 0 a' ∧
      RD (patchedRuntime v) I g
        (initState cA gh bl σ σ₀ g A I) (⟨518⟩ : UInt256)
        (attesterMultiRevokeInnerArrayInitExitStack I base len payload a')
        (attesterMultiRevokeInnerArrayInitFinalMem a')
        (attesterMultiRevokeInnerArrayInitFinalAw a')
        ByteArray.empty (cA, σ) k' C' := by
  let stk := attesterMultiRevokeInnerArrayInitStack I base len payload
  let memOf : AttesterMultiRevokeInnerArrayInitState → ByteArray := fun a => a.mem
  let awOf : AttesterMultiRevokeInnerArrayInitState → UInt256 := fun a => a.aw
  let exitStk := attesterMultiRevokeInnerArrayInitExitStack I base len payload
  let exitMem := attesterMultiRevokeInnerArrayInitFinalMem
  let exitAw := attesterMultiRevokeInnerArrayInitFinalAw
  have hexit :
      ∀ a, Inv 0 a → ∀ k C,
        RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
          (⟨475⟩ : UInt256) (stk a) (memOf a) (awOf a)
          ByteArray.empty (cA, σ) k C →
        ∃ k' C',
          RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
            (⟨518⟩ : UInt256) (exitStk a) (exitMem a) (exitAw a)
            ByteArray.empty (cA, σ) k' C' := by
    intro a hInv k C rd
    have hrem : a.remaining = (⟨1⟩ : UInt256) := by
      simpa using hremaining 0 a hInv
    exact attesterX_multiRevokeInnerArrayInitFinalIteration
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) v (slot := a.slot) (base := base) (len := len)
      (payload := payload) (mem := a.mem) (aw := a.aw)
      (by
        simpa [stk, memOf, awOf, hrem, attesterMultiRevokeInnerArrayInitStack]
          using rd)
  have hbody :
      ∀ n a, Inv (n + 1) a → ∀ k C,
        RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
          (⟨475⟩ : UInt256) (stk a) (memOf a) (awOf a)
          ByteArray.empty (cA, σ) k C →
        ∃ a' k' C',
          Inv n a' ∧
          RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
            (⟨475⟩ : UInt256) (stk a') (memOf a') (awOf a')
            ByteArray.empty (cA, σ) k' C' := by
    intro n a hInv k C rd
    let a' := attesterMultiRevokeInnerArrayInitStepState a
    have hsub :
        UInt256.sub a.remaining (⟨1⟩ : UInt256) = UInt256.ofNat (n + 1) := by
      rw [hremaining (n + 1) a hInv]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        attester_u256_ofNat_succ_sub_one (n := n + 1)
          (hbound (n + 1) a hInv)
    have hnext : UInt256.sub a.remaining (⟨1⟩ : UInt256) ≠ ⟨0⟩ := by
      rw [hsub]
      exact attester_u256_ofNat_pos_ne_zero
        (n := n + 1) (by omega) (by
          have := hbound (n + 1) a hInv
          omega)
    obtain ⟨k', C', rd'⟩ :=
      attesterX_multiRevokeInnerArrayInitNonFinalIteration
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) v (slot := a.slot) (base := base) (len := len)
        (payload := payload) (remaining := a.remaining) (mem := a.mem)
        (aw := a.aw) hnext
        (by
          simpa [stk, memOf, awOf, attesterMultiRevokeInnerArrayInitStack]
            using rd)
    refine ⟨a', k', C', hstep n a hInv, ?_⟩
    simpa [a', stk, memOf, awOf, attesterMultiRevokeInnerArrayInitStack,
      attesterMultiRevokeInnerArrayInitStepState] using rd'
  let a0 : AttesterMultiRevokeInnerArrayInitState :=
    { slot := slot, remaining := len, mem := mem, aw := aw }
  obtain ⟨a', k', C', hInvFinal, rdFinal⟩ :=
    RD.whileLoopCarryExit
      (code := patchedRuntime v) (ee := I) (g := g)
      (s0 := initState cA gh bl σ σ₀ g A I)
      (rdata := ByteArray.empty) (acc := (cA, σ))
      (header := (⟨475⟩ : UInt256)) (exit := (⟨518⟩ : UInt256))
      Inv stk memOf awOf exitStk exitMem exitAw hexit hbody
      (len.toNat - 1) a0 (by simpa [a0] using hinit) k C
      (by
        simpa [a0, stk, memOf, awOf, attesterMultiRevokeInnerArrayInitStack]
          using hreach)
  exact ⟨a', k', C', by simpa using hremaining 0 a' hInvFinal,
    hInvFinal, rdFinal⟩

theorem attesterX_multiAttestInnerArrayInitLoopWithStateInvariant
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {slot base len payload : UInt256} {mem : ByteArray} {aw : UInt256} {k C}
    (Inv : Nat → AttesterMultiAttestInnerArrayInitState → Prop)
    (hremaining :
      ∀ n a, Inv n a → a.remaining = UInt256.ofNat (n + 1))
    (hbound :
      ∀ n a, Inv n a → n + 1 < UInt256.size)
    (hstep :
      ∀ n a, Inv (n + 1) a → Inv n (attesterMultiAttestInnerArrayInitStepState a))
    (hinit :
      Inv (len.toNat - 1)
        { slot := slot, remaining := len, mem := mem, aw := aw })
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨1113⟩ : UInt256)
      [slot, len, base, ⟨0⟩, len, len, payload,
        ⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I, ⟨96⟩,
        attesterSecondArrayLengthWord I,
        attesterSecondArrayPayloadStartWord I,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨118⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ a' k' C',
      a'.remaining = (⟨1⟩ : UInt256) ∧
      Inv 0 a' ∧
      RD (patchedRuntime v) I g
        (initState cA gh bl σ σ₀ g A I) (⟨1181⟩ : UInt256)
        (attesterMultiAttestInnerArrayInitExitStack I base len payload a')
        (attesterMultiAttestInnerArrayInitFinalMem a')
        (attesterMultiAttestInnerArrayInitFinalAw a')
        ByteArray.empty (cA, σ) k' C' := by
  let stk := attesterMultiAttestInnerArrayInitStack I base len payload
  let memOf : AttesterMultiAttestInnerArrayInitState → ByteArray := fun a => a.mem
  let awOf : AttesterMultiAttestInnerArrayInitState → UInt256 := fun a => a.aw
  let exitStk := attesterMultiAttestInnerArrayInitExitStack I base len payload
  let exitMem := attesterMultiAttestInnerArrayInitFinalMem
  let exitAw := attesterMultiAttestInnerArrayInitFinalAw
  have hexit :
      ∀ a, Inv 0 a → ∀ k C,
        RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
          (⟨1113⟩ : UInt256) (stk a) (memOf a) (awOf a)
          ByteArray.empty (cA, σ) k C →
        ∃ k' C',
          RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
            (⟨1181⟩ : UInt256) (exitStk a) (exitMem a) (exitAw a)
            ByteArray.empty (cA, σ) k' C' := by
    intro a hInv k C rd
    have hrem : a.remaining = (⟨1⟩ : UInt256) := by
      simpa using hremaining 0 a hInv
    exact attesterX_multiAttestInnerArrayInitFinalIteration
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) v (slot := a.slot) (base := base) (len := len)
      (payload := payload) (mem := a.mem) (aw := a.aw)
      (by
        simpa [stk, memOf, awOf, hrem, attesterMultiAttestInnerArrayInitStack]
          using rd)
  have hbody :
      ∀ n a, Inv (n + 1) a → ∀ k C,
        RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
          (⟨1113⟩ : UInt256) (stk a) (memOf a) (awOf a)
          ByteArray.empty (cA, σ) k C →
        ∃ a' k' C',
          Inv n a' ∧
          RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
            (⟨1113⟩ : UInt256) (stk a') (memOf a') (awOf a')
            ByteArray.empty (cA, σ) k' C' := by
    intro n a hInv k C rd
    let a' := attesterMultiAttestInnerArrayInitStepState a
    have hsub :
        attesterMultiAttestInnerArrayInitDecRemaining a.remaining =
          UInt256.ofNat (n + 1) := by
      rw [hremaining (n + 1) a hInv]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        attester_u256_ofNat_succ_add_lnot_zero (n := n + 1)
          (hbound (n + 1) a hInv)
    have hnext :
        attesterMultiAttestInnerArrayInitDecRemaining a.remaining ≠ ⟨0⟩ := by
      rw [hsub]
      exact attester_u256_ofNat_pos_ne_zero
        (n := n + 1) (by omega) (by
          have := hbound (n + 1) a hInv
          omega)
    obtain ⟨k', C', rd'⟩ :=
      attesterX_multiAttestInnerArrayInitNonFinalIteration
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) v (slot := a.slot) (base := base) (len := len)
        (payload := payload) (remaining := a.remaining) (mem := a.mem)
        (aw := a.aw) hnext
        (by
          simpa [stk, memOf, awOf, attesterMultiAttestInnerArrayInitStack]
            using rd)
    refine ⟨a', k', C', hstep n a hInv, ?_⟩
    simpa [a', stk, memOf, awOf, attesterMultiAttestInnerArrayInitStack,
      attesterMultiAttestInnerArrayInitStepState] using rd'
  let a0 : AttesterMultiAttestInnerArrayInitState :=
    { slot := slot, remaining := len, mem := mem, aw := aw }
  obtain ⟨a', k', C', hInvFinal, rdFinal⟩ :=
    RD.whileLoopCarryExit
      (code := patchedRuntime v) (ee := I) (g := g)
      (s0 := initState cA gh bl σ σ₀ g A I)
      (rdata := ByteArray.empty) (acc := (cA, σ))
      (header := (⟨1113⟩ : UInt256)) (exit := (⟨1181⟩ : UInt256))
      Inv stk memOf awOf exitStk exitMem exitAw hexit hbody
      (len.toNat - 1) a0 (by simpa [a0] using hinit) k C
      (by
        simpa [a0, stk, memOf, awOf, attesterMultiAttestInnerArrayInitStack]
          using hreach)
  exact ⟨a', k', C', by simpa using hremaining 0 a' hInvFinal,
    hInvFinal, rdFinal⟩

theorem attesterX_multiRevokeFirstInnerArrayInitProgressWithStateInvariant
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    (hlenNe : attesterFirstInnerArrayLengthWord I ≠ ⟨0⟩)
    (Inv :
      AttesterMultiOuterArrayInitState → Nat →
        AttesterMultiRevokeInnerArrayInitState → Prop)
    (hremaining :
      ∀ a n b, Inv a n b → b.remaining = UInt256.ofNat (n + 1))
    (hbound :
      ∀ a n b, Inv a n b → n + 1 < UInt256.size)
    (hstep :
      ∀ a n b, Inv a (n + 1) b →
        Inv a n (attesterMultiRevokeInnerArrayInitStepState b))
    (hinit :
      ∀ a, a.remaining = (⟨1⟩ : UInt256) →
        Inv a ((attesterFirstInnerArrayLengthWord I).toNat - 1)
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
                (attesterMultiOuterArrayInitFinalAw a) })
    (hprogress :
      ∃ a' k C,
        a'.remaining = (⟨1⟩ : UInt256) ∧
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
      b'.remaining = (⟨1⟩ : UInt256) ∧
      Inv a' 0 b' ∧
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
  obtain ⟨a', k0, C0, hrem, rd0⟩ := hprogress
  have hlenNatNe : (attesterFirstInnerArrayLengthWord I).toNat ≠ 0 := by
    intro hzero
    apply hlenNe
    apply u256_inj
    simpa using hzero
  obtain ⟨b', k1, C1, hbrem, hInv, rd1⟩ :=
    attesterX_multiRevokeInnerArrayInitLoopWithStateInvariant
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (Inv := Inv a') (slot :=
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
      (hremaining a') (hbound a') (hstep a') (hinit a' hrem)
      (by simpa using rd0)
  exact ⟨a', b', k1, C1, hrem, hbrem, hInv, rd1⟩

abbrev attesterMultiRevokeInnerArrayCopyFreeWord
    (mem : ByteArray) (aw : UInt256) : UInt256 :=
  attesterMloadWord mem aw ⟨64⟩

abbrev attesterMultiRevokeInnerArrayCopyAwAfterMload
    (aw : UInt256) : UInt256 :=
  attesterMloadAw aw ⟨64⟩

abbrev attesterMultiRevokeInnerArrayCopyFreeBumpWord
    (mem : ByteArray) (aw : UInt256) : UInt256 :=
  (⟨64⟩ : UInt256) + attesterMultiRevokeInnerArrayCopyFreeWord mem aw

abbrev attesterMultiRevokeInnerArrayCopyFreeMem
    (mem : ByteArray) (aw : UInt256) : ByteArray :=
  (UInt256.toByteArray
      (attesterMultiRevokeInnerArrayCopyFreeBumpWord mem aw)).write 0 mem 64 32

abbrev attesterMultiRevokeInnerArrayCopyFreeAw
    (_mem : ByteArray) (aw : UInt256) : UInt256 :=
  UInt256.ofNat
    (MachineState.M (attesterMultiRevokeInnerArrayCopyAwAfterMload aw).toNat 64 32)

abbrev attesterMultiRevokeInnerArrayCopyCalldataOffset
    (payload idx : UInt256) : UInt256 :=
  UInt256.mul (⟨32⟩ : UInt256) idx + payload

abbrev attesterMultiRevokeInnerArrayCopyUidWord
    (I : ExecutionEnv) (payload idx : UInt256) : UInt256 :=
  calldataWord I.calldata
    (attesterMultiRevokeInnerArrayCopyCalldataOffset payload idx).toNat

abbrev attesterMultiRevokeInnerArrayCopyUidMem
    (I : ExecutionEnv) (payload idx : UInt256) (mem : ByteArray) (aw : UInt256) :
    ByteArray :=
  (UInt256.toByteArray
      (attesterMultiRevokeInnerArrayCopyUidWord I payload idx)).write 0
    (attesterMultiRevokeInnerArrayCopyFreeMem mem aw)
    (attesterMultiRevokeInnerArrayCopyFreeWord mem aw).toNat 32

abbrev attesterMultiRevokeInnerArrayCopyUidAw
    (_idx : UInt256) (mem : ByteArray) (aw : UInt256) : UInt256 :=
  UInt256.ofNat
    (MachineState.M (attesterMultiRevokeInnerArrayCopyFreeAw mem aw).toNat
      (attesterMultiRevokeInnerArrayCopyFreeWord mem aw).toNat 32)

abbrev attesterMultiRevokeInnerArrayCopyZeroWord
    (mem : ByteArray) (aw : UInt256) : UInt256 :=
  (⟨32⟩ : UInt256) + attesterMultiRevokeInnerArrayCopyFreeWord mem aw

abbrev attesterMultiRevokeInnerArrayCopyZeroMem
    (I : ExecutionEnv) (payload idx : UInt256) (mem : ByteArray) (aw : UInt256) :
    ByteArray :=
  (UInt256.toByteArray (⟨0⟩ : UInt256)).write 0
    (attesterMultiRevokeInnerArrayCopyUidMem I payload idx mem aw)
    (attesterMultiRevokeInnerArrayCopyZeroWord mem aw).toNat 32

abbrev attesterMultiRevokeInnerArrayCopyZeroAw
    (_I : ExecutionEnv) (_payload idx : UInt256) (mem : ByteArray) (aw : UInt256) :
    UInt256 :=
  UInt256.ofNat
    (MachineState.M (attesterMultiRevokeInnerArrayCopyUidAw idx mem aw).toNat
      (attesterMultiRevokeInnerArrayCopyZeroWord mem aw).toNat 32)

abbrev attesterMultiRevokeInnerArrayCopySlotWord
    (base idx : UInt256) : UInt256 :=
  (UInt256.mul (⟨32⟩ : UInt256) idx + base) + (⟨32⟩ : UInt256)

abbrev attesterMultiRevokeInnerArrayCopyStepMem
    (I : ExecutionEnv) (base payload idx : UInt256) (mem : ByteArray) (aw : UInt256) :
    ByteArray :=
  (UInt256.toByteArray (attesterMultiRevokeInnerArrayCopyFreeWord mem aw)).write 0
    (attesterMultiRevokeInnerArrayCopyZeroMem I payload idx mem aw)
    (attesterMultiRevokeInnerArrayCopySlotWord base idx).toNat 32

abbrev attesterMultiRevokeInnerArrayCopyStepAw
    (I : ExecutionEnv) (base payload idx : UInt256) (mem : ByteArray) (aw : UInt256) :
    UInt256 :=
  UInt256.ofNat
    (MachineState.M
      (attesterMloadAw
        (attesterMultiRevokeInnerArrayCopyZeroAw I payload idx mem aw) base).toNat
      (attesterMultiRevokeInnerArrayCopySlotWord base idx).toNat 32)

abbrev attesterMultiRevokeInnerArrayCopyNextIdx (idx : UInt256) : UInt256 :=
  (⟨1⟩ : UInt256) + idx

structure AttesterMultiRevokeInnerArrayCopyState where
  idx : UInt256
  mem : ByteArray
  aw : UInt256

abbrev attesterMultiRevokeInnerArrayCopyStack
    (base len payload : UInt256) (tail : List UInt256)
    (a : AttesterMultiRevokeInnerArrayCopyState) : List UInt256 :=
  a.idx :: base :: len :: len :: payload :: tail

abbrev attesterMultiRevokeInnerArrayCopyStepState
    (I : ExecutionEnv) (base payload : UInt256)
    (a : AttesterMultiRevokeInnerArrayCopyState) :
    AttesterMultiRevokeInnerArrayCopyState :=
  { idx := attesterMultiRevokeInnerArrayCopyNextIdx a.idx,
    mem := attesterMultiRevokeInnerArrayCopyStepMem I base payload a.idx a.mem a.aw,
    aw := attesterMultiRevokeInnerArrayCopyStepAw I base payload a.idx a.mem a.aw }

private theorem attesterMultiRevokeInnerArrayCopyNextIdx_ofNat
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

private theorem attesterMultiRevokeInnerArrayCopyStep_readWithPadding_preserved
    {I : ExecutionEnv} {base payload idx len : UInt256}
    {mem : ByteArray} {aw : UInt256}
    (hmem : base.toNat + 32 ≤ mem.size)
    (hread : mem.readWithPadding base.toNat 32 = UInt256.toByteArray len)
    (hgap64 : 64 - mem.size < USize.size)
    (hgapUid :
      (attesterMultiRevokeInnerArrayCopyFreeWord mem aw).toNat -
        (attesterMultiRevokeInnerArrayCopyFreeMem mem aw).size < USize.size)
    (hgapZero :
      (attesterMultiRevokeInnerArrayCopyZeroWord mem aw).toNat -
        (attesterMultiRevokeInnerArrayCopyUidMem I payload idx mem aw).size < USize.size)
    (hgapSlot :
      (attesterMultiRevokeInnerArrayCopySlotWord base idx).toNat -
        (attesterMultiRevokeInnerArrayCopyZeroMem I payload idx mem aw).size < USize.size)
    (h64 : 64 + 32 ≤ base.toNat)
    (huid :
      base.toNat + 32 ≤ (attesterMultiRevokeInnerArrayCopyFreeWord mem aw).toNat)
    (hzero :
      base.toNat + 32 ≤ (attesterMultiRevokeInnerArrayCopyZeroWord mem aw).toNat)
    (hslot :
      base.toNat + 32 ≤ (attesterMultiRevokeInnerArrayCopySlotWord base idx).toNat) :
    (attesterMultiRevokeInnerArrayCopyStepMem I base payload idx mem aw).readWithPadding
        base.toNat 32 =
      UInt256.toByteArray len := by
  have hread1 :
      (attesterMultiRevokeInnerArrayCopyFreeMem mem aw).readWithPadding
          base.toNat 32 =
        UInt256.toByteArray len := by
    change (Reasoning.Theory.writeWord mem 64
      (attesterMultiRevokeInnerArrayCopyFreeBumpWord mem aw)).readWithPadding
        base.toNat 32 = UInt256.toByteArray len
    exact attesterReadWithPadding_writeWord_preserved_below
      (mem := mem) (base := base.toNat) (writeOff := 64)
      (len := len) (writeVal := attesterMultiRevokeInnerArrayCopyFreeBumpWord mem aw)
      hmem hgap64 h64 hread
  have hmem1 :
      base.toNat + 32 ≤ (attesterMultiRevokeInnerArrayCopyFreeMem mem aw).size := by
    have hsize := writeWord_size mem 64
      (attesterMultiRevokeInnerArrayCopyFreeBumpWord mem aw) hgap64
    unfold Reasoning.Theory.writeWord at hsize
    rw [hsize]
    omega
  have hread2 :
      (attesterMultiRevokeInnerArrayCopyUidMem I payload idx mem aw).readWithPadding
          base.toNat 32 =
        UInt256.toByteArray len := by
    change (Reasoning.Theory.writeWord
      (attesterMultiRevokeInnerArrayCopyFreeMem mem aw)
      (attesterMultiRevokeInnerArrayCopyFreeWord mem aw).toNat
      (attesterMultiRevokeInnerArrayCopyUidWord I payload idx)).readWithPadding
        base.toNat 32 = UInt256.toByteArray len
    exact attesterReadWithPadding_writeWord_preserved_above
      (mem := attesterMultiRevokeInnerArrayCopyFreeMem mem aw)
      (base := base.toNat)
      (writeOff := (attesterMultiRevokeInnerArrayCopyFreeWord mem aw).toNat)
      (len := len)
      (writeVal := attesterMultiRevokeInnerArrayCopyUidWord I payload idx)
      hmem1 hgapUid huid hread1
  have hmem2 :
      base.toNat + 32 ≤
        (attesterMultiRevokeInnerArrayCopyUidMem I payload idx mem aw).size := by
    have hsize := writeWord_size (attesterMultiRevokeInnerArrayCopyFreeMem mem aw)
      (attesterMultiRevokeInnerArrayCopyFreeWord mem aw).toNat
      (attesterMultiRevokeInnerArrayCopyUidWord I payload idx) hgapUid
    unfold Reasoning.Theory.writeWord at hsize
    rw [hsize]
    omega
  have hread3 :
      (attesterMultiRevokeInnerArrayCopyZeroMem I payload idx mem aw).readWithPadding
          base.toNat 32 =
        UInt256.toByteArray len := by
    change (Reasoning.Theory.writeWord
      (attesterMultiRevokeInnerArrayCopyUidMem I payload idx mem aw)
      (attesterMultiRevokeInnerArrayCopyZeroWord mem aw).toNat
      (⟨0⟩ : UInt256)).readWithPadding base.toNat 32 =
        UInt256.toByteArray len
    exact attesterReadWithPadding_writeWord_preserved_above
      (mem := attesterMultiRevokeInnerArrayCopyUidMem I payload idx mem aw)
      (base := base.toNat)
      (writeOff := (attesterMultiRevokeInnerArrayCopyZeroWord mem aw).toNat)
      (len := len) (writeVal := (⟨0⟩ : UInt256))
      hmem2 hgapZero hzero hread2
  have hmem3 :
      base.toNat + 32 ≤
        (attesterMultiRevokeInnerArrayCopyZeroMem I payload idx mem aw).size := by
    have hsize := writeWord_size
      (attesterMultiRevokeInnerArrayCopyUidMem I payload idx mem aw)
      (attesterMultiRevokeInnerArrayCopyZeroWord mem aw).toNat
      (⟨0⟩ : UInt256) hgapZero
    unfold Reasoning.Theory.writeWord at hsize
    rw [hsize]
    omega
  change (Reasoning.Theory.writeWord
    (attesterMultiRevokeInnerArrayCopyZeroMem I payload idx mem aw)
    (attesterMultiRevokeInnerArrayCopySlotWord base idx).toNat
    (attesterMultiRevokeInnerArrayCopyFreeWord mem aw)).readWithPadding
      base.toNat 32 = UInt256.toByteArray len
  exact attesterReadWithPadding_writeWord_preserved_above
    (mem := attesterMultiRevokeInnerArrayCopyZeroMem I payload idx mem aw)
    (base := base.toNat)
    (writeOff := (attesterMultiRevokeInnerArrayCopySlotWord base idx).toNat)
    (len := len)
    (writeVal := attesterMultiRevokeInnerArrayCopyFreeWord mem aw)
    hmem3 hgapSlot hslot hread3

private theorem attesterMultiRevokeInnerArrayCopyZero_readWithPadding_preserved
    {I : ExecutionEnv} {base payload idx len : UInt256}
    {mem : ByteArray} {aw : UInt256}
    (hmem : base.toNat + 32 ≤ mem.size)
    (hread : mem.readWithPadding base.toNat 32 = UInt256.toByteArray len)
    (hgap64 : 64 - mem.size < USize.size)
    (hgapUid :
      (attesterMultiRevokeInnerArrayCopyFreeWord mem aw).toNat -
        (attesterMultiRevokeInnerArrayCopyFreeMem mem aw).size < USize.size)
    (hgapZero :
      (attesterMultiRevokeInnerArrayCopyZeroWord mem aw).toNat -
        (attesterMultiRevokeInnerArrayCopyUidMem I payload idx mem aw).size < USize.size)
    (h64 : 64 + 32 ≤ base.toNat)
    (huid :
      base.toNat + 32 ≤ (attesterMultiRevokeInnerArrayCopyFreeWord mem aw).toNat)
    (hzero :
      base.toNat + 32 ≤ (attesterMultiRevokeInnerArrayCopyZeroWord mem aw).toNat) :
    (attesterMultiRevokeInnerArrayCopyZeroMem I payload idx mem aw).readWithPadding
        base.toNat 32 =
      UInt256.toByteArray len := by
  have hread1 :
      (attesterMultiRevokeInnerArrayCopyFreeMem mem aw).readWithPadding
          base.toNat 32 =
        UInt256.toByteArray len := by
    change (Reasoning.Theory.writeWord mem 64
      (attesterMultiRevokeInnerArrayCopyFreeBumpWord mem aw)).readWithPadding
        base.toNat 32 = UInt256.toByteArray len
    exact attesterReadWithPadding_writeWord_preserved_below
      (mem := mem) (base := base.toNat) (writeOff := 64)
      (len := len) (writeVal := attesterMultiRevokeInnerArrayCopyFreeBumpWord mem aw)
      hmem hgap64 h64 hread
  have hmem1 :
      base.toNat + 32 ≤ (attesterMultiRevokeInnerArrayCopyFreeMem mem aw).size := by
    have hsize := writeWord_size mem 64
      (attesterMultiRevokeInnerArrayCopyFreeBumpWord mem aw) hgap64
    unfold Reasoning.Theory.writeWord at hsize
    rw [hsize]
    omega
  have hread2 :
      (attesterMultiRevokeInnerArrayCopyUidMem I payload idx mem aw).readWithPadding
          base.toNat 32 =
        UInt256.toByteArray len := by
    change (Reasoning.Theory.writeWord
      (attesterMultiRevokeInnerArrayCopyFreeMem mem aw)
      (attesterMultiRevokeInnerArrayCopyFreeWord mem aw).toNat
      (attesterMultiRevokeInnerArrayCopyUidWord I payload idx)).readWithPadding
        base.toNat 32 = UInt256.toByteArray len
    exact attesterReadWithPadding_writeWord_preserved_above
      (mem := attesterMultiRevokeInnerArrayCopyFreeMem mem aw)
      (base := base.toNat)
      (writeOff := (attesterMultiRevokeInnerArrayCopyFreeWord mem aw).toNat)
      (len := len)
      (writeVal := attesterMultiRevokeInnerArrayCopyUidWord I payload idx)
      hmem1 hgapUid huid hread1
  have hmem2 :
      base.toNat + 32 ≤
        (attesterMultiRevokeInnerArrayCopyUidMem I payload idx mem aw).size := by
    have hsize := writeWord_size (attesterMultiRevokeInnerArrayCopyFreeMem mem aw)
      (attesterMultiRevokeInnerArrayCopyFreeWord mem aw).toNat
      (attesterMultiRevokeInnerArrayCopyUidWord I payload idx) hgapUid
    unfold Reasoning.Theory.writeWord at hsize
    rw [hsize]
    omega
  change (Reasoning.Theory.writeWord
    (attesterMultiRevokeInnerArrayCopyUidMem I payload idx mem aw)
    (attesterMultiRevokeInnerArrayCopyZeroWord mem aw).toNat
    (⟨0⟩ : UInt256)).readWithPadding base.toNat 32 =
      UInt256.toByteArray len
  exact attesterReadWithPadding_writeWord_preserved_above
    (mem := attesterMultiRevokeInnerArrayCopyUidMem I payload idx mem aw)
    (base := base.toNat)
    (writeOff := (attesterMultiRevokeInnerArrayCopyZeroWord mem aw).toNat)
    (len := len) (writeVal := (⟨0⟩ : UInt256))
    hmem2 hgapZero hzero hread2

private theorem attesterMultiRevokeInnerArrayCopyZero_mloadLen_of_readWithPadding
    {I : ExecutionEnv} {base payload idx len : UInt256}
    {mem : ByteArray} {aw : UInt256}
    (hmem : base.toNat + 32 ≤ mem.size)
    (hread : mem.readWithPadding base.toNat 32 = UInt256.toByteArray len)
    (haw :
      ¬ base ≥
        attesterMultiRevokeInnerArrayCopyZeroAw I payload idx mem aw * (⟨32⟩ : UInt256))
    (hgap64 : 64 - mem.size < USize.size)
    (hgapUid :
      (attesterMultiRevokeInnerArrayCopyFreeWord mem aw).toNat -
        (attesterMultiRevokeInnerArrayCopyFreeMem mem aw).size < USize.size)
    (hgapZero :
      (attesterMultiRevokeInnerArrayCopyZeroWord mem aw).toNat -
        (attesterMultiRevokeInnerArrayCopyUidMem I payload idx mem aw).size < USize.size)
    (h64 : 64 + 32 ≤ base.toNat)
    (huid :
      base.toNat + 32 ≤ (attesterMultiRevokeInnerArrayCopyFreeWord mem aw).toNat)
    (hzero :
      base.toNat + 32 ≤ (attesterMultiRevokeInnerArrayCopyZeroWord mem aw).toNat) :
    attesterMloadWord
      (attesterMultiRevokeInnerArrayCopyZeroMem I payload idx mem aw)
      (attesterMultiRevokeInnerArrayCopyZeroAw I payload idx mem aw)
      base = len := by
  have hreadZero :=
    attesterMultiRevokeInnerArrayCopyZero_readWithPadding_preserved
      (I := I) (base := base) (payload := payload) (idx := idx)
      (len := len) (mem := mem) (aw := aw)
      hmem hread hgap64 hgapUid hgapZero h64 huid hzero
  have hmemZero :
      base.toNat + 32 ≤
        (attesterMultiRevokeInnerArrayCopyZeroMem I payload idx mem aw).size := by
    have hsize1 := writeWord_size mem 64
      (attesterMultiRevokeInnerArrayCopyFreeBumpWord mem aw) hgap64
    have hsize2 := writeWord_size (attesterMultiRevokeInnerArrayCopyFreeMem mem aw)
      (attesterMultiRevokeInnerArrayCopyFreeWord mem aw).toNat
      (attesterMultiRevokeInnerArrayCopyUidWord I payload idx) hgapUid
    have hsize3 := writeWord_size
      (attesterMultiRevokeInnerArrayCopyUidMem I payload idx mem aw)
      (attesterMultiRevokeInnerArrayCopyZeroWord mem aw).toNat
      (⟨0⟩ : UInt256) hgapZero
    unfold Reasoning.Theory.writeWord at hsize1 hsize2 hsize3
    rw [hsize3, hsize2, hsize1]
    omega
  exact attesterMloadWord_of_readWithPadding hmemZero haw hreadZero

theorem attesterMultiRevokeInnerArrayCopyZero_mloadLen
    {I : ExecutionEnv} {base payload idx len : UInt256}
    {mem : ByteArray} {aw : UInt256}
    (hmem : base.toNat + 32 ≤ mem.size)
    (hread : mem.readWithPadding base.toNat 32 = UInt256.toByteArray len)
    (haw :
      ¬ base ≥
        attesterMultiRevokeInnerArrayCopyZeroAw I payload idx mem aw * (⟨32⟩ : UInt256))
    (hgap64 : 64 - mem.size < USize.size)
    (hgapUid :
      (attesterMultiRevokeInnerArrayCopyFreeWord mem aw).toNat -
        (attesterMultiRevokeInnerArrayCopyFreeMem mem aw).size < USize.size)
    (hgapZero :
      (attesterMultiRevokeInnerArrayCopyZeroWord mem aw).toNat -
        (attesterMultiRevokeInnerArrayCopyUidMem I payload idx mem aw).size < USize.size)
    (h64 : 64 + 32 ≤ base.toNat)
    (huid :
      base.toNat + 32 ≤ (attesterMultiRevokeInnerArrayCopyFreeWord mem aw).toNat)
    (hzero :
      base.toNat + 32 ≤ (attesterMultiRevokeInnerArrayCopyZeroWord mem aw).toNat) :
    attesterMloadWord
      (attesterMultiRevokeInnerArrayCopyZeroMem I payload idx mem aw)
      (attesterMultiRevokeInnerArrayCopyZeroAw I payload idx mem aw)
      base = len :=
  attesterMultiRevokeInnerArrayCopyZero_mloadLen_of_readWithPadding
    (I := I) (base := base) (payload := payload) (idx := idx)
    (len := len) (mem := mem) (aw := aw)
    hmem hread haw hgap64 hgapUid hgapZero h64 huid hzero

theorem attesterMultiRevokeInnerArrayCopyStep_readWithPadding
    {I : ExecutionEnv} {base payload idx len : UInt256}
    {mem : ByteArray} {aw : UInt256}
    (hmem : base.toNat + 32 ≤ mem.size)
    (hread : mem.readWithPadding base.toNat 32 = UInt256.toByteArray len)
    (hgap64 : 64 - mem.size < USize.size)
    (hgapUid :
      (attesterMultiRevokeInnerArrayCopyFreeWord mem aw).toNat -
        (attesterMultiRevokeInnerArrayCopyFreeMem mem aw).size < USize.size)
    (hgapZero :
      (attesterMultiRevokeInnerArrayCopyZeroWord mem aw).toNat -
        (attesterMultiRevokeInnerArrayCopyUidMem I payload idx mem aw).size < USize.size)
    (hgapSlot :
      (attesterMultiRevokeInnerArrayCopySlotWord base idx).toNat -
        (attesterMultiRevokeInnerArrayCopyZeroMem I payload idx mem aw).size < USize.size)
    (h64 : 64 + 32 ≤ base.toNat)
    (huid :
      base.toNat + 32 ≤ (attesterMultiRevokeInnerArrayCopyFreeWord mem aw).toNat)
    (hzero :
      base.toNat + 32 ≤ (attesterMultiRevokeInnerArrayCopyZeroWord mem aw).toNat)
    (hslot :
      base.toNat + 32 ≤ (attesterMultiRevokeInnerArrayCopySlotWord base idx).toNat) :
    (attesterMultiRevokeInnerArrayCopyStepMem I base payload idx mem aw).readWithPadding
        base.toNat 32 =
      UInt256.toByteArray len :=
  attesterMultiRevokeInnerArrayCopyStep_readWithPadding_preserved
    (I := I) (base := base) (payload := payload) (idx := idx)
    (len := len) (mem := mem) (aw := aw)
    hmem hread hgap64 hgapUid hgapZero hgapSlot h64 huid hzero hslot

theorem attesterX_multiRevokeInnerArrayCopyExit
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {idx base len payload : UInt256} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {k C}
    (htail : tail.length ≤ 1000)
    (hge : UInt256.lt idx len = ⟨0⟩)
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨518⟩ : UInt256)
      (idx :: base :: len :: len :: payload :: tail)
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨608⟩ : UInt256)
      (idx :: base :: len :: len :: payload :: tail)
      mem aw ByteArray.empty (cA, σ) k' C' := by
  have hcond : UInt256.isZero (UInt256.lt idx len) ≠ ⟨0⟩ := by
    rw [hge]
    decide
  exact ⟨_, _, evm_run hreach with [
    raw jumpdest (by attester_decode_at v, ⟨518⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨519⟩, 0x82, .DUP3) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨520⟩, 0x81, .DUP2) (by evm_ov),
    raw lt (by attester_decode_at v, ⟨521⟩, 0x10, .LT) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨522⟩, 0x15, .ISZERO) (by evm_ov),
    raw push2 ⟨608⟩ (by attester_decode_at v, ⟨523⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jumpiT (by attester_decode_at v, ⟨526⟩, 0x57, .JUMPI)
      hcond (attesterMultiRevokeInnerArrayCopyExitJumpdest v) (by evm_ov)]⟩

set_option maxHeartbeats 1500000 in
theorem attesterX_multiRevokeInnerArrayCopyNonFinalIteration
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {idx base len payload : UInt256} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {k C}
    (htail : tail.length ≤ 1000)
    (hlt : UInt256.lt idx len = ⟨1⟩)
    (hloadLt :
      UInt256.lt idx
        (attesterMloadWord
          (attesterMultiRevokeInnerArrayCopyZeroMem I payload idx mem aw)
          (attesterMultiRevokeInnerArrayCopyZeroAw I payload idx mem aw)
          base) = ⟨1⟩)
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨518⟩ : UInt256)
      (idx :: base :: len :: len :: payload :: tail)
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨518⟩ : UInt256)
      (attesterMultiRevokeInnerArrayCopyNextIdx idx ::
        base :: len :: len :: payload :: tail)
      (attesterMultiRevokeInnerArrayCopyStepMem I base payload idx mem aw)
      (attesterMultiRevokeInnerArrayCopyStepAw I base payload idx mem aw)
      ByteArray.empty (cA, σ) k' C' := by
  let free := attesterMultiRevokeInnerArrayCopyFreeWord mem aw
  let aw1 := attesterMultiRevokeInnerArrayCopyAwAfterMload aw
  let bump := attesterMultiRevokeInnerArrayCopyFreeBumpWord mem aw
  let mem1 := attesterMultiRevokeInnerArrayCopyFreeMem mem aw
  let aw2 := attesterMultiRevokeInnerArrayCopyFreeAw mem aw
  let cdOff := attesterMultiRevokeInnerArrayCopyCalldataOffset payload idx
  let uid := attesterMultiRevokeInnerArrayCopyUidWord I payload idx
  let mem2 := attesterMultiRevokeInnerArrayCopyUidMem I payload idx mem aw
  let aw3 := attesterMultiRevokeInnerArrayCopyUidAw idx mem aw
  let zeroWord := attesterMultiRevokeInnerArrayCopyZeroWord mem aw
  let mem3 := attesterMultiRevokeInnerArrayCopyZeroMem I payload idx mem aw
  let aw4 := attesterMultiRevokeInnerArrayCopyZeroAw I payload idx mem aw
  let loadLen := attesterMloadWord mem3 aw4 base
  let aw5 := attesterMloadAw aw4 base
  let slot := attesterMultiRevokeInnerArrayCopySlotWord base idx
  let mem4 := attesterMultiRevokeInnerArrayCopyStepMem I base payload idx mem aw
  let aw6 := attesterMultiRevokeInnerArrayCopyStepAw I base payload idx mem aw
  have hcostMload64 :
      ∀ s : State,
        s.machineState.activeWords = aw →
        s.machineState.stack = (⟨64⟩ : UInt256) :: idx :: base :: len :: len :: payload :: tail →
        memoryExpansionCost s .MLOAD = Cₘ aw1 - Cₘ aw := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostStoreFree :
      ∀ s : State,
        s.machineState.activeWords = aw1 →
        s.machineState.stack = (⟨64⟩ : UInt256) :: bump :: free :: idx :: base :: len ::
          len :: payload :: tail →
        memoryExpansionCost s .MSTORE = Cₘ aw2 - Cₘ aw1 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostStoreUid :
      ∀ s : State,
        s.machineState.activeWords = aw2 →
        s.machineState.stack = free :: uid :: free :: free :: idx :: base :: len ::
          len :: payload :: tail →
        memoryExpansionCost s .MSTORE = Cₘ aw3 - Cₘ aw2 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostStoreZero :
      ∀ s : State,
        s.machineState.activeWords = aw3 →
        s.machineState.stack = zeroWord :: (⟨0⟩ : UInt256) :: zeroWord :: free ::
          idx :: base :: len :: len :: payload :: tail →
        memoryExpansionCost s .MSTORE = Cₘ aw4 - Cₘ aw3 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostMloadBase :
      ∀ s : State,
        s.machineState.activeWords = aw4 →
        s.machineState.stack = base :: idx :: base :: free :: idx :: base :: len ::
          len :: payload :: tail →
        memoryExpansionCost s .MLOAD = Cₘ aw5 - Cₘ aw4 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostStoreSlot :
      ∀ s : State,
        s.machineState.activeWords = aw5 →
        s.machineState.stack = slot :: free :: idx :: base :: len :: len :: payload :: tail →
        memoryExpansionCost s .MSTORE = Cₘ aw6 - Cₘ aw5 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hrd527 : ∃ k527 C527, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨527⟩ : UInt256)
      (idx :: base :: len :: len :: payload :: tail)
      mem aw ByteArray.empty (cA, σ) k527 C527 := by
    exact ⟨_, _, by
      simpa using evm_run hreach with [
      raw jumpdest (by attester_decode_at v, ⟨518⟩, 0x5b, .JUMPDEST) (by evm_ov),
      raw dup3 (by attester_decode_at v, ⟨519⟩, 0x82, .DUP3) (by evm_ov),
      raw dup2 (by attester_decode_at v, ⟨520⟩, 0x81, .DUP2) (by evm_ov),
      raw lt (by attester_decode_at v, ⟨521⟩, 0x10, .LT) (by evm_ov),
      raw iszero (by attester_decode_at v, ⟨522⟩, 0x15, .ISZERO) (by evm_ov),
      raw push2 ⟨608⟩ (by attester_decode_at v, ⟨523⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
      raw jumpiNT (by attester_decode_at v, ⟨526⟩, 0x57, .JUMPI)
        (by rw [hlt]; decide) (by evm_ov)]⟩
  obtain ⟨_, _, rd527⟩ := hrd527
  exact ⟨_, _, by
    simpa [free, aw1, bump, mem1, aw2, cdOff, uid, mem2, aw3,
      zeroWord, mem3, aw4, loadLen, aw5, slot, mem4, aw6,
      attesterMultiRevokeInnerArrayCopyNextIdx] using
      evm_run rd527 with [
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨527⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw mload (Cₘ aw1 - Cₘ aw) free aw1
      (by attester_decode_at v, ⟨529⟩, 0x51, .MLOAD)
      hcostMload64 (by rfl) (by rfl) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨530⟩, 0x80, .DUP1) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨531⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw add (by attester_decode_at v, ⟨533⟩, 0x01, .ADD) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨534⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw mstore (Cₘ aw2 - Cₘ aw1) mem1 aw2
      (by attester_decode_at v, ⟨536⟩, 0x52, .MSTORE)
      hcostStoreFree (by rfl) (by rfl) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨537⟩, 0x80, .DUP1) (by evm_ov),
    raw dup7 (by attester_decode_at v, ⟨538⟩, 0x86, .DUP7) (by evm_ov),
    raw dup7 (by attester_decode_at v, ⟨539⟩, 0x86, .DUP7) (by evm_ov),
    raw dup5 (by attester_decode_at v, ⟨540⟩, 0x84, .DUP5) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨541⟩, 0x81, .DUP2) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨542⟩, 0x81, .DUP2) (by evm_ov),
    raw lt (by attester_decode_at v, ⟨543⟩, 0x10, .LT) (by evm_ov),
    raw push2 ⟨555⟩ (by attester_decode_at v, ⟨544⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jumpiT (by attester_decode_at v, ⟨547⟩, 0x57, .JUMPI)
      (by rw [hlt]; decide)
      (attesterMultiRevokeInnerArrayCopyElementOkJumpdest v) (by evm_ov),
    raw jumpdest (by attester_decode_at v, ⟨555⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨556⟩, 0x90, .SWAP1) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨557⟩, 0x50, .POP) (by evm_ov),
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨558⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw mul (by attester_decode_at v, ⟨560⟩, 0x02, .MUL) (by evm_ov),
    raw add (by attester_decode_at v, ⟨561⟩, 0x01, .ADD) (by evm_ov),
    raw calldataload (by attester_decode_at v, ⟨562⟩, 0x35, .CALLDATALOAD) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨563⟩, 0x81, .DUP2) (by evm_ov),
    raw mstore (Cₘ aw3 - Cₘ aw2) mem2 aw3
      (by attester_decode_at v, ⟨564⟩, 0x52, .MSTORE)
      hcostStoreUid (by rfl) (by rfl) (by evm_ov),
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨565⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw add (by attester_decode_at v, ⟨567⟩, 0x01, .ADD) (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨568⟩, 0x5f, .PUSH0) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨569⟩, 0x81, .DUP2) (by evm_ov),
    raw mstore (Cₘ aw4 - Cₘ aw3) mem3 aw4
      (by attester_decode_at v, ⟨570⟩, 0x52, .MSTORE)
      hcostStoreZero (by rfl) (by rfl) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨571⟩, 0x50, .POP) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨572⟩, 0x82, .DUP3) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨573⟩, 0x82, .DUP3) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨574⟩, 0x81, .DUP2) (by evm_ov),
    raw mload (Cₘ aw5 - Cₘ aw4) loadLen aw5
      (by attester_decode_at v, ⟨575⟩, 0x51, .MLOAD)
      hcostMloadBase (by rfl) (by rfl) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨576⟩, 0x81, .DUP2) (by evm_ov),
    raw lt (by attester_decode_at v, ⟨577⟩, 0x10, .LT) (by evm_ov),
    raw push2 ⟨589⟩ (by attester_decode_at v, ⟨578⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jumpiT (by attester_decode_at v, ⟨581⟩, 0x57, .JUMPI)
      (by rw [hloadLt]; decide)
      (attesterMultiRevokeInnerArrayCopyStoreOkJumpdest v) (by evm_ov),
    raw jumpdest (by attester_decode_at v, ⟨589⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨590⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨592⟩, 0x90, .SWAP1) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨593⟩, 0x81, .DUP2) (by evm_ov),
    raw mul (by attester_decode_at v, ⟨594⟩, 0x02, .MUL) (by evm_ov),
    raw swap2 (by attester_decode_at v, ⟨595⟩, 0x91, .SWAP2) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨596⟩, 0x90, .SWAP1) (by evm_ov),
    raw swap2 (by attester_decode_at v, ⟨597⟩, 0x91, .SWAP2) (by evm_ov),
    raw add (by attester_decode_at v, ⟨598⟩, 0x01, .ADD) (by evm_ov),
    raw add (by attester_decode_at v, ⟨599⟩, 0x01, .ADD) (by evm_ov),
    raw mstore (Cₘ aw6 - Cₘ aw5) mem4 aw6
      (by attester_decode_at v, ⟨600⟩, 0x52, .MSTORE)
      hcostStoreSlot (by rfl) (by rfl) (by evm_ov),
    raw push1 ⟨1⟩ (by attester_decode_at v, ⟨601⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw add (by attester_decode_at v, ⟨603⟩, 0x01, .ADD) (by evm_ov),
    raw push2 ⟨518⟩ (by attester_decode_at v, ⟨604⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jump (by attester_decode_at v, ⟨607⟩, 0x56, .JUMP)
      (attesterMultiRevokeInnerArrayCopyLoopJumpdest v) (by evm_ov)]⟩

theorem attesterX_multiRevokeInnerArrayCopyNonFinalIterationOfLenReadable
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {idx base len payload : UInt256} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {k C}
    (htail : tail.length ≤ 1000)
    (hlt : UInt256.lt idx len = ⟨1⟩)
    (hloadLen :
      attesterMloadWord
        (attesterMultiRevokeInnerArrayCopyZeroMem I payload idx mem aw)
        (attesterMultiRevokeInnerArrayCopyZeroAw I payload idx mem aw)
        base = len)
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨518⟩ : UInt256)
      (idx :: base :: len :: len :: payload :: tail)
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨518⟩ : UInt256)
      (attesterMultiRevokeInnerArrayCopyNextIdx idx ::
        base :: len :: len :: payload :: tail)
      (attesterMultiRevokeInnerArrayCopyStepMem I base payload idx mem aw)
      (attesterMultiRevokeInnerArrayCopyStepAw I base payload idx mem aw)
      ByteArray.empty (cA, σ) k' C' := by
  exact attesterX_multiRevokeInnerArrayCopyNonFinalIteration
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) v
    (idx := idx) (base := base) (len := len) (payload := payload)
    (tail := tail) (mem := mem) (aw := aw) (k := k) (C := C)
    htail hlt (by rw [hloadLen, hlt]) hreach

set_option maxHeartbeats 1000000 in
theorem attesterX_multiRevokeInnerArrayCopyLoopWithReadInvariant
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {base len payload : UInt256} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {k C}
    (htail : tail.length ≤ 1000)
    (hread0 :
      attesterMloadWord
        (attesterMultiRevokeInnerArrayCopyZeroMem I payload (⟨0⟩ : UInt256) mem aw)
        (attesterMultiRevokeInnerArrayCopyZeroAw I payload (⟨0⟩ : UInt256) mem aw)
        base = len)
    (hreadStep :
      ∀ n a,
        a.idx = UInt256.ofNat (len.toNat - (n + 1)) →
        n + 1 ≤ len.toNat →
        attesterMloadWord
          (attesterMultiRevokeInnerArrayCopyZeroMem I payload a.idx a.mem a.aw)
          (attesterMultiRevokeInnerArrayCopyZeroAw I payload a.idx a.mem a.aw)
          base = len →
        attesterMloadWord
          (attesterMultiRevokeInnerArrayCopyZeroMem I payload
            (attesterMultiRevokeInnerArrayCopyStepState I base payload a).idx
            (attesterMultiRevokeInnerArrayCopyStepState I base payload a).mem
            (attesterMultiRevokeInnerArrayCopyStepState I base payload a).aw)
          (attesterMultiRevokeInnerArrayCopyZeroAw I payload
            (attesterMultiRevokeInnerArrayCopyStepState I base payload a).idx
            (attesterMultiRevokeInnerArrayCopyStepState I base payload a).mem
            (attesterMultiRevokeInnerArrayCopyStepState I base payload a).aw)
          base = len)
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨518⟩ : UInt256)
      ((⟨0⟩ : UInt256) :: base :: len :: len :: payload :: tail)
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ a' k' C',
      a'.idx = len ∧
      RD (patchedRuntime v) I g
        (initState cA gh bl σ σ₀ g A I) (⟨608⟩ : UInt256)
        (attesterMultiRevokeInnerArrayCopyStack base len payload tail a')
        a'.mem a'.aw ByteArray.empty (cA, σ) k' C' := by
  let Inv : Nat → AttesterMultiRevokeInnerArrayCopyState → Prop :=
    fun n a =>
      a.idx = UInt256.ofNat (len.toNat - n) ∧
      n ≤ len.toNat ∧
      attesterMloadWord
        (attesterMultiRevokeInnerArrayCopyZeroMem I payload a.idx a.mem a.aw)
        (attesterMultiRevokeInnerArrayCopyZeroAw I payload a.idx a.mem a.aw)
        base = len
  let stk := attesterMultiRevokeInnerArrayCopyStack base len payload tail
  let memOf : AttesterMultiRevokeInnerArrayCopyState → ByteArray := fun a => a.mem
  let awOf : AttesterMultiRevokeInnerArrayCopyState → UInt256 := fun a => a.aw
  have hexit :
      ∀ a, Inv 0 a → ∀ k C,
        RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
          (⟨518⟩ : UInt256) (stk a) (memOf a) (awOf a)
          ByteArray.empty (cA, σ) k C →
        ∃ k' C',
          RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
            (⟨608⟩ : UInt256) (stk a) (memOf a) (awOf a)
            ByteArray.empty (cA, σ) k' C' := by
    intro a hInv k C rd
    have hidxLen : a.idx = len := by
      rw [hInv.1]
      simpa using (u256_ofNat_toNat len)
    have hge : UInt256.lt a.idx len = (⟨0⟩ : UInt256) := by
      rw [hidxLen]
      exact ult_zero (a := len) (b := len) (by rfl)
    exact attesterX_multiRevokeInnerArrayCopyExit
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (idx := a.idx) (base := base) (len := len) (payload := payload)
      (tail := tail) (mem := a.mem) (aw := a.aw) (k := k) (C := C)
      htail hge
      (by simpa [stk, memOf, awOf, attesterMultiRevokeInnerArrayCopyStack] using rd)
  have hbody :
      ∀ n a, Inv (n + 1) a → ∀ k C,
        RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
          (⟨518⟩ : UInt256) (stk a) (memOf a) (awOf a)
          ByteArray.empty (cA, σ) k C →
        ∃ a' k' C',
          Inv n a' ∧
          RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
            (⟨518⟩ : UInt256) (stk a') (memOf a') (awOf a')
            ByteArray.empty (cA, σ) k' C' := by
    intro n a hInv k C rd
    let a' := attesterMultiRevokeInnerArrayCopyStepState I base payload a
    have hidxNat : a.idx.toNat = len.toNat - (n + 1) := by
      rw [hInv.1]
      exact ulit_toNat' (len.toNat - (n + 1))
        (lt_of_le_of_lt (Nat.sub_le _ _) len.val.isLt)
    have hltNat : a.idx.toNat < len.toNat := by
      have hle : n + 1 ≤ len.toNat := hInv.2.1
      omega
    have hlt : UInt256.lt a.idx len = (⟨1⟩ : UInt256) :=
      ult_one hltNat
    obtain ⟨k', C', rd'⟩ :=
      attesterX_multiRevokeInnerArrayCopyNonFinalIterationOfLenReadable
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) v
        (idx := a.idx) (base := base) (len := len) (payload := payload)
        (tail := tail) (mem := a.mem) (aw := a.aw) (k := k) (C := C)
        htail hlt hInv.2.2
        (by simpa [stk, memOf, awOf, attesterMultiRevokeInnerArrayCopyStack] using rd)
    refine ⟨a', k', C', ?_, ?_⟩
    · constructor
      · have hnext :
            attesterMultiRevokeInnerArrayCopyNextIdx a.idx =
              UInt256.ofNat (len.toNat - n) := by
          rw [hInv.1]
          exact attesterMultiRevokeInnerArrayCopyNextIdx_ofNat
            (len := len.toNat) (n := n) hInv.2.1 len.val.isLt
        simpa [a', attesterMultiRevokeInnerArrayCopyStepState] using hnext
      · constructor
        · have := hInv.2.1
          omega
        · exact hreadStep n a hInv.1 hInv.2.1 hInv.2.2
    · simpa [a', stk, memOf, awOf, attesterMultiRevokeInnerArrayCopyStack,
        attesterMultiRevokeInnerArrayCopyStepState] using rd'
  let a0 : AttesterMultiRevokeInnerArrayCopyState :=
    { idx := (⟨0⟩ : UInt256), mem := mem, aw := aw }
  have hInv0 : Inv len.toNat a0 := by
    constructor
    · have hsub : len.toNat - len.toNat = 0 := by omega
      rw [hsub]
      apply u256_inj
      rfl
    · constructor
      · omega
      · simpa [a0] using hread0
  obtain ⟨a', k', C', hInvFinal, rdFinal⟩ :=
    RD.whileLoopCarryExit
      (code := patchedRuntime v) (ee := I) (g := g)
      (s0 := initState cA gh bl σ σ₀ g A I)
      (rdata := ByteArray.empty) (acc := (cA, σ))
      (header := (⟨518⟩ : UInt256)) (exit := (⟨608⟩ : UInt256))
      Inv stk memOf awOf stk memOf awOf hexit hbody
      len.toNat a0 hInv0 k C
      (by
        simpa [a0, stk, memOf, awOf, attesterMultiRevokeInnerArrayCopyStack]
          using hreach)
  exact ⟨a', k', C', by
    have hidx := hInvFinal.1
    rw [hidx]
    simpa using (u256_ofNat_toNat len), rdFinal⟩

set_option maxHeartbeats 1000000 in
theorem attesterX_multiRevokeInnerArrayCopyLoopWithStateInvariant
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {base len payload : UInt256} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {k C}
    (htail : tail.length ≤ 1000)
    (Inv : Nat → AttesterMultiRevokeInnerArrayCopyState → Prop)
    (hidx :
      ∀ n a, Inv n a → a.idx = UInt256.ofNat (len.toNat - n))
    (hle : ∀ n a, Inv n a → n ≤ len.toNat)
    (hload :
      ∀ n a, Inv n a →
        attesterMloadWord
          (attesterMultiRevokeInnerArrayCopyZeroMem I payload a.idx a.mem a.aw)
          (attesterMultiRevokeInnerArrayCopyZeroAw I payload a.idx a.mem a.aw)
          base = len)
    (hstep :
      ∀ n a, Inv (n + 1) a →
        Inv n (attesterMultiRevokeInnerArrayCopyStepState I base payload a))
    (hinit :
      Inv len.toNat
        { idx := (⟨0⟩ : UInt256), mem := mem, aw := aw })
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨518⟩ : UInt256)
      ((⟨0⟩ : UInt256) :: base :: len :: len :: payload :: tail)
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ a' k' C',
      a'.idx = len ∧
      Inv 0 a' ∧
      RD (patchedRuntime v) I g
        (initState cA gh bl σ σ₀ g A I) (⟨608⟩ : UInt256)
        (attesterMultiRevokeInnerArrayCopyStack base len payload tail a')
        a'.mem a'.aw ByteArray.empty (cA, σ) k' C' := by
  let stk := attesterMultiRevokeInnerArrayCopyStack base len payload tail
  let memOf : AttesterMultiRevokeInnerArrayCopyState → ByteArray := fun a => a.mem
  let awOf : AttesterMultiRevokeInnerArrayCopyState → UInt256 := fun a => a.aw
  have hexit :
      ∀ a, Inv 0 a → ∀ k C,
        RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
          (⟨518⟩ : UInt256) (stk a) (memOf a) (awOf a)
          ByteArray.empty (cA, σ) k C →
        ∃ k' C',
          RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
            (⟨608⟩ : UInt256) (stk a) (memOf a) (awOf a)
            ByteArray.empty (cA, σ) k' C' := by
    intro a hInv k C rd
    have hidxLen : a.idx = len := by
      rw [hidx 0 a hInv]
      simpa using (u256_ofNat_toNat len)
    have hge : UInt256.lt a.idx len = (⟨0⟩ : UInt256) := by
      rw [hidxLen]
      exact ult_zero (a := len) (b := len) (by rfl)
    exact attesterX_multiRevokeInnerArrayCopyExit
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (idx := a.idx) (base := base) (len := len) (payload := payload)
      (tail := tail) (mem := a.mem) (aw := a.aw) (k := k) (C := C)
      htail hge
      (by simpa [stk, memOf, awOf, attesterMultiRevokeInnerArrayCopyStack] using rd)
  have hbody :
      ∀ n a, Inv (n + 1) a → ∀ k C,
        RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
          (⟨518⟩ : UInt256) (stk a) (memOf a) (awOf a)
          ByteArray.empty (cA, σ) k C →
        ∃ a' k' C',
          Inv n a' ∧
          RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
            (⟨518⟩ : UInt256) (stk a') (memOf a') (awOf a')
            ByteArray.empty (cA, σ) k' C' := by
    intro n a hInv k C rd
    let a' := attesterMultiRevokeInnerArrayCopyStepState I base payload a
    have hidxNat : a.idx.toNat = len.toNat - (n + 1) := by
      rw [hidx (n + 1) a hInv]
      exact ulit_toNat' (len.toNat - (n + 1))
        (lt_of_le_of_lt (Nat.sub_le _ _) len.val.isLt)
    have hltNat : a.idx.toNat < len.toNat := by
      have hle' : n + 1 ≤ len.toNat := hle (n + 1) a hInv
      omega
    have hlt : UInt256.lt a.idx len = (⟨1⟩ : UInt256) :=
      ult_one hltNat
    obtain ⟨k', C', rd'⟩ :=
      attesterX_multiRevokeInnerArrayCopyNonFinalIterationOfLenReadable
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) v
        (idx := a.idx) (base := base) (len := len) (payload := payload)
        (tail := tail) (mem := a.mem) (aw := a.aw) (k := k) (C := C)
        htail hlt (hload (n + 1) a hInv)
        (by simpa [stk, memOf, awOf, attesterMultiRevokeInnerArrayCopyStack] using rd)
    refine ⟨a', k', C', hstep n a hInv, ?_⟩
    simpa [a', stk, memOf, awOf, attesterMultiRevokeInnerArrayCopyStack,
      attesterMultiRevokeInnerArrayCopyStepState] using rd'
  let a0 : AttesterMultiRevokeInnerArrayCopyState :=
    { idx := (⟨0⟩ : UInt256), mem := mem, aw := aw }
  obtain ⟨a', k', C', hInvFinal, rdFinal⟩ :=
    RD.whileLoopCarryExit
      (code := patchedRuntime v) (ee := I) (g := g)
      (s0 := initState cA gh bl σ σ₀ g A I)
      (rdata := ByteArray.empty) (acc := (cA, σ))
      (header := (⟨518⟩ : UInt256)) (exit := (⟨608⟩ : UInt256))
      Inv stk memOf awOf stk memOf awOf hexit hbody
      len.toNat a0 (by simpa [a0] using hinit) k C
      (by
        simpa [a0, stk, memOf, awOf, attesterMultiRevokeInnerArrayCopyStack]
          using hreach)
  exact ⟨a', k', C',
    by
      rw [hidx 0 a' hInvFinal]
      simpa using (u256_ofNat_toNat len),
    hInvFinal, rdFinal⟩

theorem attesterX_multiRevokeFirstInnerArrayCopyProgressWithReadInvariant
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
    (hread0 :
      ∀ (a' : AttesterMultiOuterArrayInitState)
        (b' : AttesterMultiRevokeInnerArrayInitState),
        a'.remaining = (⟨1⟩ : UInt256) →
        b'.remaining = (⟨1⟩ : UInt256) →
        attesterMloadWord
          (attesterMultiRevokeInnerArrayCopyZeroMem I
            (attesterFirstInnerArrayStartWord I + ⟨32⟩)
            (⟨0⟩ : UInt256)
            (attesterMultiRevokeInnerArrayInitFinalMem b')
            (attesterMultiRevokeInnerArrayInitFinalAw b'))
          (attesterMultiRevokeInnerArrayCopyZeroAw I
            (attesterFirstInnerArrayStartWord I + ⟨32⟩)
            (⟨0⟩ : UInt256)
            (attesterMultiRevokeInnerArrayInitFinalMem b')
            (attesterMultiRevokeInnerArrayInitFinalAw b'))
          (attesterInnerArrayAllocFreeWord
            (attesterMultiOuterArrayInitFinalMem a')
            (attesterMultiOuterArrayInitFinalAw a')) =
          attesterFirstInnerArrayLengthWord I)
    (hreadStep :
      ∀ (a' : AttesterMultiOuterArrayInitState) n s,
        s.idx =
          UInt256.ofNat
            ((attesterFirstInnerArrayLengthWord I).toNat - (n + 1)) →
        n + 1 ≤ (attesterFirstInnerArrayLengthWord I).toNat →
        attesterMloadWord
          (attesterMultiRevokeInnerArrayCopyZeroMem I
            (attesterFirstInnerArrayStartWord I + ⟨32⟩) s.idx s.mem s.aw)
          (attesterMultiRevokeInnerArrayCopyZeroAw I
            (attesterFirstInnerArrayStartWord I + ⟨32⟩) s.idx s.mem s.aw)
          (attesterInnerArrayAllocFreeWord
            (attesterMultiOuterArrayInitFinalMem a')
            (attesterMultiOuterArrayInitFinalAw a')) =
          attesterFirstInnerArrayLengthWord I →
        attesterMloadWord
          (attesterMultiRevokeInnerArrayCopyZeroMem I
            (attesterFirstInnerArrayStartWord I + ⟨32⟩)
            (attesterMultiRevokeInnerArrayCopyStepState I
              (attesterInnerArrayAllocFreeWord
                (attesterMultiOuterArrayInitFinalMem a')
                (attesterMultiOuterArrayInitFinalAw a'))
              (attesterFirstInnerArrayStartWord I + ⟨32⟩) s).idx
            (attesterMultiRevokeInnerArrayCopyStepState I
              (attesterInnerArrayAllocFreeWord
                (attesterMultiOuterArrayInitFinalMem a')
                (attesterMultiOuterArrayInitFinalAw a'))
              (attesterFirstInnerArrayStartWord I + ⟨32⟩) s).mem
            (attesterMultiRevokeInnerArrayCopyStepState I
              (attesterInnerArrayAllocFreeWord
                (attesterMultiOuterArrayInitFinalMem a')
                (attesterMultiOuterArrayInitFinalAw a'))
              (attesterFirstInnerArrayStartWord I + ⟨32⟩) s).aw)
          (attesterMultiRevokeInnerArrayCopyZeroAw I
            (attesterFirstInnerArrayStartWord I + ⟨32⟩)
            (attesterMultiRevokeInnerArrayCopyStepState I
              (attesterInnerArrayAllocFreeWord
                (attesterMultiOuterArrayInitFinalMem a')
                (attesterMultiOuterArrayInitFinalAw a'))
              (attesterFirstInnerArrayStartWord I + ⟨32⟩) s).idx
            (attesterMultiRevokeInnerArrayCopyStepState I
              (attesterInnerArrayAllocFreeWord
                (attesterMultiOuterArrayInitFinalMem a')
                (attesterMultiOuterArrayInitFinalAw a'))
              (attesterFirstInnerArrayStartWord I + ⟨32⟩) s).mem
            (attesterMultiRevokeInnerArrayCopyStepState I
              (attesterInnerArrayAllocFreeWord
                (attesterMultiOuterArrayInitFinalMem a')
                (attesterMultiOuterArrayInitFinalAw a'))
              (attesterFirstInnerArrayStartWord I + ⟨32⟩) s).aw)
          (attesterInnerArrayAllocFreeWord
            (attesterMultiOuterArrayInitFinalMem a')
            (attesterMultiOuterArrayInitFinalAw a')) =
          attesterFirstInnerArrayLengthWord I) :
    ∃ (a' : AttesterMultiOuterArrayInitState),
    ∃ (b' : AttesterMultiRevokeInnerArrayInitState),
    ∃ (c' : AttesterMultiRevokeInnerArrayCopyState),
    ∃ k C,
      a'.remaining = (⟨1⟩ : UInt256) ∧
      b'.remaining = (⟨1⟩ : UInt256) ∧
      c'.idx = attesterFirstInnerArrayLengthWord I ∧
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
  obtain ⟨c', k1, C1, hcidx, rd1⟩ :=
    attesterX_multiRevokeInnerArrayCopyLoopWithReadInvariant
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
      (hread0 a' b' harem hbrem)
      (hreadStep a') (by simpa [attesterMultiRevokeInnerArrayInitExitStack] using rd0)
  exact ⟨a', b', c', k1, C1, harem, hbrem, hcidx, rd1⟩

end Benchmarks.EAS.Attester
