import Benchmarks.EAS.Attester.InnerArrayCopy

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.EAS.Attester.Immutables

namespace Benchmarks.EAS.Attester

theorem attesterToByteArray_write_eq_nat (v : UInt256) (mem : ByteArray) (off : Nat)
    (hoff : mem.size ≤ off) :
    (UInt256.toByteArray v).write 0 mem off 32 =
      mem ++ ffi.ByteArray.zeroes (off - mem.size) ++ UInt256.toByteArray v := by
  have hsz : (UInt256.toByteArray v).data.size = 32 := UInt256.toByteArrayWithSizeProof v |>.2
  have hpz : (ffi.ByteArray.zeroes (off - mem.size)).data.size = off - mem.size := by
    rw [show (ffi.ByteArray.zeroes (off - mem.size)).data.size =
        (ffi.ByteArray.zeroes (off - mem.size)).size from rfl, ByteArray_zeroes_size]
  apply ByteArray.ext
  unfold ByteArray.write
  rw [if_neg (by decide : ¬ ((32 : Nat) = 0)),
    if_neg (show ¬ (0 ≥ (UInt256.toByteArray v).size) from by
      rw [show (UInt256.toByteArray v).size = 32 from hsz]; omega)]
  simp only [ByteArray.data_copySlice, ByteArray.data_append]
  have hv : v.toByteArray.size = 32 := hsz
  have hDsz : (mem.data ++ (ffi.ByteArray.zeroes (off - mem.size)).data).size = off := by
    rw [Array.size_append, hpz]
    show mem.size + (off - mem.size) = off
    omega
  rw [hv, show (min 32 (32 - 0) : Nat) = 32 from rfl,
    show min mem.size (off + 32) - (off + 32) = 0 from by omega,
    show (ffi.ByteArray.zeroes 0).data = (#[] : Array UInt8) from by
      rw [zeroes_zero (n := 0) (by rfl)]
      rfl]
  rw [Array.append_empty]
  rw [Array.extract_eq_self_of_le (by rw [hDsz]),
    Array.extract_eq_self_of_le (show v.toByteArray.data.size ≤ 0 + (32 + 0) from by rw [hsz]),
    Array.extract_eq_empty_of_le (by rw [hDsz]; omega),
    Array.append_empty]

theorem attesterWriteWord_size_nat (mem : ByteArray) (off : Nat) (word : UInt256) :
    (Reasoning.Theory.writeWord mem off word).size = max mem.size (off + 32) := by
  unfold Reasoning.Theory.writeWord
  by_cases hoff : off ≤ mem.size
  · rw [toByteArray_write32_size_of_le mem word off mem.size (max mem.size (off + 32))
      rfl hoff rfl]
  · have hge : mem.size ≤ off := by omega
    rw [attesterToByteArray_write_eq_nat word mem off hge]
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray_zeroes_size, toByteArray_size]
    rw [max_eq_right (by omega)]
    omega

theorem attesterWriteWord_size_ge_nat (mem : ByteArray) (off : Nat) (word : UInt256) :
    mem.size ≤ (Reasoning.Theory.writeWord mem off word).size := by
  rw [attesterWriteWord_size_nat]
  exact Nat.le_max_left _ _

theorem attesterWriteWord_read_back_nat (mem : ByteArray) (off : Nat) (word : UInt256) :
    (Reasoning.Theory.writeWord mem off word).readWithPadding off 32 =
      UInt256.toByteArray word := by
  unfold Reasoning.Theory.writeWord
  by_cases hle : off ≤ mem.size
  · rw [write32_read_back _ _ off (by rw [toByteArray_size]) hle]
    rw [show 32 = (UInt256.toByteArray word).size by rw [toByteArray_size]]
    exact byteArray_extract_self _
  · have hge : mem.size ≤ off := by omega
    rw [attesterToByteArray_write_eq_nat word mem off hge]
    rw [readWithPadding_eq_extract _ off (by
      rw [ByteArray.size_append, ByteArray.size_append, ByteArray_zeroes_size, toByteArray_size]
      omega)]
    rw [extract_append_right_window
      (mem ++ ffi.ByteArray.zeroes (off - mem.size))
      (UInt256.toByteArray word) off (off + 32) (by
        rw [ByteArray.size_append, ByteArray_zeroes_size]
        omega)]
    rw [ByteArray.size_append, ByteArray_zeroes_size]
    rw [show off - (mem.size + (off - mem.size)) = 0 by omega,
      show off + 32 - (mem.size + (off - mem.size)) = 32 by omega]
    rw [show (UInt256.toByteArray word).extract 0 32 = UInt256.toByteArray word from by
      rw [show 32 = (UInt256.toByteArray word).size by rw [toByteArray_size]]
      exact byteArray_extract_self _]

theorem attesterWriteWord_read_below_len_nat (mem : ByteArray) (off : Nat)
    (word : UInt256) (read len : Nat)
    (hread : read + len ≤ mem.size) (hbelow : read + len ≤ off)
    (hpos : 0 < len) (hlen64 : len < 2 ^ 64) :
    (Reasoning.Theory.writeWord mem off word).readWithPadding read len =
      mem.readWithPadding read len := by
  unfold Reasoning.Theory.writeWord
  by_cases hle : off ≤ mem.size
  · exact write32_read_below_len _ _ off read len (by rw [toByteArray_size]) hle
      hbelow hread hpos hlen64
  · have hge : mem.size ≤ off := by omega
    rw [attesterToByteArray_write_eq_nat word mem off hge]
    rw [readWithPadding_eq_extract' _ read len hpos hlen64 (by
      rw [ByteArray.size_append, ByteArray.size_append, ByteArray_zeroes_size, toByteArray_size]
      omega)]
    rw [extract_append_left _ _ _ _ (by
      rw [ByteArray.size_append, ByteArray_zeroes_size]
      omega)]
    rw [extract_append_left _ _ _ _ hread]
    exact (readWithPadding_eq_extract' _ read len hpos hlen64 hread).symm

theorem attesterWriteWord_read_preserved_len_nat (mem : ByteArray) (off read len : Nat)
    (word : UInt256)
    (hdisj :
      (read + len ≤ off ∧ read + len ≤ mem.size) ∨
      (off + 32 ≤ read ∧ read + len ≤ mem.size))
    (hpos : 0 < len) (hlen64 : len < 2 ^ 64) :
    (Reasoning.Theory.writeWord mem off word).readWithPadding read len =
      mem.readWithPadding read len := by
  rcases hdisj with hbelow | habove
  · exact attesterWriteWord_read_below_len_nat mem off word read len
      hbelow.2 hbelow.1 hpos hlen64
  · unfold Reasoning.Theory.writeWord
    exact write32_read_above_len _ _ off read len (by rw [toByteArray_size])
      (by omega) habove.1 habove.2 hpos hlen64

theorem attesterReadWithPadding_writeWord_preserved_above_nat
    {mem : ByteArray} {base writeOff : Nat} {len writeVal : UInt256}
    (hmem : base + 32 ≤ mem.size)
    (habove : base + 32 ≤ writeOff)
    (hread : mem.readWithPadding base 32 = UInt256.toByteArray len) :
    (Reasoning.Theory.writeWord mem writeOff writeVal).readWithPadding base 32 =
      UInt256.toByteArray len := by
  rw [attesterWriteWord_read_preserved_len_nat mem writeOff base 32 writeVal
    (Or.inl ⟨habove, hmem⟩) (by norm_num) (by norm_num), hread]

theorem attesterReadWithPadding_writeWord_preserved_below_nat
    {mem : ByteArray} {base writeOff : Nat} {len writeVal : UInt256}
    (hmem : base + 32 ≤ mem.size)
    (hbelow : writeOff + 32 ≤ base)
    (hread : mem.readWithPadding base 32 = UInt256.toByteArray len) :
    (Reasoning.Theory.writeWord mem writeOff writeVal).readWithPadding base 32 =
      UInt256.toByteArray len := by
  rw [attesterWriteWord_read_preserved_len_nat mem writeOff base 32 writeVal
    (Or.inr ⟨hbelow, hmem⟩) (by norm_num) (by norm_num), hread]

theorem attesterMultiOuterArrayLenMem_read128 (I : ExecutionEnv) :
    (attesterMultiOuterArrayLenMem I).readWithPadding 128 32 =
      UInt256.toByteArray (attesterFirstArrayLengthWord I) := by
  unfold attesterMultiOuterArrayLenMem
  change
    (Reasoning.Theory.writeWord solcFreePtrMem 128
      (attesterFirstArrayLengthWord I)).readWithPadding 128 32 =
      UInt256.toByteArray (attesterFirstArrayLengthWord I)
  exact attesterWriteWord_read_back_nat solcFreePtrMem 128
    (attesterFirstArrayLengthWord I)

theorem attesterMultiOuterArrayAllocMem_read128 (I : ExecutionEnv) :
    (attesterMultiOuterArrayAllocMem I).readWithPadding 128 32 =
      UInt256.toByteArray (attesterFirstArrayLengthWord I) := by
  unfold attesterMultiOuterArrayAllocMem
  change
    (Reasoning.Theory.writeWord (attesterMultiOuterArrayLenMem I) 64
      (attesterMultiOuterArrayAllocEndWord I)).readWithPadding 128 32 =
      UInt256.toByteArray (attesterFirstArrayLengthWord I)
  exact attesterReadWithPadding_writeWord_preserved_below_nat
    (mem := attesterMultiOuterArrayLenMem I)
    (base := 128) (writeOff := 64)
    (len := attesterFirstArrayLengthWord I)
    (writeVal := attesterMultiOuterArrayAllocEndWord I)
    (by rw [attesterMultiOuterArrayLenMem_size I])
    (by norm_num)
    (attesterMultiOuterArrayLenMem_read128 I)

theorem attesterMultiOuterArrayAllocEndWord_toNat {I : ExecutionEnv}
    (hlen : (attesterFirstArrayLengthWord I).toNat ≤ solcMaxU64) :
    (attesterMultiOuterArrayAllocEndWord I).toNat =
      160 + 32 * (attesterFirstArrayLengthWord I).toNat := by
  unfold attesterMultiOuterArrayAllocEndWord
  have hmul :
      (UInt256.mul (⟨32⟩ : UInt256) (attesterFirstArrayLengthWord I)).toNat =
        32 * (attesterFirstArrayLengthWord I).toNat := by
    rw [u256_mul_toNat]
    rw [show (⟨32⟩ : UInt256).toNat = 32 by decide]
    exact Nat.mod_eq_of_lt (by
      norm_num [solcMaxU64, UInt256.size] at hlen ⊢
      omega)
  have hinner :
      (((⟨32⟩ : UInt256) +
          UInt256.mul (⟨32⟩ : UInt256) (attesterFirstArrayLengthWord I)).toNat) =
        32 + 32 * (attesterFirstArrayLengthWord I).toNat := by
    rw [uadd_toNat, hmul]
    rw [show (⟨32⟩ : UInt256).toNat = 32 by decide]
    exact Nat.mod_eq_of_lt (by
      norm_num [solcMaxU64, UInt256.size] at hlen ⊢
      omega)
  rw [uadd_toNat, hinner]
  rw [show (⟨128⟩ : UInt256).toNat = 128 by decide]
  rw [show 128 + (32 + 32 * (attesterFirstArrayLengthWord I).toNat) =
      160 + 32 * (attesterFirstArrayLengthWord I).toNat by omega]
  exact Nat.mod_eq_of_lt (by
    have hbound : 32 * (attesterFirstArrayLengthWord I).toNat ≤
        32 * solcMaxU64 := Nat.mul_le_mul_left 32 hlen
    norm_num [solcMaxU64, UInt256.size] at hbound ⊢
    omega)

theorem attesterInnerArrayAllocEndWord_toNat
    {len free : UInt256}
    (hfree : free.toNat + 32 + 32 * len.toNat < UInt256.size) :
    (free + ((⟨32⟩ : UInt256) + UInt256.mul (⟨32⟩ : UInt256) len)).toNat =
      free.toNat + 32 + 32 * len.toNat := by
  have hmul :
      (UInt256.mul (⟨32⟩ : UInt256) len).toNat = 32 * len.toNat := by
    rw [u256_mul_toNat]
    rw [show (⟨32⟩ : UInt256).toNat = 32 by decide]
    exact Nat.mod_eq_of_lt (by omega)
  have hinner :
      (((⟨32⟩ : UInt256) + UInt256.mul (⟨32⟩ : UInt256) len).toNat) =
        32 + 32 * len.toNat := by
    rw [uadd_toNat, hmul]
    rw [show (⟨32⟩ : UInt256).toNat = 32 by decide]
    exact Nat.mod_eq_of_lt (by omega)
  rw [uadd_toNat, hinner]
  rw [show free.toNat + (32 + 32 * len.toNat) =
      free.toNat + 32 + 32 * len.toNat by omega]
  exact Nat.mod_eq_of_lt hfree

theorem attesterMultiRevokeInnerArrayCopySlotWord_toNat
    {base idx : UInt256}
    (hbound : base.toNat + 32 + 32 * idx.toNat < UInt256.size) :
    (attesterMultiRevokeInnerArrayCopySlotWord base idx).toNat =
      base.toNat + 32 + 32 * idx.toNat := by
  unfold attesterMultiRevokeInnerArrayCopySlotWord
  have hmul :
      (UInt256.mul (⟨32⟩ : UInt256) idx).toNat = 32 * idx.toNat := by
    rw [u256_mul_toNat]
    rw [show (⟨32⟩ : UInt256).toNat = 32 by decide]
    exact Nat.mod_eq_of_lt (by omega)
  have hadd :
      (UInt256.mul (⟨32⟩ : UInt256) idx + base).toNat =
        32 * idx.toNat + base.toNat := by
    rw [uadd_toNat, hmul]
    exact Nat.mod_eq_of_lt (by omega)
  rw [uadd_toNat, hadd]
  rw [show (⟨32⟩ : UInt256).toNat = 32 by decide]
  rw [show 32 * idx.toNat + base.toNat + 32 =
      base.toNat + 32 + 32 * idx.toNat by omega]
  exact Nat.mod_eq_of_lt hbound

theorem attesterMultiRevokeInnerArrayCopySlotWord_above_base
    {base idx : UInt256}
    (hbound : base.toNat + 32 + 32 * idx.toNat < UInt256.size) :
    base.toNat + 32 ≤
      (attesterMultiRevokeInnerArrayCopySlotWord base idx).toNat := by
  rw [attesterMultiRevokeInnerArrayCopySlotWord_toNat (base := base) (idx := idx) hbound]
  omega

theorem attesterMultiRevokeInnerArrayCopyZeroWord_toNat
    {mem : ByteArray} {aw : UInt256}
    (hfree32 : (attesterMultiRevokeInnerArrayCopyFreeWord mem aw).toNat + 32 <
      UInt256.size) :
    (attesterMultiRevokeInnerArrayCopyZeroWord mem aw).toNat =
      (attesterMultiRevokeInnerArrayCopyFreeWord mem aw).toNat + 32 := by
  unfold attesterMultiRevokeInnerArrayCopyZeroWord
  exact uadd_lit32_toNat
    (attesterMultiRevokeInnerArrayCopyFreeWord mem aw) hfree32

theorem attesterMloadActiveWordsCovers
    {base aw : UInt256}
    (hawMul : aw.toNat * 32 < UInt256.size)
    (hcovered : base.toNat + 32 ≤ aw.toNat * 32) :
    ¬ base ≥ aw * (⟨32⟩ : UInt256) := by
  intro hge
  have hmul :
      (aw * (⟨32⟩ : UInt256)).toNat = aw.toNat * 32 := by
    apply umul_toNat
    rw [show (⟨32⟩ : UInt256).toNat = 32 by decide]
    exact hawMul
  have hle : aw.toNat * 32 ≤ base.toNat := by
    change (aw * (⟨32⟩ : UInt256)).toNat ≤ base.toNat at hge
    rwa [hmul] at hge
  omega

theorem attesterMachineStateM_covers_word32 (s f : Nat) :
    f + 32 ≤ 32 * MachineState.M s f 32 := by
  unfold MachineState.M
  have hceil : f + 32 ≤ 32 * ((f + 32 + 31) / 32) := by
    have hdiv :
        (f + 32 + 31) / 32 ≤ (f + 32 + 31) / 32 := le_rfl
    rw [Nat.div_le_iff_le_mul (by decide : 0 < 32)] at hdiv
    omega
  have hmax : (f + 32 + 31) / 32 ≤ max s ((f + 32 + 31) / 32) :=
    Nat.le_max_right _ _
  nlinarith

theorem attesterMachineStateM_ge (s f l : Nat) :
    s ≤ MachineState.M s f l := by
  unfold MachineState.M
  cases l <;> simp

theorem attesterMachineStateM32_mul32_lt
    {s f : Nat}
    (hs : s * 32 < UInt256.size)
    (hf : f + 63 < UInt256.size) :
    MachineState.M s f 32 * 32 < UInt256.size := by
  unfold MachineState.M
  change max s ((f + 32 + 31) / 32) * 32 < UInt256.size
  have hceil : ((f + 32 + 31) / 32) * 32 ≤ f + 32 + 31 :=
    Nat.div_mul_le_self _ _
  by_cases hle : s ≤ (f + 32 + 31) / 32
  · rw [max_eq_right hle]
    omega
  · rw [max_eq_left (by omega)]
    exact hs

theorem attesterMachineStateM32_lt
    {s f : Nat}
    (hs : s * 32 < UInt256.size)
    (hf : f + 63 < UInt256.size) :
    MachineState.M s f 32 < UInt256.size := by
  have hmul := attesterMachineStateM32_mul32_lt (s := s) (f := f) hs hf
  have hle : MachineState.M s f 32 ≤ MachineState.M s f 32 * 32 := by
    nlinarith
  omega

theorem attesterMloadAw_ge
    {aw off : UInt256} {n : Nat}
    (hM : MachineState.M aw.toNat off.toNat 32 < UInt256.size)
    (hawGe : n ≤ aw.toNat) :
    n ≤ (attesterMloadAw aw off).toNat := by
  unfold attesterMloadAw
  rw [ulit_toNat' _ hM]
  exact le_trans hawGe (attesterMachineStateM_ge aw.toNat off.toNat 32)

theorem attesterMloadActiveWordsAfterM
    {base : UInt256} {s : Nat}
    (hM : MachineState.M s base.toNat 32 < UInt256.size)
    (hMul : MachineState.M s base.toNat 32 * 32 < UInt256.size) :
    ¬ base ≥
      UInt256.ofNat (MachineState.M s base.toNat 32) * (⟨32⟩ : UInt256) := by
  apply attesterMloadActiveWordsCovers
  · rw [ulit_toNat' _ hM]
    exact hMul
  · rw [ulit_toNat' _ hM]
    simpa [Nat.mul_comm] using attesterMachineStateM_covers_word32 s base.toNat

theorem attesterMload64ActiveWordsGe3
    {aw : UInt256}
    (hawMul : aw.toNat * 32 < UInt256.size)
    (hawGe : 3 ≤ aw.toNat) :
    ¬ (⟨64⟩ : UInt256) ≥ aw * (⟨32⟩ : UInt256) := by
  apply attesterMloadActiveWordsCovers
  · exact hawMul
  · rw [show (⟨64⟩ : UInt256).toNat = 64 by decide]
    nlinarith

theorem attester_uadd_lit64_toNat
    (a : UInt256) (h : a.toNat + 64 < UInt256.size) :
    (((⟨64⟩ : UInt256) + a).toNat = a.toNat + 64) := by
  rw [uadd_toNat, show (⟨64⟩ : UInt256).toNat = 64 by decide]
  rw [show 64 + a.toNat = a.toNat + 64 by omega]
  exact Nat.mod_eq_of_lt h

theorem attesterMultiOuterArrayInitStep_read64
    {slot : UInt256} {mem : ByteArray} {aw : UInt256}
    (hfree : 64 + 32 ≤ (attesterMultiOuterArrayInitFreeWord mem aw).toNat)
    (hoffset : 64 + 32 ≤ (attesterMultiOuterArrayInitOffsetWord mem aw).toNat)
    (hslot : 64 + 32 ≤ slot.toNat) :
    (attesterMultiOuterArrayInitStepMem slot mem aw).readWithPadding 64 32 =
      UInt256.toByteArray
        ((⟨64⟩ : UInt256) + attesterMultiOuterArrayInitFreeWord mem aw) := by
  have hread1 :
      (attesterMultiOuterArrayInitFreeMem mem aw).readWithPadding 64 32 =
        UInt256.toByteArray
          ((⟨64⟩ : UInt256) + attesterMultiOuterArrayInitFreeWord mem aw) := by
    change (Reasoning.Theory.writeWord mem 64
      ((⟨64⟩ : UInt256) + attesterMultiOuterArrayInitFreeWord mem aw)).readWithPadding
        64 32 =
        UInt256.toByteArray
          ((⟨64⟩ : UInt256) + attesterMultiOuterArrayInitFreeWord mem aw)
    exact attesterWriteWord_read_back_nat mem 64
      ((⟨64⟩ : UInt256) + attesterMultiOuterArrayInitFreeWord mem aw)
  have hmem1 : 64 + 32 ≤ (attesterMultiOuterArrayInitFreeMem mem aw).size := by
    have hsize := attesterWriteWord_size_nat mem 64
      ((⟨64⟩ : UInt256) + attesterMultiOuterArrayInitFreeWord mem aw)
    change 64 + 32 ≤
      (Reasoning.Theory.writeWord mem 64
        ((⟨64⟩ : UInt256) + attesterMultiOuterArrayInitFreeWord mem aw)).size
    rw [hsize]
    change 96 ≤ max mem.size (64 + 32)
    exact Nat.le_max_right _ _
  have hread2 :
      (attesterMultiOuterArrayInitZeroMem mem aw).readWithPadding 64 32 =
        UInt256.toByteArray
          ((⟨64⟩ : UInt256) + attesterMultiOuterArrayInitFreeWord mem aw) := by
    change (Reasoning.Theory.writeWord
      (attesterMultiOuterArrayInitFreeMem mem aw)
      (attesterMultiOuterArrayInitFreeWord mem aw).toNat
      (⟨0⟩ : UInt256)).readWithPadding 64 32 =
        UInt256.toByteArray
          ((⟨64⟩ : UInt256) + attesterMultiOuterArrayInitFreeWord mem aw)
    exact attesterReadWithPadding_writeWord_preserved_above_nat
      (mem := attesterMultiOuterArrayInitFreeMem mem aw)
      (base := 64)
      (writeOff := (attesterMultiOuterArrayInitFreeWord mem aw).toNat)
      (len := ((⟨64⟩ : UInt256) + attesterMultiOuterArrayInitFreeWord mem aw))
      (writeVal := (⟨0⟩ : UInt256))
      hmem1 hfree hread1
  have hmem2 : 64 + 32 ≤ (attesterMultiOuterArrayInitZeroMem mem aw).size := by
    have hsize := attesterWriteWord_size_nat (attesterMultiOuterArrayInitFreeMem mem aw)
      (attesterMultiOuterArrayInitFreeWord mem aw).toNat
      (⟨0⟩ : UInt256)
    change 64 + 32 ≤
      (Reasoning.Theory.writeWord (attesterMultiOuterArrayInitFreeMem mem aw)
        (attesterMultiOuterArrayInitFreeWord mem aw).toNat
        (⟨0⟩ : UInt256)).size
    rw [hsize]
    exact le_trans hmem1 (Nat.le_max_left _ _)
  have hread3 :
      (attesterMultiOuterArrayInitOffsetMem mem aw).readWithPadding 64 32 =
        UInt256.toByteArray
          ((⟨64⟩ : UInt256) + attesterMultiOuterArrayInitFreeWord mem aw) := by
    change (Reasoning.Theory.writeWord
      (attesterMultiOuterArrayInitZeroMem mem aw)
      (attesterMultiOuterArrayInitOffsetWord mem aw).toNat
      (⟨96⟩ : UInt256)).readWithPadding 64 32 =
        UInt256.toByteArray
          ((⟨64⟩ : UInt256) + attesterMultiOuterArrayInitFreeWord mem aw)
    exact attesterReadWithPadding_writeWord_preserved_above_nat
      (mem := attesterMultiOuterArrayInitZeroMem mem aw)
      (base := 64)
      (writeOff := (attesterMultiOuterArrayInitOffsetWord mem aw).toNat)
      (len := ((⟨64⟩ : UInt256) + attesterMultiOuterArrayInitFreeWord mem aw))
      (writeVal := (⟨96⟩ : UInt256))
      hmem2 hoffset hread2
  have hmem3 : 64 + 32 ≤ (attesterMultiOuterArrayInitOffsetMem mem aw).size := by
    have hsize := attesterWriteWord_size_nat (attesterMultiOuterArrayInitZeroMem mem aw)
      (attesterMultiOuterArrayInitOffsetWord mem aw).toNat
      (⟨96⟩ : UInt256)
    change 64 + 32 ≤
      (Reasoning.Theory.writeWord (attesterMultiOuterArrayInitZeroMem mem aw)
        (attesterMultiOuterArrayInitOffsetWord mem aw).toNat
        (⟨96⟩ : UInt256)).size
    rw [hsize]
    exact le_trans hmem2 (Nat.le_max_left _ _)
  change (Reasoning.Theory.writeWord
    (attesterMultiOuterArrayInitOffsetMem mem aw) slot.toNat
    (attesterMultiOuterArrayInitFreeWord mem aw)).readWithPadding 64 32 =
      UInt256.toByteArray
        ((⟨64⟩ : UInt256) + attesterMultiOuterArrayInitFreeWord mem aw)
  exact attesterReadWithPadding_writeWord_preserved_above_nat
    (mem := attesterMultiOuterArrayInitOffsetMem mem aw)
    (base := 64) (writeOff := slot.toNat)
    (len := ((⟨64⟩ : UInt256) + attesterMultiOuterArrayInitFreeWord mem aw))
    (writeVal := attesterMultiOuterArrayInitFreeWord mem aw)
    hmem3 hslot hread3

theorem attesterMultiOuterArrayInitStep_readWithPadding_nat
    {base slot len : UInt256} {mem : ByteArray} {aw : UInt256}
    (hmem : base.toNat + 32 ≤ mem.size)
    (hread : mem.readWithPadding base.toNat 32 = UInt256.toByteArray len)
    (h64 : 64 + 32 ≤ base.toNat)
    (hfree : base.toNat + 32 ≤ (attesterMultiOuterArrayInitFreeWord mem aw).toNat)
    (hoffset :
      base.toNat + 32 ≤ (attesterMultiOuterArrayInitOffsetWord mem aw).toNat)
    (hslot : base.toNat + 32 ≤ slot.toNat) :
    (attesterMultiOuterArrayInitStepMem slot mem aw).readWithPadding
        base.toNat 32 =
      UInt256.toByteArray len := by
  have hread1 :
      (attesterMultiOuterArrayInitFreeMem mem aw).readWithPadding base.toNat 32 =
        UInt256.toByteArray len := by
    change (Reasoning.Theory.writeWord mem 64
      ((⟨64⟩ : UInt256) + attesterMultiOuterArrayInitFreeWord mem aw)).readWithPadding
        base.toNat 32 =
        UInt256.toByteArray len
    exact attesterReadWithPadding_writeWord_preserved_below_nat
      (mem := mem) (base := base.toNat) (writeOff := 64)
      (len := len)
      (writeVal :=
        ((⟨64⟩ : UInt256) + attesterMultiOuterArrayInitFreeWord mem aw))
      hmem h64 hread
  have hmem1 :
      base.toNat + 32 ≤ (attesterMultiOuterArrayInitFreeMem mem aw).size := by
    change base.toNat + 32 ≤
      (Reasoning.Theory.writeWord mem 64
        ((⟨64⟩ : UInt256) + attesterMultiOuterArrayInitFreeWord mem aw)).size
    exact le_trans hmem
      (attesterWriteWord_size_ge_nat mem 64
        ((⟨64⟩ : UInt256) + attesterMultiOuterArrayInitFreeWord mem aw))
  have hread2 :
      (attesterMultiOuterArrayInitZeroMem mem aw).readWithPadding base.toNat 32 =
        UInt256.toByteArray len := by
    change (Reasoning.Theory.writeWord
      (attesterMultiOuterArrayInitFreeMem mem aw)
      (attesterMultiOuterArrayInitFreeWord mem aw).toNat
      (⟨0⟩ : UInt256)).readWithPadding base.toNat 32 =
        UInt256.toByteArray len
    exact attesterReadWithPadding_writeWord_preserved_above_nat
      (mem := attesterMultiOuterArrayInitFreeMem mem aw)
      (base := base.toNat)
      (writeOff := (attesterMultiOuterArrayInitFreeWord mem aw).toNat)
      (len := len) (writeVal := (⟨0⟩ : UInt256))
      hmem1 hfree hread1
  have hmem2 :
      base.toNat + 32 ≤ (attesterMultiOuterArrayInitZeroMem mem aw).size := by
    change base.toNat + 32 ≤
      (Reasoning.Theory.writeWord
        (attesterMultiOuterArrayInitFreeMem mem aw)
        (attesterMultiOuterArrayInitFreeWord mem aw).toNat
        (⟨0⟩ : UInt256)).size
    exact le_trans hmem1
      (attesterWriteWord_size_ge_nat
        (attesterMultiOuterArrayInitFreeMem mem aw)
        (attesterMultiOuterArrayInitFreeWord mem aw).toNat
        (⟨0⟩ : UInt256))
  have hread3 :
      (attesterMultiOuterArrayInitOffsetMem mem aw).readWithPadding base.toNat 32 =
        UInt256.toByteArray len := by
    change (Reasoning.Theory.writeWord
      (attesterMultiOuterArrayInitZeroMem mem aw)
      (attesterMultiOuterArrayInitOffsetWord mem aw).toNat
      (⟨96⟩ : UInt256)).readWithPadding base.toNat 32 =
        UInt256.toByteArray len
    exact attesterReadWithPadding_writeWord_preserved_above_nat
      (mem := attesterMultiOuterArrayInitZeroMem mem aw)
      (base := base.toNat)
      (writeOff := (attesterMultiOuterArrayInitOffsetWord mem aw).toNat)
      (len := len) (writeVal := (⟨96⟩ : UInt256))
      hmem2 hoffset hread2
  have hmem3 :
      base.toNat + 32 ≤ (attesterMultiOuterArrayInitOffsetMem mem aw).size := by
    change base.toNat + 32 ≤
      (Reasoning.Theory.writeWord
        (attesterMultiOuterArrayInitZeroMem mem aw)
        (attesterMultiOuterArrayInitOffsetWord mem aw).toNat
        (⟨96⟩ : UInt256)).size
    exact le_trans hmem2
      (attesterWriteWord_size_ge_nat
        (attesterMultiOuterArrayInitZeroMem mem aw)
        (attesterMultiOuterArrayInitOffsetWord mem aw).toNat
        (⟨96⟩ : UInt256))
  change (Reasoning.Theory.writeWord
    (attesterMultiOuterArrayInitOffsetMem mem aw) slot.toNat
    (attesterMultiOuterArrayInitFreeWord mem aw)).readWithPadding base.toNat 32 =
      UInt256.toByteArray len
  exact attesterReadWithPadding_writeWord_preserved_above_nat
    (mem := attesterMultiOuterArrayInitOffsetMem mem aw)
    (base := base.toNat) (writeOff := slot.toNat) (len := len)
    (writeVal := attesterMultiOuterArrayInitFreeWord mem aw)
    hmem3 hslot hread3

theorem attesterMultiOuterArrayInitStep_size_ge
    {slot : UInt256} {mem : ByteArray} {aw : UInt256} :
    mem.size ≤ (attesterMultiOuterArrayInitStepMem slot mem aw).size := by
  apply le_trans (attesterWriteWord_size_ge_nat mem 64
    ((⟨64⟩ : UInt256) + attesterMultiOuterArrayInitFreeWord mem aw))
  apply le_trans (attesterWriteWord_size_ge_nat
    (attesterMultiOuterArrayInitFreeMem mem aw)
    (attesterMultiOuterArrayInitFreeWord mem aw).toNat
    (⟨0⟩ : UInt256))
  apply le_trans (attesterWriteWord_size_ge_nat
    (attesterMultiOuterArrayInitZeroMem mem aw)
    (attesterMultiOuterArrayInitOffsetWord mem aw).toNat
    (⟨96⟩ : UInt256))
  exact attesterWriteWord_size_ge_nat
    (attesterMultiOuterArrayInitOffsetMem mem aw) slot.toNat
    (attesterMultiOuterArrayInitFreeWord mem aw)

theorem attesterMultiOuterArrayInitStep_mload64
    {slot : UInt256} {mem : ByteArray} {aw : UInt256}
    (hfree : 64 + 32 ≤ (attesterMultiOuterArrayInitFreeWord mem aw).toNat)
    (hoffset : 64 + 32 ≤ (attesterMultiOuterArrayInitOffsetWord mem aw).toNat)
    (hslot : 64 + 32 ≤ slot.toNat)
    (haw :
      ¬ (⟨64⟩ : UInt256) ≥
        attesterMultiOuterArrayInitStepAw slot mem aw * (⟨32⟩ : UInt256)) :
    attesterMultiOuterArrayInitFreeWord
        (attesterMultiOuterArrayInitStepMem slot mem aw)
        (attesterMultiOuterArrayInitStepAw slot mem aw) =
      (⟨64⟩ : UInt256) + attesterMultiOuterArrayInitFreeWord mem aw := by
  have hread := attesterMultiOuterArrayInitStep_read64
    (slot := slot) (mem := mem) (aw := aw)
    hfree hoffset hslot
  have hmem : (⟨64⟩ : UInt256).toNat + 32 ≤
      (attesterMultiOuterArrayInitStepMem slot mem aw).size := by
    have hsize4 := attesterWriteWord_size_nat (attesterMultiOuterArrayInitOffsetMem mem aw)
      slot.toNat (attesterMultiOuterArrayInitFreeWord mem aw)
    change (⟨64⟩ : UInt256).toNat + 32 ≤
      (Reasoning.Theory.writeWord (attesterMultiOuterArrayInitOffsetMem mem aw)
        slot.toNat (attesterMultiOuterArrayInitFreeWord mem aw)).size
    rw [hsize4]
    change 96 ≤ max (attesterMultiOuterArrayInitOffsetMem mem aw).size (slot.toNat + 32)
    exact le_trans (by omega) (Nat.le_max_right _ _)
  exact attesterMloadWord_of_readWithPadding hmem haw hread

theorem attesterMultiOuterArrayInitStep_freeWord_toNat
    {slot : UInt256} {mem : ByteArray} {aw : UInt256}
    (hfree : 64 + 32 ≤ (attesterMultiOuterArrayInitFreeWord mem aw).toNat)
    (hoffset : 64 + 32 ≤ (attesterMultiOuterArrayInitOffsetWord mem aw).toNat)
    (hslot : 64 + 32 ≤ slot.toNat)
    (hawMul :
      (attesterMultiOuterArrayInitStepAw slot mem aw).toNat * 32 < UInt256.size)
    (hawGe : 3 ≤ (attesterMultiOuterArrayInitStepAw slot mem aw).toNat)
    (hfreeBound : (attesterMultiOuterArrayInitFreeWord mem aw).toNat + 64 < UInt256.size) :
    (attesterMultiOuterArrayInitFreeWord
        (attesterMultiOuterArrayInitStepMem slot mem aw)
        (attesterMultiOuterArrayInitStepAw slot mem aw)).toNat =
      (attesterMultiOuterArrayInitFreeWord mem aw).toNat + 64 := by
  rw [attesterMultiOuterArrayInitStep_mload64
    (slot := slot) (mem := mem) (aw := aw)
    hfree hoffset hslot
    (attesterMload64ActiveWordsGe3 hawMul hawGe)]
  exact attester_uadd_lit64_toNat
    (attesterMultiOuterArrayInitFreeWord mem aw) hfreeBound

theorem attesterMultiOuterArrayInitStepAw_bounds
    {slot : UInt256} {mem : ByteArray} {aw : UInt256}
    (hawGe : 3 ≤ aw.toNat)
    (hawMul : aw.toNat * 32 < UInt256.size)
    (hfree95 : (attesterMultiOuterArrayInitFreeWord mem aw).toNat + 95 < UInt256.size)
    (hslot63 : slot.toNat + 63 < UInt256.size) :
    3 ≤ (attesterMultiOuterArrayInitStepAw slot mem aw).toNat ∧
      (attesterMultiOuterArrayInitStepAw slot mem aw).toNat * 32 < UInt256.size := by
  let aw1 := attesterMultiOuterArrayInitAwAfterMload aw
  let aw2 := attesterMultiOuterArrayInitFreeAw aw
  let aw3 := attesterMultiOuterArrayInitZeroAw mem aw
  let aw4 := attesterMultiOuterArrayInitOffsetAw mem aw
  let free := attesterMultiOuterArrayInitFreeWord mem aw
  let offset := attesterMultiOuterArrayInitOffsetWord mem aw
  have h64_63 : (⟨64⟩ : UInt256).toNat + 63 < UInt256.size := by decide
  have hM1 : MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32 < UInt256.size :=
    attesterMachineStateM32_lt (s := aw.toNat) (f := (⟨64⟩ : UInt256).toNat)
      hawMul h64_63
  have hM1Mul :
      MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32 * 32 < UInt256.size :=
    attesterMachineStateM32_mul32_lt (s := aw.toNat)
      (f := (⟨64⟩ : UInt256).toNat) hawMul h64_63
  have haw1Ge : 3 ≤ aw1.toNat := by
    unfold aw1 attesterMultiOuterArrayInitAwAfterMload attesterMloadAw
    rw [ulit_toNat' _ hM1]
    exact le_trans hawGe
      (attesterMachineStateM_ge aw.toNat (⟨64⟩ : UInt256).toNat 32)
  have haw1Mul : aw1.toNat * 32 < UInt256.size := by
    unfold aw1 attesterMultiOuterArrayInitAwAfterMload attesterMloadAw
    rw [ulit_toNat' _ hM1]
    exact hM1Mul
  have hM2 : MachineState.M aw1.toNat 64 32 < UInt256.size :=
    attesterMachineStateM32_lt (s := aw1.toNat) (f := 64)
      haw1Mul (by norm_num [UInt256.size])
  have hM2Mul :
      MachineState.M aw1.toNat 64 32 * 32 < UInt256.size :=
    attesterMachineStateM32_mul32_lt (s := aw1.toNat)
      (f := 64) haw1Mul (by norm_num [UInt256.size])
  have haw2Ge : 3 ≤ aw2.toNat := by
    unfold aw2 attesterMultiOuterArrayInitFreeAw
    rw [ulit_toNat' _ hM2]
    exact le_trans haw1Ge
      (attesterMachineStateM_ge aw1.toNat 64 32)
  have haw2Mul : aw2.toNat * 32 < UInt256.size := by
    unfold aw2 attesterMultiOuterArrayInitFreeAw
    rw [ulit_toNat' _ hM2]
    exact hM2Mul
  have hfree63 : free.toNat + 63 < UInt256.size := by
    unfold free
    omega
  have hM3 : MachineState.M aw2.toNat free.toNat 32 < UInt256.size :=
    attesterMachineStateM32_lt (s := aw2.toNat) (f := free.toNat) haw2Mul hfree63
  have hM3Mul : MachineState.M aw2.toNat free.toNat 32 * 32 < UInt256.size :=
    attesterMachineStateM32_mul32_lt (s := aw2.toNat) (f := free.toNat) haw2Mul hfree63
  have haw3Ge : 3 ≤ aw3.toNat := by
    unfold aw3 attesterMultiOuterArrayInitZeroAw
    rw [ulit_toNat' _ hM3]
    exact le_trans haw2Ge
      (attesterMachineStateM_ge
        (attesterMultiOuterArrayInitFreeAw aw).toNat
        (attesterMultiOuterArrayInitFreeWord mem aw).toNat 32)
  have haw3Mul : aw3.toNat * 32 < UInt256.size := by
    unfold aw3 attesterMultiOuterArrayInitZeroAw
    rw [ulit_toNat' _ hM3]
    exact hM3Mul
  have hfree32 : free.toNat + 32 < UInt256.size := by
    unfold free
    omega
  have hoffToNat : offset.toNat = free.toNat + 32 := by
    unfold offset attesterMultiOuterArrayInitOffsetWord free
    exact uadd_word_lit32_toNat (attesterMultiOuterArrayInitFreeWord mem aw) hfree32
  have hoff63 : offset.toNat + 63 < UInt256.size := by
    rw [hoffToNat]
    omega
  have hM4 : MachineState.M aw3.toNat offset.toNat 32 < UInt256.size :=
    attesterMachineStateM32_lt (s := aw3.toNat) (f := offset.toNat) haw3Mul hoff63
  have hM4Mul : MachineState.M aw3.toNat offset.toNat 32 * 32 < UInt256.size :=
    attesterMachineStateM32_mul32_lt (s := aw3.toNat) (f := offset.toNat) haw3Mul hoff63
  have haw4Ge : 3 ≤ aw4.toNat := by
    unfold aw4 attesterMultiOuterArrayInitOffsetAw
    rw [ulit_toNat' _ hM4]
    exact le_trans haw3Ge
      (attesterMachineStateM_ge
        (attesterMultiOuterArrayInitZeroAw mem aw).toNat
        (attesterMultiOuterArrayInitOffsetWord mem aw).toNat 32)
  have haw4Mul : aw4.toNat * 32 < UInt256.size := by
    unfold aw4 attesterMultiOuterArrayInitOffsetAw
    rw [ulit_toNat' _ hM4]
    exact hM4Mul
  have hM5 : MachineState.M aw4.toNat slot.toNat 32 < UInt256.size :=
    attesterMachineStateM32_lt (s := aw4.toNat) (f := slot.toNat) haw4Mul hslot63
  have hM5Mul : MachineState.M aw4.toNat slot.toNat 32 * 32 < UInt256.size :=
    attesterMachineStateM32_mul32_lt (s := aw4.toNat) (f := slot.toNat) haw4Mul hslot63
  constructor
  · unfold attesterMultiOuterArrayInitStepAw
    rw [ulit_toNat' _ hM5]
    exact le_trans haw4Ge
      (attesterMachineStateM_ge
        (attesterMultiOuterArrayInitOffsetAw mem aw).toNat slot.toNat 32)
  · unfold attesterMultiOuterArrayInitStepAw
    rw [ulit_toNat' _ hM5]
    exact hM5Mul

theorem attesterInnerArrayAllocMem_read64
    {len : UInt256} {mem : ByteArray} {aw : UInt256} :
    (attesterInnerArrayAllocMem len mem aw).readWithPadding 64 32 =
      UInt256.toByteArray (attesterInnerArrayAllocEndWord len mem aw) := by
  change (Reasoning.Theory.writeWord (attesterInnerArrayAllocLenMem len mem aw)
    64 (attesterInnerArrayAllocEndWord len mem aw)).readWithPadding 64 32 =
      UInt256.toByteArray (attesterInnerArrayAllocEndWord len mem aw)
  exact attesterWriteWord_read_back_nat
    (attesterInnerArrayAllocLenMem len mem aw) 64
    (attesterInnerArrayAllocEndWord len mem aw)

theorem attesterInnerArrayAllocMem_mload64
    {len : UInt256} {mem : ByteArray} {aw : UInt256}
    (haw :
      ¬ (⟨64⟩ : UInt256) ≥
        attesterInnerArrayAllocAw len mem aw * (⟨32⟩ : UInt256)) :
    attesterInnerArrayAllocFreeWord
        (attesterInnerArrayAllocMem len mem aw)
        (attesterInnerArrayAllocAw len mem aw) =
      attesterInnerArrayAllocEndWord len mem aw := by
  have hread := attesterInnerArrayAllocMem_read64
    (len := len) (mem := mem) (aw := aw)
  have hmem : (⟨64⟩ : UInt256).toNat + 32 ≤
      (attesterInnerArrayAllocMem len mem aw).size := by
    have hsize := attesterWriteWord_size_nat (attesterInnerArrayAllocLenMem len mem aw)
      64 (attesterInnerArrayAllocEndWord len mem aw)
    change (⟨64⟩ : UInt256).toNat + 32 ≤
      (Reasoning.Theory.writeWord (attesterInnerArrayAllocLenMem len mem aw)
        64 (attesterInnerArrayAllocEndWord len mem aw)).size
    rw [hsize]
    change 96 ≤ max (attesterInnerArrayAllocLenMem len mem aw).size (64 + 32)
    exact Nat.le_max_right _ _
  exact attesterMloadWord_of_readWithPadding hmem haw hread

theorem attesterInnerArrayAllocMem_freeWord_toNat
    {len : UInt256} {mem : ByteArray} {aw : UInt256}
    (hawMul : (attesterInnerArrayAllocAw len mem aw).toNat * 32 < UInt256.size)
    (hawGe : 3 ≤ (attesterInnerArrayAllocAw len mem aw).toNat)
    (hbound :
      (attesterInnerArrayAllocFreeWord mem aw).toNat + 32 + 32 * len.toNat <
        UInt256.size) :
    (attesterInnerArrayAllocFreeWord
        (attesterInnerArrayAllocMem len mem aw)
        (attesterInnerArrayAllocAw len mem aw)).toNat =
      (attesterInnerArrayAllocFreeWord mem aw).toNat + 32 + 32 * len.toNat := by
  rw [attesterInnerArrayAllocMem_mload64
    (len := len) (mem := mem) (aw := aw)
    (attesterMload64ActiveWordsGe3 hawMul hawGe)]
  exact attesterInnerArrayAllocEndWord_toNat hbound

theorem attesterInnerArrayAllocAw_bounds
    {len : UInt256} {mem : ByteArray} {aw : UInt256}
    (hawGe : 3 ≤ aw.toNat)
    (hawMul : aw.toNat * 32 < UInt256.size)
    (hfree63 : (attesterInnerArrayAllocFreeWord mem aw).toNat + 63 < UInt256.size) :
    3 ≤ (attesterInnerArrayAllocAw len mem aw).toNat ∧
      (attesterInnerArrayAllocAw len mem aw).toNat * 32 < UInt256.size := by
  let aw1 := attesterInnerArrayAllocAwAfterMload aw
  let aw2 := attesterInnerArrayAllocLenAw len mem aw
  have h64_63 : (⟨64⟩ : UInt256).toNat + 63 < UInt256.size := by decide
  have hM1 : MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32 < UInt256.size :=
    attesterMachineStateM32_lt (s := aw.toNat) (f := (⟨64⟩ : UInt256).toNat)
      hawMul h64_63
  have hM1Mul :
      MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32 * 32 < UInt256.size :=
    attesterMachineStateM32_mul32_lt (s := aw.toNat)
      (f := (⟨64⟩ : UInt256).toNat) hawMul h64_63
  have haw1Ge : 3 ≤ aw1.toNat := by
    unfold aw1 attesterInnerArrayAllocAwAfterMload attesterMloadAw
    rw [ulit_toNat' _ hM1]
    exact le_trans hawGe
      (attesterMachineStateM_ge aw.toNat (⟨64⟩ : UInt256).toNat 32)
  have haw1Mul : aw1.toNat * 32 < UInt256.size := by
    unfold aw1 attesterInnerArrayAllocAwAfterMload attesterMloadAw
    rw [ulit_toNat' _ hM1]
    exact hM1Mul
  have hM2 :
      MachineState.M aw1.toNat (attesterInnerArrayAllocFreeWord mem aw).toNat 32 <
        UInt256.size :=
    attesterMachineStateM32_lt (s := aw1.toNat)
      (f := (attesterInnerArrayAllocFreeWord mem aw).toNat) haw1Mul hfree63
  have hM2Mul :
      MachineState.M aw1.toNat (attesterInnerArrayAllocFreeWord mem aw).toNat 32 * 32 <
        UInt256.size :=
    attesterMachineStateM32_mul32_lt (s := aw1.toNat)
      (f := (attesterInnerArrayAllocFreeWord mem aw).toNat) haw1Mul hfree63
  have haw2Ge : 3 ≤ aw2.toNat := by
    unfold aw2 attesterInnerArrayAllocLenAw
    rw [ulit_toNat' _ hM2]
    exact le_trans haw1Ge
      (attesterMachineStateM_ge
        (attesterInnerArrayAllocAwAfterMload aw).toNat
        (attesterInnerArrayAllocFreeWord mem aw).toNat 32)
  have haw2Mul : aw2.toNat * 32 < UInt256.size := by
    unfold aw2 attesterInnerArrayAllocLenAw
    rw [ulit_toNat' _ hM2]
    exact hM2Mul
  have hM3 : MachineState.M aw2.toNat 64 32 < UInt256.size :=
    attesterMachineStateM32_lt (s := aw2.toNat) (f := 64) haw2Mul
      (by norm_num [UInt256.size])
  have hM3Mul : MachineState.M aw2.toNat 64 32 * 32 < UInt256.size :=
    attesterMachineStateM32_mul32_lt (s := aw2.toNat) (f := 64) haw2Mul
      (by norm_num [UInt256.size])
  constructor
  · unfold attesterInnerArrayAllocAw
    rw [ulit_toNat' _ hM3]
    exact le_trans haw2Ge
      (attesterMachineStateM_ge
        (attesterInnerArrayAllocLenAw len mem aw).toNat 64 32)
  · unfold attesterInnerArrayAllocAw
    rw [ulit_toNat' _ hM3]
    exact hM3Mul

theorem attesterInnerArrayAllocMem_base_size
    {len : UInt256} {mem : ByteArray} {aw : UInt256} :
    (attesterInnerArrayAllocFreeWord mem aw).toNat + 32 ≤
      (attesterInnerArrayAllocMem len mem aw).size := by
  let base := attesterInnerArrayAllocFreeWord mem aw
  have hmemLen :
      base.toNat + 32 ≤ (attesterInnerArrayAllocLenMem len mem aw).size := by
    have hsize := attesterWriteWord_size_nat mem base.toNat len
    change base.toNat + 32 ≤ (Reasoning.Theory.writeWord mem base.toNat len).size
    rw [hsize]
    exact Nat.le_max_right _ _
  have hsize := attesterWriteWord_size_nat (attesterInnerArrayAllocLenMem len mem aw)
    64 (attesterInnerArrayAllocEndWord len mem aw)
  change base.toNat + 32 ≤
    (Reasoning.Theory.writeWord (attesterInnerArrayAllocLenMem len mem aw)
      64 (attesterInnerArrayAllocEndWord len mem aw)).size
  rw [hsize]
  exact le_trans hmemLen (Nat.le_max_left _ _)

theorem attesterInnerArrayAllocMem_size_ge
    {len : UInt256} {mem : ByteArray} {aw : UInt256} :
    mem.size ≤ (attesterInnerArrayAllocMem len mem aw).size := by
  apply le_trans (attesterWriteWord_size_ge_nat mem
    (attesterInnerArrayAllocFreeWord mem aw).toNat len)
  exact attesterWriteWord_size_ge_nat
    (attesterInnerArrayAllocLenMem len mem aw) 64
    (attesterInnerArrayAllocEndWord len mem aw)

theorem attesterInnerArrayAllocMem_readWithPadding_at_nat
    {readBase len readLen : UInt256} {mem : ByteArray} {aw : UInt256}
    (hmem : readBase.toNat + 32 ≤ mem.size)
    (hread : mem.readWithPadding readBase.toNat 32 = UInt256.toByteArray readLen)
    (h64 : 64 + 32 ≤ readBase.toNat)
    (hbase :
      readBase.toNat + 32 ≤ (attesterInnerArrayAllocFreeWord mem aw).toNat) :
    (attesterInnerArrayAllocMem len mem aw).readWithPadding readBase.toNat 32 =
      UInt256.toByteArray readLen := by
  let base := attesterInnerArrayAllocFreeWord mem aw
  have hreadLen :
      (attesterInnerArrayAllocLenMem len mem aw).readWithPadding
          readBase.toNat 32 =
        UInt256.toByteArray readLen := by
    change (Reasoning.Theory.writeWord mem base.toNat len).readWithPadding
        readBase.toNat 32 =
      UInt256.toByteArray readLen
    exact attesterReadWithPadding_writeWord_preserved_above_nat
      (mem := mem) (base := readBase.toNat) (writeOff := base.toNat)
      (len := readLen) (writeVal := len)
      hmem hbase hread
  have hmemLen :
      readBase.toNat + 32 ≤ (attesterInnerArrayAllocLenMem len mem aw).size := by
    change readBase.toNat + 32 ≤
      (Reasoning.Theory.writeWord mem base.toNat len).size
    exact le_trans hmem
      (attesterWriteWord_size_ge_nat mem base.toNat len)
  change (Reasoning.Theory.writeWord
      (attesterInnerArrayAllocLenMem len mem aw) 64
      (attesterInnerArrayAllocEndWord len mem aw)).readWithPadding
        readBase.toNat 32 =
      UInt256.toByteArray readLen
  exact attesterReadWithPadding_writeWord_preserved_below_nat
    (mem := attesterInnerArrayAllocLenMem len mem aw)
    (base := readBase.toNat) (writeOff := 64) (len := readLen)
    (writeVal := attesterInnerArrayAllocEndWord len mem aw)
    hmemLen h64 hreadLen

theorem attesterInnerArrayAllocMem_readWithPadding_len_nat
    {len : UInt256} {mem : ByteArray} {aw : UInt256}
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
    exact attesterWriteWord_read_back_nat mem base.toNat len
  have hmemLen :
      base.toNat + 32 ≤ (attesterInnerArrayAllocLenMem len mem aw).size := by
    have hsize := attesterWriteWord_size_nat mem base.toNat len
    change base.toNat + 32 ≤ (Reasoning.Theory.writeWord mem base.toNat len).size
    rw [hsize]
    exact Nat.le_max_right _ _
  change (Reasoning.Theory.writeWord
      (attesterInnerArrayAllocLenMem len mem aw) 64
      (attesterInnerArrayAllocEndWord len mem aw)).readWithPadding
        base.toNat 32 =
      UInt256.toByteArray len
  exact attesterReadWithPadding_writeWord_preserved_below_nat
    (mem := attesterInnerArrayAllocLenMem len mem aw)
    (base := base.toNat) (writeOff := 64) (len := len)
    (writeVal := attesterInnerArrayAllocEndWord len mem aw)
    hmemLen h64 hreadLen

theorem attesterInnerArrayAllocMem_mloadLen_nat
    {len : UInt256} {mem : ByteArray} {aw : UInt256}
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
    attesterInnerArrayAllocMem_readWithPadding_len_nat
      (len := len) (mem := mem) (aw := aw) h64
  have hmemLen :
      base.toNat + 32 ≤ (attesterInnerArrayAllocLenMem len mem aw).size := by
    have hsize := attesterWriteWord_size_nat mem base.toNat len
    change base.toNat + 32 ≤ (Reasoning.Theory.writeWord mem base.toNat len).size
    rw [hsize]
    exact Nat.le_max_right _ _
  have hmem :
      base.toNat + 32 ≤ (attesterInnerArrayAllocMem len mem aw).size := by
    have hsize := attesterWriteWord_size_nat (attesterInnerArrayAllocLenMem len mem aw)
      64 (attesterInnerArrayAllocEndWord len mem aw)
    change base.toNat + 32 ≤
      (Reasoning.Theory.writeWord (attesterInnerArrayAllocLenMem len mem aw)
        64 (attesterInnerArrayAllocEndWord len mem aw)).size
    rw [hsize]
    exact le_trans hmemLen (Nat.le_max_left _ _)
  exact attesterMloadWord_of_readWithPadding hmem haw (by simpa [base] using hread)

theorem attesterMultiRevokeInnerArrayInitStep_readWithPadding_nat
    {base slot len : UInt256} {mem : ByteArray} {aw : UInt256}
    (hmem : base.toNat + 32 ≤ mem.size)
    (hread : mem.readWithPadding base.toNat 32 = UInt256.toByteArray len)
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
    exact attesterReadWithPadding_writeWord_preserved_below_nat
      (mem := mem) (base := base.toNat) (writeOff := 64)
      (len := len)
      (writeVal :=
        ((⟨64⟩ : UInt256) + attesterMultiOuterArrayInitFreeWord mem aw))
      hmem h64 hread
  have hmem1 :
      base.toNat + 32 ≤ (attesterMultiOuterArrayInitFreeMem mem aw).size := by
    have hsize := attesterWriteWord_size_nat mem 64
      ((⟨64⟩ : UInt256) + attesterMultiOuterArrayInitFreeWord mem aw)
    change base.toNat + 32 ≤
      (Reasoning.Theory.writeWord mem 64
        ((⟨64⟩ : UInt256) + attesterMultiOuterArrayInitFreeWord mem aw)).size
    rw [hsize]
    exact le_trans hmem (Nat.le_max_left _ _)
  have hread2 :
      (attesterMultiOuterArrayInitZeroMem mem aw).readWithPadding base.toNat 32 =
        UInt256.toByteArray len := by
    change (Reasoning.Theory.writeWord
      (attesterMultiOuterArrayInitFreeMem mem aw)
      (attesterMultiOuterArrayInitFreeWord mem aw).toNat
      (⟨0⟩ : UInt256)).readWithPadding base.toNat 32 =
        UInt256.toByteArray len
    exact attesterReadWithPadding_writeWord_preserved_above_nat
      (mem := attesterMultiOuterArrayInitFreeMem mem aw)
      (base := base.toNat)
      (writeOff := (attesterMultiOuterArrayInitFreeWord mem aw).toNat)
      (len := len) (writeVal := (⟨0⟩ : UInt256))
      hmem1 hfree hread1
  have hmem2 :
      base.toNat + 32 ≤ (attesterMultiOuterArrayInitZeroMem mem aw).size := by
    have hsize := attesterWriteWord_size_nat
      (attesterMultiOuterArrayInitFreeMem mem aw)
      (attesterMultiOuterArrayInitFreeWord mem aw).toNat
      (⟨0⟩ : UInt256)
    change base.toNat + 32 ≤
      (Reasoning.Theory.writeWord
        (attesterMultiOuterArrayInitFreeMem mem aw)
        (attesterMultiOuterArrayInitFreeWord mem aw).toNat
        (⟨0⟩ : UInt256)).size
    rw [hsize]
    exact le_trans hmem1 (Nat.le_max_left _ _)
  have hread3 :
      (attesterMultiRevokeInnerArrayInitSecondZeroMem mem aw).readWithPadding
          base.toNat 32 =
        UInt256.toByteArray len := by
    change (Reasoning.Theory.writeWord
      (attesterMultiOuterArrayInitZeroMem mem aw)
      (attesterMultiRevokeInnerArrayInitSecondZeroWord mem aw).toNat
      (⟨0⟩ : UInt256)).readWithPadding base.toNat 32 =
        UInt256.toByteArray len
    exact attesterReadWithPadding_writeWord_preserved_above_nat
      (mem := attesterMultiOuterArrayInitZeroMem mem aw)
      (base := base.toNat)
      (writeOff := (attesterMultiRevokeInnerArrayInitSecondZeroWord mem aw).toNat)
      (len := len) (writeVal := (⟨0⟩ : UInt256))
      hmem2 hsecond hread2
  have hmem3 :
      base.toNat + 32 ≤
        (attesterMultiRevokeInnerArrayInitSecondZeroMem mem aw).size := by
    have hsize := attesterWriteWord_size_nat
      (attesterMultiOuterArrayInitZeroMem mem aw)
      (attesterMultiRevokeInnerArrayInitSecondZeroWord mem aw).toNat
      (⟨0⟩ : UInt256)
    change base.toNat + 32 ≤
      (Reasoning.Theory.writeWord
        (attesterMultiOuterArrayInitZeroMem mem aw)
        (attesterMultiRevokeInnerArrayInitSecondZeroWord mem aw).toNat
        (⟨0⟩ : UInt256)).size
    rw [hsize]
    exact le_trans hmem2 (Nat.le_max_left _ _)
  change (Reasoning.Theory.writeWord
    (attesterMultiRevokeInnerArrayInitSecondZeroMem mem aw)
    slot.toNat (attesterMultiOuterArrayInitFreeWord mem aw)).readWithPadding
      base.toNat 32 =
    UInt256.toByteArray len
  exact attesterReadWithPadding_writeWord_preserved_above_nat
    (mem := attesterMultiRevokeInnerArrayInitSecondZeroMem mem aw)
    (base := base.toNat) (writeOff := slot.toNat) (len := len)
    (writeVal := attesterMultiOuterArrayInitFreeWord mem aw)
    hmem3 hslot hread3

theorem attesterMultiRevokeInnerArrayInitStep_read64
    {slot : UInt256} {mem : ByteArray} {aw : UInt256}
    (hfree : 64 + 32 ≤ (attesterMultiOuterArrayInitFreeWord mem aw).toNat)
    (hsecond :
      64 + 32 ≤ (attesterMultiRevokeInnerArrayInitSecondZeroWord mem aw).toNat)
    (hslot : 64 + 32 ≤ slot.toNat) :
    (attesterMultiRevokeInnerArrayInitStepMem slot mem aw).readWithPadding 64 32 =
      UInt256.toByteArray
        ((⟨64⟩ : UInt256) + attesterMultiOuterArrayInitFreeWord mem aw) := by
  have hread1 :
      (attesterMultiOuterArrayInitFreeMem mem aw).readWithPadding 64 32 =
        UInt256.toByteArray
          ((⟨64⟩ : UInt256) + attesterMultiOuterArrayInitFreeWord mem aw) := by
    change (Reasoning.Theory.writeWord mem 64
      ((⟨64⟩ : UInt256) + attesterMultiOuterArrayInitFreeWord mem aw)).readWithPadding
        64 32 =
        UInt256.toByteArray
          ((⟨64⟩ : UInt256) + attesterMultiOuterArrayInitFreeWord mem aw)
    exact attesterWriteWord_read_back_nat mem 64
      ((⟨64⟩ : UInt256) + attesterMultiOuterArrayInitFreeWord mem aw)
  have hmem1 : 64 + 32 ≤ (attesterMultiOuterArrayInitFreeMem mem aw).size := by
    have hsize := attesterWriteWord_size_nat mem 64
      ((⟨64⟩ : UInt256) + attesterMultiOuterArrayInitFreeWord mem aw)
    change 64 + 32 ≤
      (Reasoning.Theory.writeWord mem 64
        ((⟨64⟩ : UInt256) + attesterMultiOuterArrayInitFreeWord mem aw)).size
    rw [hsize]
    change 96 ≤ max mem.size (64 + 32)
    exact Nat.le_max_right _ _
  have hread2 :
      (attesterMultiOuterArrayInitZeroMem mem aw).readWithPadding 64 32 =
        UInt256.toByteArray
          ((⟨64⟩ : UInt256) + attesterMultiOuterArrayInitFreeWord mem aw) := by
    change (Reasoning.Theory.writeWord
      (attesterMultiOuterArrayInitFreeMem mem aw)
      (attesterMultiOuterArrayInitFreeWord mem aw).toNat
      (⟨0⟩ : UInt256)).readWithPadding 64 32 =
        UInt256.toByteArray
          ((⟨64⟩ : UInt256) + attesterMultiOuterArrayInitFreeWord mem aw)
    exact attesterReadWithPadding_writeWord_preserved_above_nat
      (mem := attesterMultiOuterArrayInitFreeMem mem aw)
      (base := 64)
      (writeOff := (attesterMultiOuterArrayInitFreeWord mem aw).toNat)
      (len := ((⟨64⟩ : UInt256) + attesterMultiOuterArrayInitFreeWord mem aw))
      (writeVal := (⟨0⟩ : UInt256))
      hmem1 hfree hread1
  have hmem2 : 64 + 32 ≤ (attesterMultiOuterArrayInitZeroMem mem aw).size := by
    have hsize := attesterWriteWord_size_nat (attesterMultiOuterArrayInitFreeMem mem aw)
      (attesterMultiOuterArrayInitFreeWord mem aw).toNat
      (⟨0⟩ : UInt256)
    change 64 + 32 ≤
      (Reasoning.Theory.writeWord (attesterMultiOuterArrayInitFreeMem mem aw)
        (attesterMultiOuterArrayInitFreeWord mem aw).toNat
        (⟨0⟩ : UInt256)).size
    rw [hsize]
    exact le_trans hmem1 (Nat.le_max_left _ _)
  have hread3 :
      (attesterMultiRevokeInnerArrayInitSecondZeroMem mem aw).readWithPadding 64 32 =
        UInt256.toByteArray
          ((⟨64⟩ : UInt256) + attesterMultiOuterArrayInitFreeWord mem aw) := by
    change (Reasoning.Theory.writeWord
      (attesterMultiOuterArrayInitZeroMem mem aw)
      (attesterMultiRevokeInnerArrayInitSecondZeroWord mem aw).toNat
      (⟨0⟩ : UInt256)).readWithPadding 64 32 =
        UInt256.toByteArray
          ((⟨64⟩ : UInt256) + attesterMultiOuterArrayInitFreeWord mem aw)
    exact attesterReadWithPadding_writeWord_preserved_above_nat
      (mem := attesterMultiOuterArrayInitZeroMem mem aw)
      (base := 64)
      (writeOff := (attesterMultiRevokeInnerArrayInitSecondZeroWord mem aw).toNat)
      (len := ((⟨64⟩ : UInt256) + attesterMultiOuterArrayInitFreeWord mem aw))
      (writeVal := (⟨0⟩ : UInt256))
      hmem2 hsecond hread2
  have hmem3 :
      64 + 32 ≤ (attesterMultiRevokeInnerArrayInitSecondZeroMem mem aw).size := by
    have hsize := attesterWriteWord_size_nat (attesterMultiOuterArrayInitZeroMem mem aw)
      (attesterMultiRevokeInnerArrayInitSecondZeroWord mem aw).toNat
      (⟨0⟩ : UInt256)
    change 64 + 32 ≤
      (Reasoning.Theory.writeWord (attesterMultiOuterArrayInitZeroMem mem aw)
        (attesterMultiRevokeInnerArrayInitSecondZeroWord mem aw).toNat
        (⟨0⟩ : UInt256)).size
    rw [hsize]
    exact le_trans hmem2 (Nat.le_max_left _ _)
  change (Reasoning.Theory.writeWord
    (attesterMultiRevokeInnerArrayInitSecondZeroMem mem aw) slot.toNat
    (attesterMultiOuterArrayInitFreeWord mem aw)).readWithPadding 64 32 =
      UInt256.toByteArray
        ((⟨64⟩ : UInt256) + attesterMultiOuterArrayInitFreeWord mem aw)
  exact attesterReadWithPadding_writeWord_preserved_above_nat
    (mem := attesterMultiRevokeInnerArrayInitSecondZeroMem mem aw)
    (base := 64) (writeOff := slot.toNat)
    (len := ((⟨64⟩ : UInt256) + attesterMultiOuterArrayInitFreeWord mem aw))
    (writeVal := attesterMultiOuterArrayInitFreeWord mem aw)
    hmem3 hslot hread3

theorem attesterMultiRevokeInnerArrayInitStep_mload64
    {slot : UInt256} {mem : ByteArray} {aw : UInt256}
    (hfree : 64 + 32 ≤ (attesterMultiOuterArrayInitFreeWord mem aw).toNat)
    (hsecond :
      64 + 32 ≤ (attesterMultiRevokeInnerArrayInitSecondZeroWord mem aw).toNat)
    (hslot : 64 + 32 ≤ slot.toNat)
    (haw :
      ¬ (⟨64⟩ : UInt256) ≥
        attesterMultiRevokeInnerArrayInitStepAw slot mem aw * (⟨32⟩ : UInt256)) :
    attesterMultiOuterArrayInitFreeWord
        (attesterMultiRevokeInnerArrayInitStepMem slot mem aw)
        (attesterMultiRevokeInnerArrayInitStepAw slot mem aw) =
      (⟨64⟩ : UInt256) + attesterMultiOuterArrayInitFreeWord mem aw := by
  have hread := attesterMultiRevokeInnerArrayInitStep_read64
    (slot := slot) (mem := mem) (aw := aw)
    hfree hsecond hslot
  have hmem : (⟨64⟩ : UInt256).toNat + 32 ≤
      (attesterMultiRevokeInnerArrayInitStepMem slot mem aw).size := by
    have hsize := attesterWriteWord_size_nat
      (attesterMultiRevokeInnerArrayInitSecondZeroMem mem aw)
      slot.toNat (attesterMultiOuterArrayInitFreeWord mem aw)
    change (⟨64⟩ : UInt256).toNat + 32 ≤
      (Reasoning.Theory.writeWord
        (attesterMultiRevokeInnerArrayInitSecondZeroMem mem aw)
        slot.toNat (attesterMultiOuterArrayInitFreeWord mem aw)).size
    rw [hsize]
    change 96 ≤ max (attesterMultiRevokeInnerArrayInitSecondZeroMem mem aw).size
      (slot.toNat + 32)
    exact le_trans (by omega) (Nat.le_max_right _ _)
  exact attesterMloadWord_of_readWithPadding hmem haw hread

theorem attesterMultiRevokeInnerArrayInitStep_freeWord_toNat
    {slot : UInt256} {mem : ByteArray} {aw : UInt256}
    (hfree : 64 + 32 ≤ (attesterMultiOuterArrayInitFreeWord mem aw).toNat)
    (hsecond :
      64 + 32 ≤ (attesterMultiRevokeInnerArrayInitSecondZeroWord mem aw).toNat)
    (hslot : 64 + 32 ≤ slot.toNat)
    (hawMul :
      (attesterMultiRevokeInnerArrayInitStepAw slot mem aw).toNat * 32 <
        UInt256.size)
    (hawGe : 3 ≤ (attesterMultiRevokeInnerArrayInitStepAw slot mem aw).toNat)
    (hfreeBound : (attesterMultiOuterArrayInitFreeWord mem aw).toNat + 64 < UInt256.size) :
    (attesterMultiOuterArrayInitFreeWord
        (attesterMultiRevokeInnerArrayInitStepMem slot mem aw)
        (attesterMultiRevokeInnerArrayInitStepAw slot mem aw)).toNat =
      (attesterMultiOuterArrayInitFreeWord mem aw).toNat + 64 := by
  rw [attesterMultiRevokeInnerArrayInitStep_mload64
    (slot := slot) (mem := mem) (aw := aw)
    hfree hsecond hslot
    (attesterMload64ActiveWordsGe3 hawMul hawGe)]
  exact attester_uadd_lit64_toNat
    (attesterMultiOuterArrayInitFreeWord mem aw) hfreeBound

theorem attesterMultiRevokeInnerArrayInitSecondZeroWord_toNat
    {mem : ByteArray} {aw : UInt256}
    (hfree32 : (attesterMultiOuterArrayInitFreeWord mem aw).toNat + 32 < UInt256.size) :
    (attesterMultiRevokeInnerArrayInitSecondZeroWord mem aw).toNat =
      (attesterMultiOuterArrayInitFreeWord mem aw).toNat + 32 := by
  unfold attesterMultiRevokeInnerArrayInitSecondZeroWord
  exact uadd_word_lit32_toNat (attesterMultiOuterArrayInitFreeWord mem aw) hfree32

theorem attesterMultiRevokeInnerArrayInitStepAw_bounds
    {slot : UInt256} {mem : ByteArray} {aw : UInt256}
    (hawGe : 3 ≤ aw.toNat)
    (hawMul : aw.toNat * 32 < UInt256.size)
    (hfree63 : (attesterMultiOuterArrayInitFreeWord mem aw).toNat + 63 < UInt256.size)
    (hsecond63 : (attesterMultiRevokeInnerArrayInitSecondZeroWord mem aw).toNat + 63 <
      UInt256.size)
    (hslot63 : slot.toNat + 63 < UInt256.size) :
    3 ≤ (attesterMultiRevokeInnerArrayInitStepAw slot mem aw).toNat ∧
      (attesterMultiRevokeInnerArrayInitStepAw slot mem aw).toNat * 32 <
        UInt256.size := by
  let aw1 := attesterMultiOuterArrayInitAwAfterMload aw
  let aw2 := attesterMultiOuterArrayInitFreeAw aw
  let aw3 := attesterMultiOuterArrayInitZeroAw mem aw
  let aw4 := attesterMultiRevokeInnerArrayInitSecondZeroAw mem aw
  have h64_63 : (⟨64⟩ : UInt256).toNat + 63 < UInt256.size := by decide
  have hM1 : MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32 < UInt256.size :=
    attesterMachineStateM32_lt (s := aw.toNat) (f := (⟨64⟩ : UInt256).toNat)
      hawMul h64_63
  have hM1Mul :
      MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32 * 32 < UInt256.size :=
    attesterMachineStateM32_mul32_lt (s := aw.toNat)
      (f := (⟨64⟩ : UInt256).toNat) hawMul h64_63
  have haw1Ge : 3 ≤ aw1.toNat := by
    unfold aw1 attesterMultiOuterArrayInitAwAfterMload attesterMloadAw
    rw [ulit_toNat' _ hM1]
    exact le_trans hawGe
      (attesterMachineStateM_ge aw.toNat (⟨64⟩ : UInt256).toNat 32)
  have haw1Mul : aw1.toNat * 32 < UInt256.size := by
    unfold aw1 attesterMultiOuterArrayInitAwAfterMload attesterMloadAw
    rw [ulit_toNat' _ hM1]
    exact hM1Mul
  have hM2 : MachineState.M aw1.toNat 64 32 < UInt256.size :=
    attesterMachineStateM32_lt (s := aw1.toNat) (f := 64)
      haw1Mul (by norm_num [UInt256.size])
  have hM2Mul :
      MachineState.M aw1.toNat 64 32 * 32 < UInt256.size :=
    attesterMachineStateM32_mul32_lt (s := aw1.toNat)
      (f := 64) haw1Mul (by norm_num [UInt256.size])
  have haw2Ge : 3 ≤ aw2.toNat := by
    unfold aw2 attesterMultiOuterArrayInitFreeAw
    rw [ulit_toNat' _ hM2]
    exact le_trans haw1Ge
      (attesterMachineStateM_ge aw1.toNat 64 32)
  have haw2Mul : aw2.toNat * 32 < UInt256.size := by
    unfold aw2 attesterMultiOuterArrayInitFreeAw
    rw [ulit_toNat' _ hM2]
    exact hM2Mul
  have hM3 : MachineState.M aw2.toNat
      (attesterMultiOuterArrayInitFreeWord mem aw).toNat 32 < UInt256.size :=
    attesterMachineStateM32_lt (s := aw2.toNat)
      (f := (attesterMultiOuterArrayInitFreeWord mem aw).toNat) haw2Mul hfree63
  have hM3Mul : MachineState.M aw2.toNat
      (attesterMultiOuterArrayInitFreeWord mem aw).toNat 32 * 32 < UInt256.size :=
    attesterMachineStateM32_mul32_lt (s := aw2.toNat)
      (f := (attesterMultiOuterArrayInitFreeWord mem aw).toNat) haw2Mul hfree63
  have haw3Ge : 3 ≤ aw3.toNat := by
    unfold aw3 attesterMultiOuterArrayInitZeroAw
    rw [ulit_toNat' _ hM3]
    exact le_trans haw2Ge
      (attesterMachineStateM_ge
        (attesterMultiOuterArrayInitFreeAw aw).toNat
        (attesterMultiOuterArrayInitFreeWord mem aw).toNat 32)
  have haw3Mul : aw3.toNat * 32 < UInt256.size := by
    unfold aw3 attesterMultiOuterArrayInitZeroAw
    rw [ulit_toNat' _ hM3]
    exact hM3Mul
  have hM4 :
      MachineState.M aw3.toNat
        (attesterMultiRevokeInnerArrayInitSecondZeroWord mem aw).toNat 32 <
        UInt256.size :=
    attesterMachineStateM32_lt (s := aw3.toNat)
      (f := (attesterMultiRevokeInnerArrayInitSecondZeroWord mem aw).toNat)
      haw3Mul hsecond63
  have hM4Mul :
      MachineState.M aw3.toNat
        (attesterMultiRevokeInnerArrayInitSecondZeroWord mem aw).toNat 32 * 32 <
        UInt256.size :=
    attesterMachineStateM32_mul32_lt (s := aw3.toNat)
      (f := (attesterMultiRevokeInnerArrayInitSecondZeroWord mem aw).toNat)
      haw3Mul hsecond63
  have haw4Ge : 3 ≤ aw4.toNat := by
    unfold aw4 attesterMultiRevokeInnerArrayInitSecondZeroAw
    rw [ulit_toNat' _ hM4]
    exact le_trans haw3Ge
      (attesterMachineStateM_ge
        (attesterMultiOuterArrayInitZeroAw mem aw).toNat
        (attesterMultiRevokeInnerArrayInitSecondZeroWord mem aw).toNat 32)
  have haw4Mul : aw4.toNat * 32 < UInt256.size := by
    unfold aw4 attesterMultiRevokeInnerArrayInitSecondZeroAw
    rw [ulit_toNat' _ hM4]
    exact hM4Mul
  have hM5 :
      MachineState.M aw4.toNat slot.toNat 32 < UInt256.size :=
    attesterMachineStateM32_lt (s := aw4.toNat) (f := slot.toNat)
      haw4Mul hslot63
  have hM5Mul :
      MachineState.M aw4.toNat slot.toNat 32 * 32 < UInt256.size :=
    attesterMachineStateM32_mul32_lt (s := aw4.toNat) (f := slot.toNat)
      haw4Mul hslot63
  constructor
  · unfold attesterMultiRevokeInnerArrayInitStepAw
    rw [ulit_toNat' _ hM5]
    exact le_trans haw4Ge
      (attesterMachineStateM_ge
        (attesterMultiRevokeInnerArrayInitSecondZeroAw mem aw).toNat
        slot.toNat 32)
  · unfold attesterMultiRevokeInnerArrayInitStepAw
    rw [ulit_toNat' _ hM5]
    exact hM5Mul

theorem attesterMultiRevokeInnerArrayInitStep_base_size
    {base slot len : UInt256} {mem : ByteArray} {aw : UInt256}
    (hmem : base.toNat + 32 ≤ mem.size) :
    base.toNat + 32 ≤
      (attesterMultiRevokeInnerArrayInitStepMem slot mem aw).size := by
  have hsize1 := attesterWriteWord_size_nat mem 64
    ((⟨64⟩ : UInt256) + attesterMultiOuterArrayInitFreeWord mem aw)
  have hsize2 := attesterWriteWord_size_nat
    (attesterMultiOuterArrayInitFreeMem mem aw)
    (attesterMultiOuterArrayInitFreeWord mem aw).toNat
    (⟨0⟩ : UInt256)
  have hsize3 := attesterWriteWord_size_nat
    (attesterMultiOuterArrayInitZeroMem mem aw)
    (attesterMultiRevokeInnerArrayInitSecondZeroWord mem aw).toNat
    (⟨0⟩ : UInt256)
  have hsize4 := attesterWriteWord_size_nat
    (attesterMultiRevokeInnerArrayInitSecondZeroMem mem aw)
    slot.toNat (attesterMultiOuterArrayInitFreeWord mem aw)
  change base.toNat + 32 ≤
    (Reasoning.Theory.writeWord
      (attesterMultiRevokeInnerArrayInitSecondZeroMem mem aw)
      slot.toNat (attesterMultiOuterArrayInitFreeWord mem aw)).size
  rw [hsize4]
  change base.toNat + 32 ≤ max
    (attesterMultiRevokeInnerArrayInitSecondZeroMem mem aw).size (slot.toNat + 32)
  apply le_trans _ (Nat.le_max_left _ _)
  change base.toNat + 32 ≤
    (Reasoning.Theory.writeWord
      (attesterMultiOuterArrayInitZeroMem mem aw)
      (attesterMultiRevokeInnerArrayInitSecondZeroWord mem aw).toNat
      (⟨0⟩ : UInt256)).size
  rw [hsize3]
  apply le_trans _ (Nat.le_max_left _ _)
  change base.toNat + 32 ≤
    (Reasoning.Theory.writeWord
      (attesterMultiOuterArrayInitFreeMem mem aw)
      (attesterMultiOuterArrayInitFreeWord mem aw).toNat
      (⟨0⟩ : UInt256)).size
  rw [hsize2]
  apply le_trans _ (Nat.le_max_left _ _)
  change base.toNat + 32 ≤
    (Reasoning.Theory.writeWord mem 64
      ((⟨64⟩ : UInt256) + attesterMultiOuterArrayInitFreeWord mem aw)).size
  rw [hsize1]
  exact le_trans hmem (Nat.le_max_left _ _)

theorem attesterMultiRevokeInnerArrayInitStep_size_ge
    {slot : UInt256} {mem : ByteArray} {aw : UInt256} :
    mem.size ≤ (attesterMultiRevokeInnerArrayInitStepMem slot mem aw).size := by
  apply le_trans (attesterWriteWord_size_ge_nat mem 64
    ((⟨64⟩ : UInt256) + attesterMultiOuterArrayInitFreeWord mem aw))
  apply le_trans (attesterWriteWord_size_ge_nat
    (attesterMultiOuterArrayInitFreeMem mem aw)
    (attesterMultiOuterArrayInitFreeWord mem aw).toNat
    (⟨0⟩ : UInt256))
  apply le_trans (attesterWriteWord_size_ge_nat
    (attesterMultiOuterArrayInitZeroMem mem aw)
    (attesterMultiRevokeInnerArrayInitSecondZeroWord mem aw).toNat
    (⟨0⟩ : UInt256))
  exact attesterWriteWord_size_ge_nat
    (attesterMultiRevokeInnerArrayInitSecondZeroMem mem aw) slot.toNat
    (attesterMultiOuterArrayInitFreeWord mem aw)

theorem attesterMultiRevokeInnerArrayCopyStep_read64
    {I : ExecutionEnv} {base payload idx : UInt256}
    {mem : ByteArray} {aw : UInt256}
    (hfree : 64 + 32 ≤ (attesterMultiRevokeInnerArrayCopyFreeWord mem aw).toNat)
    (hzero : 64 + 32 ≤ (attesterMultiRevokeInnerArrayCopyZeroWord mem aw).toNat)
    (hslot :
      64 + 32 ≤ (attesterMultiRevokeInnerArrayCopySlotWord base idx).toNat) :
    (attesterMultiRevokeInnerArrayCopyStepMem I base payload idx mem aw).readWithPadding
        64 32 =
      UInt256.toByteArray
        ((⟨64⟩ : UInt256) + attesterMultiRevokeInnerArrayCopyFreeWord mem aw) := by
  have hread1 :
      (attesterMultiRevokeInnerArrayCopyFreeMem mem aw).readWithPadding 64 32 =
        UInt256.toByteArray
          ((⟨64⟩ : UInt256) + attesterMultiRevokeInnerArrayCopyFreeWord mem aw) := by
    change (Reasoning.Theory.writeWord mem 64
      ((⟨64⟩ : UInt256) + attesterMultiRevokeInnerArrayCopyFreeWord mem aw)).readWithPadding
        64 32 =
        UInt256.toByteArray
          ((⟨64⟩ : UInt256) + attesterMultiRevokeInnerArrayCopyFreeWord mem aw)
    exact attesterWriteWord_read_back_nat mem 64
      ((⟨64⟩ : UInt256) + attesterMultiRevokeInnerArrayCopyFreeWord mem aw)
  have hmem1 : 64 + 32 ≤ (attesterMultiRevokeInnerArrayCopyFreeMem mem aw).size := by
    have hsize := attesterWriteWord_size_nat mem 64
      ((⟨64⟩ : UInt256) + attesterMultiRevokeInnerArrayCopyFreeWord mem aw)
    change 64 + 32 ≤
      (Reasoning.Theory.writeWord mem 64
        ((⟨64⟩ : UInt256) + attesterMultiRevokeInnerArrayCopyFreeWord mem aw)).size
    rw [hsize]
    change 96 ≤ max mem.size (64 + 32)
    exact Nat.le_max_right _ _
  have hread2 :
      (attesterMultiRevokeInnerArrayCopyUidMem I payload idx mem aw).readWithPadding
          64 32 =
        UInt256.toByteArray
          ((⟨64⟩ : UInt256) + attesterMultiRevokeInnerArrayCopyFreeWord mem aw) := by
    change (Reasoning.Theory.writeWord
      (attesterMultiRevokeInnerArrayCopyFreeMem mem aw)
      (attesterMultiRevokeInnerArrayCopyFreeWord mem aw).toNat
      (attesterMultiRevokeInnerArrayCopyUidWord I payload idx)).readWithPadding
        64 32 =
        UInt256.toByteArray
          ((⟨64⟩ : UInt256) + attesterMultiRevokeInnerArrayCopyFreeWord mem aw)
    exact attesterReadWithPadding_writeWord_preserved_above_nat
      (mem := attesterMultiRevokeInnerArrayCopyFreeMem mem aw)
      (base := 64)
      (writeOff := (attesterMultiRevokeInnerArrayCopyFreeWord mem aw).toNat)
      (len := ((⟨64⟩ : UInt256) + attesterMultiRevokeInnerArrayCopyFreeWord mem aw))
      (writeVal := attesterMultiRevokeInnerArrayCopyUidWord I payload idx)
      hmem1 hfree hread1
  have hmem2 :
      64 + 32 ≤ (attesterMultiRevokeInnerArrayCopyUidMem I payload idx mem aw).size := by
    have hsize := attesterWriteWord_size_nat (attesterMultiRevokeInnerArrayCopyFreeMem mem aw)
      (attesterMultiRevokeInnerArrayCopyFreeWord mem aw).toNat
      (attesterMultiRevokeInnerArrayCopyUidWord I payload idx)
    change 64 + 32 ≤
      (Reasoning.Theory.writeWord (attesterMultiRevokeInnerArrayCopyFreeMem mem aw)
        (attesterMultiRevokeInnerArrayCopyFreeWord mem aw).toNat
        (attesterMultiRevokeInnerArrayCopyUidWord I payload idx)).size
    rw [hsize]
    exact le_trans hmem1 (Nat.le_max_left _ _)
  have hread3 :
      (attesterMultiRevokeInnerArrayCopyZeroMem I payload idx mem aw).readWithPadding
          64 32 =
        UInt256.toByteArray
          ((⟨64⟩ : UInt256) + attesterMultiRevokeInnerArrayCopyFreeWord mem aw) := by
    change (Reasoning.Theory.writeWord
      (attesterMultiRevokeInnerArrayCopyUidMem I payload idx mem aw)
      (attesterMultiRevokeInnerArrayCopyZeroWord mem aw).toNat
      (⟨0⟩ : UInt256)).readWithPadding 64 32 =
        UInt256.toByteArray
          ((⟨64⟩ : UInt256) + attesterMultiRevokeInnerArrayCopyFreeWord mem aw)
    exact attesterReadWithPadding_writeWord_preserved_above_nat
      (mem := attesterMultiRevokeInnerArrayCopyUidMem I payload idx mem aw)
      (base := 64)
      (writeOff := (attesterMultiRevokeInnerArrayCopyZeroWord mem aw).toNat)
      (len := ((⟨64⟩ : UInt256) + attesterMultiRevokeInnerArrayCopyFreeWord mem aw))
      (writeVal := (⟨0⟩ : UInt256))
      hmem2 hzero hread2
  have hmem3 :
      64 + 32 ≤
        (attesterMultiRevokeInnerArrayCopyZeroMem I payload idx mem aw).size := by
    have hsize := attesterWriteWord_size_nat
      (attesterMultiRevokeInnerArrayCopyUidMem I payload idx mem aw)
      (attesterMultiRevokeInnerArrayCopyZeroWord mem aw).toNat
      (⟨0⟩ : UInt256)
    change 64 + 32 ≤
      (Reasoning.Theory.writeWord
        (attesterMultiRevokeInnerArrayCopyUidMem I payload idx mem aw)
        (attesterMultiRevokeInnerArrayCopyZeroWord mem aw).toNat
        (⟨0⟩ : UInt256)).size
    rw [hsize]
    exact le_trans hmem2 (Nat.le_max_left _ _)
  change (Reasoning.Theory.writeWord
    (attesterMultiRevokeInnerArrayCopyZeroMem I payload idx mem aw)
    (attesterMultiRevokeInnerArrayCopySlotWord base idx).toNat
    (attesterMultiRevokeInnerArrayCopyFreeWord mem aw)).readWithPadding 64 32 =
      UInt256.toByteArray
        ((⟨64⟩ : UInt256) + attesterMultiRevokeInnerArrayCopyFreeWord mem aw)
  exact attesterReadWithPadding_writeWord_preserved_above_nat
    (mem := attesterMultiRevokeInnerArrayCopyZeroMem I payload idx mem aw)
    (base := 64)
    (writeOff := (attesterMultiRevokeInnerArrayCopySlotWord base idx).toNat)
    (len := ((⟨64⟩ : UInt256) + attesterMultiRevokeInnerArrayCopyFreeWord mem aw))
    (writeVal := attesterMultiRevokeInnerArrayCopyFreeWord mem aw)
    hmem3 hslot hread3

theorem attesterMultiRevokeInnerArrayCopyZero_readWithPadding_nat
    {I : ExecutionEnv} {base payload idx len : UInt256}
    {mem : ByteArray} {aw : UInt256}
    (hmem : base.toNat + 32 ≤ mem.size)
    (hread : mem.readWithPadding base.toNat 32 = UInt256.toByteArray len)
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
    exact attesterReadWithPadding_writeWord_preserved_below_nat
      (mem := mem) (base := base.toNat) (writeOff := 64)
      (len := len) (writeVal := attesterMultiRevokeInnerArrayCopyFreeBumpWord mem aw)
      hmem h64 hread
  have hmem1 :
      base.toNat + 32 ≤ (attesterMultiRevokeInnerArrayCopyFreeMem mem aw).size := by
    have hsize := attesterWriteWord_size_nat mem 64
      (attesterMultiRevokeInnerArrayCopyFreeBumpWord mem aw)
    change base.toNat + 32 ≤
      (Reasoning.Theory.writeWord mem 64
        (attesterMultiRevokeInnerArrayCopyFreeBumpWord mem aw)).size
    rw [hsize]
    exact le_trans hmem (Nat.le_max_left _ _)
  have hread2 :
      (attesterMultiRevokeInnerArrayCopyUidMem I payload idx mem aw).readWithPadding
          base.toNat 32 =
        UInt256.toByteArray len := by
    change (Reasoning.Theory.writeWord
      (attesterMultiRevokeInnerArrayCopyFreeMem mem aw)
      (attesterMultiRevokeInnerArrayCopyFreeWord mem aw).toNat
      (attesterMultiRevokeInnerArrayCopyUidWord I payload idx)).readWithPadding
        base.toNat 32 = UInt256.toByteArray len
    exact attesterReadWithPadding_writeWord_preserved_above_nat
      (mem := attesterMultiRevokeInnerArrayCopyFreeMem mem aw)
      (base := base.toNat)
      (writeOff := (attesterMultiRevokeInnerArrayCopyFreeWord mem aw).toNat)
      (len := len)
      (writeVal := attesterMultiRevokeInnerArrayCopyUidWord I payload idx)
      hmem1 huid hread1
  have hmem2 :
      base.toNat + 32 ≤
        (attesterMultiRevokeInnerArrayCopyUidMem I payload idx mem aw).size := by
    have hsize := attesterWriteWord_size_nat (attesterMultiRevokeInnerArrayCopyFreeMem mem aw)
      (attesterMultiRevokeInnerArrayCopyFreeWord mem aw).toNat
      (attesterMultiRevokeInnerArrayCopyUidWord I payload idx)
    change base.toNat + 32 ≤
      (Reasoning.Theory.writeWord
        (attesterMultiRevokeInnerArrayCopyFreeMem mem aw)
        (attesterMultiRevokeInnerArrayCopyFreeWord mem aw).toNat
        (attesterMultiRevokeInnerArrayCopyUidWord I payload idx)).size
    rw [hsize]
    exact le_trans hmem1 (Nat.le_max_left _ _)
  change (Reasoning.Theory.writeWord
    (attesterMultiRevokeInnerArrayCopyUidMem I payload idx mem aw)
    (attesterMultiRevokeInnerArrayCopyZeroWord mem aw).toNat
    (⟨0⟩ : UInt256)).readWithPadding base.toNat 32 =
      UInt256.toByteArray len
  exact attesterReadWithPadding_writeWord_preserved_above_nat
    (mem := attesterMultiRevokeInnerArrayCopyUidMem I payload idx mem aw)
    (base := base.toNat)
    (writeOff := (attesterMultiRevokeInnerArrayCopyZeroWord mem aw).toNat)
    (len := len) (writeVal := (⟨0⟩ : UInt256))
    hmem2 hzero hread2

theorem attesterMultiRevokeInnerArrayCopyZero_mloadLen_nat
    {I : ExecutionEnv} {base payload idx len : UInt256}
    {mem : ByteArray} {aw : UInt256}
    (hmem : base.toNat + 32 ≤ mem.size)
    (hread : mem.readWithPadding base.toNat 32 = UInt256.toByteArray len)
    (haw :
      ¬ base ≥
        attesterMultiRevokeInnerArrayCopyZeroAw I payload idx mem aw * (⟨32⟩ : UInt256))
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
    attesterMultiRevokeInnerArrayCopyZero_readWithPadding_nat
      (I := I) (base := base) (payload := payload) (idx := idx)
      (len := len) (mem := mem) (aw := aw)
      hmem hread h64 huid hzero
  have hmem1 :
      base.toNat + 32 ≤ (attesterMultiRevokeInnerArrayCopyFreeMem mem aw).size := by
    have hsize := attesterWriteWord_size_nat mem 64
      (attesterMultiRevokeInnerArrayCopyFreeBumpWord mem aw)
    change base.toNat + 32 ≤
      (Reasoning.Theory.writeWord mem 64
        (attesterMultiRevokeInnerArrayCopyFreeBumpWord mem aw)).size
    rw [hsize]
    exact le_trans hmem (Nat.le_max_left _ _)
  have hmem2 :
      base.toNat + 32 ≤
        (attesterMultiRevokeInnerArrayCopyUidMem I payload idx mem aw).size := by
    have hsize := attesterWriteWord_size_nat (attesterMultiRevokeInnerArrayCopyFreeMem mem aw)
      (attesterMultiRevokeInnerArrayCopyFreeWord mem aw).toNat
      (attesterMultiRevokeInnerArrayCopyUidWord I payload idx)
    change base.toNat + 32 ≤
      (Reasoning.Theory.writeWord
        (attesterMultiRevokeInnerArrayCopyFreeMem mem aw)
        (attesterMultiRevokeInnerArrayCopyFreeWord mem aw).toNat
        (attesterMultiRevokeInnerArrayCopyUidWord I payload idx)).size
    rw [hsize]
    exact le_trans hmem1 (Nat.le_max_left _ _)
  have hmemZero :
      base.toNat + 32 ≤
        (attesterMultiRevokeInnerArrayCopyZeroMem I payload idx mem aw).size := by
    have hsize := attesterWriteWord_size_nat
      (attesterMultiRevokeInnerArrayCopyUidMem I payload idx mem aw)
      (attesterMultiRevokeInnerArrayCopyZeroWord mem aw).toNat
      (⟨0⟩ : UInt256)
    change base.toNat + 32 ≤
      (Reasoning.Theory.writeWord
        (attesterMultiRevokeInnerArrayCopyUidMem I payload idx mem aw)
        (attesterMultiRevokeInnerArrayCopyZeroWord mem aw).toNat
      (⟨0⟩ : UInt256)).size
    rw [hsize]
    exact le_trans hmem2 (Nat.le_max_left _ _)
  exact attesterMloadWord_of_readWithPadding hmemZero haw hreadZero

theorem attesterMultiRevokeInnerArrayCopyStep_readWithPadding_nat
    {I : ExecutionEnv} {base payload idx len : UInt256}
    {mem : ByteArray} {aw : UInt256}
    (hmem : base.toNat + 32 ≤ mem.size)
    (hread : mem.readWithPadding base.toNat 32 = UInt256.toByteArray len)
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
  have hreadZero :=
    attesterMultiRevokeInnerArrayCopyZero_readWithPadding_nat
      (I := I) (base := base) (payload := payload) (idx := idx)
      (len := len) (mem := mem) (aw := aw)
      hmem hread h64 huid hzero
  have hmem1 :
      base.toNat + 32 ≤ (attesterMultiRevokeInnerArrayCopyFreeMem mem aw).size := by
    have hsize := attesterWriteWord_size_nat mem 64
      (attesterMultiRevokeInnerArrayCopyFreeBumpWord mem aw)
    change base.toNat + 32 ≤
      (Reasoning.Theory.writeWord mem 64
        (attesterMultiRevokeInnerArrayCopyFreeBumpWord mem aw)).size
    rw [hsize]
    exact le_trans hmem (Nat.le_max_left _ _)
  have hmem2 :
      base.toNat + 32 ≤
        (attesterMultiRevokeInnerArrayCopyUidMem I payload idx mem aw).size := by
    have hsize := attesterWriteWord_size_nat (attesterMultiRevokeInnerArrayCopyFreeMem mem aw)
      (attesterMultiRevokeInnerArrayCopyFreeWord mem aw).toNat
      (attesterMultiRevokeInnerArrayCopyUidWord I payload idx)
    change base.toNat + 32 ≤
      (Reasoning.Theory.writeWord
        (attesterMultiRevokeInnerArrayCopyFreeMem mem aw)
        (attesterMultiRevokeInnerArrayCopyFreeWord mem aw).toNat
        (attesterMultiRevokeInnerArrayCopyUidWord I payload idx)).size
    rw [hsize]
    exact le_trans hmem1 (Nat.le_max_left _ _)
  have hmem3 :
      base.toNat + 32 ≤
        (attesterMultiRevokeInnerArrayCopyZeroMem I payload idx mem aw).size := by
    have hsize := attesterWriteWord_size_nat
      (attesterMultiRevokeInnerArrayCopyUidMem I payload idx mem aw)
      (attesterMultiRevokeInnerArrayCopyZeroWord mem aw).toNat
      (⟨0⟩ : UInt256)
    change base.toNat + 32 ≤
      (Reasoning.Theory.writeWord
        (attesterMultiRevokeInnerArrayCopyUidMem I payload idx mem aw)
        (attesterMultiRevokeInnerArrayCopyZeroWord mem aw).toNat
        (⟨0⟩ : UInt256)).size
    rw [hsize]
    exact le_trans hmem2 (Nat.le_max_left _ _)
  change (Reasoning.Theory.writeWord
    (attesterMultiRevokeInnerArrayCopyZeroMem I payload idx mem aw)
    (attesterMultiRevokeInnerArrayCopySlotWord base idx).toNat
    (attesterMultiRevokeInnerArrayCopyFreeWord mem aw)).readWithPadding
      base.toNat 32 = UInt256.toByteArray len
  exact attesterReadWithPadding_writeWord_preserved_above_nat
    (mem := attesterMultiRevokeInnerArrayCopyZeroMem I payload idx mem aw)
    (base := base.toNat)
    (writeOff := (attesterMultiRevokeInnerArrayCopySlotWord base idx).toNat)
    (len := len)
    (writeVal := attesterMultiRevokeInnerArrayCopyFreeWord mem aw)
    hmem3 hslot hreadZero

theorem attesterMultiRevokeInnerArrayCopyStep_readWithPadding_at_nat
    {I : ExecutionEnv} {readBase base payload idx len : UInt256}
    {mem : ByteArray} {aw : UInt256}
    (hmem : readBase.toNat + 32 ≤ mem.size)
    (hread : mem.readWithPadding readBase.toNat 32 = UInt256.toByteArray len)
    (h64 : 64 + 32 ≤ readBase.toNat)
    (huid :
      readBase.toNat + 32 ≤ (attesterMultiRevokeInnerArrayCopyFreeWord mem aw).toNat)
    (hzero :
      readBase.toNat + 32 ≤ (attesterMultiRevokeInnerArrayCopyZeroWord mem aw).toNat)
    (hslot :
      readBase.toNat + 32 ≤ (attesterMultiRevokeInnerArrayCopySlotWord base idx).toNat) :
    (attesterMultiRevokeInnerArrayCopyStepMem I base payload idx mem aw).readWithPadding
        readBase.toNat 32 =
      UInt256.toByteArray len := by
  have hreadZero :=
    attesterMultiRevokeInnerArrayCopyZero_readWithPadding_nat
      (I := I) (base := readBase) (payload := payload) (idx := idx)
      (len := len) (mem := mem) (aw := aw)
      hmem hread h64 huid hzero
  have hmem1 :
      readBase.toNat + 32 ≤ (attesterMultiRevokeInnerArrayCopyFreeMem mem aw).size := by
    change readBase.toNat + 32 ≤
      (Reasoning.Theory.writeWord mem 64
        (attesterMultiRevokeInnerArrayCopyFreeBumpWord mem aw)).size
    exact le_trans hmem
      (attesterWriteWord_size_ge_nat mem 64
        (attesterMultiRevokeInnerArrayCopyFreeBumpWord mem aw))
  have hmem2 :
      readBase.toNat + 32 ≤
        (attesterMultiRevokeInnerArrayCopyUidMem I payload idx mem aw).size := by
    change readBase.toNat + 32 ≤
      (Reasoning.Theory.writeWord
        (attesterMultiRevokeInnerArrayCopyFreeMem mem aw)
        (attesterMultiRevokeInnerArrayCopyFreeWord mem aw).toNat
        (attesterMultiRevokeInnerArrayCopyUidWord I payload idx)).size
    exact le_trans hmem1
      (attesterWriteWord_size_ge_nat
        (attesterMultiRevokeInnerArrayCopyFreeMem mem aw)
        (attesterMultiRevokeInnerArrayCopyFreeWord mem aw).toNat
        (attesterMultiRevokeInnerArrayCopyUidWord I payload idx))
  have hmem3 :
      readBase.toNat + 32 ≤
        (attesterMultiRevokeInnerArrayCopyZeroMem I payload idx mem aw).size := by
    change readBase.toNat + 32 ≤
      (Reasoning.Theory.writeWord
        (attesterMultiRevokeInnerArrayCopyUidMem I payload idx mem aw)
        (attesterMultiRevokeInnerArrayCopyZeroWord mem aw).toNat
        (⟨0⟩ : UInt256)).size
    exact le_trans hmem2
      (attesterWriteWord_size_ge_nat
        (attesterMultiRevokeInnerArrayCopyUidMem I payload idx mem aw)
        (attesterMultiRevokeInnerArrayCopyZeroWord mem aw).toNat
        (⟨0⟩ : UInt256))
  change (Reasoning.Theory.writeWord
    (attesterMultiRevokeInnerArrayCopyZeroMem I payload idx mem aw)
    (attesterMultiRevokeInnerArrayCopySlotWord base idx).toNat
    (attesterMultiRevokeInnerArrayCopyFreeWord mem aw)).readWithPadding
      readBase.toNat 32 = UInt256.toByteArray len
  exact attesterReadWithPadding_writeWord_preserved_above_nat
    (mem := attesterMultiRevokeInnerArrayCopyZeroMem I payload idx mem aw)
    (base := readBase.toNat)
    (writeOff := (attesterMultiRevokeInnerArrayCopySlotWord base idx).toNat)
    (len := len)
    (writeVal := attesterMultiRevokeInnerArrayCopyFreeWord mem aw)
    hmem3 hslot hreadZero

theorem attesterMultiRevokeInnerArrayCopyStep_readWithPadding_at_nat_disj
    {I : ExecutionEnv} {readBase base payload idx len : UInt256}
    {mem : ByteArray} {aw : UInt256}
    (hmem : readBase.toNat + 32 ≤ mem.size)
    (hread : mem.readWithPadding readBase.toNat 32 = UInt256.toByteArray len)
    (h64 : 64 + 32 ≤ readBase.toNat)
    (huid :
      readBase.toNat + 32 ≤ (attesterMultiRevokeInnerArrayCopyFreeWord mem aw).toNat)
    (hzero :
      readBase.toNat + 32 ≤ (attesterMultiRevokeInnerArrayCopyZeroWord mem aw).toNat)
    (hslotDisj :
      readBase.toNat + 32 ≤ (attesterMultiRevokeInnerArrayCopySlotWord base idx).toNat ∨
        (attesterMultiRevokeInnerArrayCopySlotWord base idx).toNat + 32 ≤ readBase.toNat) :
    (attesterMultiRevokeInnerArrayCopyStepMem I base payload idx mem aw).readWithPadding
        readBase.toNat 32 =
      UInt256.toByteArray len := by
  have hreadZero :=
    attesterMultiRevokeInnerArrayCopyZero_readWithPadding_nat
      (I := I) (base := readBase) (payload := payload) (idx := idx)
      (len := len) (mem := mem) (aw := aw)
      hmem hread h64 huid hzero
  have hmem1 :
      readBase.toNat + 32 ≤ (attesterMultiRevokeInnerArrayCopyFreeMem mem aw).size := by
    change readBase.toNat + 32 ≤
      (Reasoning.Theory.writeWord mem 64
        (attesterMultiRevokeInnerArrayCopyFreeBumpWord mem aw)).size
    exact le_trans hmem
      (attesterWriteWord_size_ge_nat mem 64
        (attesterMultiRevokeInnerArrayCopyFreeBumpWord mem aw))
  have hmem2 :
      readBase.toNat + 32 ≤
        (attesterMultiRevokeInnerArrayCopyUidMem I payload idx mem aw).size := by
    change readBase.toNat + 32 ≤
      (Reasoning.Theory.writeWord
        (attesterMultiRevokeInnerArrayCopyFreeMem mem aw)
        (attesterMultiRevokeInnerArrayCopyFreeWord mem aw).toNat
        (attesterMultiRevokeInnerArrayCopyUidWord I payload idx)).size
    exact le_trans hmem1
      (attesterWriteWord_size_ge_nat
        (attesterMultiRevokeInnerArrayCopyFreeMem mem aw)
        (attesterMultiRevokeInnerArrayCopyFreeWord mem aw).toNat
        (attesterMultiRevokeInnerArrayCopyUidWord I payload idx))
  have hmem3 :
      readBase.toNat + 32 ≤
        (attesterMultiRevokeInnerArrayCopyZeroMem I payload idx mem aw).size := by
    change readBase.toNat + 32 ≤
      (Reasoning.Theory.writeWord
        (attesterMultiRevokeInnerArrayCopyUidMem I payload idx mem aw)
        (attesterMultiRevokeInnerArrayCopyZeroWord mem aw).toNat
        (⟨0⟩ : UInt256)).size
    exact le_trans hmem2
      (attesterWriteWord_size_ge_nat
        (attesterMultiRevokeInnerArrayCopyUidMem I payload idx mem aw)
        (attesterMultiRevokeInnerArrayCopyZeroWord mem aw).toNat
        (⟨0⟩ : UInt256))
  change (Reasoning.Theory.writeWord
    (attesterMultiRevokeInnerArrayCopyZeroMem I payload idx mem aw)
    (attesterMultiRevokeInnerArrayCopySlotWord base idx).toNat
    (attesterMultiRevokeInnerArrayCopyFreeWord mem aw)).readWithPadding
      readBase.toNat 32 = UInt256.toByteArray len
  rcases hslotDisj with hslotAbove | hslotBelow
  · exact attesterReadWithPadding_writeWord_preserved_above_nat
      (mem := attesterMultiRevokeInnerArrayCopyZeroMem I payload idx mem aw)
      (base := readBase.toNat)
      (writeOff := (attesterMultiRevokeInnerArrayCopySlotWord base idx).toNat)
      (len := len)
      (writeVal := attesterMultiRevokeInnerArrayCopyFreeWord mem aw)
      hmem3 hslotAbove hreadZero
  · exact attesterReadWithPadding_writeWord_preserved_below_nat
      (mem := attesterMultiRevokeInnerArrayCopyZeroMem I payload idx mem aw)
      (base := readBase.toNat)
      (writeOff := (attesterMultiRevokeInnerArrayCopySlotWord base idx).toNat)
      (len := len)
      (writeVal := attesterMultiRevokeInnerArrayCopyFreeWord mem aw)
      hmem3 hslotBelow hreadZero

theorem attesterMultiRevokeInnerArrayCopyStep_read_current_slot
    {I : ExecutionEnv} {base payload idx : UInt256}
    {mem : ByteArray} {aw : UInt256} :
    (attesterMultiRevokeInnerArrayCopyStepMem I base payload idx mem aw).readWithPadding
        (attesterMultiRevokeInnerArrayCopySlotWord base idx).toNat 32 =
      UInt256.toByteArray (attesterMultiRevokeInnerArrayCopyFreeWord mem aw) := by
  change (Reasoning.Theory.writeWord
    (attesterMultiRevokeInnerArrayCopyZeroMem I payload idx mem aw)
    (attesterMultiRevokeInnerArrayCopySlotWord base idx).toNat
    (attesterMultiRevokeInnerArrayCopyFreeWord mem aw)).readWithPadding
      (attesterMultiRevokeInnerArrayCopySlotWord base idx).toNat 32 =
    UInt256.toByteArray (attesterMultiRevokeInnerArrayCopyFreeWord mem aw)
  exact attesterWriteWord_read_back_nat
    (attesterMultiRevokeInnerArrayCopyZeroMem I payload idx mem aw)
    (attesterMultiRevokeInnerArrayCopySlotWord base idx).toNat
    (attesterMultiRevokeInnerArrayCopyFreeWord mem aw)

theorem attesterMultiRevokeInnerArrayCopyStep_read_current_uid
    {I : ExecutionEnv} {base payload idx : UInt256}
    {mem : ByteArray} {aw : UInt256}
    (hzeroToNat :
      (attesterMultiRevokeInnerArrayCopyZeroWord mem aw).toNat =
        (attesterMultiRevokeInnerArrayCopyFreeWord mem aw).toNat + 32)
    (hslotDisj :
      (attesterMultiRevokeInnerArrayCopyFreeWord mem aw).toNat + 32 ≤
          (attesterMultiRevokeInnerArrayCopySlotWord base idx).toNat ∨
        (attesterMultiRevokeInnerArrayCopySlotWord base idx).toNat + 32 ≤
          (attesterMultiRevokeInnerArrayCopyFreeWord mem aw).toNat) :
    (attesterMultiRevokeInnerArrayCopyStepMem I base payload idx mem aw).readWithPadding
        (attesterMultiRevokeInnerArrayCopyFreeWord mem aw).toNat 32 =
      UInt256.toByteArray (attesterMultiRevokeInnerArrayCopyUidWord I payload idx) := by
  let free := attesterMultiRevokeInnerArrayCopyFreeWord mem aw
  let zero := attesterMultiRevokeInnerArrayCopyZeroWord mem aw
  let slot := attesterMultiRevokeInnerArrayCopySlotWord base idx
  let uidWord := attesterMultiRevokeInnerArrayCopyUidWord I payload idx
  have hreadUid :
      (attesterMultiRevokeInnerArrayCopyUidMem I payload idx mem aw).readWithPadding
          free.toNat 32 =
        UInt256.toByteArray uidWord := by
    change (Reasoning.Theory.writeWord
        (attesterMultiRevokeInnerArrayCopyFreeMem mem aw)
        free.toNat uidWord).readWithPadding free.toNat 32 =
      UInt256.toByteArray uidWord
    exact attesterWriteWord_read_back_nat
      (attesterMultiRevokeInnerArrayCopyFreeMem mem aw) free.toNat uidWord
  have hmemUid :
      free.toNat + 32 ≤
        (attesterMultiRevokeInnerArrayCopyUidMem I payload idx mem aw).size := by
    change free.toNat + 32 ≤
      (Reasoning.Theory.writeWord
        (attesterMultiRevokeInnerArrayCopyFreeMem mem aw)
        free.toNat uidWord).size
    rw [attesterWriteWord_size_nat
      (attesterMultiRevokeInnerArrayCopyFreeMem mem aw) free.toNat uidWord]
    exact Nat.le_max_right _ _
  have hreadZero :
      (attesterMultiRevokeInnerArrayCopyZeroMem I payload idx mem aw).readWithPadding
          free.toNat 32 =
        UInt256.toByteArray uidWord := by
    change (Reasoning.Theory.writeWord
        (attesterMultiRevokeInnerArrayCopyUidMem I payload idx mem aw)
        zero.toNat (⟨0⟩ : UInt256)).readWithPadding free.toNat 32 =
      UInt256.toByteArray uidWord
    exact attesterReadWithPadding_writeWord_preserved_above_nat
      (mem := attesterMultiRevokeInnerArrayCopyUidMem I payload idx mem aw)
      (base := free.toNat) (writeOff := zero.toNat)
      (len := uidWord) (writeVal := (⟨0⟩ : UInt256))
      hmemUid (by rw [hzeroToNat]) hreadUid
  have hmemZero :
      free.toNat + 32 ≤
        (attesterMultiRevokeInnerArrayCopyZeroMem I payload idx mem aw).size := by
    change free.toNat + 32 ≤
      (Reasoning.Theory.writeWord
        (attesterMultiRevokeInnerArrayCopyUidMem I payload idx mem aw)
        zero.toNat (⟨0⟩ : UInt256)).size
    exact le_trans hmemUid
      (attesterWriteWord_size_ge_nat
        (attesterMultiRevokeInnerArrayCopyUidMem I payload idx mem aw)
        zero.toNat (⟨0⟩ : UInt256))
  change (Reasoning.Theory.writeWord
    (attesterMultiRevokeInnerArrayCopyZeroMem I payload idx mem aw)
    slot.toNat free).readWithPadding free.toNat 32 =
      UInt256.toByteArray uidWord
  rcases hslotDisj with hslotAbove | hslotBelow
  · exact attesterReadWithPadding_writeWord_preserved_above_nat
      (mem := attesterMultiRevokeInnerArrayCopyZeroMem I payload idx mem aw)
      (base := free.toNat) (writeOff := slot.toNat)
      (len := uidWord) (writeVal := free)
      hmemZero hslotAbove hreadZero
  · exact attesterReadWithPadding_writeWord_preserved_below_nat
      (mem := attesterMultiRevokeInnerArrayCopyZeroMem I payload idx mem aw)
      (base := free.toNat) (writeOff := slot.toNat)
      (len := uidWord) (writeVal := free)
      hmemZero hslotBelow hreadZero

theorem attesterMultiRevokeInnerArrayCopyStep_read_current_zero
    {I : ExecutionEnv} {base payload idx : UInt256}
    {mem : ByteArray} {aw : UInt256}
    (hslotDisj :
      (attesterMultiRevokeInnerArrayCopyZeroWord mem aw).toNat + 32 ≤
          (attesterMultiRevokeInnerArrayCopySlotWord base idx).toNat ∨
        (attesterMultiRevokeInnerArrayCopySlotWord base idx).toNat + 32 ≤
          (attesterMultiRevokeInnerArrayCopyZeroWord mem aw).toNat) :
    (attesterMultiRevokeInnerArrayCopyStepMem I base payload idx mem aw).readWithPadding
        (attesterMultiRevokeInnerArrayCopyZeroWord mem aw).toNat 32 =
      UInt256.toByteArray (⟨0⟩ : UInt256) := by
  let zero := attesterMultiRevokeInnerArrayCopyZeroWord mem aw
  let slot := attesterMultiRevokeInnerArrayCopySlotWord base idx
  let free := attesterMultiRevokeInnerArrayCopyFreeWord mem aw
  have hreadZero :
      (attesterMultiRevokeInnerArrayCopyZeroMem I payload idx mem aw).readWithPadding
          zero.toNat 32 =
        UInt256.toByteArray (⟨0⟩ : UInt256) := by
    change (Reasoning.Theory.writeWord
        (attesterMultiRevokeInnerArrayCopyUidMem I payload idx mem aw)
        zero.toNat (⟨0⟩ : UInt256)).readWithPadding zero.toNat 32 =
      UInt256.toByteArray (⟨0⟩ : UInt256)
    exact attesterWriteWord_read_back_nat
      (attesterMultiRevokeInnerArrayCopyUidMem I payload idx mem aw)
      zero.toNat (⟨0⟩ : UInt256)
  have hmemZero :
      zero.toNat + 32 ≤
        (attesterMultiRevokeInnerArrayCopyZeroMem I payload idx mem aw).size := by
    change zero.toNat + 32 ≤
      (Reasoning.Theory.writeWord
        (attesterMultiRevokeInnerArrayCopyUidMem I payload idx mem aw)
        zero.toNat (⟨0⟩ : UInt256)).size
    rw [attesterWriteWord_size_nat
      (attesterMultiRevokeInnerArrayCopyUidMem I payload idx mem aw)
      zero.toNat (⟨0⟩ : UInt256)]
    exact Nat.le_max_right _ _
  change (Reasoning.Theory.writeWord
    (attesterMultiRevokeInnerArrayCopyZeroMem I payload idx mem aw)
    slot.toNat free).readWithPadding zero.toNat 32 =
      UInt256.toByteArray (⟨0⟩ : UInt256)
  rcases hslotDisj with hslotAbove | hslotBelow
  · exact attesterReadWithPadding_writeWord_preserved_above_nat
      (mem := attesterMultiRevokeInnerArrayCopyZeroMem I payload idx mem aw)
      (base := zero.toNat) (writeOff := slot.toNat)
      (len := (⟨0⟩ : UInt256)) (writeVal := free)
      hmemZero hslotAbove hreadZero
  · exact attesterReadWithPadding_writeWord_preserved_below_nat
      (mem := attesterMultiRevokeInnerArrayCopyZeroMem I payload idx mem aw)
      (base := zero.toNat) (writeOff := slot.toNat)
      (len := (⟨0⟩ : UInt256)) (writeVal := free)
      hmemZero hslotBelow hreadZero

theorem attesterMultiRevokeInnerArrayCopyStep_base_size
    {I : ExecutionEnv} {base payload idx : UInt256}
    {mem : ByteArray} {aw : UInt256}
    (hmem : base.toNat + 32 ≤ mem.size) :
    base.toNat + 32 ≤
      (attesterMultiRevokeInnerArrayCopyStepMem I base payload idx mem aw).size := by
  have hsize1 := attesterWriteWord_size_nat mem 64
    (attesterMultiRevokeInnerArrayCopyFreeBumpWord mem aw)
  have hsize2 := attesterWriteWord_size_nat
    (attesterMultiRevokeInnerArrayCopyFreeMem mem aw)
    (attesterMultiRevokeInnerArrayCopyFreeWord mem aw).toNat
    (attesterMultiRevokeInnerArrayCopyUidWord I payload idx)
  have hsize3 := attesterWriteWord_size_nat
    (attesterMultiRevokeInnerArrayCopyUidMem I payload idx mem aw)
    (attesterMultiRevokeInnerArrayCopyZeroWord mem aw).toNat
    (⟨0⟩ : UInt256)
  have hsize4 := attesterWriteWord_size_nat
    (attesterMultiRevokeInnerArrayCopyZeroMem I payload idx mem aw)
    (attesterMultiRevokeInnerArrayCopySlotWord base idx).toNat
    (attesterMultiRevokeInnerArrayCopyFreeWord mem aw)
  change base.toNat + 32 ≤
    (Reasoning.Theory.writeWord
      (attesterMultiRevokeInnerArrayCopyZeroMem I payload idx mem aw)
      (attesterMultiRevokeInnerArrayCopySlotWord base idx).toNat
      (attesterMultiRevokeInnerArrayCopyFreeWord mem aw)).size
  rw [hsize4]
  apply le_trans _ (Nat.le_max_left _ _)
  change base.toNat + 32 ≤
    (Reasoning.Theory.writeWord
      (attesterMultiRevokeInnerArrayCopyUidMem I payload idx mem aw)
      (attesterMultiRevokeInnerArrayCopyZeroWord mem aw).toNat
      (⟨0⟩ : UInt256)).size
  rw [hsize3]
  apply le_trans _ (Nat.le_max_left _ _)
  change base.toNat + 32 ≤
    (Reasoning.Theory.writeWord
      (attesterMultiRevokeInnerArrayCopyFreeMem mem aw)
      (attesterMultiRevokeInnerArrayCopyFreeWord mem aw).toNat
      (attesterMultiRevokeInnerArrayCopyUidWord I payload idx)).size
  rw [hsize2]
  apply le_trans _ (Nat.le_max_left _ _)
  change base.toNat + 32 ≤
    (Reasoning.Theory.writeWord mem 64
      (attesterMultiRevokeInnerArrayCopyFreeBumpWord mem aw)).size
  rw [hsize1]
  exact le_trans hmem (Nat.le_max_left _ _)

theorem attesterMultiRevokeInnerArrayCopyStep_size_ge
    {I : ExecutionEnv} {base payload idx : UInt256}
    {mem : ByteArray} {aw : UInt256} :
    mem.size ≤ (attesterMultiRevokeInnerArrayCopyStepMem I base payload idx mem aw).size := by
  apply le_trans (attesterWriteWord_size_ge_nat mem 64
    (attesterMultiRevokeInnerArrayCopyFreeBumpWord mem aw))
  apply le_trans (attesterWriteWord_size_ge_nat
    (attesterMultiRevokeInnerArrayCopyFreeMem mem aw)
    (attesterMultiRevokeInnerArrayCopyFreeWord mem aw).toNat
    (attesterMultiRevokeInnerArrayCopyUidWord I payload idx))
  apply le_trans (attesterWriteWord_size_ge_nat
    (attesterMultiRevokeInnerArrayCopyUidMem I payload idx mem aw)
    (attesterMultiRevokeInnerArrayCopyZeroWord mem aw).toNat
    (⟨0⟩ : UInt256))
  exact attesterWriteWord_size_ge_nat
    (attesterMultiRevokeInnerArrayCopyZeroMem I payload idx mem aw)
    (attesterMultiRevokeInnerArrayCopySlotWord base idx).toNat
    (attesterMultiRevokeInnerArrayCopyFreeWord mem aw)

theorem attesterMultiRevokeInnerArrayCopyStep_mload64
    {I : ExecutionEnv} {base payload idx : UInt256}
    {mem : ByteArray} {aw : UInt256}
    (hfree : 64 + 32 ≤ (attesterMultiRevokeInnerArrayCopyFreeWord mem aw).toNat)
    (hzero : 64 + 32 ≤ (attesterMultiRevokeInnerArrayCopyZeroWord mem aw).toNat)
    (hslot :
      64 + 32 ≤ (attesterMultiRevokeInnerArrayCopySlotWord base idx).toNat)
    (haw :
      ¬ (⟨64⟩ : UInt256) ≥
        attesterMultiRevokeInnerArrayCopyStepAw I base payload idx mem aw *
          (⟨32⟩ : UInt256)) :
    attesterMultiRevokeInnerArrayCopyFreeWord
        (attesterMultiRevokeInnerArrayCopyStepMem I base payload idx mem aw)
        (attesterMultiRevokeInnerArrayCopyStepAw I base payload idx mem aw) =
      (⟨64⟩ : UInt256) + attesterMultiRevokeInnerArrayCopyFreeWord mem aw := by
  have hread := attesterMultiRevokeInnerArrayCopyStep_read64
    (I := I) (base := base) (payload := payload) (idx := idx)
    (mem := mem) (aw := aw)
    hfree hzero hslot
  have hmem : (⟨64⟩ : UInt256).toNat + 32 ≤
      (attesterMultiRevokeInnerArrayCopyStepMem I base payload idx mem aw).size := by
    have hsize := attesterWriteWord_size_nat
      (attesterMultiRevokeInnerArrayCopyZeroMem I payload idx mem aw)
      (attesterMultiRevokeInnerArrayCopySlotWord base idx).toNat
      (attesterMultiRevokeInnerArrayCopyFreeWord mem aw)
    change (⟨64⟩ : UInt256).toNat + 32 ≤
      (Reasoning.Theory.writeWord
        (attesterMultiRevokeInnerArrayCopyZeroMem I payload idx mem aw)
        (attesterMultiRevokeInnerArrayCopySlotWord base idx).toNat
        (attesterMultiRevokeInnerArrayCopyFreeWord mem aw)).size
    rw [hsize]
    change 96 ≤ max
      (attesterMultiRevokeInnerArrayCopyZeroMem I payload idx mem aw).size
      ((attesterMultiRevokeInnerArrayCopySlotWord base idx).toNat + 32)
    exact le_trans (by omega) (Nat.le_max_right _ _)
  exact attesterMloadWord_of_readWithPadding hmem haw hread

theorem attesterMultiRevokeInnerArrayCopyStepAw_bounds
    {I : ExecutionEnv} {base payload idx : UInt256}
    {mem : ByteArray} {aw : UInt256}
    (hawGe : 3 ≤ aw.toNat)
    (hawMul : aw.toNat * 32 < UInt256.size)
    (hbase63 : base.toNat + 63 < UInt256.size)
    (hfree63 : (attesterMultiRevokeInnerArrayCopyFreeWord mem aw).toNat + 63 <
      UInt256.size)
    (hzero63 : (attesterMultiRevokeInnerArrayCopyZeroWord mem aw).toNat + 63 <
      UInt256.size)
    (hslot63 : (attesterMultiRevokeInnerArrayCopySlotWord base idx).toNat + 63 <
      UInt256.size) :
    3 ≤ (attesterMultiRevokeInnerArrayCopyStepAw I base payload idx mem aw).toNat ∧
      (attesterMultiRevokeInnerArrayCopyStepAw I base payload idx mem aw).toNat * 32 <
        UInt256.size := by
  let aw1 := attesterMultiRevokeInnerArrayCopyAwAfterMload aw
  let aw2 := attesterMultiRevokeInnerArrayCopyFreeAw mem aw
  let aw3 := attesterMultiRevokeInnerArrayCopyUidAw idx mem aw
  let aw4 := attesterMultiRevokeInnerArrayCopyZeroAw I payload idx mem aw
  let aw5 := attesterMloadAw aw4 base
  let free := attesterMultiRevokeInnerArrayCopyFreeWord mem aw
  let zero := attesterMultiRevokeInnerArrayCopyZeroWord mem aw
  let slot := attesterMultiRevokeInnerArrayCopySlotWord base idx
  have h64_63 : (⟨64⟩ : UInt256).toNat + 63 < UInt256.size := by decide
  have hM1 : MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32 < UInt256.size :=
    attesterMachineStateM32_lt (s := aw.toNat) (f := (⟨64⟩ : UInt256).toNat)
      hawMul h64_63
  have hM1Mul :
      MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32 * 32 < UInt256.size :=
    attesterMachineStateM32_mul32_lt (s := aw.toNat)
      (f := (⟨64⟩ : UInt256).toNat) hawMul h64_63
  have haw1Ge : 3 ≤ aw1.toNat := by
    unfold aw1 attesterMultiRevokeInnerArrayCopyAwAfterMload attesterMloadAw
    rw [ulit_toNat' _ hM1]
    exact le_trans hawGe
      (attesterMachineStateM_ge aw.toNat (⟨64⟩ : UInt256).toNat 32)
  have haw1Mul : aw1.toNat * 32 < UInt256.size := by
    unfold aw1 attesterMultiRevokeInnerArrayCopyAwAfterMload attesterMloadAw
    rw [ulit_toNat' _ hM1]
    exact hM1Mul
  have hM2 : MachineState.M aw1.toNat 64 32 < UInt256.size :=
    attesterMachineStateM32_lt (s := aw1.toNat) (f := 64)
      haw1Mul (by norm_num [UInt256.size])
  have hM2Mul : MachineState.M aw1.toNat 64 32 * 32 < UInt256.size :=
    attesterMachineStateM32_mul32_lt (s := aw1.toNat) (f := 64)
      haw1Mul (by norm_num [UInt256.size])
  have haw2Ge : 3 ≤ aw2.toNat := by
    unfold aw2 attesterMultiRevokeInnerArrayCopyFreeAw
    rw [ulit_toNat' _ hM2]
    exact le_trans haw1Ge
      (attesterMachineStateM_ge aw1.toNat 64 32)
  have haw2Mul : aw2.toNat * 32 < UInt256.size := by
    unfold aw2 attesterMultiRevokeInnerArrayCopyFreeAw
    rw [ulit_toNat' _ hM2]
    exact hM2Mul
  have hM3 : MachineState.M aw2.toNat free.toNat 32 < UInt256.size :=
    attesterMachineStateM32_lt (s := aw2.toNat) (f := free.toNat)
      haw2Mul (by simpa [free] using hfree63)
  have hM3Mul : MachineState.M aw2.toNat free.toNat 32 * 32 < UInt256.size :=
    attesterMachineStateM32_mul32_lt (s := aw2.toNat) (f := free.toNat)
      haw2Mul (by simpa [free] using hfree63)
  have haw3Ge : 3 ≤ aw3.toNat := by
    unfold aw3 attesterMultiRevokeInnerArrayCopyUidAw
    rw [ulit_toNat' _ hM3]
    exact le_trans haw2Ge
      (attesterMachineStateM_ge
        (attesterMultiRevokeInnerArrayCopyFreeAw mem aw).toNat
        (attesterMultiRevokeInnerArrayCopyFreeWord mem aw).toNat 32)
  have haw3Mul : aw3.toNat * 32 < UInt256.size := by
    unfold aw3 attesterMultiRevokeInnerArrayCopyUidAw
    rw [ulit_toNat' _ hM3]
    exact hM3Mul
  have hM4 : MachineState.M aw3.toNat zero.toNat 32 < UInt256.size :=
    attesterMachineStateM32_lt (s := aw3.toNat) (f := zero.toNat)
      haw3Mul (by simpa [zero] using hzero63)
  have hM4Mul : MachineState.M aw3.toNat zero.toNat 32 * 32 < UInt256.size :=
    attesterMachineStateM32_mul32_lt (s := aw3.toNat) (f := zero.toNat)
      haw3Mul (by simpa [zero] using hzero63)
  have haw4Ge : 3 ≤ aw4.toNat := by
    unfold aw4 attesterMultiRevokeInnerArrayCopyZeroAw
    rw [ulit_toNat' _ hM4]
    exact le_trans haw3Ge
      (attesterMachineStateM_ge
        (attesterMultiRevokeInnerArrayCopyUidAw idx mem aw).toNat
        (attesterMultiRevokeInnerArrayCopyZeroWord mem aw).toNat 32)
  have haw4Mul : aw4.toNat * 32 < UInt256.size := by
    unfold aw4 attesterMultiRevokeInnerArrayCopyZeroAw
    rw [ulit_toNat' _ hM4]
    exact hM4Mul
  have hM5 : MachineState.M aw4.toNat base.toNat 32 < UInt256.size :=
    attesterMachineStateM32_lt (s := aw4.toNat) (f := base.toNat)
      haw4Mul hbase63
  have hM5Mul : MachineState.M aw4.toNat base.toNat 32 * 32 < UInt256.size :=
    attesterMachineStateM32_mul32_lt (s := aw4.toNat) (f := base.toNat)
      haw4Mul hbase63
  have haw5Ge : 3 ≤ aw5.toNat := by
    unfold aw5 attesterMloadAw
    rw [ulit_toNat' _ hM5]
    exact le_trans haw4Ge
      (attesterMachineStateM_ge aw4.toNat base.toNat 32)
  have haw5Mul : aw5.toNat * 32 < UInt256.size := by
    unfold aw5 attesterMloadAw
    rw [ulit_toNat' _ hM5]
    exact hM5Mul
  have hM6 : MachineState.M aw5.toNat slot.toNat 32 < UInt256.size :=
    attesterMachineStateM32_lt (s := aw5.toNat) (f := slot.toNat)
      haw5Mul (by simpa [slot] using hslot63)
  have hM6Mul : MachineState.M aw5.toNat slot.toNat 32 * 32 < UInt256.size :=
    attesterMachineStateM32_mul32_lt (s := aw5.toNat) (f := slot.toNat)
      haw5Mul (by simpa [slot] using hslot63)
  constructor
  · unfold attesterMultiRevokeInnerArrayCopyStepAw
    rw [ulit_toNat' _ hM6]
    exact le_trans haw5Ge
      (attesterMachineStateM_ge
        (attesterMloadAw
          (attesterMultiRevokeInnerArrayCopyZeroAw I payload idx mem aw) base).toNat
        (attesterMultiRevokeInnerArrayCopySlotWord base idx).toNat 32)
  · unfold attesterMultiRevokeInnerArrayCopyStepAw
    rw [ulit_toNat' _ hM6]
    exact hM6Mul

theorem attesterMultiRevokeInnerArrayCopyStep_freeWord_toNat
    {I : ExecutionEnv} {base payload idx : UInt256}
    {mem : ByteArray} {aw : UInt256}
    (hfree : 64 + 32 ≤ (attesterMultiRevokeInnerArrayCopyFreeWord mem aw).toNat)
    (hzero : 64 + 32 ≤ (attesterMultiRevokeInnerArrayCopyZeroWord mem aw).toNat)
    (hslot :
      64 + 32 ≤ (attesterMultiRevokeInnerArrayCopySlotWord base idx).toNat)
    (hawMul :
      (attesterMultiRevokeInnerArrayCopyStepAw I base payload idx mem aw).toNat * 32 <
        UInt256.size)
    (hawGe :
      3 ≤ (attesterMultiRevokeInnerArrayCopyStepAw I base payload idx mem aw).toNat)
    (hfreeBound :
      (attesterMultiRevokeInnerArrayCopyFreeWord mem aw).toNat + 64 < UInt256.size) :
    (attesterMultiRevokeInnerArrayCopyFreeWord
        (attesterMultiRevokeInnerArrayCopyStepMem I base payload idx mem aw)
        (attesterMultiRevokeInnerArrayCopyStepAw I base payload idx mem aw)).toNat =
      (attesterMultiRevokeInnerArrayCopyFreeWord mem aw).toNat + 64 := by
  rw [attesterMultiRevokeInnerArrayCopyStep_mload64
    (I := I) (base := base) (payload := payload) (idx := idx)
    (mem := mem) (aw := aw)
    hfree hzero hslot
    (attesterMload64ActiveWordsGe3 hawMul hawGe)]
  exact attester_uadd_lit64_toNat
    (attesterMultiRevokeInnerArrayCopyFreeWord mem aw) hfreeBound

theorem attesterMultiRevokeInnerArrayCopyZeroAw_covers_base
    {I : ExecutionEnv} {base payload idx : UInt256}
    {mem : ByteArray} {aw : UInt256}
    (hawGe : 3 ≤ aw.toNat)
    (hawMul : aw.toNat * 32 < UInt256.size)
    (hfree63 : (attesterMultiRevokeInnerArrayCopyFreeWord mem aw).toNat + 63 <
      UInt256.size)
    (hzero63 : (attesterMultiRevokeInnerArrayCopyZeroWord mem aw).toNat + 63 <
      UInt256.size)
    (hzeroGe : base.toNat + 32 ≤
      (attesterMultiRevokeInnerArrayCopyZeroWord mem aw).toNat) :
    ¬ base ≥
      attesterMultiRevokeInnerArrayCopyZeroAw I payload idx mem aw *
        (⟨32⟩ : UInt256) := by
  let aw1 := attesterMultiRevokeInnerArrayCopyAwAfterMload aw
  let aw2 := attesterMultiRevokeInnerArrayCopyFreeAw mem aw
  let aw3 := attesterMultiRevokeInnerArrayCopyUidAw idx mem aw
  let aw4 := attesterMultiRevokeInnerArrayCopyZeroAw I payload idx mem aw
  let free := attesterMultiRevokeInnerArrayCopyFreeWord mem aw
  let zero := attesterMultiRevokeInnerArrayCopyZeroWord mem aw
  have h64_63 : (⟨64⟩ : UInt256).toNat + 63 < UInt256.size := by decide
  have hM1 : MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32 < UInt256.size :=
    attesterMachineStateM32_lt (s := aw.toNat) (f := (⟨64⟩ : UInt256).toNat)
      hawMul h64_63
  have hM1Mul :
      MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32 * 32 < UInt256.size :=
    attesterMachineStateM32_mul32_lt (s := aw.toNat)
      (f := (⟨64⟩ : UInt256).toNat) hawMul h64_63
  have haw1Ge : 3 ≤ aw1.toNat := by
    unfold aw1 attesterMultiRevokeInnerArrayCopyAwAfterMload attesterMloadAw
    rw [ulit_toNat' _ hM1]
    exact le_trans hawGe
      (attesterMachineStateM_ge aw.toNat (⟨64⟩ : UInt256).toNat 32)
  have haw1Mul : aw1.toNat * 32 < UInt256.size := by
    unfold aw1 attesterMultiRevokeInnerArrayCopyAwAfterMload attesterMloadAw
    rw [ulit_toNat' _ hM1]
    exact hM1Mul
  have hM2 : MachineState.M aw1.toNat 64 32 < UInt256.size :=
    attesterMachineStateM32_lt (s := aw1.toNat) (f := 64)
      haw1Mul (by norm_num [UInt256.size])
  have hM2Mul : MachineState.M aw1.toNat 64 32 * 32 < UInt256.size :=
    attesterMachineStateM32_mul32_lt (s := aw1.toNat) (f := 64)
      haw1Mul (by norm_num [UInt256.size])
  have haw2Ge : 3 ≤ aw2.toNat := by
    unfold aw2 attesterMultiRevokeInnerArrayCopyFreeAw
    rw [ulit_toNat' _ hM2]
    exact le_trans haw1Ge
      (attesterMachineStateM_ge aw1.toNat 64 32)
  have haw2Mul : aw2.toNat * 32 < UInt256.size := by
    unfold aw2 attesterMultiRevokeInnerArrayCopyFreeAw
    rw [ulit_toNat' _ hM2]
    exact hM2Mul
  have hM3 : MachineState.M aw2.toNat free.toNat 32 < UInt256.size :=
    attesterMachineStateM32_lt (s := aw2.toNat) (f := free.toNat)
      haw2Mul (by simpa [free] using hfree63)
  have hM3Mul : MachineState.M aw2.toNat free.toNat 32 * 32 < UInt256.size :=
    attesterMachineStateM32_mul32_lt (s := aw2.toNat) (f := free.toNat)
      haw2Mul (by simpa [free] using hfree63)
  have haw3Ge : 3 ≤ aw3.toNat := by
    unfold aw3 attesterMultiRevokeInnerArrayCopyUidAw
    rw [ulit_toNat' _ hM3]
    exact le_trans haw2Ge
      (attesterMachineStateM_ge
        (attesterMultiRevokeInnerArrayCopyFreeAw mem aw).toNat
        (attesterMultiRevokeInnerArrayCopyFreeWord mem aw).toNat 32)
  have haw3Mul : aw3.toNat * 32 < UInt256.size := by
    unfold aw3 attesterMultiRevokeInnerArrayCopyUidAw
    rw [ulit_toNat' _ hM3]
    exact hM3Mul
  have hM4 : MachineState.M aw3.toNat zero.toNat 32 < UInt256.size :=
    attesterMachineStateM32_lt (s := aw3.toNat) (f := zero.toNat)
      haw3Mul (by simpa [zero] using hzero63)
  have hM4Mul : MachineState.M aw3.toNat zero.toNat 32 * 32 < UInt256.size :=
    attesterMachineStateM32_mul32_lt (s := aw3.toNat) (f := zero.toNat)
      haw3Mul (by simpa [zero] using hzero63)
  apply attesterMloadActiveWordsCovers
  · unfold attesterMultiRevokeInnerArrayCopyZeroAw
    rw [ulit_toNat' _ hM4]
    exact hM4Mul
  · unfold attesterMultiRevokeInnerArrayCopyZeroAw
    rw [ulit_toNat' _ hM4]
    have hcover := attesterMachineStateM_covers_word32 aw3.toNat zero.toNat
    have hcovered : base.toNat + 32 ≤ 32 * MachineState.M aw3.toNat zero.toNat 32 :=
      le_trans hzeroGe (le_trans (Nat.le_add_right zero.toNat 32) hcover)
    simpa [Nat.mul_comm] using hcovered

theorem attesterMultiRevokeInnerArrayCopyZero_mloadLen_of_bounds_nat
    {I : ExecutionEnv} {base payload idx len : UInt256}
    {mem : ByteArray} {aw : UInt256}
    (hmem : base.toNat + 32 ≤ mem.size)
    (hread : mem.readWithPadding base.toNat 32 = UInt256.toByteArray len)
    (hawGe : 3 ≤ aw.toNat)
    (hawMul : aw.toNat * 32 < UInt256.size)
    (hfree96 :
      (attesterMultiRevokeInnerArrayCopyFreeWord mem aw).toNat + 96 <
        UInt256.size)
    (h64 : 64 + 32 ≤ base.toNat)
    (hfree :
      base.toNat + 32 ≤ (attesterMultiRevokeInnerArrayCopyFreeWord mem aw).toNat)
    (hzero :
      base.toNat + 32 ≤ (attesterMultiRevokeInnerArrayCopyZeroWord mem aw).toNat) :
    attesterMloadWord
      (attesterMultiRevokeInnerArrayCopyZeroMem I payload idx mem aw)
      (attesterMultiRevokeInnerArrayCopyZeroAw I payload idx mem aw)
      base = len := by
  have hfree63 :
      (attesterMultiRevokeInnerArrayCopyFreeWord mem aw).toNat + 63 <
        UInt256.size := by
    omega
  have hfree32 :
      (attesterMultiRevokeInnerArrayCopyFreeWord mem aw).toNat + 32 <
        UInt256.size := by
    omega
  have hzeroToNat :
      (attesterMultiRevokeInnerArrayCopyZeroWord mem aw).toNat =
        (attesterMultiRevokeInnerArrayCopyFreeWord mem aw).toNat + 32 :=
    attesterMultiRevokeInnerArrayCopyZeroWord_toNat hfree32
  have hzero63 :
      (attesterMultiRevokeInnerArrayCopyZeroWord mem aw).toNat + 63 <
        UInt256.size := by
    rw [hzeroToNat]
    omega
  exact attesterMultiRevokeInnerArrayCopyZero_mloadLen_nat
    (I := I) (base := base) (payload := payload) (idx := idx)
    (len := len) (mem := mem) (aw := aw)
    hmem hread
    (attesterMultiRevokeInnerArrayCopyZeroAw_covers_base
      (I := I) (base := base) (payload := payload) (idx := idx)
      (mem := mem) (aw := aw)
      hawGe hawMul hfree63 hzero63 hzero)
    h64 hfree hzero

end Benchmarks.EAS.Attester
