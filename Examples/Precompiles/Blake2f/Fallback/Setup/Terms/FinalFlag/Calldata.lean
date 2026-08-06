import Examples.Precompiles.Blake2f.Fallback.Setup.Terms.Compression

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-! ## Calldata final-flag bridge

The fallback checks the final flag with `CALLDATALOAD 212; BYTE 0; GT 1`.  The trusted model is
stated against `calldata[212]!`.  These local lemmas connect those two views under the EIP-152
length guard. -/

theorem calldata_drop212 (cd : ByteArray) (hlen : cd.size = 213) :
    cd.data.toList.drop 212 = [cd[212]!] := by
  change cd.data.size = 213 at hlen
  rw [List.drop_eq_getElem_cons (by rw [Array.length_toList]; omega)]
  have htail : cd.data.toList.drop (212 + 1) = [] := by
    apply List.eq_nil_of_length_eq_zero
    rw [List.length_drop, Array.length_toList]
    omega
  rw [htail]
  congr
  rw [Array.getElem_toList]
  rw [getElem!_pos]
  rfl

theorem readBytes212_extract_one (cd : ByteArray) (hlen : cd.size = 213) :
    (cd.readBytes 212 32).extract 0 1 = ⟨#[cd[212]!]⟩ := by
  unfold ByteArray.readBytes
  rw [if_pos (by decide : (decide (212 < 2 ^ 64) && decide (32 < 2 ^ 64)) = true)]
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [ByteArray.data_extract]
  rw [Array.toList_extract]
  rw [List.extract_eq_take_drop]
  rw [ByteArray.data_append, Array.toList_append]
  rw [ByteArray.data_copySlice]
  simp [calldata_drop212 cd hlen]

theorem copySlice212_size (cd : ByteArray) (hlen : cd.size = 213) :
    (cd.copySlice 212 ByteArray.empty 0 32).size = 1 := by
  show (cd.copySlice 212 ByteArray.empty 0 32).data.size = 1
  rw [ByteArray.data_copySlice]
  rw [Array.size_append, Array.size_append, Array.size_extract, Array.size_extract]
  change cd.data.size = 213 at hlen
  simp [hlen]

theorem readBytes212_size (cd : ByteArray) (hlen : cd.size = 213) :
    (cd.readBytes 212 32).size = 32 := by
  unfold ByteArray.readBytes
  rw [if_pos (by decide : (decide (212 < 2 ^ 64) && decide (32 < 2 ^ 64)) = true)]
  rw [ByteArray.size_append]
  rw [copySlice212_size cd hlen]
  change 1 + (ffi.ByteArray.zeroes (32 - 1)).data.size = 32
  simp [ffi.ByteArray.zeroes]

theorem readBytes212_eq_tail_padded (cd : ByteArray) (hlen : cd.size = 213) :
    cd.readBytes 212 32 = cd.extract 212 213 ++ ffi.ByteArray.zeroes 31 := by
  unfold ByteArray.readBytes
  rw [if_pos (by decide : (decide (212 < 2 ^ 64) && decide (32 < 2 ^ 64)) = true)]
  have hcopy :
      cd.copySlice 212 ByteArray.empty 0 32 = cd.extract 212 213 := by
    apply ByteArray.ext
    apply Array.toList_inj.mp
    rw [ByteArray.data_copySlice, ByteArray.data_extract]
    rw [Array.toList_append, Array.toList_append, Array.toList_extract, Array.toList_extract]
    rw [List.extract_eq_take_drop, List.extract_eq_take_drop]
    simp [hlen]
  rw [hcopy]
  have hsize : (cd.extract 212 213).size = 1 := by
    rw [ByteArray.size_extract]
    omega
  simp [hsize]

theorem solcBytesSetPaddedMem_read372 (cd : ByteArray) (hlen : cd.size = 213) :
    (solcBytesSetPaddedMem cd (UInt256.ofNat 213) ⟨0⟩).readWithPadding 372 32 =
      cd.readBytes 212 32 := by
  let base := solcBytesSetCalldataMem cd (UInt256.ofNat 213) ⟨0⟩
  have hlenWord : (UInt256.ofNat 213).toNat ≠ 0 := by decide
  have hsrc : (⟨0⟩ : UInt256).toNat + (UInt256.ofNat 213).toNat ≤ cd.size := by
    rw [hlen]
    decide
  have hbaseSize : base.size = 373 := by
    change (solcBytesSetCalldataMem cd (UInt256.ofNat 213) ⟨0⟩).size = 373
    rw [solcBytesSetCalldataMem_size cd (UInt256.ofNat 213) ⟨0⟩ hlenWord hsrc]
    decide
  have hpayload :
      base.extract 160 (160 + (UInt256.ofNat 213).toNat) =
        cd.extract (⟨0⟩ : UInt256).toNat
          ((⟨0⟩ : UInt256).toNat + (UInt256.ofNat 213).toNat) := by
    change
      (solcBytesSetCalldataMem cd (UInt256.ofNat 213) ⟨0⟩).extract
          160 (160 + (UInt256.ofNat 213).toNat) =
        cd.extract (⟨0⟩ : UInt256).toNat
          ((⟨0⟩ : UInt256).toNat + (UInt256.ofNat 213).toNat)
    exact solcBytesSetCalldataMem_extract_payload cd (UInt256.ofNat 213) ⟨0⟩ hlenWord hsrc
  have hpayloadTail :
      base.extract 372 373 = cd.extract 212 213 := by
    have h := congrArg (fun b : ByteArray => b.extract 212 213) hpayload
    change
      (base.extract 160 (160 + (UInt256.ofNat 213).toNat)).extract 212 213 =
        (cd.extract (⟨0⟩ : UInt256).toNat
          ((⟨0⟩ : UInt256).toNat + (UInt256.ofNat 213).toNat)).extract 212 213 at h
    rw [extract_extract_BA] at h
    rw [extract_extract_BA] at h
    simpa using h
  unfold solcBytesSetPaddedMem
  change
    ((⟨0⟩ : UInt256).toByteArray.write 0 base
        (((⟨160⟩ : UInt256) + UInt256.ofNat 213).toNat) 32).readWithPadding 372 32 =
      cd.readBytes 212 32
  have hend : (((⟨160⟩ : UInt256) + UInt256.ofNat 213).toNat) = 373 := by
    native_decide
  rw [hend]
  rw [toByteArray_write_eq (⟨0⟩ : UInt256) base 373 (by rw [hbaseSize])
    (by rw [hbaseSize]; exact lt_usize 0 (by norm_num))]
  have hzero0 : ffi.ByteArray.zeroes (373 - base.size) = ByteArray.empty := by
    rw [hbaseSize]
    exact zeroes_zero (n := 0) (by rfl)
  rw [hzero0, ByteArray.append_empty]
  rw [readWithPadding_eq_extract' _ 372 32 (by decide) (by decide) (by
    rw [ByteArray.size_append, hbaseSize, toByteArray_size]
    decide)]
  rw [extract_append_span base (UInt256.toByteArray (⟨0⟩ : UInt256)) 372 404
    (by rw [hbaseSize]; decide) (by rw [hbaseSize]; decide)]
  rw [hbaseSize]
  rw [show 404 - 373 = 31 by decide]
  rw [hpayloadTail]
  rw [zero_toByteArray_eq_zeroes32]
  rw [zeroes32_extract_zeroes 31 (by decide)]
  exact (readBytes212_eq_tail_padded cd hlen).symm

theorem readWithPadding_extract_first_of_in_bounds
    (mem : ByteArray) (addr : Nat) (h : addr + 32 ≤ mem.size) :
    (mem.readWithPadding addr 32).extract 0 1 = mem.readWithPadding addr 1 := by
  rw [readWithPadding_eq_extract' mem addr 32 (by decide) (by decide) h]
  rw [readWithPadding_eq_extract' mem addr 1 (by decide) (by decide) (by omega)]
  rw [extract_extract_BA]
  rw [show addr + 0 = addr by omega]
  rw [show min (addr + 1) (addr + 32) = addr + 1 by omega]

theorem solcBytesSetPaddedMem_read372_first
    (cd : ByteArray) (hlen : cd.size = 213) :
    ((solcBytesSetPaddedMem cd (UInt256.ofNat 213) ⟨0⟩).readWithPadding 372 32).extract 0 1 =
      ⟨#[cd[212]!]⟩ := by
  rw [solcBytesSetPaddedMem_read372 cd hlen]
  exact readBytes212_extract_one cd hlen

end Blake2f
