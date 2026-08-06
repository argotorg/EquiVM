import Examples.Precompiles.Blake2f.Fallback.Setup.Terms

/-!
# BLAKE2F fallback/model parser bridge

This module contains model-facing facts about the bytecode parser terms.  It is intentionally
separate from the RDx trace modules: editing these pure bytearray/word bridge lemmas should not
force rechecking the instruction trace proofs.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem solcBytesSetPaddedMem_read160_raw
    (cd : ByteArray) (hlen : cd.size = 213) :
    (solcBytesSetPaddedMem cd (UInt256.ofNat 213) ⟨0⟩).readWithPadding 160 32 =
      (cd.extract (⟨0⟩ : UInt256).toNat
        ((⟨0⟩ : UInt256).toNat + (UInt256.ofNat 213).toNat)).extract
        (32 * 0) (32 * 0 + 32) := by
  have hsrc : (⟨0⟩ : UInt256).toNat + (UInt256.ofNat 213).toNat ≤ cd.size := by
    rw [hlen]
    decide
  exact
    solcBytesSetPaddedMem_read_payload_word cd (UInt256.ofNat 213) ⟨0⟩ 0
      (by decide)
      (by native_decide)
      hsrc
      (by decide)

theorem solcBytesSetPaddedMem_read160
    (cd : ByteArray) (hlen : cd.size = 213) :
    (solcBytesSetPaddedMem cd (UInt256.ofNat 213) ⟨0⟩).readWithPadding 160 32 =
      cd.extract 0 32 := by
  rw [solcBytesSetPaddedMem_read160_raw cd hlen]
  apply ByteArray.ext
  simp only [ByteArray.data_extract, Array.extract_extract]
  congr 2

theorem fromBytes'_append_single (bs : List UInt8) (b : UInt8) :
    fromBytes' (bs ++ [b]) = fromBytes' bs + 256 ^ bs.length * b.toNat := by
  induction bs with
  | nil =>
      simp [fromBytes']
  | cons a bs ih =>
      simp [fromBytes', ih, Nat.pow_succ, Nat.mul_add, Nat.add_assoc, Nat.mul_comm,
        Nat.mul_assoc]

theorem fromBytesBigEndian_cons (b : UInt8) (bs : List UInt8) :
    fromBytesBigEndian (b :: bs) =
      b.toNat * 256 ^ bs.length + fromBytesBigEndian bs := by
  unfold fromBytesBigEndian Function.comp
  rw [List.reverse_cons, fromBytes'_append_single, List.length_reverse]
  ring

theorem bytesToBigEndianNat_foldl_acc (bs : List UInt8) (acc : Nat) :
    bs.foldl (fun acc b => acc * 256 + b.toNat) acc =
      acc * 256 ^ bs.length + fromBytesBigEndian bs := by
  induction bs generalizing acc with
  | nil =>
      simp [fromBytesBigEndian, fromBytes']
  | cons b bs ih =>
      simp only [List.foldl_cons, List.length_cons]
      rw [ih (acc * 256 + b.toNat), fromBytesBigEndian_cons b bs]
      ring

theorem fromBytesBigEndian_eq_foldl (bs : List UInt8) :
    fromBytesBigEndian bs = bs.foldl (fun acc b => acc * 256 + b.toNat) 0 := by
  rw [bytesToBigEndianNat_foldl_acc bs 0]
  simp

theorem hArrayAllocMem_read160 (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (hArrayAllocMem I).readWithPadding 160 32 =
      (solcBytesSetPaddedMem I.calldata (UInt256.ofNat 213) ⟨0⟩).readWithPadding 160 32 := by
  have hsrc : (⟨0⟩ : UInt256).toNat + (UInt256.ofNat 213).toNat ≤ I.calldata.size := by
    rw [hlen]
    decide
  unfold hArrayAllocMem
  exact write32_read_above_len (UInt256.toByteArray (UInt256.ofNat 640))
    (solcBytesSetPaddedMem I.calldata (UInt256.ofNat 213) ⟨0⟩) 64 160 32
    (by rw [toByteArray_size])
    (by
      rw [solcBytesSetPaddedMem_size I.calldata (UInt256.ofNat 213) ⟨0⟩
        (by decide) hsrc (by native_decide)]
      decide)
    (by decide)
    (by
      rw [solcBytesSetPaddedMem_size I.calldata (UInt256.ofNat 213) ⟨0⟩
        (by decide) hsrc (by native_decide)]
      decide)
    (by decide)
    (by decide)

theorem hArrayZeroMem_read160 (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (hArrayZeroMem I).readWithPadding 160 32 =
      (solcBytesSetPaddedMem I.calldata (UInt256.ofNat 213) ⟨0⟩).readWithPadding 160 32 := by
  have hsize : (hArrayAllocMem I).size = 405 := hArrayAllocMem_size I hlen
  unfold hArrayZeroMem ByteArray.write
  rw [if_neg (by decide : ¬ 256 = 0)]
  rw [if_pos (by rw [hlen])]
  simp [hsize]
  change ((ffi.ByteArray.zeroes 21).copySlice 0 (hArrayAllocMem I) 384 21).readWithPadding
    160 32 = (solcBytesSetPaddedMem I.calldata (UInt256.ofNat 213) ⟨0⟩).readWithPadding 160 32
  rw [copySlice_read_below_gen]
  exact hArrayAllocMem_read160 I hlen
  · decide
  · rw [hsize]
    decide
  · decide
  · decide

theorem mArrayAllocMem_read160 (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (mArrayAllocMem I).readWithPadding 160 32 =
      (solcBytesSetPaddedMem I.calldata (UInt256.ofNat 213) ⟨0⟩).readWithPadding 160 32 := by
  unfold mArrayAllocMem
  rw [write32_read_above_len (UInt256.toByteArray (UInt256.ofNat 1152))
    (hArrayZeroMem I) 64 160 32
    (by rw [toByteArray_size])
    (by rw [hArrayZeroMem_size I hlen]; decide)
    (by decide)
    (by rw [hArrayZeroMem_size I hlen]; decide)
    (by decide)
    (by decide)]
  exact hArrayZeroMem_read160 I hlen

theorem mArrayZeroMem_read160 (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (mArrayZeroMem I).readWithPadding 160 32 =
      (solcBytesSetPaddedMem I.calldata (UInt256.ofNat 213) ⟨0⟩).readWithPadding 160 32 := by
  have hsize : (mArrayAllocMem I).size = 405 := mArrayAllocMem_size I hlen
  unfold mArrayZeroMem ByteArray.write
  rw [if_neg (by decide : ¬ 512 = 0)]
  rw [if_pos (by rw [hlen])]
  simp [hsize]
  change ((ffi.ByteArray.zeroes 0).copySlice 0 (mArrayAllocMem I) 405 0).readWithPadding
    160 32 = (solcBytesSetPaddedMem I.calldata (UInt256.ofNat 213) ⟨0⟩).readWithPadding 160 32
  rw [copySlice_read_below_gen]
  exact mArrayAllocMem_read160 I hlen
  · decide
  · rw [hsize]
    decide
  · decide
  · decide

theorem tArrayAllocMem_read160 (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (tArrayAllocMem I).readWithPadding 160 32 =
      (solcBytesSetPaddedMem I.calldata (UInt256.ofNat 213) ⟨0⟩).readWithPadding 160 32 := by
  unfold tArrayAllocMem
  rw [write32_read_above_len (UInt256.toByteArray (UInt256.ofNat 1216))
    (mArrayZeroMem I) 64 160 32
    (by rw [toByteArray_size])
    (by rw [mArrayZeroMem_size I hlen]; decide)
    (by decide)
    (by rw [mArrayZeroMem_size I hlen]; decide)
    (by decide)
    (by decide)]
  exact mArrayZeroMem_read160 I hlen

theorem tArrayZeroMem_read160 (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (tArrayZeroMem I).readWithPadding 160 32 =
      (solcBytesSetPaddedMem I.calldata (UInt256.ofNat 213) ⟨0⟩).readWithPadding 160 32 := by
  have hsize : (tArrayAllocMem I).size = 405 := tArrayAllocMem_size I hlen
  unfold tArrayZeroMem ByteArray.write
  rw [if_neg (by decide : ¬ 64 = 0)]
  rw [if_pos (by rw [hlen])]
  simp [hsize]
  change ((ffi.ByteArray.zeroes 0).copySlice 0 (tArrayAllocMem I) 405 0).readWithPadding
    160 32 = (solcBytesSetPaddedMem I.calldata (UInt256.ofNat 213) ⟨0⟩).readWithPadding 160 32
  rw [copySlice_read_below_gen]
  exact tArrayAllocMem_read160 I hlen
  · decide
  · rw [hsize]
    decide
  · decide
  · decide

theorem inputFirstWord_eq_calldata_word
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    inputFirstWord I = uInt256OfByteArray (I.calldata.readBytes 0 32) := by
  rw [uInt256OfByteArray_eq]
  unfold inputFirstWord
  congr 1
  unfold fromByteArrayBigEndian
  rw [byteArray_toList_eq, byteArray_toList_eq]
  rw [tArrayZeroMem_read160 I hlen, solcBytesSetPaddedMem_read160 I.calldata hlen]
  rw [readBytes_at_toList_any]
  · rw [ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop,
      List.drop_zero]
  · rw [hlen]
    decide

theorem inputFirstWord_shiftRight_toNat_eq_modelRounds
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (UInt256.shiftRight (inputFirstWord I) ⟨224⟩).toNat = Model.rounds I.calldata := by
  rw [inputFirstWord_eq_calldata_word I hlen]
  rw [selector_toNat I.calldata (by rw [hlen]; decide)]
  unfold Model.rounds Model.bytesToBigEndianNat
  rw [fromBytesBigEndian_eq_foldl]
  rw [byteArray_toList_eq (I.calldata.extract 0 4), ByteArray.data_extract,
    Array.toList_extract, List.extract_eq_take_drop, List.drop_zero]

theorem modelRounds_eq_inputFirstWord_shiftRight
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    Model.rounds I.calldata =
      (UInt256.shiftRight (inputFirstWord I) ⟨224⟩).toNat :=
  (inputFirstWord_shiftRight_toNat_eq_modelRounds I hlen).symm

theorem modelOutput_eq_compressBytes_zero_of_rounds_zero
    (input : ByteArray) (hrounds : Model.rounds input = 0) :
    Model.output input = Model.compressBytes input 0 := by
  unfold Model.output
  rw [hrounds]

theorem bytecodeRoundGuard_zero_of_modelRounds_zero
    (I : ExecutionEnv) (hlen : I.calldata.size = 213)
    (hrounds : Model.rounds I.calldata = 0) :
    UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) = ⟨0⟩ := by
  apply ult_zero
  rw [inputFirstWord_shiftRight_toNat_eq_modelRounds I hlen, hrounds]
  decide

theorem modelRounds_zero_of_bytecodeRoundGuard
    (I : ExecutionEnv) (hlen : I.calldata.size = 213)
    (hcond : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) = ⟨0⟩) :
    Model.rounds I.calldata = 0 := by
  have hnot : ¬ 0 < (UInt256.shiftRight (inputFirstWord I) ⟨224⟩).toNat := by
    intro hpos
    have hlt : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) = ⟨1⟩ := by
      apply ult_one
      simpa using hpos
    rw [hlt] at hcond
    contradiction
  have hzero : (UInt256.shiftRight (inputFirstWord I) ⟨224⟩).toNat = 0 := by
    omega
  rw [← inputFirstWord_shiftRight_toNat_eq_modelRounds I hlen]
  exact hzero

theorem bytecodeRoundGuard_one_of_modelRounds_pos
    (I : ExecutionEnv) (hlen : I.calldata.size = 213)
    (hrounds : 0 < Model.rounds I.calldata) :
    UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) = ⟨1⟩ := by
  apply ult_one
  rw [inputFirstWord_shiftRight_toNat_eq_modelRounds I hlen]
  exact hrounds

theorem bytecodeRoundGuard_ne_zero_of_modelRounds_pos
    (I : ExecutionEnv) (hlen : I.calldata.size = 213)
    (hrounds : 0 < Model.rounds I.calldata) :
    UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩ := by
  rw [bytecodeRoundGuard_one_of_modelRounds_pos I hlen hrounds]
  decide

theorem modelRounds_pos_of_bytecodeRoundGuard_ne_zero
    (I : ExecutionEnv) (hlen : I.calldata.size = 213)
    (hcond : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    0 < Model.rounds I.calldata := by
  by_contra hnot
  have hzero : Model.rounds I.calldata = 0 := by omega
  exact hcond (bytecodeRoundGuard_zero_of_modelRounds_zero I hlen hzero)

end Blake2f
