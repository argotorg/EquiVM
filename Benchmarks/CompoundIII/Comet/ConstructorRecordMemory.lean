import Benchmarks.CompoundIII.Comet.ConstructorScalarRead

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def constructorRecordWord (c : ConstructorConfig) (i : Nat) : UInt256 :=
  (c.scalars.map ScalarReturn.word).getD i ⟨0⟩

def constructorScalarMemory (c : ConstructorConfig) : Nat → ByteArray
  | 0 => constructorRecordMemory c
  | n + 1 => writeWord (constructorScalarMemory c n)
      (constructorRecordBase c + 32 * n) (constructorRecordWord c n)

theorem constructorRecordBase_toNat {c : ConstructorConfig}
    (hsize : 22161 + 224 * c.assetConfigs.length < UInt256.size) :
    (UInt256.ofNat (constructorRecordBase c)).toNat = constructorRecordBase c :=
  UInt256.toNat_ofNat_of_lt (by unfold constructorRecordBase; omega)

theorem constructorRecordBase_add_toNat {c : ConstructorConfig} {off : Nat} (hoff : off ≤ 672)
    (hsize : 22161 + 224 * c.assetConfigs.length < UInt256.size) :
    (UInt256.ofNat (constructorRecordBase c) + UInt256.ofNat off).toNat =
      constructorRecordBase c + off := by
  apply uadd_ofNat_toNat
  · unfold constructorRecordBase; omega
  · have : 672 < UInt256.size := by decide
    omega
  · unfold constructorRecordBase; omega

theorem constructorRecordMemory_size (c : ConstructorConfig) :
    (constructorRecordMemory c).size = constructorRecordBase c := by
  rw [constructorRecordMemory, writeWord_sparse_size, constructorCopiedMemory_size]
  unfold constructorRecordBase
  omega

theorem constructorScalarMemory_size (c : ConstructorConfig) (n : Nat) :
    (constructorScalarMemory c n).size = constructorRecordBase c + 32 * n := by
  induction n with
  | zero => simpa only [constructorScalarMemory, Nat.mul_zero, Nat.add_zero]
      using constructorRecordMemory_size c
  | succ n ih =>
    rw [constructorScalarMemory, writeWord_sparse_size, ih]
    omega

theorem constructorScalarMemory_prefix (c : ConstructorConfig) (n : Nat) :
    MemoryPrefix (constructorCopiedMemory c) (constructorScalarMemory c n)
      (constructorRecordBase c) := by
  induction n with
  | zero => exact memoryPrefix_sparse_writeWord _ _ _ _ (Or.inr (by decide))
  | succ n ih =>
    exact ih.trans (memoryPrefix_sparse_writeWord _ _ _ _ (Or.inl (by omega)))

theorem constructorScalarMemory_loadArgument (c : ConstructorConfig) (n i : Nat)
    (hi : i < c.argumentWords.length)
    (hsize : 22161 + 224 * c.assetConfigs.length < UInt256.size) :
    memLoad (UInt256.ofNat (928 + 32 * i)) (constructorScalarMemory c n) = c.argumentWords[i] := by
  have hlen : 32 * c.argumentWords.length = 736 + 224 * c.assetConfigs.length := by
    have hh := congrArg ByteArray.size c.encodedArgs_wordBytes
    simpa only [List.size_toByteArray, ConstructorConfig.encodedArgs_length, wordBytes_size]
      using hh.symm
  have hoff : (UInt256.ofNat (928 + 32 * i)).toNat = 928 + 32 * i :=
    UInt256.toNat_ofNat_of_lt (by omega)
  apply mloadWordValue_of_readWithPadding
  · rw [hoff, constructorScalarMemory_size]; unfold constructorRecordBase; omega
  · rw [hoff, (constructorScalarMemory_prefix c n).read _ (by omega)
      (by unfold constructorRecordBase; omega) (by rw [constructorCopiedMemory_size]; omega)]
    exact constructorCopiedMemory_word _ _ hi

theorem constructorRecordWord_argument {c : ConstructorConfig} {i : Nat} (hi : i < 20) :
    c.argumentWords[i + 1]? = some (constructorRecordWord c i) := by
  have hs : (c.scalars.map ScalarReturn.word).length = 20 := rfl
  simp only [ConstructorConfig.argumentWords, List.cons_append, List.nil_append,
    List.getElem?_cons_succ, List.append_assoc]
  rw [List.getElem?_append_left (by rw [hs]; exact hi),
    List.getElem?_eq_getElem (by rw [hs]; exact hi), List.getElem_eq_getD ⟨0⟩]
  rfl

theorem constructorScalarMemory_loadScalar (c : ConstructorConfig) (n i : Nat) (hi : i < 20)
    (hsize : 22161 + 224 * c.assetConfigs.length < UInt256.size) :
    memLoad (UInt256.ofNat (960 + 32 * i)) (constructorScalarMemory c n) =
      constructorRecordWord c i := by
  have hs := constructorRecordWord_argument (c := c) hi
  obtain ⟨hindex, hword⟩ := List.getElem?_eq_some_iff.mp hs
  have hload := constructorScalarMemory_loadArgument c n (i + 1) hindex hsize
  rw [hword, show 928 + 32 * (i + 1) = 960 + 32 * i by omega] at hload
  exact hload

theorem constructorScalarMemory_arrayOffset (c : ConstructorConfig) (n : Nat)
    (hsize : 22161 + 224 * c.assetConfigs.length < UInt256.size) :
    memLoad (UInt256.ofNat 1600) (constructorScalarMemory c n) = ⟨672⟩ := by
  have hs : c.argumentWords[21]? = some (⟨672⟩ : UInt256) := rfl
  obtain ⟨hi, hw⟩ := List.getElem?_eq_some_iff.mp hs
  have h := constructorScalarMemory_loadArgument c n 21 hi hsize
  rw [hw] at h
  exact h

theorem constructorScalarMemory_arrayLength (c : ConstructorConfig) (n : Nat)
    (hsize : 22161 + 224 * c.assetConfigs.length < UInt256.size) :
    memLoad (UInt256.ofNat 1632) (constructorScalarMemory c n) =
      UInt256.ofNat c.assetConfigs.length := by
  have hs : c.argumentWords[22]? = some (UInt256.ofNat c.assetConfigs.length) := rfl
  obtain ⟨hi, hw⟩ := List.getElem?_eq_some_iff.mp hs
  have h := constructorScalarMemory_loadArgument c n 22 hi hsize
  rw [hw] at h
  exact h

theorem constructorScalarMemory_readFree (c : ConstructorConfig) (n : Nat) :
    (constructorScalarMemory c n).readWithPadding 64 32 =
      (UInt256.ofNat (constructorRecordBase c + 672)).toByteArray := by
  induction n with
  | zero => exact writeWord_sparse_read_back _ _ _
  | succ n ih =>
    rw [constructorScalarMemory, writeWord_sparse_read_preserved _ _ _ _ (Or.inl ⟨?_, ?_⟩), ih]
    · unfold constructorRecordBase; omega
    · rw [constructorScalarMemory_size]; unfold constructorRecordBase; omega

theorem constructorScalarMemory_free (c : ConstructorConfig) (n : Nat) :
    memLoad (UInt256.ofNat 64) (constructorScalarMemory c n) =
      UInt256.ofNat (constructorRecordBase c + 672) := by
  apply mloadWordValue_of_readWithPadding
  · rw [constructorScalarMemory_size]; change 64 < _; unfold constructorRecordBase; omega
  · exact constructorScalarMemory_readFree _ _

theorem constructorAddressScalar_canonical (a : AccountAddress) :
    (constructorAddressScalar a).word.toNat < 2^160 := word_val_addr_canonical a

theorem constructorUintScalar_canonical (width : BitWidth) (n : Fin (2^width.val)) :
    (constructorUintScalar width n).word.toNat < 2^width.val := by
  change (UInt256.ofNat n.val).toNat < _
  rw [UInt256.toNat_ofNat_of_lt (lt_of_lt_of_le n.isLt
    (Nat.pow_le_pow_right (by decide) width.property.2.1))]
  exact n.isLt

end Benchmarks.CompoundIII.Comet
