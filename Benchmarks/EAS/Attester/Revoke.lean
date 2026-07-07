import Benchmarks.EAS.Attester.Common
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.EAS.Attester.Immutables

namespace Benchmarks.EAS.Attester

/-! ## `revoke(bytes32,bytes32)` -/

def attesterRevokeSchemaBytes (I : ExecutionEnv) : List UInt8 :=
  (I.calldata.toList.drop 4).take 32

def attesterRevokeUidBytes (I : ExecutionEnv) : List UInt8 :=
  (I.calldata.toList.drop 36).take 32

def attesterRevokeSchemaWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

def attesterRevokeUidWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

def attesterRevokeStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "schema" (.fixedBytes bytes32Width (attesterRevokeSchemaBytes I))).insert
    "uid" (.fixedBytes bytes32Width (attesterRevokeUidBytes I))

def attesterRevokeDataValue (I : ExecutionEnv) : Value :=
  .tuple [.fixedBytes bytes32Width (attesterRevokeUidBytes I), .int 0]

def attesterRevokeRequestValue (I : ExecutionEnv) : Value :=
  .tuple [.fixedBytes bytes32Width (attesterRevokeSchemaBytes I), attesterRevokeDataValue I]

def attesterRevokeArgVals (I : ExecutionEnv) : List Value :=
  [attesterRevokeRequestValue I]

private theorem byteArray_toList_toByteArray (b : ByteArray) :
    b.toList.toByteArray = b := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [byteArray_toList_eq]
  simp

def attesterRevokeExternalCalldata (I : ExecutionEnv) : ByteArray :=
  revokeSelector ++
    UInt256.toByteArray (attesterRevokeSchemaWord I) ++
    UInt256.toByteArray (attesterRevokeUidWord I) ++
    UInt256.toByteArray ⟨0⟩

private abbrev attesterRevokeWriteWord (mem : ByteArray) (off : Nat)
    (w : UInt256) : ByteArray :=
  (UInt256.toByteArray w).write 0 mem off 32

def attesterRevokeEasWord (v : AttesterImmutables) : UInt256 :=
  EVM.Word.ofNat v.eas.toNat

def attesterRevokeTargetWord (v : AttesterImmutables) : UInt256 :=
  UInt256.land solcAddrMask (attesterRevokeEasWord v)

theorem attesterRevokeEasWord_canonical (v : AttesterImmutables) :
    (attesterRevokeEasWord v).toNat < EVM.addressModulus := by
  change (UInt256.ofNat v.eas.val).toNat < EVM.addressModulus
  rw [UInt256.toNat_ofNat_of_lt]
  · change v.eas.val < AccountAddress.size
    exact v.eas.isLt
  · exact lt_of_lt_of_le v.eas.isLt (by decide)

theorem attesterRevokeEasWord_clean (v : AttesterImmutables) :
    UInt256.land solcAddrMask (attesterRevokeEasWord v) =
      attesterRevokeEasWord v :=
  solcAddrMask_clean_left (attesterRevokeEasWord_canonical v)

theorem attesterRevokeTargetWord_eq_easWord (v : AttesterImmutables) :
    attesterRevokeTargetWord v = attesterRevokeEasWord v := by
  unfold attesterRevokeTargetWord
  rw [attesterRevokeEasWord_clean]

theorem attesterRevokeTarget_eq (v : AttesterImmutables) :
    EVM.address v.eas = AccountAddress.ofUInt256 (attesterRevokeTargetWord v) := by
  rw [attesterRevokeTargetWord_eq_easWord]
  have hleft : EVM.address (v.eas : Nat) = v.eas := by
    apply Fin.ext
    simp [EVM.address, EVM.uintN]
    exact Nat.mod_eq_of_lt v.eas.isLt
  have hright : AccountAddress.ofUInt256 (attesterRevokeEasWord v) = v.eas := by
    change AccountAddress.ofUInt256 (UInt256.ofNat v.eas.val) = v.eas
    exact accountAddress_roundtrip v.eas
  rw [hleft, hright]

noncomputable def attesterRevokeMem192 : ByteArray :=
  writeCascade solcFreePtrMem [(64, (⟨192⟩ : UInt256))]

noncomputable def attesterRevokeMemSchema (I : ExecutionEnv) : ByteArray :=
  writeCascade attesterRevokeMem192 [(128, attesterRevokeSchemaWord I)]

noncomputable def attesterRevokeMem256 (I : ExecutionEnv) : ByteArray :=
  writeCascade (attesterRevokeMemSchema I) [(64, (⟨256⟩ : UInt256))]

noncomputable def attesterRevokeMemUid (I : ExecutionEnv) : ByteArray :=
  writeCascade (attesterRevokeMem256 I) [(192, attesterRevokeUidWord I)]

noncomputable def attesterRevokeMemValue (I : ExecutionEnv) : ByteArray :=
  writeCascade (attesterRevokeMemUid I) [(224, (⟨0⟩ : UInt256))]

noncomputable def attesterRevokeMemDataOffset (I : ExecutionEnv) : ByteArray :=
  writeCascade (attesterRevokeMemValue I) [(160, (⟨192⟩ : UInt256))]

def attesterRevokeSelectorWord : UInt256 :=
  UInt256.shiftLeft (⟨0x46926267⟩ : UInt256) ⟨224⟩

noncomputable def attesterRevokeCallMemSelector (I : ExecutionEnv) : ByteArray :=
  writeCascade (attesterRevokeMemDataOffset I) [(256, attesterRevokeSelectorWord)]

noncomputable def attesterRevokeCallMemSchema (I : ExecutionEnv) : ByteArray :=
  writeCascade (attesterRevokeCallMemSelector I) [(260, attesterRevokeSchemaWord I)]

noncomputable def attesterRevokeCallMemUid (I : ExecutionEnv) : ByteArray :=
  writeCascade (attesterRevokeCallMemSchema I) [(292, attesterRevokeUidWord I)]

noncomputable def attesterRevokeCallMem (I : ExecutionEnv) : ByteArray :=
  writeCascade (attesterRevokeCallMemUid I) [(324, (⟨0⟩ : UInt256))]

theorem attesterRevokeMem192_size :
    attesterRevokeMem192.size = 96 := by
  unfold attesterRevokeMem192
  exact writeCascade_size_of_base solcFreePtrMem [(64, (⟨192⟩ : UInt256))]
    (base := 96) (out := 96) solcFreePtrMem_size
    (by norm_num [WriteGapsOk, USize.size]) (by norm_num [writeCascadeSize])

theorem attesterRevokeMemSchema_size (I : ExecutionEnv) :
    (attesterRevokeMemSchema I).size = 160 := by
  unfold attesterRevokeMemSchema
  exact writeCascade_size_of_base attesterRevokeMem192 [(128, attesterRevokeSchemaWord I)]
    (base := 96) (out := 160) attesterRevokeMem192_size
    (by
      simp [WriteGapsOk]
      exact lt_usize 32 (by norm_num))
    (by norm_num [writeCascadeSize])

theorem attesterRevokeMem256_size (I : ExecutionEnv) :
    (attesterRevokeMem256 I).size = 160 := by
  unfold attesterRevokeMem256
  exact writeCascade_size_of_base (attesterRevokeMemSchema I) [(64, (⟨256⟩ : UInt256))]
    (base := 160) (out := 160) (attesterRevokeMemSchema_size I)
    (by norm_num [WriteGapsOk, USize.size]) (by norm_num [writeCascadeSize])

theorem attesterRevokeMemUid_size (I : ExecutionEnv) :
    (attesterRevokeMemUid I).size = 224 := by
  unfold attesterRevokeMemUid
  exact writeCascade_size_of_base (attesterRevokeMem256 I) [(192, attesterRevokeUidWord I)]
    (base := 160) (out := 224) (attesterRevokeMem256_size I)
    (by
      simp [WriteGapsOk]
      exact lt_usize 32 (by norm_num))
    (by norm_num [writeCascadeSize])

theorem attesterRevokeMemValue_size (I : ExecutionEnv) :
    (attesterRevokeMemValue I).size = 256 := by
  unfold attesterRevokeMemValue
  exact writeCascade_size_of_base (attesterRevokeMemUid I) [(224, (⟨0⟩ : UInt256))]
    (base := 224) (out := 256) (attesterRevokeMemUid_size I)
    (by norm_num [WriteGapsOk, USize.size]) (by norm_num [writeCascadeSize])

theorem attesterRevokeMemDataOffset_size (I : ExecutionEnv) :
    (attesterRevokeMemDataOffset I).size = 256 := by
  unfold attesterRevokeMemDataOffset
  exact writeCascade_size_of_base (attesterRevokeMemValue I) [(160, (⟨192⟩ : UInt256))]
    (base := 256) (out := 256) (attesterRevokeMemValue_size I)
    (by norm_num [WriteGapsOk, USize.size]) (by norm_num [writeCascadeSize])

theorem attesterRevokeCallMemSelector_size (I : ExecutionEnv) :
    (attesterRevokeCallMemSelector I).size = 288 := by
  unfold attesterRevokeCallMemSelector
  exact writeCascade_size_of_base (attesterRevokeMemDataOffset I)
    [(256, attesterRevokeSelectorWord)] (base := 256) (out := 288)
    (attesterRevokeMemDataOffset_size I)
    (by norm_num [WriteGapsOk, USize.size]) (by norm_num [writeCascadeSize])

theorem attesterRevokeCallMemSchema_size (I : ExecutionEnv) :
    (attesterRevokeCallMemSchema I).size = 292 := by
  unfold attesterRevokeCallMemSchema
  exact writeCascade_size_of_base (attesterRevokeCallMemSelector I)
    [(260, attesterRevokeSchemaWord I)] (base := 288) (out := 292)
    (attesterRevokeCallMemSelector_size I)
    (by norm_num [WriteGapsOk, USize.size]) (by norm_num [writeCascadeSize])

theorem attesterRevokeCallMemUid_size (I : ExecutionEnv) :
    (attesterRevokeCallMemUid I).size = 324 := by
  unfold attesterRevokeCallMemUid
  exact writeCascade_size_of_base (attesterRevokeCallMemSchema I)
    [(292, attesterRevokeUidWord I)] (base := 292) (out := 324)
    (attesterRevokeCallMemSchema_size I)
    (by norm_num [WriteGapsOk, USize.size]) (by norm_num [writeCascadeSize])

theorem attesterRevokeCallMem_size (I : ExecutionEnv) :
    (attesterRevokeCallMem I).size = 356 := by
  unfold attesterRevokeCallMem
  exact writeCascade_size_of_base (attesterRevokeCallMemUid I) [(324, (⟨0⟩ : UInt256))]
    (base := 324) (out := 356) (attesterRevokeCallMemUid_size I)
    (by norm_num [WriteGapsOk, USize.size]) (by norm_num [writeCascadeSize])

theorem attesterRevokeMem192_read64 :
    attesterRevokeMem192.readWithPadding 64 32 = UInt256.toByteArray ⟨192⟩ := by
  unfold attesterRevokeMem192
  exact writeCascade_read_word_of_head_of_base solcFreePtrMem (base := 96)
    (word := (⟨192⟩ : UInt256)) (rest := [])
    (hbase := solcFreePtrMem_size) (hgap := by norm_num [USize.size])
    (hlater := by norm_num [WindowDisjointFromWrites, USize.size])

theorem attesterRevokeMem256_read64 (I : ExecutionEnv) :
    (attesterRevokeMem256 I).readWithPadding 64 32 = UInt256.toByteArray ⟨256⟩ := by
  unfold attesterRevokeMem256
  exact writeCascade_read_word_of_head_of_base (attesterRevokeMemSchema I) (base := 160)
    (word := (⟨256⟩ : UInt256)) (rest := [])
    (hbase := attesterRevokeMemSchema_size I) (hgap := by norm_num [USize.size])
    (hlater := by norm_num [WindowDisjointFromWrites, USize.size])

theorem attesterRevokeMemSchema_read128 (I : ExecutionEnv) :
    (attesterRevokeMemSchema I).readWithPadding 128 32 =
      UInt256.toByteArray (attesterRevokeSchemaWord I) := by
  unfold attesterRevokeMemSchema
  exact writeCascade_read_word_of_head_of_base attesterRevokeMem192 (base := 96)
    (word := attesterRevokeSchemaWord I) (rest := [])
    (hbase := attesterRevokeMem192_size) (hgap := by exact lt_usize 32 (by norm_num))
    (hlater := by norm_num [WindowDisjointFromWrites, USize.size])

theorem attesterRevokeMemSchema_read64 (I : ExecutionEnv) :
    (attesterRevokeMemSchema I).readWithPadding 64 32 = UInt256.toByteArray ⟨192⟩ := by
  unfold attesterRevokeMemSchema
  rw [writeCascade_read_preserved_len attesterRevokeMem192
    [(128, attesterRevokeSchemaWord I)] 64 32 (by
      rw [attesterRevokeMem192_size]
      simp [WindowDisjointFromWrites]
      exact lt_usize 32 (by norm_num)) (by norm_num) (by norm_num)]
  exact attesterRevokeMem192_read64

theorem attesterRevokeMemDataOffset_read160 (I : ExecutionEnv) :
    (attesterRevokeMemDataOffset I).readWithPadding 160 32 = UInt256.toByteArray ⟨192⟩ := by
  unfold attesterRevokeMemDataOffset
  exact writeCascade_read_word_of_head_of_base (attesterRevokeMemValue I) (base := 256)
    (word := (⟨192⟩ : UInt256)) (rest := [])
    (hbase := attesterRevokeMemValue_size I) (hgap := by norm_num [USize.size])
    (hlater := by norm_num [WindowDisjointFromWrites, USize.size])

theorem attesterRevokeMemUid_read192 (I : ExecutionEnv) :
    (attesterRevokeMemUid I).readWithPadding 192 32 =
      UInt256.toByteArray (attesterRevokeUidWord I) := by
  unfold attesterRevokeMemUid
  exact writeCascade_read_word_of_head_of_base (attesterRevokeMem256 I) (base := 160)
    (word := attesterRevokeUidWord I) (rest := [])
    (hbase := attesterRevokeMem256_size I) (hgap := by exact lt_usize 32 (by norm_num))
    (hlater := by norm_num [WindowDisjointFromWrites, USize.size])

theorem attesterRevokeMemValue_read224 (I : ExecutionEnv) :
    (attesterRevokeMemValue I).readWithPadding 224 32 = UInt256.toByteArray ⟨0⟩ := by
  unfold attesterRevokeMemValue
  exact writeCascade_read_word_of_head_of_base (attesterRevokeMemUid I) (base := 224)
    (word := (⟨0⟩ : UInt256)) (rest := [])
    (hbase := attesterRevokeMemUid_size I) (hgap := by norm_num [USize.size])
    (hlater := by norm_num [WindowDisjointFromWrites, USize.size])

theorem attesterRevokeCallMem_read64 (I : ExecutionEnv) :
    (attesterRevokeCallMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨256⟩ := by
  unfold attesterRevokeCallMem
  rw [writeCascade_read_preserved_len (attesterRevokeCallMemUid I)
    [(324, (⟨0⟩ : UInt256))] 64 32 (by
      rw [attesterRevokeCallMemUid_size I]
      norm_num [WindowDisjointFromWrites, USize.size]) (by norm_num) (by norm_num)]
  unfold attesterRevokeCallMemUid
  rw [writeCascade_read_preserved_len (attesterRevokeCallMemSchema I)
    [(292, attesterRevokeUidWord I)] 64 32 (by
      rw [attesterRevokeCallMemSchema_size I]
      norm_num [WindowDisjointFromWrites, USize.size]) (by norm_num) (by norm_num)]
  unfold attesterRevokeCallMemSchema
  rw [writeCascade_read_preserved_len (attesterRevokeCallMemSelector I)
    [(260, attesterRevokeSchemaWord I)] 64 32 (by
      rw [attesterRevokeCallMemSelector_size I]
      norm_num [WindowDisjointFromWrites, USize.size]) (by norm_num) (by norm_num)]
  unfold attesterRevokeCallMemSelector
  rw [writeCascade_read_preserved_len (attesterRevokeMemDataOffset I)
    [(256, attesterRevokeSelectorWord)] 64 32 (by
      rw [attesterRevokeMemDataOffset_size I]
      norm_num [WindowDisjointFromWrites, USize.size]) (by norm_num) (by norm_num)]
  unfold attesterRevokeMemDataOffset
  rw [writeCascade_read_preserved_len (attesterRevokeMemValue I)
    [(160, (⟨192⟩ : UInt256))] 64 32 (by
      rw [attesterRevokeMemValue_size I]
      norm_num [WindowDisjointFromWrites, USize.size]) (by norm_num) (by norm_num)]
  unfold attesterRevokeMemValue
  rw [writeCascade_read_preserved_len (attesterRevokeMemUid I)
    [(224, (⟨0⟩ : UInt256))] 64 32 (by
      rw [attesterRevokeMemUid_size I]
      norm_num [WindowDisjointFromWrites, USize.size]) (by norm_num) (by norm_num)]
  unfold attesterRevokeMemUid
  rw [writeCascade_read_preserved_len (attesterRevokeMem256 I)
    [(192, attesterRevokeUidWord I)] 64 32 (by
      rw [attesterRevokeMem256_size I]
      simp [WindowDisjointFromWrites]
      exact lt_usize 32 (by norm_num)) (by norm_num) (by norm_num)]
  exact attesterRevokeMem256_read64 I

theorem attesterRevokeMemDataOffset_read64 (I : ExecutionEnv) :
    (attesterRevokeMemDataOffset I).readWithPadding 64 32 = UInt256.toByteArray ⟨256⟩ := by
  unfold attesterRevokeMemDataOffset
  rw [writeCascade_read_preserved_len (attesterRevokeMemValue I)
    [(160, (⟨192⟩ : UInt256))] 64 32 (by
      rw [attesterRevokeMemValue_size I]
      norm_num [WindowDisjointFromWrites, USize.size]) (by norm_num) (by norm_num)]
  unfold attesterRevokeMemValue
  rw [writeCascade_read_preserved_len (attesterRevokeMemUid I)
    [(224, (⟨0⟩ : UInt256))] 64 32 (by
      rw [attesterRevokeMemUid_size I]
      norm_num [WindowDisjointFromWrites, USize.size]) (by norm_num) (by norm_num)]
  unfold attesterRevokeMemUid
  rw [writeCascade_read_preserved_len (attesterRevokeMem256 I)
    [(192, attesterRevokeUidWord I)] 64 32 (by
      rw [attesterRevokeMem256_size I]
      simp [WindowDisjointFromWrites]
      exact lt_usize 32 (by norm_num)) (by norm_num) (by norm_num)]
  exact attesterRevokeMem256_read64 I

theorem attesterRevokeMemDataOffset_read128 (I : ExecutionEnv) :
    (attesterRevokeMemDataOffset I).readWithPadding 128 32 =
      UInt256.toByteArray (attesterRevokeSchemaWord I) := by
  unfold attesterRevokeMemDataOffset
  rw [writeCascade_read_preserved_len (attesterRevokeMemValue I)
    [(160, (⟨192⟩ : UInt256))] 128 32 (by
      rw [attesterRevokeMemValue_size I]
      norm_num [WindowDisjointFromWrites, USize.size]) (by norm_num) (by norm_num)]
  unfold attesterRevokeMemValue
  rw [writeCascade_read_preserved_len (attesterRevokeMemUid I)
    [(224, (⟨0⟩ : UInt256))] 128 32 (by
      rw [attesterRevokeMemUid_size I]
      norm_num [WindowDisjointFromWrites, USize.size]) (by norm_num) (by norm_num)]
  unfold attesterRevokeMemUid
  rw [writeCascade_read_preserved_len (attesterRevokeMem256 I)
    [(192, attesterRevokeUidWord I)] 128 32 (by
      rw [attesterRevokeMem256_size I]
      simp [WindowDisjointFromWrites]
      exact lt_usize 32 (by norm_num)) (by norm_num) (by norm_num)]
  unfold attesterRevokeMem256
  rw [writeCascade_read_preserved_len (attesterRevokeMemSchema I)
    [(64, (⟨256⟩ : UInt256))] 128 32 (by
      rw [attesterRevokeMemSchema_size I]
      norm_num [WindowDisjointFromWrites, USize.size]) (by norm_num) (by norm_num)]
  exact attesterRevokeMemSchema_read128 I

theorem attesterRevokeMemDataOffset_read192 (I : ExecutionEnv) :
    (attesterRevokeMemDataOffset I).readWithPadding 192 32 =
      UInt256.toByteArray (attesterRevokeUidWord I) := by
  unfold attesterRevokeMemDataOffset
  rw [writeCascade_read_preserved_len (attesterRevokeMemValue I)
    [(160, (⟨192⟩ : UInt256))] 192 32 (by
      rw [attesterRevokeMemValue_size I]
      norm_num [WindowDisjointFromWrites, USize.size]) (by norm_num) (by norm_num)]
  unfold attesterRevokeMemValue
  rw [writeCascade_read_preserved_len (attesterRevokeMemUid I)
    [(224, (⟨0⟩ : UInt256))] 192 32 (by
      rw [attesterRevokeMemUid_size I]
      norm_num [WindowDisjointFromWrites, USize.size]) (by norm_num) (by norm_num)]
  exact attesterRevokeMemUid_read192 I

theorem attesterRevokeMemDataOffset_read224 (I : ExecutionEnv) :
    (attesterRevokeMemDataOffset I).readWithPadding 224 32 = UInt256.toByteArray ⟨0⟩ := by
  unfold attesterRevokeMemDataOffset
  rw [writeCascade_read_preserved_len (attesterRevokeMemValue I)
    [(160, (⟨192⟩ : UInt256))] 224 32 (by
      rw [attesterRevokeMemValue_size I]
      norm_num [WindowDisjointFromWrites, USize.size]) (by norm_num) (by norm_num)]
  exact attesterRevokeMemValue_read224 I

theorem attesterRevokeCallMemSelector_read128 (I : ExecutionEnv) :
    (attesterRevokeCallMemSelector I).readWithPadding 128 32 =
      UInt256.toByteArray (attesterRevokeSchemaWord I) := by
  unfold attesterRevokeCallMemSelector
  rw [writeCascade_read_preserved_len (attesterRevokeMemDataOffset I)
    [(256, attesterRevokeSelectorWord)] 128 32 (by
      rw [attesterRevokeMemDataOffset_size I]
      norm_num [WindowDisjointFromWrites, USize.size]) (by norm_num) (by norm_num)]
  exact attesterRevokeMemDataOffset_read128 I

theorem attesterRevokeCallMemSchema_read160 (I : ExecutionEnv) :
    (attesterRevokeCallMemSchema I).readWithPadding 160 32 = UInt256.toByteArray ⟨192⟩ := by
  unfold attesterRevokeCallMemSchema
  rw [writeCascade_read_preserved_len (attesterRevokeCallMemSelector I)
    [(260, attesterRevokeSchemaWord I)] 160 32 (by
      rw [attesterRevokeCallMemSelector_size I]
      norm_num [WindowDisjointFromWrites, USize.size]) (by norm_num) (by norm_num)]
  unfold attesterRevokeCallMemSelector
  rw [writeCascade_read_preserved_len (attesterRevokeMemDataOffset I)
    [(256, attesterRevokeSelectorWord)] 160 32 (by
      rw [attesterRevokeMemDataOffset_size I]
      norm_num [WindowDisjointFromWrites, USize.size]) (by norm_num) (by norm_num)]
  exact attesterRevokeMemDataOffset_read160 I

theorem attesterRevokeCallMemSchema_read192 (I : ExecutionEnv) :
    (attesterRevokeCallMemSchema I).readWithPadding 192 32 =
      UInt256.toByteArray (attesterRevokeUidWord I) := by
  unfold attesterRevokeCallMemSchema
  rw [writeCascade_read_preserved_len (attesterRevokeCallMemSelector I)
    [(260, attesterRevokeSchemaWord I)] 192 32 (by
      rw [attesterRevokeCallMemSelector_size I]
      norm_num [WindowDisjointFromWrites, USize.size]) (by norm_num) (by norm_num)]
  unfold attesterRevokeCallMemSelector
  rw [writeCascade_read_preserved_len (attesterRevokeMemDataOffset I)
    [(256, attesterRevokeSelectorWord)] 192 32 (by
      rw [attesterRevokeMemDataOffset_size I]
      norm_num [WindowDisjointFromWrites, USize.size]) (by norm_num) (by norm_num)]
  exact attesterRevokeMemDataOffset_read192 I

theorem attesterRevokeCallMemUid_read224 (I : ExecutionEnv) :
    (attesterRevokeCallMemUid I).readWithPadding 224 32 = UInt256.toByteArray ⟨0⟩ := by
  unfold attesterRevokeCallMemUid
  rw [writeCascade_read_preserved_len (attesterRevokeCallMemSchema I)
    [(292, attesterRevokeUidWord I)] 224 32 (by
      rw [attesterRevokeCallMemSchema_size I]
      norm_num [WindowDisjointFromWrites, USize.size]) (by norm_num) (by norm_num)]
  unfold attesterRevokeCallMemSchema
  rw [writeCascade_read_preserved_len (attesterRevokeCallMemSelector I)
    [(260, attesterRevokeSchemaWord I)] 224 32 (by
      rw [attesterRevokeCallMemSelector_size I]
      norm_num [WindowDisjointFromWrites, USize.size]) (by norm_num) (by norm_num)]
  unfold attesterRevokeCallMemSelector
  rw [writeCascade_read_preserved_len (attesterRevokeMemDataOffset I)
    [(256, attesterRevokeSelectorWord)] 224 32 (by
      rw [attesterRevokeMemDataOffset_size I]
      norm_num [WindowDisjointFromWrites, USize.size]) (by norm_num) (by norm_num)]
  exact attesterRevokeMemDataOffset_read224 I

theorem attesterRevokeSelectorWord_read0_4 :
    (UInt256.toByteArray attesterRevokeSelectorWord).extract 0 4 = revokeSelector := by
  native_decide

theorem attesterRevokeCallMem_read256_4 (I : ExecutionEnv) :
    (attesterRevokeCallMem I).readWithPadding 256 4 = revokeSelector := by
  unfold attesterRevokeCallMem
  rw [writeCascade_read_preserved_len (attesterRevokeCallMemUid I)
    [(324, (⟨0⟩ : UInt256))] 256 4 (by
      rw [attesterRevokeCallMemUid_size I]
      norm_num [WindowDisjointFromWrites, USize.size]) (by norm_num) (by norm_num)]
  unfold attesterRevokeCallMemUid
  rw [writeCascade_read_preserved_len (attesterRevokeCallMemSchema I)
    [(292, attesterRevokeUidWord I)] 256 4 (by
      rw [attesterRevokeCallMemSchema_size I]
      norm_num [WindowDisjointFromWrites, USize.size]) (by norm_num) (by norm_num)]
  unfold attesterRevokeCallMemSchema
  rw [writeCascade_read_preserved_len (attesterRevokeCallMemSelector I)
    [(260, attesterRevokeSchemaWord I)] 256 4 (by
      rw [attesterRevokeCallMemSelector_size I]
      norm_num [WindowDisjointFromWrites, USize.size]) (by norm_num) (by norm_num)]
  unfold attesterRevokeCallMemSelector
  rw [writeCascade_read_window_of_head (attesterRevokeMemDataOffset I)
    256 0 4 attesterRevokeSelectorWord []
    (by rw [attesterRevokeMemDataOffset_size I]; norm_num [USize.size])
    (by rw [attesterRevokeMemDataOffset_size I]; norm_num [WindowDisjointFromWrites, USize.size])
    (by norm_num) (by norm_num) (by norm_num)]
  exact attesterRevokeSelectorWord_read0_4

theorem attesterRevokeCallMem_read260 (I : ExecutionEnv) :
    (attesterRevokeCallMem I).readWithPadding 260 32 =
      UInt256.toByteArray (attesterRevokeSchemaWord I) := by
  unfold attesterRevokeCallMem
  rw [writeCascade_read_preserved_len (attesterRevokeCallMemUid I)
    [(324, (⟨0⟩ : UInt256))] 260 32 (by
      rw [attesterRevokeCallMemUid_size I]
      norm_num [WindowDisjointFromWrites, USize.size]) (by norm_num) (by norm_num)]
  unfold attesterRevokeCallMemUid
  rw [writeCascade_read_preserved_len (attesterRevokeCallMemSchema I)
    [(292, attesterRevokeUidWord I)] 260 32 (by
      rw [attesterRevokeCallMemSchema_size I]
      norm_num [WindowDisjointFromWrites, USize.size]) (by norm_num) (by norm_num)]
  unfold attesterRevokeCallMemSchema
  exact writeCascade_read_word_of_head_of_base (attesterRevokeCallMemSelector I)
    (base := 288) (word := attesterRevokeSchemaWord I)
    (rest := [])
    (hbase := attesterRevokeCallMemSelector_size I) (hgap := by norm_num [USize.size])
    (hlater := by norm_num [WindowDisjointFromWrites, USize.size])

theorem attesterRevokeCallMem_read292 (I : ExecutionEnv) :
    (attesterRevokeCallMem I).readWithPadding 292 32 =
      UInt256.toByteArray (attesterRevokeUidWord I) := by
  unfold attesterRevokeCallMem
  rw [writeCascade_read_preserved_len (attesterRevokeCallMemUid I)
    [(324, (⟨0⟩ : UInt256))] 292 32 (by
      rw [attesterRevokeCallMemUid_size I]
      norm_num [WindowDisjointFromWrites, USize.size]) (by norm_num) (by norm_num)]
  unfold attesterRevokeCallMemUid
  exact writeCascade_read_word_of_head_of_base (attesterRevokeCallMemSchema I)
    (base := 292) (word := attesterRevokeUidWord I)
    (rest := [])
    (hbase := attesterRevokeCallMemSchema_size I) (hgap := by norm_num [USize.size])
    (hlater := by norm_num [WindowDisjointFromWrites, USize.size])

theorem attesterRevokeCallMem_read324 (I : ExecutionEnv) :
    (attesterRevokeCallMem I).readWithPadding 324 32 = UInt256.toByteArray ⟨0⟩ := by
  unfold attesterRevokeCallMem
  exact writeCascade_read_word_of_head_of_base (attesterRevokeCallMemUid I)
    (base := 324) (word := (⟨0⟩ : UInt256)) (rest := [])
    (hbase := attesterRevokeCallMemUid_size I) (hgap := by norm_num [USize.size])
    (hlater := by norm_num [WindowDisjointFromWrites, USize.size])

theorem attesterRevokeCallMem_read256_100 (I : ExecutionEnv) :
    (attesterRevokeCallMem I).readWithPadding 256 100 =
      attesterRevokeExternalCalldata I := by
  rw [byteArray_readWithPadding_split (attesterRevokeCallMem I) 256 4 96
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [attesterRevokeCallMem_size I])]
  rw [attesterRevokeCallMem_read256_4]
  rw [byteArray_readWithPadding_split (attesterRevokeCallMem I) 260 32 64
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [attesterRevokeCallMem_size I])]
  rw [attesterRevokeCallMem_read260]
  rw [byteArray_readWithPadding_split (attesterRevokeCallMem I) 292 32 32
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [attesterRevokeCallMem_size I])]
  rw [attesterRevokeCallMem_read292, attesterRevokeCallMem_read324]
  unfold attesterRevokeExternalCalldata
  apply ByteArray.ext
  simp [ByteArray.data_append, Array.append_assoc]

theorem attesterDecodeABIValues_bytes32_bytes32_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32) :
    decodeABIValues? [bytes32, bytes32] bytes 0 0 64 64 =
      some ([.fixedBytes bytes32Width (bytes.take 32),
        .fixedBytes bytes32Width ((bytes.drop 32).take 32)], 64) := by
  have hge32 : 32 ≤ bytes.length - 32 := by
    rw [List.length_take, List.length_drop] at hlen32
    omega
  simp [decodeABIValues?, bytes32, bytes32Width, isDynamicABIType,
    staticABIEncodedSize?, decodeABIValue?, readBytes?, zeroPadding?, hlen0]
  rw [if_pos hge32]
  simp [List.take_take]

theorem attesterDecodeABIValues_bytes32_bytes32_none_short {bytes : List UInt8}
    (hshort : bytes.length < 64) :
    decodeABIValues? [bytes32, bytes32] bytes 0 0 64 64 = none := by
  simp only [decodeABIValues?, bytes32, bytes32Width, isDynamicABIType,
    Bool.false_eq_true, if_false, staticABIEncodedSize?, bind, Option.bind, Nat.zero_add]
  by_cases h32 : bytes.length < 32
  · have htake0n : ¬ (bytes.take 32).length = 32 := by
      rw [List.length_take]
      omega
    have hnot : ¬ 32 ≤ bytes.length := by omega
    simp [decodeABIValue?, readBytes?, zeroPadding?, hnot, htake0n]
  · have htake0 : (bytes.take 32).length = 32 := by
      rw [List.length_take]
      omega
    have htake32n : ¬ ((bytes.drop 32).take 32).length = 32 := by
      rw [List.length_take, List.length_drop]
      omega
    have hnot : ¬ 32 ≤ bytes.length - 32 := by
      rw [List.length_take, List.length_drop] at htake32n
      omega
    simp [decodeABIValue?, readBytes?, zeroPadding?, htake0, hnot, htake32n]

theorem attesterDecode_revoke_ok (v : AttesterImmutables) {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4) :
    decodeCalldataWithMode (config v).abiDecodeMode
        ((revokeTransition v).params.map Param.name)
        (transitionSignature (revokeTransition v)).paramTypes I.calldata =
      some (attesterRevokeStore I) := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake36 : ((I.calldata.toList.drop 36).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  show decodeCalldata ["schema", "uid"] [bytes32, bytes32] I.calldata =
    some (attesterRevokeStore I)
  unfold decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
  rw [if_neg (by simp [bytes32, isDynamicABIType])]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [if_neg (by simp [solcTotalSizeDynamicGuard])]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [bytes32, bytes32] = some 64 by native_decide]
  simp only [bind, Option.bind]
  rw [attesterDecodeABIValues_bytes32_bytes32_ok (bytes := I.calldata.toList.drop 4)
    (by simpa using htake4)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36)]
  rw [if_neg (by rw [List.length_drop, htlen]; omega :
    ¬ (I.calldata.toList.drop 4).length < 64)]
  simp [decodeCalldata.insertValues, attesterRevokeStore, attesterRevokeSchemaBytes,
    attesterRevokeUidBytes]

theorem attesterDecode_revoke_none_short (v : AttesterImmutables) {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode (config v).abiDecodeMode
        ((revokeTransition v).params.map Param.name)
        (transitionSignature (revokeTransition v)).paramTypes I.calldata = none := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  show decodeCalldata ["schema", "uid"] [bytes32, bytes32] I.calldata = none
  unfold decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
  rw [if_neg (by simp [bytes32, isDynamicABIType])]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [if_neg (by simp [solcTotalSizeDynamicGuard])]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [bytes32, bytes32] = some 64 by native_decide]
  simp only [bind, Option.bind]
  rw [attesterDecodeABIValues_bytes32_bytes32_none_short
    (bytes := I.calldata.toList.drop 4) (by rw [List.length_drop, htlen]; omega)]
  rw [if_pos (by rw [List.length_drop, htlen]; omega :
    (I.calldata.toList.drop 4).length < 64)]

theorem attesterDecode_revoke_none_huge (v : AttesterImmutables) {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldataWithMode (config v).abiDecodeMode
        ((revokeTransition v).params.map Param.name)
        (transitionSignature (revokeTransition v)).paramTypes I.calldata = none := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  show decodeCalldata ["schema", "uid"] [bytes32, bytes32] I.calldata = none
  unfold decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
  rw [if_neg (by simp [bytes32, isDynamicABIType])]
  rw [if_pos]
  · exact ⟨rfl, by rw [List.length_drop, htlen]; omega⟩

theorem attesterRevokeSchemaBytes_eq_toBytesBE {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) :
    attesterRevokeSchemaBytes I = EVM.Word.toBytesBE (attesterRevokeSchemaWord I) := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hlen : (attesterRevokeSchemaBytes I).length = 32 := by
    simp [attesterRevokeSchemaBytes, List.length_take, List.length_drop, htlen]
    omega
  have hword : ABI.bytesToWord (attesterRevokeSchemaBytes I) =
      attesterRevokeSchemaWord I := by
    simpa [attesterRevokeSchemaBytes, attesterRevokeSchemaWord, calldataWord,
      show (⟨4⟩ : UInt256).toNat = 4 from by decide]
      using decode_word_at_eq I.calldata 4 (by omega) (by norm_num)
  rw [← hword]
  exact (toBytesBE_bytesToWord_of_length hlen).symm

theorem attesterRevokeUidBytes_eq_toBytesBE {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) :
    attesterRevokeUidBytes I = EVM.Word.toBytesBE (attesterRevokeUidWord I) := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hlen : (attesterRevokeUidBytes I).length = 32 := by
    simp [attesterRevokeUidBytes, List.length_take, List.length_drop, htlen]
    omega
  have hword : ABI.bytesToWord (attesterRevokeUidBytes I) =
      attesterRevokeUidWord I := by
    simpa [attesterRevokeUidBytes, attesterRevokeUidWord, calldataWord,
      show (⟨36⟩ : UInt256).toNat = 36 from by decide]
      using decode_word_at_eq I.calldata 36 (by omega) (by norm_num)
  rw [← hword]
  exact (toBytesBE_bytesToWord_of_length hlen).symm

theorem attesterEncodeRevoke_eq (v : AttesterImmutables) {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) :
    (config v).externalABI.encode? "revoke" (attesterRevokeArgVals I) =
      some (attesterRevokeExternalCalldata I) := by
  have hschema := attesterRevokeSchemaBytes_eq_toBytesBE (I := I) hsz68
  have huid := attesterRevokeUidBytes_eq_toBytesBE (I := I) hsz68
  have hschemaLen : (EVM.Word.toBytesBE (attesterRevokeSchemaWord I)).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size (attesterRevokeSchemaWord I)
  have huidLen : (EVM.Word.toBytesBE (attesterRevokeUidWord I)).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size (attesterRevokeUidWord I)
  have hpow256 : 0 < EVM.twoPow 256 := by norm_num [EVM.twoPow]
  have hzeroLen : (EVM.Word.ofNat 0).toBytesBE.length = 32 := by
    simpa [list_toByteArray_size] using word_toBytesBE_toByteArray_size (EVM.Word.ofNat 0)
  have hwordNat0 : EVM.Word.ofNat 0 = (⟨0⟩ : UInt256) := by native_decide
  have hword0 : EVM.word 0 = (⟨0⟩ : UInt256) := rfl
  simp [config, attesterExternalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?,
    ABI.encodeABIArrayElems?, ABI.encodeABIStaticArrayElems?,
    ABI.encodeABIDynamicArrayElemsFrom?, ABI.abiTupleHeadSize?,
    ABI.staticABIEncodedSize?, ABI.staticABIEncodedSizeList?, ABI.isDynamicABIType,
    ABI.isDynamicABITypeList, attesterRevokeArgVals, attesterRevokeRequestValue,
    attesterRevokeDataValue, attesterRevokeExternalCalldata, revocationRequestTy,
    revocationRequestDataTy, bytes32, bytes32Width, uint256, uint256Int, revokeSelector,
    selectorBytes, hschema, huid, hschemaLen, huidLen, hpow256, hzeroLen, ABI.natBytes,
    ABI.padRightToWord, ABI.paddedSize, ABI.zeroBytes,
    word_toBytesBE_toByteArray_eq_toByteArray, list_toByteArray_append]
  apply ByteArray.ext
  simp [ByteArray.data_append, ByteArray.append_assoc, byteArray_toList_toByteArray,
    hwordNat0, hword0]

theorem attesterEvalRevokeArgs (v : AttesterImmutables) (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExprs? (config v)
        { contract := contract v, locals := attesterRevokeStore I } evm
        [revocationRequest (.var "schema") (.var "uid")] =
      .ok (attesterRevokeArgVals I) := by
  simp [attesterRevokeStore, attesterRevokeArgVals, attesterRevokeRequestValue,
    attesterRevokeDataValue, revocationRequest, revocationData, evalExprs?,
    evalExprList?, evalExpr?, EvalResult.bind, bind, pure, EvalResult.ofOption,
    Std.HashMap.getElem_insert]

theorem attesterDecode_revoke_return_ok (v : AttesterImmutables) (out : ByteArray) :
    (config v).externalABI.decode? "revoke" out = some [] := by
  simp [config, attesterExternalABI, decodeVoid?]

theorem attesterRevokeBodySuccess (v : AttesterImmutables)
    (evm evm' : EVM.State) (locals : Store) {argVals : List Value}
    {out : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hguard : evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.binary .gt (.extCodeSize (easExpr v)) (.intLit 0)) = .ok (.bool true))
    (hargs : evalExprs? (config v) { contract := contract v, locals := locals } evm
      [revocationRequest (.var "schema") (.var "uid")] = .ok argVals)
    (hcall : typedCallViaEVM (config v) evm (EVM.address v.eas) "revoke" 0 argVals
      (true, evm', out))
    (hdec : (config v).externalABI.decode? "revoke" out = some []) :
    ExecTransitionBody (config v) (contract v) evm locals (revokeTransition v).body
      (.returned
        { contract := contract v, locals := locals.insert "_revoke" (collapseReturns []) }
        evm' none) := by
  exact ExecFuncBody.execBlockOK <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      checkedExternalCallSuccess
        (receiver := easExpr v) (retVar := "_revoke") (name := "revoke")
        (sendVal := 0) (args := [revocationRequest (.var "schema") (.var "uid")])
        hguard
        (attesterEvalEasExpr v { contract := contract v, locals := locals } evm)
        hargs hcall hdec

theorem attesterRevokeBodyCallFailure (v : AttesterImmutables)
    (evm evm' : EVM.State) (locals : Store) {argVals : List Value}
    {out : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hguard : evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.binary .gt (.extCodeSize (easExpr v)) (.intLit 0)) = .ok (.bool true))
    (hargs : evalExprs? (config v) { contract := contract v, locals := locals } evm
      [revocationRequest (.var "schema") (.var "uid")] = .ok argVals)
    (hcall : typedCallViaEVM (config v) evm (EVM.address v.eas) "revoke" 0 argVals
      (false, evm', out)) :
    ExecTransitionBody (config v) (contract v) evm locals (revokeTransition v).body .reverted := by
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      checkedExternalCallFailure
        (receiver := easExpr v) (retVar := "_revoke") (name := "revoke")
        (sendVal := 0) (args := [revocationRequest (.var "schema") (.var "uid")])
        hguard
        (attesterEvalEasExpr v { contract := contract v, locals := locals } evm)
        hargs hcall

theorem attesterRevokeBodyNoCode (v : AttesterImmutables)
    (evm : EVM.State) (locals : Store)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hguard : evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.binary .gt (.extCodeSize (easExpr v)) (.intLit 0)) = .ok (.bool false)) :
    ExecTransitionBody (config v) (contract v) evm locals (revokeTransition v).body .reverted := by
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      checkedExternalCallNoCode
        (receiver := easExpr v) (retVar := "_revoke") (name := "revoke")
        (sendVal := 0) (args := [revocationRequest (.var "schema") (.var "uid")])
        hguard

theorem attesterX_revokeWrapper {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hcode : I.code = patchedRuntime v) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hmultiRevoke : (attesterMultiRevokeSelBytes == I.calldata.extract 0 4) = false)
    (hmultiAttest : (attesterMultiAttestSelBytes == I.calldata.extract 0 4) = false)
    (hattest : (attesterAttestSelBytes == I.calldata.extract 0 4) = false)
    (hrevoke : (attesterRevokeSelBytes == I.calldata.extract 0 4) = true) :
    ∃ k C, RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I) (⟨173⟩ : UInt256)
        [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode
    (by attester_decode) (by attester_decode) (by attester_decode)
    (by attester_decode) (by attester_decode) (by attester_decode)
  obtain ⟨_, _, h17⟩ := solcGuardCallvalueZero
    (ctgt := (⟨15⟩ : UInt256)) (opC := .PUSH2) (wC := 2)
    h0 hwv (by decide) (by attester_decode)
    (by attester_decode) (by attester_decode)
    (by attester_decode) (attesterGuardJumpdest v)
  obtain ⟨k25, C25, h25raw⟩ := solcCalldataOk
    (bodyPc := (⟨17⟩ : UInt256)) (selLoadTgt := attesterDispatchRevertPc)
    (opR := .PUSH2) (wR := 2)
    h17 hsz hsize (by attester_decode) (by attester_decode) (by attester_decode)
    (by decide) (by attester_decode) (by attester_decode)
  have h25 :
      RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I) (⟨25⟩ : UInt256)
        [] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k25 C25 := by
    simpa using h25raw
  obtain ⟨k30, C30, h30raw⟩ := solcSelectorLoad h25
    (by attester_decode) (by attester_decode) (by attester_decode) (by attester_decode) (by simp)
  have h30 :
      RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I) attesterFirstArmPc
        [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k30 C30 := by
    simpa [attesterFirstArmPc, solcSelectorWord] using h30raw
  have heqMultiRevoke := attesterMultiRevokeEqZero I hsz hmultiRevoke
  have heqMultiAttest := attesterMultiAttestEqZero I hsz hmultiAttest
  have heqAttest := attesterAttestEqZero I hsz hattest
  have heqRevoke := attesterRevokeEqNonzero I hsz hrevoke
  exact ⟨_, _, h30
    |>.selectorArmNotTaken (selNat := (⟨0x13fde550⟩ : UInt256))
      (tgt := (⟨78⟩ : UInt256)) (width := 2) (op := .PUSH2)
      (by attester_decode) (by attester_decode) (by attester_decode)
      (by decide) (by attester_decode) (by attester_decode) heqMultiRevoke (by simp)
    |>.selectorArmNotTaken (selNat := (⟨0x54e1db35⟩ : UInt256))
      (tgt := (⟨99⟩ : UInt256)) (width := 2) (op := .PUSH2)
      (by attester_decode) (by attester_decode) (by attester_decode)
      (by decide) (by attester_decode) (by attester_decode) heqMultiAttest (by simp)
    |>.selectorArmNotTaken (selNat := (⟨0x72b9966d⟩ : UInt256))
      (tgt := (⟨140⟩ : UInt256)) (width := 2) (op := .PUSH2)
      (by attester_decode) (by attester_decode) (by attester_decode)
      (by decide) (by attester_decode) (by attester_decode) heqAttest (by simp)
    |>.selectorArmTaken (selNat := (⟨0xc2664610⟩ : UInt256))
      (tgt := (⟨173⟩ : UInt256)) (width := 2) (op := .PUSH2)
      (by attester_decode) (by attester_decode) (by attester_decode)
      (by decide) (by attester_decode) (by attester_decode) heqRevoke
      (attesterRevokeWrapperJumpdest v) (by simp)⟩

theorem attesterX_revokeToDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hreach : ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨173⟩ : UInt256)
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2281⟩ : UInt256)
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨187⟩, ⟨97⟩, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd173⟩ := hreach
  exact ⟨_, _, evm_run rd173 with [
    raw jumpdest (by attester_decode_at v, ⟨173⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push2 ⟨97⟩ (by attester_decode_at v, ⟨174⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw push2 ⟨187⟩ (by attester_decode_at v, ⟨177⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw calldatasize (by attester_decode_at v, ⟨180⟩, 0x36, .CALLDATASIZE) (by evm_ov),
    raw push1 ⟨4⟩ (by attester_decode_at v, ⟨181⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw push2 ⟨2281⟩ (by attester_decode_at v, ⟨183⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jump (by attester_decode_at v, ⟨186⟩, 0x56, .JUMP)
      (attesterAttestDecoderJumpdest v) (by evm_ov)]⟩

theorem attesterX_revokeDecodeRevert {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ =
      ⟨1⟩)
    (hreach : ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨173⟩ : UInt256)
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev (patchedRuntime v) g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2281⟩ := attesterX_revokeToDecoder (v := v) hreach
  exact evm_run rd2281 with [
    raw jumpdest (by attester_decode_at v, ⟨2281⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨2282⟩, 0x5f, .PUSH0) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨2283⟩, 0x80, .DUP1) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨2284⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup4 (by attester_decode_at v, ⟨2286⟩, 0x83, .DUP4) (by evm_ov),
    raw dup6 (by attester_decode_at v, ⟨2287⟩, 0x85, .DUP6) (by evm_ov),
    raw sub (by attester_decode_at v, ⟨2288⟩, 0x03, .SUB) (by evm_ov),
    raw slt (by attester_decode_at v, ⟨2289⟩, 0x12, .SLT) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨2290⟩, 0x15, .ISZERO) (by evm_ov),
    raw push2 ⟨2298⟩ (by attester_decode_at v, ⟨2291⟩, 0x61, (.Push .PUSH2))
      (by evm_ov),
    raw jumpiNT (by attester_decode_at v, ⟨2294⟩, 0x57, .JUMPI) (by rw [hslt]; decide)
      (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨2295⟩, 0x5f, .PUSH0) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨2296⟩, 0x80, .DUP1) (by evm_ov),
    raw rev 0 (by attester_decode_at v, ⟨2297⟩, 0xfd, .REVERT)
      (fun s _ hstks => memExpRevert0 s hstks) (by evm_ov)]

theorem attesterX_revokeDecodeShort {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hcode : I.code = patchedRuntime v) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hmultiRevoke : (attesterMultiRevokeSelBytes == I.calldata.extract 0 4) = false)
    (hmultiAttest : (attesterMultiAttestSelBytes == I.calldata.extract 0 4) = false)
    (hattest : (attesterAttestSelBytes == I.calldata.extract 0 4) = false)
    (hrevoke : (attesterRevokeSelBytes == I.calldata.extract 0 4) = true) :
    RDrev (patchedRuntime v) g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ =
      ⟨1⟩ :=
    solcDecodeLenCheckShort_4_64 hsz4 hshort hsize
  exact attesterX_revokeDecodeRevert (v := v) hslt
    (attesterX_revokeWrapper (g := g) v hcode hwv hsz4 hsize hmultiRevoke
      hmultiAttest hattest hrevoke)

theorem attesterX_revokeDecodeHuge {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hcode : I.code = patchedRuntime v) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hmultiRevoke : (attesterMultiRevokeSelBytes == I.calldata.extract 0 4) = false)
    (hmultiAttest : (attesterMultiAttestSelBytes == I.calldata.extract 0 4) = false)
    (hattest : (attesterAttestSelBytes == I.calldata.extract 0 4) = false)
    (hrevoke : (attesterRevokeSelBytes == I.calldata.extract 0 4) = true) :
    RDrev (patchedRuntime v) g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ =
      ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_64 hbig hsize
  exact attesterX_revokeDecodeRevert (v := v) hslt
    (attesterX_revokeWrapper (g := g) v hcode hwv hsz4 hsize hmultiRevoke
      hmultiAttest hattest hrevoke)

theorem attesterX_revokeDecoded {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨173⟩ : UInt256)
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨1863⟩ : UInt256)
      [attesterRevokeUidWord I, attesterRevokeSchemaWord I, ⟨97⟩, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ =
      ⟨0⟩ :=
    solcDecodeLenCheckOk_4_64 hsz68 hsmall hsize
  obtain ⟨_, _, rd2281⟩ := attesterX_revokeToDecoder (v := v) hreach
  have rd187 := evm_run rd2281 with [
    raw jumpdest (by attester_decode_at v, ⟨2281⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨2282⟩, 0x5f, .PUSH0) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨2283⟩, 0x80, .DUP1) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨2284⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup4 (by attester_decode_at v, ⟨2286⟩, 0x83, .DUP4) (by evm_ov),
    raw dup6 (by attester_decode_at v, ⟨2287⟩, 0x85, .DUP6) (by evm_ov),
    raw sub (by attester_decode_at v, ⟨2288⟩, 0x03, .SUB) (by evm_ov),
    raw slt (by attester_decode_at v, ⟨2289⟩, 0x12, .SLT) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨2290⟩, 0x15, .ISZERO) (by evm_ov),
    raw push2 ⟨2298⟩ (by attester_decode_at v, ⟨2291⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jumpiT (by attester_decode_at v, ⟨2294⟩, 0x57, .JUMPI)
      (by rw [hslt]; decide) (attesterAttestDecodeOkJumpdest v) (by evm_ov),
    raw jumpdest (by attester_decode_at v, ⟨2298⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨2299⟩, 0x50, .POP) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨2300⟩, 0x50, .POP) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨2301⟩, 0x80, .DUP1) (by evm_ov),
    raw calldataload (by attester_decode_at v, ⟨2302⟩, 0x35, .CALLDATALOAD) (by evm_ov),
    raw swap3 (by attester_decode_at v, ⟨2303⟩, 0x92, .SWAP3) (by evm_ov),
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨2304⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨2306⟩, 0x90, .SWAP1) (by evm_ov),
    raw swap2 (by attester_decode_at v, ⟨2307⟩, 0x91, .SWAP2) (by evm_ov),
    raw add (by attester_decode_at v, ⟨2308⟩, 0x01, .ADD) (by evm_ov),
    raw calldataload (by attester_decode_at v, ⟨2309⟩, 0x35, .CALLDATALOAD) (by evm_ov),
    raw swap2 (by attester_decode_at v, ⟨2310⟩, 0x91, .SWAP2) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨2311⟩, 0x50, .POP) (by evm_ov),
    raw jump (by attester_decode_at v, ⟨2312⟩, 0x56, .JUMP)
      (attesterRevokeDecodedJumpdest v) (by evm_ov)]
  have rd1863 := evm_run rd187 with [
    raw jumpdest (by attester_decode_at v, ⟨187⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push2 ⟨1863⟩ (by attester_decode_at v, ⟨188⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jump (by attester_decode_at v, ⟨191⟩, 0x56, .JUMP)
      (attesterRevokeBodyJumpdest v) (by evm_ov)]
  exact ⟨_, _, by
    simpa [attesterRevokeUidWord, attesterRevokeSchemaWord, calldataWord,
      show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      show (⟨36⟩ : UInt256).toNat = 36 from by decide] using rd1863⟩

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem attesterX_revokeToExtcodesize {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨173⟩ : UInt256)
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2001⟩ : UInt256)
      [attesterRevokeTargetWord v, attesterRevokeTargetWord v, ⟨0⟩, ⟨256⟩, ⟨100⟩,
        ⟨256⟩, ⟨0⟩, ⟨356⟩, ⟨0x46926267⟩, attesterRevokeTargetWord v,
        attesterRevokeUidWord I, attesterRevokeSchemaWord I, ⟨97⟩, solcSelectorWord I]
      (attesterRevokeCallMem I) (UInt256.ofNat 12) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1863⟩ := attesterX_revokeDecoded (v := v) hsz68 hsize hsmall hreach
  have rd1938 := evm_run rd1863 with [
    raw jumpdest (by attester_decode_at v, ⟨1863⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨1864⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨1866⟩, 0x80, .DUP1) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3)
      (by attester_decode_at v, ⟨1867⟩, 0x51, .MLOAD)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨1868⟩, 0x80, .DUP1) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨1869⟩, 0x82, .DUP3) (by evm_ov),
    raw add (by attester_decode_at v, ⟨1870⟩, 0x01, .ADD) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨1871⟩, 0x82, .DUP3) (by evm_ov),
    raw mstore 0 attesterRevokeMem192 (UInt256.ofNat 3)
      (by attester_decode_at v, ⟨1872⟩, 0x52, .MSTORE) mem_cost
      (by rfl) (by decide) (by evm_ov),
    raw dup4 (by attester_decode_at v, ⟨1873⟩, 0x83, .DUP4) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨1874⟩, 0x81, .DUP2) (by evm_ov),
    raw mstore 6 (attesterRevokeMemSchema I) (UInt256.ofNat 5)
      (by attester_decode_at v, ⟨1875⟩, 0x52, .MSTORE) mem_cost
      (by rfl) (by decide) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨1876⟩, 0x81, .DUP2) (by evm_ov),
    raw mload 0 ⟨192⟩ (UInt256.ofNat 5)
      (by attester_decode_at v, ⟨1877⟩, 0x51, .MLOAD)
      mem_cost
      (mloadWordValue_of_readWithPadding
        (by rw [attesterRevokeMemSchema_size I]; decide) (by decide)
        (attesterRevokeMemSchema_read64 I))
      (by decide) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨1878⟩, 0x80, .DUP1) (by evm_ov),
    raw dup4 (by attester_decode_at v, ⟨1879⟩, 0x83, .DUP4) (by evm_ov),
    raw add (by attester_decode_at v, ⟨1880⟩, 0x01, .ADD) (by evm_ov),
    raw dup4 (by attester_decode_at v, ⟨1881⟩, 0x83, .DUP4) (by evm_ov),
    raw mstore 0 (attesterRevokeMem256 I) (UInt256.ofNat 5)
      (by attester_decode_at v, ⟨1882⟩, 0x52, .MSTORE) mem_cost
      (by rfl) (by decide) (by evm_ov),
    raw dup4 (by attester_decode_at v, ⟨1883⟩, 0x83, .DUP4) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨1884⟩, 0x81, .DUP2) (by evm_ov),
    raw mstore 6 (attesterRevokeMemUid I) (UInt256.ofNat 7)
      (by attester_decode_at v, ⟨1885⟩, 0x52, .MSTORE) mem_cost
      (by rfl) (by decide) (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨1886⟩, 0x5f, .PUSH0) (by evm_ov),
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨1887⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨1889⟩, 0x80, .DUP1) (by evm_ov),
    raw dup4 (by attester_decode_at v, ⟨1890⟩, 0x83, .DUP4) (by evm_ov),
    raw add (by attester_decode_at v, ⟨1891⟩, 0x01, .ADD) (by evm_ov),
    raw swap2 (by attester_decode_at v, ⟨1892⟩, 0x91, .SWAP2) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨1893⟩, 0x90, .SWAP1) (by evm_ov),
    raw swap2 (by attester_decode_at v, ⟨1894⟩, 0x91, .SWAP2) (by evm_ov),
    raw mstore 3 (attesterRevokeMemValue I) (UInt256.ofNat 8)
      (by attester_decode_at v, ⟨1895⟩, 0x52, .MSTORE) mem_cost
      (by rfl) (by decide) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨1896⟩, 0x80, .DUP1) (by evm_ov),
    raw dup4 (by attester_decode_at v, ⟨1897⟩, 0x83, .DUP4) (by evm_ov),
    raw add (by attester_decode_at v, ⟨1898⟩, 0x01, .ADD) (by evm_ov),
    raw swap2 (by attester_decode_at v, ⟨1899⟩, 0x91, .SWAP2) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨1900⟩, 0x82, .DUP3) (by evm_ov),
    raw mstore 0 (attesterRevokeMemDataOffset I) (UInt256.ofNat 8)
      (by attester_decode_at v, ⟨1901⟩, 0x52, .MSTORE) mem_cost
      (by rfl) (by decide) (by evm_ov),
    raw swap3 (by attester_decode_at v, ⟨1902⟩, 0x92, .SWAP3) (by evm_ov),
    raw mload 0 ⟨256⟩ (UInt256.ofNat 8)
      (by attester_decode_at v, ⟨1903⟩, 0x51, .MLOAD)
      mem_cost
      (mloadWordValue_of_readWithPadding
        (by rw [attesterRevokeMemDataOffset_size I]; decide) (by decide)
        (attesterRevokeMemDataOffset_read64 I))
      (by decide) (by evm_ov),
    raw push4 ⟨0x46926267⟩ (by attester_decode_at v, ⟨1904⟩, 0x63, (.Push .PUSH4))
      (by evm_ov),
    raw push1 ⟨224⟩ (by attester_decode_at v, ⟨1909⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw shl (by attester_decode_at v, ⟨1911⟩, 0x1b, .SHL) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨1912⟩, 0x81, .DUP2) (by evm_ov),
    raw mstore 3 (attesterRevokeCallMemSelector I) (UInt256.ofNat 9)
      (by attester_decode_at v, ⟨1913⟩, 0x52, .MSTORE) mem_cost
      (by rfl) (by decide) (by evm_ov),
    raw swap2 (by attester_decode_at v, ⟨1914⟩, 0x91, .SWAP2) (by evm_ov),
    raw mload 0 (attesterRevokeSchemaWord I) (UInt256.ofNat 9)
      (by attester_decode_at v, ⟨1915⟩, 0x51, .MLOAD)
      mem_cost
      (mloadWordValue_of_readWithPadding
        (by rw [attesterRevokeCallMemSelector_size I]; decide) (by decide)
        (attesterRevokeCallMemSelector_read128 I))
      (by decide) (by evm_ov),
    raw push1 ⟨4⟩ (by attester_decode_at v, ⟨1916⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup4 (by attester_decode_at v, ⟨1918⟩, 0x83, .DUP4) (by evm_ov),
    raw add (by attester_decode_at v, ⟨1919⟩, 0x01, .ADD) (by evm_ov),
    raw mstore 3 (attesterRevokeCallMemSchema I) (UInt256.ofNat 10)
      (by attester_decode_at v, ⟨1920⟩, 0x52, .MSTORE) mem_cost
      (by rfl) (by decide) (by evm_ov),
    raw mload 0 ⟨192⟩ (UInt256.ofNat 10)
      (by attester_decode_at v, ⟨1921⟩, 0x51, .MLOAD)
      mem_cost
      (mloadWordValue_of_readWithPadding
        (by rw [attesterRevokeCallMemSchema_size I]; decide) (by decide)
        (attesterRevokeCallMemSchema_read160 I))
      (by decide) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨1922⟩, 0x80, .DUP1) (by evm_ov),
    raw mload 0 (attesterRevokeUidWord I) (UInt256.ofNat 10)
      (by attester_decode_at v, ⟨1923⟩, 0x51, .MLOAD)
      mem_cost
      (mloadWordValue_of_readWithPadding
        (by rw [attesterRevokeCallMemSchema_size I]; decide) (by decide)
        (attesterRevokeCallMemSchema_read192 I))
      (by decide) (by evm_ov),
    raw push1 ⟨36⟩ (by attester_decode_at v, ⟨1924⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup4 (by attester_decode_at v, ⟨1926⟩, 0x83, .DUP4) (by evm_ov),
    raw add (by attester_decode_at v, ⟨1927⟩, 0x01, .ADD) (by evm_ov),
    raw mstore 3 (attesterRevokeCallMemUid I) (UInt256.ofNat 11)
      (by attester_decode_at v, ⟨1928⟩, 0x52, .MSTORE) mem_cost
      (by rfl) (by decide) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨1929⟩, 0x90, .SWAP1) (by evm_ov),
    raw swap2 (by attester_decode_at v, ⟨1930⟩, 0x91, .SWAP2) (by evm_ov),
    raw add (by attester_decode_at v, ⟨1931⟩, 0x01, .ADD) (by evm_ov),
    raw mload 0 ⟨0⟩ (UInt256.ofNat 11)
      (by attester_decode_at v, ⟨1932⟩, 0x51, .MLOAD)
      mem_cost
      (mloadWordValue_of_readWithPadding
        (by rw [attesterRevokeCallMemUid_size I]; decide) (by decide)
        (attesterRevokeCallMemUid_read224 I))
      (by decide) (by evm_ov),
    raw push1 ⟨68⟩ (by attester_decode_at v, ⟨1933⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨1935⟩, 0x82, .DUP3) (by evm_ov),
    raw add (by attester_decode_at v, ⟨1936⟩, 0x01, .ADD) (by evm_ov),
    raw mstore 3 (attesterRevokeCallMem I) (UInt256.ofNat 12)
      (by attester_decode_at v, ⟨1937⟩, 0x52, .MSTORE) mem_cost
      (by rfl) (by decide) (by evm_ov)]
  have rd1971 := rd1938.pushConst (attesterRevokeEasWord v) (width := 32) (op := .PUSH32)
    (by decide) (attesterDecodeEasWord1938 v) (by evm_ov)
  have rd2001 := evm_run rd1971 with [
    raw push1 ⟨1⟩ (by attester_decode_at v, ⟨1971⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw push1 ⟨1⟩ (by attester_decode_at v, ⟨1973⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw push1 ⟨160⟩ (by attester_decode_at v, ⟨1975⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw shl (by attester_decode_at v, ⟨1977⟩, 0x1b, .SHL) (by evm_ov),
    raw sub (by attester_decode_at v, ⟨1978⟩, 0x03, .SUB) (by evm_ov),
    raw and (by attester_decode_at v, ⟨1979⟩, 0x16, .AND) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨1980⟩, 0x90, .SWAP1) (by evm_ov),
    raw push4 ⟨0x46926267⟩ (by attester_decode_at v, ⟨1981⟩, 0x63, (.Push .PUSH4))
      (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨1986⟩, 0x90, .SWAP1) (by evm_ov),
    raw push1 ⟨100⟩ (by attester_decode_at v, ⟨1987⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw add (by attester_decode_at v, ⟨1989⟩, 0x01, .ADD) (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨1990⟩, 0x5f, .PUSH0) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨1991⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw mload 0 ⟨256⟩ (UInt256.ofNat 12)
      (by attester_decode_at v, ⟨1993⟩, 0x51, .MLOAD)
      mem_cost
      (mloadWordValue_of_readWithPadding
        (by rw [attesterRevokeCallMem_size I]; decide) (by decide)
        (attesterRevokeCallMem_read64 I))
      (by decide) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨1994⟩, 0x80, .DUP1) (by evm_ov),
    raw dup4 (by attester_decode_at v, ⟨1995⟩, 0x83, .DUP4) (by evm_ov),
    raw sub (by attester_decode_at v, ⟨1996⟩, 0x03, .SUB) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨1997⟩, 0x81, .DUP2) (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨1998⟩, 0x5f, .PUSH0) (by evm_ov),
    raw dup8 (by attester_decode_at v, ⟨1999⟩, 0x87, .DUP8) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨2000⟩, 0x80, .DUP1) (by evm_ov)]
  exact ⟨_, _, by
    simpa [attesterRevokeTargetWord, attesterRevokeEasWord,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask by decide,
      show UInt256.land solcAddrMask (EVM.Word.ofNat v.eas.toNat) =
        UInt256.land (EVM.Word.ofNat v.eas.toNat) solcAddrMask by
          exact u256_land_comm solcAddrMask (EVM.Word.ofNat v.eas.toNat),
      show UInt256.sub (⟨356⟩ : UInt256) ⟨256⟩ = (⟨100⟩ : UInt256) by decide]
      using rd2001⟩

private theorem attester_uniswapExtCodeSizeWord_ne_zero_lookup_code_pos
    {σ : AccountMap} {target : UInt256} {addr : AccountAddress}
    (haddr : addr = AccountAddress.ofUInt256 target)
    (hne : Reasoning.Theory.uniswapExtCodeSizeWord σ target ≠ ⟨0⟩) :
    0 < (UInt256.ofNat
      ((σ.find? addr).option 0 (fun acc => acc.code.size))).toNat := by
  subst addr
  unfold Reasoning.Theory.uniswapExtCodeSizeWord at hne
  cases hacc : σ.find? (AccountAddress.ofUInt256 target) with
  | none =>
      exfalso
      exact hne (by simp [hacc, Option.option])
  | some acc =>
      have hwordNe : UInt256.ofNat acc.code.size ≠ (⟨0⟩ : UInt256) := by
        intro hzero
        exact hne (by simpa [hacc] using hzero)
      have htoNatNe : (UInt256.ofNat acc.code.size).toNat ≠ 0 := by
        intro hzeroNat
        apply hwordNe
        cases hword : UInt256.ofNat acc.code.size with
        | mk val =>
            cases val using Fin.cases
            · rfl
            · simp [UInt256.toNat, hword] at hzeroNat
      simpa [hacc] using Nat.pos_of_ne_zero htoNatNe

private theorem attester_uniswapExtCodeSizeWord_zero_lookup_code_zero
    {σ : AccountMap} {target : UInt256} {addr : AccountAddress}
    (haddr : addr = AccountAddress.ofUInt256 target)
    (hzero : Reasoning.Theory.uniswapExtCodeSizeWord σ target = ⟨0⟩) :
    (UInt256.ofNat
      ((σ.find? addr).option 0 (fun acc => acc.code.size))).toNat = 0 := by
  subst addr
  unfold Reasoning.Theory.uniswapExtCodeSizeWord at hzero
  cases hacc : σ.find? (AccountAddress.ofUInt256 target) with
  | none =>
      simpa [hacc, Option.option] using
        (show (UInt256.ofNat 0).toNat = 0 from by native_decide)
  | some acc =>
      have hword := congrArg UInt256.toNat hzero
      simpa [hacc] using hword

theorem attesterEvalExtCodeGuard_true (v : AttesterImmutables)
    {evm : EVM.State} {locals : Store} {receiver : Expr} {target : AccountAddress}
    (hreceiver :
      evalExpr? (config v) { contract := contract v, locals := locals } evm receiver =
        .ok (.address target))
    (hcode :
      0 < (UInt256.ofNat
        ((evm.lookupAccount target).option 0 (fun acc => acc.code.size))).toNat) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.binary .gt (.extCodeSize receiver) (.intLit 0)) = .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hreceiver, evalBinaryOp?, EVM.Word.ofNat, hcode]

theorem attesterEvalExtCodeGuard_false (v : AttesterImmutables)
    {evm : EVM.State} {locals : Store} {receiver : Expr} {target : AccountAddress}
    (hreceiver :
      evalExpr? (config v) { contract := contract v, locals := locals } evm receiver =
        .ok (.address target))
    (hcode :
      (UInt256.ofNat
        ((evm.lookupAccount target).option 0 (fun acc => acc.code.size))).toNat = 0) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.binary .gt (.extCodeSize receiver) (.intLit 0)) = .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, hreceiver, evalBinaryOp?, EVM.Word.ofNat, hcode]

theorem attesterRevokeCodeSize_ne_accountMapEquiv (v : AttesterImmutables)
    {σ τ : AccountMap}
    (hAccounts : accountMapEquiv σ τ)
    (hne :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (attesterRevokeTargetWord v) ≠ ⟨0⟩) :
    Reasoning.Theory.uniswapExtCodeSizeWord τ (attesterRevokeTargetWord v) ≠ ⟨0⟩ := by
  intro hzero
  apply hne
  have hsame :=
    Reasoning.Theory.uniswapExtCodeSizeWord_accountMapEquiv hAccounts
      (attesterRevokeTargetWord v)
  rw [hsame]
  exact hzero

theorem attesterRevokeCodeSize_zero_accountMapEquiv (v : AttesterImmutables)
    {σ τ : AccountMap}
    (hAccounts : accountMapEquiv σ τ)
    (hzero :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (attesterRevokeTargetWord v) = ⟨0⟩) :
    Reasoning.Theory.uniswapExtCodeSizeWord τ (attesterRevokeTargetWord v) = ⟨0⟩ := by
  have hsame :=
    Reasoning.Theory.uniswapExtCodeSizeWord_accountMapEquiv hAccounts
      (attesterRevokeTargetWord v)
  rw [← hsame]
  exact hzero

theorem attesterRevokeEasCode_pos_of_codeSize_ne
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hne :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (attesterRevokeTargetWord v) ≠ ⟨0⟩) :
    0 < (UInt256.ofNat
      (((initState cA gh bl σ σ₀ g A I).lookupAccount (EVM.address v.eas)).option 0
        (fun acc => acc.code.size))).toNat := by
  simpa [initState, State.lookupAccount] using
    attester_uniswapExtCodeSizeWord_ne_zero_lookup_code_pos
      (σ := σ) (target := attesterRevokeTargetWord v) (addr := EVM.address v.eas)
      (attesterRevokeTarget_eq v) hne

theorem attesterRevokeEasCode_zero_of_codeSize_zero
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hzero :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (attesterRevokeTargetWord v) = ⟨0⟩) :
    (UInt256.ofNat
      (((initState cA gh bl σ σ₀ g A I).lookupAccount (EVM.address v.eas)).option 0
        (fun acc => acc.code.size))).toNat = 0 := by
  simpa [initState, State.lookupAccount] using
    attester_uniswapExtCodeSizeWord_zero_lookup_code_zero
      (σ := σ) (target := attesterRevokeTargetWord v) (addr := EVM.address v.eas)
      (attesterRevokeTarget_eq v) hzero

theorem attesterX_revokeNoCode {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hcode : I.code = patchedRuntime v) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsz68 : 68 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hmultiRevoke : (attesterMultiRevokeSelBytes == I.calldata.extract 0 4) = false)
    (hmultiAttest : (attesterMultiAttestSelBytes == I.calldata.extract 0 4) = false)
    (hattest : (attesterAttestSelBytes == I.calldata.extract 0 4) = false)
    (hrevoke : (attesterRevokeSelBytes == I.calldata.extract 0 4) = true)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (attesterRevokeTargetWord v) = ⟨0⟩) :
    RDrev (patchedRuntime v) g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2001⟩ :=
    attesterX_revokeToExtcodesize (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) v hsz68 hsize hsmall
      (attesterX_revokeWrapper (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) v hcode hwv hsz4
        hsize hmultiRevoke hmultiAttest hattest hrevoke)
  obtain ⟨k2002, C2002, rd2002raw⟩ := RD.uniswapExtcodesize rd2001
    (by attester_decode_at v, ⟨2001⟩, 0x3b, .EXTCODESIZE) (by simp)
  have rd2002 : RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
      (⟨2002⟩ : UInt256)
      [Reasoning.Theory.uniswapExtCodeSizeWord σ (attesterRevokeTargetWord v),
        attesterRevokeTargetWord v, ⟨0⟩, ⟨256⟩, ⟨100⟩, ⟨256⟩, ⟨0⟩,
        ⟨356⟩, ⟨0x46926267⟩, attesterRevokeTargetWord v,
        attesterRevokeUidWord I, attesterRevokeSchemaWord I, ⟨97⟩, solcSelectorWord I]
      (attesterRevokeCallMem I) (UInt256.ofNat 12) ByteArray.empty (cA, σ)
      k2002 C2002 := by
    simpa using rd2002raw
  exact evm_run rd2002 with [
    raw iszero (by attester_decode_at v, ⟨2002⟩, 0x15, .ISZERO) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨2003⟩, 0x80, .DUP1) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨2004⟩, 0x15, .ISZERO) (by evm_ov),
    raw push2 ⟨2012⟩ (by attester_decode_at v, ⟨2005⟩, 0x61, (.Push .PUSH2))
      (by evm_ov),
    raw jumpiNT (by attester_decode_at v, ⟨2008⟩, 0x57, .JUMPI)
      (by rw [hcodeSize]; decide) (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨2009⟩, 0x5f, .PUSH0) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨2010⟩, 0x80, .DUP1) (by evm_ov),
    raw rev 0 (by attester_decode_at v, ⟨2011⟩, 0xfd, .REVERT)
      (fun s _ hstks => memExpRevert0 s hstks) (by evm_ov)]

theorem attesterX_revokePostCall {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨173⟩ : UInt256)
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (attesterRevokeTargetWord v) ≠ ⟨0⟩)
    (hperm : I.perm = true) (hdepth : I.depth.val < 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (o : ByteArray) (A' : Substate) (k' C' : ℕ),
      RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I) (⟨2016⟩ : UInt256)
        ((if z then ⟨1⟩ else ⟨0⟩) ::
          ⟨356⟩ :: ⟨0x46926267⟩ :: attesterRevokeTargetWord v ::
          attesterRevokeUidWord I :: attesterRevokeSchemaWord I :: ⟨97⟩ ::
          solcSelectorWord I :: [])
        (o.write 0 (attesterRevokeCallMem I) 256
          (min (⟨0⟩ : UInt256) (UInt256.ofNat o.size)).toNat)
        ⟨12⟩ o (cA', σ') k' C'
    ∧ typedCallViaEVM (config v) (initState cA gh bl σ σ₀ g A I)
        (EVM.address v.eas) "revoke" 0 (attesterRevokeArgVals I)
        (z, { initState cA gh bl σ σ₀ g A I with
                accountMap := σ', substate := A', createdAccounts := cA' }, o) true
    ∧ o.size < UInt256.size := by
  obtain ⟨_, _, rd2001⟩ :=
    attesterX_revokeToExtcodesize (v := v) hsz68 hsize hsmall hreach
  obtain ⟨_, _, _, rd2015⟩ :=
    RD.uniswapExtcodesizeGuardOkGas (pc := ⟨2001⟩) (okPc := ⟨2012⟩)
      rd2001 hcodeSize
      (by attester_decode_at v, ⟨2001⟩, 0x3b, .EXTCODESIZE)
      (by attester_decode_at v, ⟨2002⟩, 0x15, .ISZERO)
      (by attester_decode_at v, ⟨2003⟩, 0x80, .DUP1)
      (by attester_decode_at v, ⟨2004⟩, 0x15, .ISZERO)
      (by attester_decode_at v, ⟨2005⟩, 0x61, (.Push .PUSH2))
      (by attester_decode_at v, ⟨2008⟩, 0x57, .JUMPI)
      (attesterRevokeExtcodesizeOkJumpdest v)
      (by attester_decode_at v, ⟨2012⟩, 0x5b, .JUMPDEST)
      (by attester_decode_at v, ⟨2013⟩, 0x50, .POP)
      (by attester_decode_at v, ⟨2014⟩, 0x5a, .GAS)
      (by norm_num)
  obtain ⟨cA', σ', z, o, A_in, callGas, k', C', hTheta, rd2016raw, hosz⟩ :=
    rd2015.call (by attester_decode_at v, ⟨2015⟩, 0xf1, .CALL) hdepth
      (by norm_num)
  obtain ⟨g'', A', hΘ⟩ := hTheta
  refine ⟨cA', σ', z, o, A', k', C', ?_, ?_, hosz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 12).toNat
          (⟨256⟩ : UInt256).toNat (⟨100⟩ : UInt256).toNat)
          (⟨256⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) = (⟨12⟩ : UInt256) := by
        decide
    have rd2016 : RD (patchedRuntime v) I g
        (initState cA gh bl σ σ₀ g A I) (⟨2015⟩ + ⟨1⟩)
        ((if z then ⟨1⟩ else ⟨0⟩) ::
          ⟨356⟩ :: ⟨0x46926267⟩ :: attesterRevokeTargetWord v ::
          attesterRevokeUidWord I :: attesterRevokeSchemaWord I :: ⟨97⟩ ::
          solcSelectorWord I :: [])
        (o.write 0 (attesterRevokeCallMem I) 256
          (min (⟨0⟩ : UInt256) (UInt256.ofNat o.size)).toNat)
        ⟨12⟩ o (cA', σ') k' C' :=
      haw ▸ rd2016raw
    simpa using rd2016
  · refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := true) (targetWord := attesterRevokeTargetWord v)
      (mem := attesterRevokeCallMem I) (inOff := ⟨256⟩) (inSize := ⟨100⟩)
      (hdepth := fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
      (htgt := attesterRevokeTarget_eq v) (hcd := ?_) (hΘ := ?_)
    · rw [show (⟨256⟩ : UInt256).toNat = 256 by decide,
          show (⟨100⟩ : UInt256).toNat = 100 by decide,
          attesterRevokeCallMem_read256_100]
      exact attesterEncodeRevoke_eq v hsz68
    · simpa [initState, hperm] using hΘ

theorem attesterX_revokePostRevert {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : ℕ} {rest : List UInt256}
    (rd : RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I) (⟨2016⟩ : UInt256)
      (⟨0⟩ :: rest) mem aw rdata acc k C)
    (hrdataSize : rdata.size < UInt256.size)
    (hov : rest.length + 5 ≤ 1024) :
    RDrev (patchedRuntime v) g (initState cA gh bl σ σ₀ g A I) := by
  have rd2023 : RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
      (⟨2023⟩ : UInt256) (UInt256.isZero ⟨0⟩ :: rest) mem aw rdata acc _ _ :=
    evm_run rd with [
      raw iszero (by attester_decode_at v, ⟨2016⟩, 0x15, .ISZERO) (by evm_ov),
      raw dup1 (by attester_decode_at v, ⟨2017⟩, 0x80, .DUP1) (by evm_ov),
      raw iszero (by attester_decode_at v, ⟨2018⟩, 0x15, .ISZERO) (by evm_ov),
      raw push2 ⟨2030⟩ (by attester_decode_at v, ⟨2019⟩, 0x61, (.Push .PUSH2))
        (by evm_ov),
      raw jumpiNT (by attester_decode_at v, ⟨2022⟩, 0x57, .JUMPI) (by decide)
        (by evm_ov)]
  have rd2024 := RD.returndatasize rd2023
    (by attester_decode_at v, ⟨2023⟩, 0x3d, .RETURNDATASIZE)
    (by simp only [List.length_cons]; omega)
  have rd2025 := RD.push0 rd2024
    (by attester_decode_at v, ⟨2024⟩, 0x5f, .PUSH0)
    (by simp only [List.length_cons]; omega)
  have rd2026 := RD.dup1 rd2025
    (by attester_decode_at v, ⟨2025⟩, 0x80, .DUP1)
    (by simp only [List.length_cons]; omega)
  have rd2027 : RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
      (⟨2027⟩ : UInt256) (UInt256.isZero ⟨0⟩ :: rest)
      (rdata.write 0 mem 0 (UInt256.ofNat rdata.size).toNat)
      (UInt256.ofNat (MachineState.M aw.toNat 0 (UInt256.ofNat rdata.size).toNat))
      rdata acc _ _ :=
    RD.returndatacopy
      (Cₘ (UInt256.ofNat (MachineState.M aw.toNat 0 (UInt256.ofNat rdata.size).toNat)) - Cₘ aw)
      (rdata.write 0 mem 0 (UInt256.ofNat rdata.size).toNat)
      (UInt256.ofNat (MachineState.M aw.toNat 0 (UInt256.ofNat rdata.size).toNat))
      rd2026
      (by attester_decode_at v, ⟨2026⟩, 0x3e, .RETURNDATACOPY)
      (by
        rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl, Nat.zero_add]
        rw [show (UInt256.ofNat rdata.size).toNat = rdata.size from
          ulit_toNat' rdata.size hrdataSize])
      (by
        intro s haws hstks
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hstks, haws,
          List.getElem!_cons_zero, List.getElem!_cons_succ,
          show (⟨0⟩ : UInt256).toNat = 0 from rfl])
      rfl rfl (by simp only [List.length_cons]; omega)
  have rd2028 := RD.returndatasize rd2027
    (by attester_decode_at v, ⟨2027⟩, 0x3d, .RETURNDATASIZE)
    (by simp only [List.length_cons]; omega)
  have rd2029 := RD.push0 rd2028
    (by attester_decode_at v, ⟨2028⟩, 0x5f, .PUSH0)
    (by simp only [List.length_cons]; omega)
  exact RD.rev _ rd2029
    (by attester_decode_at v, ⟨2029⟩, 0xfd, .REVERT)
    (fun s haws hstks => by rw [memExpRevertZeroOff s hstks, haws])
    (by simp only [List.length_cons]; omega)

theorem attesterX_revokeSuccessStop {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I) (⟨2016⟩ : UInt256)
      [⟨1⟩, ⟨356⟩, ⟨0x46926267⟩, attesterRevokeTargetWord v,
        attesterRevokeUidWord I, attesterRevokeSchemaWord I, ⟨97⟩, solcSelectorWord I]
      mem ⟨12⟩ o acc k C) :
    RDret (patchedRuntime v) g (initState cA gh bl σ σ₀ g A I) acc ByteArray.empty := by
  obtain ⟨_, _, rd2032⟩ :=
    RD.uniswapCallSuccessGuardOk (pc := ⟨2016⟩) (okPc := ⟨2030⟩) rd
      (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by attester_decode_at v, ⟨2016⟩, 0x15, .ISZERO)
      (by attester_decode_at v, ⟨2017⟩, 0x80, .DUP1)
      (by attester_decode_at v, ⟨2018⟩, 0x15, .ISZERO)
      (by attester_decode_at v, ⟨2019⟩, 0x61, (.Push .PUSH2))
      (by attester_decode_at v, ⟨2022⟩, 0x57, .JUMPI)
      (attesterRevokeCallOkJumpdest v)
      (by attester_decode_at v, ⟨2030⟩, 0x5b, .JUMPDEST)
      (by attester_decode_at v, ⟨2031⟩, 0x50, .POP)
      (by simp)
  have rd97 := evm_run rd2032 with [
    raw pop (by attester_decode_at v, ⟨2032⟩, 0x50, .POP) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨2033⟩, 0x50, .POP) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨2034⟩, 0x50, .POP) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨2035⟩, 0x50, .POP) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨2036⟩, 0x50, .POP) (by evm_ov),
    raw jump (by attester_decode_at v, ⟨2037⟩, 0x56, .JUMP)
      (attesterNoReturnDoneJumpdest v) (by evm_ov)]
  have rd98 := evm_run rd97 with [
    raw jumpdest (by attester_decode_at v, ⟨97⟩, 0x5b, .JUMPDEST) (by evm_ov)]
  exact RD.stop rd98 (by attester_decode_at v, ⟨98⟩, 0x00, .STOP) (by evm_ov)

theorem attesterX_revokeCallDepthLimit {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hcode : I.code = patchedRuntime v) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsz68 : 68 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hmultiRevoke : (attesterMultiRevokeSelBytes == I.calldata.extract 0 4) = false)
    (hmultiAttest : (attesterMultiAttestSelBytes == I.calldata.extract 0 4) = false)
    (hattest : (attesterAttestSelBytes == I.calldata.extract 0 4) = false)
    (hrevoke : (attesterRevokeSelBytes == I.calldata.extract 0 4) = true)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (attesterRevokeTargetWord v) ≠ ⟨0⟩)
    (hdepth : I.depth = 1024) :
    RDrev (patchedRuntime v) g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2001⟩ :=
    attesterX_revokeToExtcodesize (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) v hsz68 hsize hsmall
      (attesterX_revokeWrapper (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) v hcode hwv hsz4
        hsize hmultiRevoke hmultiAttest hattest hrevoke)
  obtain ⟨_, _, _, rd2015⟩ :=
    RD.uniswapExtcodesizeGuardOkGas (pc := ⟨2001⟩) (okPc := ⟨2012⟩)
      rd2001 hcodeSize
      (by attester_decode_at v, ⟨2001⟩, 0x3b, .EXTCODESIZE)
      (by attester_decode_at v, ⟨2002⟩, 0x15, .ISZERO)
      (by attester_decode_at v, ⟨2003⟩, 0x80, .DUP1)
      (by attester_decode_at v, ⟨2004⟩, 0x15, .ISZERO)
      (by attester_decode_at v, ⟨2005⟩, 0x61, (.Push .PUSH2))
      (by attester_decode_at v, ⟨2008⟩, 0x57, .JUMPI)
      (attesterRevokeExtcodesizeOkJumpdest v)
      (by attester_decode_at v, ⟨2012⟩, 0x5b, .JUMPDEST)
      (by attester_decode_at v, ⟨2013⟩, 0x50, .POP)
      (by attester_decode_at v, ⟨2014⟩, 0x5a, .GAS)
      (by norm_num)
  obtain ⟨k', C', rd2016raw⟩ :=
    rd2015.callDepthLimit (by attester_decode_at v, ⟨2015⟩, 0xf1, .CALL) hdepth
      (by norm_num)
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 12).toNat
        (⟨256⟩ : UInt256).toNat (⟨100⟩ : UInt256).toNat)
        (⟨256⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) = (⟨12⟩ : UInt256) := by
      decide
  have rd2016 : RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
      (⟨2016⟩ : UInt256)
      [⟨0⟩, ⟨356⟩, ⟨0x46926267⟩, attesterRevokeTargetWord v,
        attesterRevokeUidWord I, attesterRevokeSchemaWord I, ⟨97⟩, solcSelectorWord I]
      (ByteArray.empty.write 0 (attesterRevokeCallMem I) 256
        (min (⟨0⟩ : UInt256) (UInt256.ofNat ByteArray.empty.size)).toNat)
      ⟨12⟩ ByteArray.empty (cA, σ) k' C' := by
    have rd := haw ▸ rd2016raw
    simpa using rd
  exact attesterX_revokePostRevert (v := v) rd2016 (by native_decide) (by simp)

theorem attesterRevokeBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (v : AttesterImmutables) {code : ByteArray}
    (hpatch : patchRuntime attesterBytecode (patches v) = some code)
    (hcode : I.code = code)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hmultiRevoke : (attesterMultiRevokeSelBytes == I.calldata.extract 0 4) = false)
    (hmultiAttest : (attesterMultiAttestSelBytes == I.calldata.extract 0 4) = false)
    (hattest : (attesterAttestSelBytes == I.calldata.extract 0 4) = false)
    (hrevoke : (attesterRevokeSelBytes == I.calldata.extract 0 4) = true)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hpatched : code = patchedRuntime v := code_eq_patchedRuntime_of_patch hpatch
  have hIcode : I.code = patchedRuntime v := hcode.trans hpatched
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I attesterRevokeSelBytes attesterRevokeSelBytes_size hrevoke
  have hd := attesterDispatch_revoke v hmultiRevoke hmultiAttest hattest hrevoke
  by_cases hsz68 : 68 ≤ I.calldata.size
  · by_cases hsmall : I.calldata.size < 2 ^ 255 + 4
    · let gS : Sat256 := Sat256.ofUInt256 g
      let evmEvm : EVM.State := initState cA gh bl σ_evm σ₀ gS A I
      let evmSolm : EVM.State := initState cA gh bl σ_solm σ₀ gS A I
      have hdec := attesterDecode_revoke_ok v hsz68 hsmall
      have hwvSolm : evmSolm.executionEnv.weiValue = ⟨0⟩ := by
        simp [evmSolm, initState, hwv]
      have hargsSolm :
          evalExprs? (config v)
              { contract := contract v, locals := attesterRevokeStore I } evmSolm
              [revocationRequest (.var "schema") (.var "uid")] =
            .ok (attesterRevokeArgVals I) :=
        attesterEvalRevokeArgs v evmSolm I
      have hreach :=
        attesterX_revokeWrapper (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
          (σ₀ := σ₀) (A := A) (I := I) (g := gS) v hIcode hwv hsz4 hsize
          hmultiRevoke hmultiAttest hattest hrevoke
      by_cases hcodeSizeEvm :
          Reasoning.Theory.uniswapExtCodeSizeWord σ_evm (attesterRevokeTargetWord v) = ⟨0⟩
      · have hrdrev :=
          attesterX_revokeNoCode (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
            (σ₀ := σ₀) (A := A) (I := I) (g := gS) v hIcode hwv hsz4 hsize
            hsz68 hsmall hmultiRevoke hmultiAttest hattest hrevoke hcodeSizeEvm
        have hcodeSizeSolm :
            Reasoning.Theory.uniswapExtCodeSizeWord σ_solm (attesterRevokeTargetWord v) =
              ⟨0⟩ :=
          attesterRevokeCodeSize_zero_accountMapEquiv v hAccounts hcodeSizeEvm
        have hcodeSolmRaw :=
          attesterRevokeEasCode_zero_of_codeSize_zero
            (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
            (A := A) (I := I) (g := gS) v hcodeSizeSolm
        have haddr : EVM.address v.eas = v.eas := by
          apply Fin.ext
          simp [EVM.address, EVM.uintN]
          exact Nat.mod_eq_of_lt v.eas.isLt
        have hcodeSolm :
            (UInt256.ofNat
              ((evmSolm.lookupAccount v.eas).option 0 (fun acc => acc.code.size))).toNat =
                0 := by
          simpa [evmSolm, haddr] using hcodeSolmRaw
        have hguard :
            evalExpr? (config v)
                { contract := contract v, locals := attesterRevokeStore I } evmSolm
                (.binary .gt (.extCodeSize (easExpr v)) (.intLit 0)) =
              .ok (.bool false) :=
          attesterEvalExtCodeGuard_false v
            (attesterEvalEasExpr v
              { contract := contract v, locals := attesterRevokeStore I } evmSolm)
            hcodeSolm
        have hbody :=
          attesterRevokeBodyNoCode v evmSolm (attesterRevokeStore I) hwvSolm hguard
        exact hrdrev.reEquivExecutionRevert hIcode hd hdec hbody
      · have hcodeSizeSolmNe :
            Reasoning.Theory.uniswapExtCodeSizeWord σ_solm (attesterRevokeTargetWord v) ≠
              ⟨0⟩ :=
          attesterRevokeCodeSize_ne_accountMapEquiv v hAccounts hcodeSizeEvm
        have hcodeSolmRaw :=
          attesterRevokeEasCode_pos_of_codeSize_ne
            (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
            (A := A) (I := I) (g := gS) v hcodeSizeSolmNe
        have haddr : EVM.address v.eas = v.eas := by
          apply Fin.ext
          simp [EVM.address, EVM.uintN]
          exact Nat.mod_eq_of_lt v.eas.isLt
        have hcodeSolm :
            0 < (UInt256.ofNat
              ((evmSolm.lookupAccount v.eas).option 0 (fun acc => acc.code.size))).toNat := by
          simpa [evmSolm, haddr] using hcodeSolmRaw
        have hguard :
            evalExpr? (config v)
                { contract := contract v, locals := attesterRevokeStore I } evmSolm
                (.binary .gt (.extCodeSize (easExpr v)) (.intLit 0)) =
              .ok (.bool true) :=
          attesterEvalExtCodeGuard_true v
            (attesterEvalEasExpr v
              { contract := contract v, locals := attesterRevokeStore I } evmSolm)
            hcodeSolm
        by_cases hdepth : I.depth.val < 1024
        · obtain ⟨cA', σ', z, o, A', k', C', rd2016, hcallEvm, hosize⟩ :=
            attesterX_revokePostCall (cA := cA) (gh := gh) (bl := bl)
              (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := gS) v
              hsz68 hsize hsmall hreach hcodeSizeEvm hperm hdepth
          let evmPostEvm : EVM.State :=
            { evmEvm with accountMap := σ', substate := A', createdAccounts := cA' }
          have hcallEvm' :
              typedCallViaEVM (config v) evmEvm (EVM.address v.eas) "revoke" 0
                (attesterRevokeArgVals I) (z, evmPostEvm, o) true := by
            simpa [evmEvm, evmPostEvm] using hcallEvm
          obtain ⟨σSolmPost, ASolmPost, hcallSolm, hStateCall⟩ :=
            typedCallViaEVM_initState_EVMStateEquiv (hcall := hcallEvm')
              (by simp [evmEvm, evmSolm, evmPostEvm, initState]) hAccounts
          let evmPostSolm : EVM.State :=
            { evmSolm with
              accountMap := σSolmPost, substate := ASolmPost, createdAccounts := cA' }
          have hcallSolm' :
              typedCallViaEVM (config v) evmSolm (EVM.address v.eas) "revoke" 0
                (attesterRevokeArgVals I) (z, evmPostSolm, o) true := by
            simpa [evmPostSolm] using hcallSolm
          have hStateCall' : EVMStateEquiv evmPostEvm evmPostSolm := by
            simpa [evmPostSolm] using hStateCall
          cases z
          · simp only [Bool.false_eq_true, if_false] at rd2016 hcallSolm'
            have hrdrev := attesterX_revokePostRevert (v := v) rd2016 hosize (by simp)
            have hbody :=
              attesterRevokeBodyCallFailure v evmSolm evmPostSolm
                (attesterRevokeStore I) hwvSolm hguard hargsSolm hcallSolm'
            exact hrdrev.reEquivExecutionRevert hIcode hd hdec hbody
          · simp only [Bool.true_eq_false, if_true] at rd2016 hcallSolm'
            have hrdret := attesterX_revokeSuccessStop (v := v) rd2016
            have hretdec := attesterDecode_revoke_return_ok v o
            have hbody :=
              attesterRevokeBodySuccess v evmSolm evmPostSolm
                (attesterRevokeStore I) hwvSolm hguard hargsSolm hcallSolm' hretdec
            have henc : returnEquiv ByteArray.empty none (revokeTransition v).returnType := by
              rw [show (revokeTransition v).returnType = [] by rfl]
              exact returnEquiv.fallthrough rfl (by rfl) (by native_decide)
            exact hrdret.reEquivExecutionGenEVMStateEquiv hIcode hd hdec hbody
              rfl (accountMapEquiv.refl σ') hStateCall' henc
        · have hdepth1024 : I.depth = 1024 := by
            apply Fin.ext
            have hlt := I.depth.isLt
            rw [not_lt] at hdepth
            omega
          have hrdrev :=
            attesterX_revokeCallDepthLimit (cA := cA) (gh := gh) (bl := bl)
              (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := gS) v hIcode
              hwv hsz4 hsize hsz68 hsmall hmultiRevoke hmultiAttest hattest hrevoke
              hcodeSizeEvm hdepth1024
          have hdepthInit : evmSolm.executionEnv.depth = 1024 := by
            simpa [evmSolm, initState] using hdepth1024
          have hcallSolm :
              typedCallViaEVM (config v) evmSolm (EVM.address v.eas) "revoke" 0
                (attesterRevokeArgVals I)
                (false,
                  { evmSolm with
                    substate := (evmSolm.addAccessedAccount (EVM.address v.eas)).substate },
                  ByteArray.empty)
                true :=
            callNotMade_depthLimit
              (cfg := config v) (evm := evmSolm) (tgt := EVM.address v.eas)
              (name := "revoke") (args := attesterRevokeArgVals I) (callPerm := true)
              (attesterEncodeRevoke_eq v hsz68) hdepthInit
          have hbody :=
            attesterRevokeBodyCallFailure v evmSolm
              ({ evmSolm with
                substate := (evmSolm.addAccessedAccount (EVM.address v.eas)).substate })
              (attesterRevokeStore I) hwvSolm hguard hargsSolm hcallSolm
          exact hrdrev.reEquivExecutionRevert hIcode hd hdec hbody
    · have hbig : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      have hdec := attesterDecode_revoke_none_huge v hbig
      exact (attesterX_revokeDecodeHuge (g := Sat256.ofUInt256 g) v hIcode hwv hsz4
          hsize hbig hmultiRevoke hmultiAttest hattest hrevoke)
        |>.reEquivDecodingFailed hIcode hd hdec
  · have hshort : I.calldata.size < 68 := by omega
    have hdec := attesterDecode_revoke_none_short v hsz4 hshort
    exact (attesterX_revokeDecodeShort (g := Sat256.ofUInt256 g) v hIcode hwv hsz4
        hsize hshort hmultiRevoke hmultiAttest hattest hrevoke)
      |>.reEquivDecodingFailed hIcode hd hdec

end Benchmarks.EAS.Attester
