import Benchmarks.EAS.Attester.MultiRevokeEncoderExact

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.EAS.Attester.Immutables

namespace Benchmarks.EAS.Attester

def attesterWordBytesList (w : UInt256) : List UInt8 :=
  EVM.Word.toBytesBE w

def attesterWordsBytesList : List UInt256 → List UInt8
  | [] => []
  | w :: rest => attesterWordBytesList w ++ attesterWordsBytesList rest

theorem attesterNatBytes_eq_toBytesBE (n : Nat) :
    ABI.natBytes n = EVM.Word.toBytesBE (UInt256.ofNat n) := rfl

@[simp] theorem attesterWordsBytesList_nil :
    attesterWordsBytesList [] = [] := rfl

@[simp] theorem attesterWordsBytesList_cons (w : UInt256) (rest : List UInt256) :
    attesterWordsBytesList (w :: rest) =
      EVM.Word.toBytesBE w ++ attesterWordsBytesList rest := rfl

theorem attesterWordsBytesList_append (xs ys : List UInt256) :
    attesterWordsBytesList (xs ++ ys) =
      attesterWordsBytesList xs ++ attesterWordsBytesList ys := by
  induction xs with
  | nil =>
      simp [attesterWordsBytesList]
  | cons x xs ih =>
      simp [attesterWordBytesList, attesterWordsBytesList, ih, List.append_assoc]

theorem attesterWordsBytesList_cons_toByteArray (w : UInt256) (rest : List UInt256) :
    (attesterWordsBytesList (w :: rest)).toByteArray =
      UInt256.toByteArray w ++ (attesterWordsBytesList rest).toByteArray := by
  simp [attesterWordsBytesList, attesterWordBytesList,
    word_toBytesBE_toByteArray_eq_toByteArray]

theorem attesterWordsBytesList_length (words : List UInt256) :
    (attesterWordsBytesList words).length = 32 * words.length := by
  induction words with
  | nil =>
      simp [attesterWordsBytesList]
  | cons word rest ih =>
      have hwordLen : (attesterWordBytesList word).length = 32 := by
        have h := word_toBytesBE_toByteArray_size word
        rw [list_toByteArray_size] at h
        simpa [attesterWordBytesList] using h
      simp [attesterWordsBytesList, ih, hwordLen]
      omega

def AttesterWordsAt (mem : ByteArray) (base : Nat) (words : List UInt256) : Prop :=
  base + 32 * words.length ≤ mem.size ∧
  ∀ {idx word}, lookupNth? words idx = some word →
    mem.readWithPadding (base + 32 * idx) 32 = UInt256.toByteArray word

theorem AttesterWordsAt.tail
    {mem : ByteArray} {base : Nat} {word : UInt256} {words : List UInt256}
    (h : AttesterWordsAt mem base (word :: words)) :
    AttesterWordsAt mem (base + 32) words := by
  constructor
  · have hb := h.1
    simp at hb
    omega
  · intro idx w hlookup
    have htail := h.2 (idx := idx + 1) (word := w) (by
      simpa [lookupNth?] using hlookup)
    rw [show base + 32 + 32 * idx = base + 32 * (idx + 1) by omega]
    exact htail

theorem AttesterWordsAt.readWithPadding_eq
    {mem : ByteArray} {base : Nat} :
    ∀ words : List UInt256,
      32 * words.length < 2 ^ 64 →
      AttesterWordsAt mem base words →
        mem.readWithPadding base (32 * words.length) =
          (attesterWordsBytesList words).toByteArray
  | [], _hlen, _h => by
      rw [show 32 * ([] : List UInt256).length = 0 by rfl]
      rw [byteArray_readWithPadding_zero]
      rfl
  | word :: [], _hlen, h => by
      have hhead := h.2 (idx := 0) (word := word) (by simp [lookupNth?])
      rw [show 32 * [word].length = 32 by norm_num]
      rw [show base + 32 * 0 = base by omega] at hhead
      rw [hhead]
      rw [attesterWordsBytesList_cons_toByteArray word []]
      simp [attesterWordsBytesList]
  | word :: next :: rest, hlen, h => by
      let words := next :: rest
      have hhead := h.2 (idx := 0) (word := word) (by simp [lookupNth?])
      have htail : AttesterWordsAt mem (base + 32) words :=
        AttesterWordsAt.tail h
      have htailLen : 32 * words.length < 2 ^ 64 := by
        dsimp [words]
        simp at hlen ⊢
        omega
      have htailRead :=
        AttesterWordsAt.readWithPadding_eq (mem := mem) (base := base + 32)
          words htailLen htail
      have hlenSplit : 32 + 32 * words.length < 2 ^ 64 := by
        rw [show 32 + 32 * words.length = 32 * (word :: words).length by
          simp [words]
          omega]
        exact hlen
      have hboundSplit : base + 32 + 32 * words.length ≤ mem.size := by
        have hbound := h.1
        dsimp [words] at hbound ⊢
        omega
      rw [show 32 * (word :: words).length = 32 + 32 * words.length by
        simp [words]
        omega]
      rw [byteArray_readWithPadding_split mem base 32 (32 * words.length)
        (by norm_num)
        (by simp [words])
        (by norm_num)
        htailLen
        hlenSplit
        hboundSplit]
      rw [show base + 32 * 0 = base by omega] at hhead
      rw [hhead, htailRead]
      rw [attesterWordsBytesList_cons_toByteArray word words,
        attesterWordsBytesList_cons_toByteArray next rest]

theorem lookupNth?_append_cases {α : Type} :
    ∀ {xs ys : List α} {idx : Nat} {value : α},
      lookupNth? (xs ++ ys) idx = some value →
        (idx < xs.length ∧ lookupNth? xs idx = some value) ∨
          (xs.length ≤ idx ∧ lookupNth? ys (idx - xs.length) = some value)
  | [], ys, idx, value, h => by
      right
      simpa using h
  | x :: xs, ys, 0, value, h => by
      left
      constructor
      · simp
      · simpa [lookupNth?] using h
  | x :: xs, ys, idx + 1, value, h => by
      have htail : lookupNth? (xs ++ ys) idx = some value := by
        simpa [lookupNth?] using h
      rcases lookupNth?_append_cases htail with hleft | hright
      · left
        rcases hleft with ⟨hlt, hlookup⟩
        constructor
        · simp
          omega
        · simpa [lookupNth?] using hlookup
      · right
        rcases hright with ⟨hle, hlookup⟩
        constructor
        · simp
          omega
        · have hsub : idx + 1 - (x :: xs).length = idx - xs.length := by
            simp
          simpa [hsub] using hlookup

theorem AttesterWordsAt.writeWord_preserved
    {mem : ByteArray} {base off : Nat} {words : List UInt256} {write : UInt256}
    (h : AttesterWordsAt mem base words)
    (hdisj : off + 32 ≤ base ∨ base + 32 * words.length ≤ off) :
    AttesterWordsAt (Reasoning.Theory.writeWord mem off write) base words := by
  constructor
  · exact le_trans h.1 (attesterWriteWord_size_ge_nat mem off write)
  · intro idx word hlookup
    have hidx : idx < words.length := lookupNth?_some_length hlookup
    have hreadBound : base + 32 * idx + 32 ≤ mem.size := by
      have hbound := h.1
      have hmul : 32 * (idx + 1) ≤ 32 * words.length :=
        Nat.mul_le_mul_left 32 (Nat.succ_le_of_lt hidx)
      omega
    have hpres :
        (Reasoning.Theory.writeWord mem off write).readWithPadding
            (base + 32 * idx) 32 =
          mem.readWithPadding (base + 32 * idx) 32 := by
      exact attesterWriteWord_read_preserved_len_nat mem off
        (base + 32 * idx) 32 write
        (by
          rcases hdisj with hbefore | hafter
          · exact Or.inr ⟨by omega, hreadBound⟩
          · exact Or.inl ⟨by omega, hreadBound⟩)
        (by norm_num) (by norm_num)
    rw [hpres]
    exact h.2 hlookup

theorem AttesterWordsAt.writeWord_append
    {mem : ByteArray} {base : Nat} {words : List UInt256} {word : UInt256}
    (h : AttesterWordsAt mem base words) :
    AttesterWordsAt
      (Reasoning.Theory.writeWord mem (base + 32 * words.length) word)
      base (words ++ [word]) := by
  constructor
  · rw [attesterWriteWord_size_nat]
    simp
    omega
  · intro idx readWord hlookup
    have hidxTotal : idx < (words ++ [word]).length :=
      lookupNth?_some_length hlookup
    rcases lookupNth?_append_cases hlookup with hleft | hright
    · rcases hleft with ⟨_hlt, hlookupOld⟩
      have hpreserved :
          AttesterWordsAt
            (Reasoning.Theory.writeWord mem (base + 32 * words.length) word)
            base words :=
        AttesterWordsAt.writeWord_preserved h (Or.inr (by rfl))
      exact hpreserved.2 hlookupOld
    · rcases hright with ⟨hge, hlookupTail⟩
      cases hdelta : idx - words.length with
      | zero =>
          have hreadWord : readWord = word := by
            have htailEq : word = readWord := by
              simpa [lookupNth?, hdelta] using hlookupTail
            exact htailEq.symm
          have hidx : idx = words.length := by
            simp at hidxTotal
            omega
          rw [hidx, hreadWord]
          exact attesterWriteWord_read_back_nat mem (base + 32 * words.length) word
      | succ delta =>
          simp [lookupNth?, hdelta] at hlookupTail

theorem AttesterWordsAt.append
    {mem : ByteArray} {base : Nat} {xs ys : List UInt256}
    (hxs : AttesterWordsAt mem base xs)
    (hys : AttesterWordsAt mem (base + 32 * xs.length) ys) :
    AttesterWordsAt mem base (xs ++ ys) := by
  constructor
  · have hx := hxs.1
    have hy := hys.1
    simp
    omega
  · intro idx word hlookup
    rcases lookupNth?_append_cases hlookup with hleft | hright
    · rcases hleft with ⟨_hlt, hlookupXs⟩
      exact hxs.2 hlookupXs
    · rcases hright with ⟨_hge, hlookupYs⟩
      have hyRead := hys.2 hlookupYs
      rw [show base + 32 * idx =
          base + 32 * xs.length + 32 * (idx - xs.length) by
        have hidx : idx < (xs ++ ys).length := lookupNth?_some_length hlookup
        have hge : xs.length ≤ idx := _hge
        simp at hidx
        omega]
      exact hyRead

theorem attesterWriteWord_read_window_nat
    (mem : ByteArray) (off start len : Nat) (word : UInt256)
    (hwithin : start + len ≤ 32) (hpos : 0 < len) (hlen64 : len < 2 ^ 64) :
    (Reasoning.Theory.writeWord mem off word).readWithPadding (off + start) len =
      (UInt256.toByteArray word).extract start (start + len) := by
  unfold Reasoning.Theory.writeWord
  by_cases hle : off ≤ mem.size
  · exact toByteArray_write_read_window_of_gap word mem off start len
      hwithin hpos hlen64 (by
        rw [Nat.sub_eq_zero_of_le hle]
        exact lt_usize 0 (by norm_num))
  · have hge : mem.size ≤ off := by omega
    rw [attesterToByteArray_write_eq_nat word mem off hge]
    have hprefix :
        (mem ++ ffi.ByteArray.zeroes (off - mem.size)).size = off := by
      rw [ByteArray.size_append, ByteArray_zeroes_size]
      omega
    rw [readWithPadding_eq_extract' _ (off + start) len hpos hlen64 (by
      rw [ByteArray.size_append, hprefix, toByteArray_size]
      omega)]
    rw [extract_append_right_window _ _ _ _ (by rw [hprefix]; omega), hprefix]
    rw [show off + start - off = start by omega,
      show off + start + len - off = start + len by omega]

theorem attesterMultiRevokeSelectorWord_extract4 :
    (UInt256.toByteArray attesterMultiRevokeSelectorWord).extract 0 4 =
      multiRevokeSelector := by
  native_decide

theorem attesterBytes32ValueWord?_encodeABIValue
    {value : Value} {w : UInt256}
    (h : attesterBytes32ValueWord? value = some w) :
    ABI.encodeABIValue? bytes32 value = some (EVM.Word.toBytesBE w) := by
  cases value with
  | fixedBytes n bytes =>
      dsimp [attesterBytes32ValueWord?] at h
      by_cases hn : n = bytes32Width ∧ bytes.length = 32
      · simp [hn] at h
        cases h
        rcases hn with ⟨rfl, hlen⟩
        simp [ABI.encodeABIValue?, bytes32, bytes32Width, hlen, ABI.zeroBytes,
          Nat.add_comm, toBytesBE_bytesToWord_of_length hlen]
      · simp [hn] at h
  | _ =>
      simp [attesterBytes32ValueWord?] at h

theorem attesterEncodeABIValue_bytes32_eq_bind (value : Value) :
    ABI.encodeABIValue? bytes32 value =
      (attesterBytes32ValueWord? value).bind
        (fun w => some (EVM.Word.toBytesBE w)) := by
  cases value with
  | fixedBytes n bytes =>
      by_cases hn : n = bytes32Width
      · subst hn
        by_cases hlen : bytes.length = 32
        · simp [ABI.encodeABIValue?, bytes32, bytes32Width,
            attesterBytes32ValueWord?, hlen, ABI.zeroBytes, Nat.add_comm,
            toBytesBE_bytesToWord_of_length hlen]
        · simp [ABI.encodeABIValue?, bytes32, bytes32Width,
            attesterBytes32ValueWord?, hlen]
      ·
        by_cases hif : n = (31 : Fin 32) ∧ bytes.length = 32
        · exact False.elim (hn (by
            simpa [bytes32Width] using hif.1))
        · simp [ABI.encodeABIValue?, bytes32, bytes32Width,
            attesterBytes32ValueWord?, hif]
  | _ =>
      simp [ABI.encodeABIValue?, ABI.encodeABIWord?, bytes32,
        attesterBytes32ValueWord?]

theorem attesterEncodeABIValue_uint256_zero :
    ABI.encodeABIValue? uint256 (.int 0) =
      some (EVM.Word.toBytesBE (⟨0⟩ : UInt256)) := by
  have hpow : 0 < EVM.twoPow 256 := by norm_num [EVM.twoPow]
  have hword : EVM.word 0 = (⟨0⟩ : UInt256) := rfl
  simp [ABI.encodeABIValue?, ABI.encodeABIWord?, uint256, uint256Int, hpow,
    hword]

def attesterRevocationDataEncodedWords? : List Value → Option (List UInt256)
  | [] => some []
  | uid :: rest => do
      let uidWord <- attesterBytes32ValueWord? uid
      let restWords <- attesterRevocationDataEncodedWords? rest
      some (uidWord :: (⟨0⟩ : UInt256) :: restWords)

theorem attesterRevocationDataEncodedWords?_length
    {uids : List Value} {words : List UInt256}
    (h : attesterRevocationDataEncodedWords? uids = some words) :
    words.length = 2 * uids.length := by
  induction uids generalizing words with
  | nil =>
      simp [attesterRevocationDataEncodedWords?] at h
      cases h
      simp
  | cons uid rest ih =>
      simp [attesterRevocationDataEncodedWords?] at h
      cases hUid : attesterBytes32ValueWord? uid with
      | none =>
          simp [hUid] at h
      | some uidWord =>
          cases hRest : attesterRevocationDataEncodedWords? rest with
          | none =>
              simp [hUid, hRest] at h
          | some restWords =>
              simp [hUid, hRest] at h
              cases h
              have hlen := ih hRest
              simp [hlen]
              omega

theorem attesterRevocationDataEncodedWords?_some_of_words
    {uids : List Value}
    (hwords :
      ∀ {j uid}, lookupNth? uids j = some uid →
        ∃ uidWord, attesterBytes32ValueWord? uid = some uidWord) :
    ∃ words,
      attesterRevocationDataEncodedWords? uids = some words ∧
      words.length = 2 * uids.length := by
  induction uids with
  | nil =>
      refine ⟨[], ?_, ?_⟩
      · simp [attesterRevocationDataEncodedWords?]
      · simp
  | cons uid rest ih =>
      obtain ⟨uidWord, hUidWord⟩ :=
        hwords (j := 0) (uid := uid) (by simp [lookupNth?])
      have hrestWords :
          ∀ {j uid}, lookupNth? rest j = some uid →
            ∃ uidWord, attesterBytes32ValueWord? uid = some uidWord := by
        intro j uid hlookup
        exact hwords (j := j + 1) (uid := uid) (by
          simp [lookupNth?, hlookup])
      obtain ⟨restWords, hRest, hRestLen⟩ := ih hrestWords
      refine ⟨uidWord :: (⟨0⟩ : UInt256) :: restWords, ?_, ?_⟩
      · simp [attesterRevocationDataEncodedWords?, hUidWord, hRest]
      · simp [hRestLen]
        omega

theorem attesterRevocationDataValues_length (uids : List Value) :
    (attesterRevocationDataValues uids).length = uids.length := by
  induction uids with
  | nil => simp [attesterRevocationDataValues]
  | cons uid rest ih => simp [attesterRevocationDataValues, ih]

theorem attesterEncodeABIValue_revocationDataValue (uid : Value) :
    ABI.encodeABIValue? revocationRequestDataTy (attesterRevocationDataValue uid) =
      (attesterBytes32ValueWord? uid).bind
        (fun uidWord =>
          some (attesterWordsBytesList [uidWord, (⟨0⟩ : UInt256)])) := by
  cases h : attesterBytes32ValueWord? uid with
  | none =>
      simp [attesterRevocationDataValue, revocationRequestDataTy,
        ABI.encodeABIValue?, ABI.encodeABIValues?, ABI.encodeABIValuesFrom?,
        ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?,
        ABI.staticABIEncodedSizeList?, ABI.isDynamicABIType,
        attesterEncodeABIValue_bytes32_eq_bind, h]
  | some uidWord =>
      have hUidEnc : ABI.encodeABIValue? bytes32 uid =
          some (EVM.Word.toBytesBE uidWord) :=
        attesterBytes32ValueWord?_encodeABIValue h
      have hUidEnc' :
          ABI.encodeABIValue? (ABIType.elem (ElemType.bytes (31 : Fin 32))) uid =
            some (EVM.Word.toBytesBE uidWord) := by
        simpa [bytes32, bytes32Width] using hUidEnc
      have hpow : 0 < EVM.twoPow 256 := by norm_num [EVM.twoPow]
      have hword : EVM.word 0 = (⟨0⟩ : UInt256) := rfl
      simp [attesterRevocationDataValue, revocationRequestDataTy,
        ABI.encodeABIValue?, ABI.encodeABIValues?, ABI.encodeABIValuesFrom?,
        ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?,
        ABI.staticABIEncodedSizeList?, ABI.isDynamicABIType,
        bytes32, bytes32Width, uint256, uint256Int]
      rw [hUidEnc']
      simp [ABI.encodeABIWord?, hpow, hword, attesterWordsBytesList]

theorem attesterEncodeABIStaticArrayElems_revocationDataValues :
    ∀ uids : List Value,
      ABI.encodeABIStaticArrayElems? revocationRequestDataTy
          (attesterRevocationDataValues uids) =
        (attesterRevocationDataEncodedWords? uids).bind
          (fun words => some (attesterWordsBytesList words))
  | [] => by
      simp [attesterRevocationDataValues, attesterRevocationDataEncodedWords?,
        ABI.encodeABIStaticArrayElems?]
  | uid :: rest => by
      cases hUid : attesterBytes32ValueWord? uid with
      | none =>
          simp [attesterRevocationDataValues, attesterRevocationDataEncodedWords?,
            ABI.encodeABIStaticArrayElems?,
            attesterEncodeABIValue_revocationDataValue, hUid]
      | some uidWord =>
          cases hRest : attesterRevocationDataEncodedWords? rest with
          | none =>
              simp [attesterRevocationDataValues, attesterRevocationDataEncodedWords?,
                ABI.encodeABIStaticArrayElems?,
                attesterEncodeABIValue_revocationDataValue, hUid, hRest,
                attesterEncodeABIStaticArrayElems_revocationDataValues rest]
          | some restWords =>
              simp [attesterRevocationDataValues, attesterRevocationDataEncodedWords?,
                ABI.encodeABIStaticArrayElems?,
                attesterEncodeABIValue_revocationDataValue, hUid, hRest,
                attesterEncodeABIStaticArrayElems_revocationDataValues rest,
                attesterWordsBytesList, List.append_assoc]

def attesterMultiRevokeRequestEncodedWords?
    (schema : Value) (uids : List Value) : Option (List UInt256) := do
  let schemaWord <- attesterBytes32ValueWord? schema
  let dataWords <- attesterRevocationDataEncodedWords? uids
  some (schemaWord :: (⟨64⟩ : UInt256) :: UInt256.ofNat uids.length :: dataWords)

theorem attesterMultiRevokeRequestEncodedWords?_length
    {schema : Value} {uids : List Value} {words : List UInt256}
    (h : attesterMultiRevokeRequestEncodedWords? schema uids = some words) :
    words.length = 3 + 2 * uids.length := by
  simp [attesterMultiRevokeRequestEncodedWords?] at h
  cases hSchema : attesterBytes32ValueWord? schema with
  | none =>
      simp [hSchema] at h
  | some schemaWord =>
      cases hData : attesterRevocationDataEncodedWords? uids with
      | none =>
          simp [hSchema, hData] at h
      | some dataWords =>
          simp [hSchema, hData] at h
          cases h
          have hDataLen :=
            attesterRevocationDataEncodedWords?_length (uids := uids)
              (words := dataWords) hData
          simp [hDataLen]
          omega

theorem attesterMultiRevokeRequestEncodedWords?_some_of_words
    {schema : Value} {uids : List Value}
    (hschema : ∃ schemaWord, attesterBytes32ValueWord? schema = some schemaWord)
    (huids :
      ∀ {j uid}, lookupNth? uids j = some uid →
        ∃ uidWord, attesterBytes32ValueWord? uid = some uidWord) :
    ∃ words,
      attesterMultiRevokeRequestEncodedWords? schema uids = some words ∧
      words.length = 3 + 2 * uids.length := by
  rcases hschema with ⟨schemaWord, hschemaWord⟩
  obtain ⟨dataWords, hData, hDataLen⟩ :=
    attesterRevocationDataEncodedWords?_some_of_words huids
  refine ⟨schemaWord :: (⟨64⟩ : UInt256) :: UInt256.ofNat uids.length :: dataWords,
    ?_, ?_⟩
  · simp [attesterMultiRevokeRequestEncodedWords?, hschemaWord, hData]
  · simp [hDataLen]
    omega

theorem attesterEncodeABIValue_revocationDataArray (uids : List Value) :
    ABI.encodeABIValue? (.dynamicArray revocationRequestDataTy)
        (.array (attesterRevocationDataValues uids)) =
      (attesterRevocationDataEncodedWords? uids).bind
        (fun words =>
          some (attesterWordsBytesList (UInt256.ofNat uids.length :: words))) := by
  have hArray :
      ABI.encodeABIValue? (.dynamicArray revocationRequestDataTy)
          (.array (attesterRevocationDataValues uids)) =
        (ABI.encodeABIStaticArrayElems? revocationRequestDataTy
            (attesterRevocationDataValues uids)).bind
          (fun encodedElems =>
            some (ABI.natBytes (attesterRevocationDataValues uids).length ++
              encodedElems)) := by
    simp [ABI.encodeABIValue?, ABI.encodeABIArrayElems?,
      ABI.isDynamicABIType, ABI.isDynamicABITypeList, revocationRequestDataTy,
      bytes32, bytes32Width, uint256, uint256Int]
  have hElems :=
    attesterEncodeABIStaticArrayElems_revocationDataValues uids
  rw [hArray, hElems]
  cases h : attesterRevocationDataEncodedWords? uids with
  | none =>
      simp [h]
  | some words =>
      simp [h,
        attesterNatBytes_eq_toBytesBE, attesterRevocationDataValues_length,
        attesterWordBytesList, attesterWordsBytesList]

theorem attesterEncodeABIValue_multiRevokeRequestValue
    (schema : Value) (uids : List Value) :
    ABI.encodeABIValue? multiRevocationRequestTy
        (attesterMultiRevokeRequestValue schema uids) =
      (attesterMultiRevokeRequestEncodedWords? schema uids).bind
        (fun words => some (attesterWordsBytesList words)) := by
  cases hSchema : attesterBytes32ValueWord? schema with
  | none =>
      simp [attesterMultiRevokeRequestValue, multiRevocationRequestTy,
        ABI.encodeABIValue?, ABI.encodeABIValues?, ABI.encodeABIValuesFrom?,
        ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?,
        ABI.staticABIEncodedSizeList?, ABI.isDynamicABIType,
        attesterEncodeABIValue_bytes32_eq_bind,
        attesterMultiRevokeRequestEncodedWords?, hSchema]
  | some schemaWord =>
      have hSchemaEnc : ABI.encodeABIValue? bytes32 schema =
          some (EVM.Word.toBytesBE schemaWord) :=
        attesterBytes32ValueWord?_encodeABIValue hSchema
      have hSchemaEnc' :
          ABI.encodeABIValue? (ABIType.elem (ElemType.bytes (31 : Fin 32))) schema =
            some (EVM.Word.toBytesBE schemaWord) := by
        simpa [bytes32, bytes32Width] using hSchemaEnc
      cases hData : attesterRevocationDataEncodedWords? uids with
      | none =>
          simp [attesterMultiRevokeRequestValue, multiRevocationRequestTy,
            ABI.encodeABIValue?, ABI.encodeABIValues?, ABI.encodeABIValuesFrom?,
            ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?,
            ABI.staticABIEncodedSizeList?, ABI.isDynamicABIType,
            bytes32, bytes32Width, uint256, uint256Int,
            attesterEncodeABIValue_revocationDataArray,
            attesterMultiRevokeRequestEncodedWords?, hSchema, hData]
      | some dataWords =>
          have h64 : UInt256.ofNat 64 = (⟨64⟩ : UInt256) := by native_decide
          simp [attesterMultiRevokeRequestValue, multiRevocationRequestTy,
            ABI.encodeABIValue?, ABI.encodeABIValues?, ABI.encodeABIValuesFrom?,
            ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?,
            ABI.staticABIEncodedSizeList?, ABI.isDynamicABIType,
            bytes32, bytes32Width, uint256, uint256Int,
            attesterEncodeABIValue_revocationDataArray,
            attesterMultiRevokeRequestEncodedWords?, hSchema, hData]
          rw [hSchemaEnc']
          simp [attesterNatBytes_eq_toBytesBE, h64, attesterWordsBytesList,
            List.append_assoc]

def attesterMultiRevokeRequestArrayElemsWordsFrom?
    (headSize : Nat) :
    List Value → List Value → List UInt256 → List UInt256 → Option (List UInt256)
  | [], _, head, tail => some (head ++ tail)
  | _ :: _, [], head, tail => some (head ++ tail)
  | schema :: schemas, .array uids :: schemaUids, head, tail => do
      let encoded <- attesterMultiRevokeRequestEncodedWords? schema uids
      attesterMultiRevokeRequestArrayElemsWordsFrom? headSize schemas schemaUids
        (head ++ [UInt256.ofNat (headSize + 32 * tail.length)])
        (tail ++ encoded)
  | _ :: _, _ :: _, head, tail => some (head ++ tail)

def attesterMultiRevokeRequestArrayElemsWords?
    (schemas schemaUids : List Value) : Option (List UInt256) :=
  attesterMultiRevokeRequestArrayElemsWordsFrom?
    ((attesterMultiRevokeRequestValues schemas schemaUids).length * 32)
    schemas schemaUids [] []

theorem attesterMultiRevokeRequestArrayElemsWordsFrom?_some_of_words :
    ∀ (schemas schemaUids : List Value) (headSize : Nat)
      (head tail : List UInt256),
      schemaUids.length = schemas.length →
      (∀ {idx schema}, lookupNth? schemas idx = some schema →
        ∃ schemaWord, attesterBytes32ValueWord? schema = some schemaWord) →
      (∀ {idx value}, lookupNth? schemaUids idx = some value →
        ∃ uids,
          value = .array uids ∧
          (∀ {j uid}, lookupNth? uids j = some uid →
            ∃ uidWord, attesterBytes32ValueWord? uid = some uidWord)) →
      ∃ words,
        attesterMultiRevokeRequestArrayElemsWordsFrom?
          headSize schemas schemaUids head tail = some words
  | [], [], headSize, head, tail, _hlen, _hschemas, _huidss => by
      refine ⟨head ++ tail, ?_⟩
      simp [attesterMultiRevokeRequestArrayElemsWordsFrom?]
  | [], _ :: _, headSize, head, tail, hlen, _hschemas, _huidss => by
      simp at hlen
  | _ :: _, [], headSize, head, tail, hlen, _hschemas, _huidss => by
      simp at hlen
  | schema :: schemas, value :: schemaUids, headSize, head, tail, hlen,
      hschemas, huidss => by
      obtain ⟨schemaWord, hschemaWord⟩ :=
        hschemas (idx := 0) (schema := schema) (by simp [lookupNth?])
      obtain ⟨uids, hvalue, huidsWords⟩ :=
        huidss (idx := 0) (value := value) (by simp [lookupNth?])
      subst value
      have hlenTail : schemaUids.length = schemas.length := by
        simp at hlen
        exact hlen
      have hschemasTail :
          ∀ {idx schema}, lookupNth? schemas idx = some schema →
            ∃ schemaWord, attesterBytes32ValueWord? schema = some schemaWord := by
        intro idx schema hlookup
        exact hschemas (idx := idx + 1) (schema := schema) (by
          simp [lookupNth?, hlookup])
      have huidssTail :
          ∀ {idx value}, lookupNth? schemaUids idx = some value →
            ∃ uids,
              value = .array uids ∧
              (∀ {j uid}, lookupNth? uids j = some uid →
                ∃ uidWord, attesterBytes32ValueWord? uid = some uidWord) := by
        intro idx value hlookup
        exact huidss (idx := idx + 1) (value := value) (by
          simp [lookupNth?, hlookup])
      obtain ⟨encoded, hencoded, _hencodedLen⟩ :=
        attesterMultiRevokeRequestEncodedWords?_some_of_words
          (schema := schema) (uids := uids)
          ⟨schemaWord, hschemaWord⟩ huidsWords
      obtain ⟨words, hwords⟩ :=
        attesterMultiRevokeRequestArrayElemsWordsFrom?_some_of_words
          schemas schemaUids headSize
          (head ++ [UInt256.ofNat (headSize + 32 * tail.length)])
          (tail ++ encoded) hlenTail hschemasTail huidssTail
      refine ⟨words, ?_⟩
      simp [attesterMultiRevokeRequestArrayElemsWordsFrom?, hencoded, hwords]

theorem attesterMultiRevokeRequestArrayElemsWords?_some_of_words
    {schemas schemaUids : List Value}
    (hlen : schemaUids.length = schemas.length)
    (hschemas :
      ∀ {idx schema}, lookupNth? schemas idx = some schema →
        ∃ schemaWord, attesterBytes32ValueWord? schema = some schemaWord)
    (huidss :
      ∀ {idx value}, lookupNth? schemaUids idx = some value →
        ∃ uids,
          value = .array uids ∧
          (∀ {j uid}, lookupNth? uids j = some uid →
            ∃ uidWord, attesterBytes32ValueWord? uid = some uidWord)) :
    ∃ words,
      attesterMultiRevokeRequestArrayElemsWords? schemas schemaUids = some words := by
  exact
    attesterMultiRevokeRequestArrayElemsWordsFrom?_some_of_words
      schemas schemaUids
      ((attesterMultiRevokeRequestValues schemas schemaUids).length * 32)
      [] [] hlen hschemas huidss

theorem attesterMultiRevokeRequestArrayElemsWords?_some_of_memoryLayout
    {schemas schemaUids : List Value} {mem : ByteArray} {aw outerBase : UInt256}
    (hlen : schemaUids.length = schemas.length)
    (huidssShape :
      ∀ {idx value}, lookupNth? schemaUids idx = some value →
        ∃ uids, value = .array uids)
    (hlayout :
      AttesterMultiRevokeRequestsMemoryLayout
        schemas schemaUids schemas.length mem aw outerBase) :
    ∃ words,
      attesterMultiRevokeRequestArrayElemsWords? schemas schemaUids = some words := by
  have hschemas :
      ∀ {idx schema}, lookupNth? schemas idx = some schema →
        ∃ schemaWord, attesterBytes32ValueWord? schema = some schemaWord := by
    intro idx schema hschema
    have hidxSchemas : idx < schemas.length := lookupNth?_some_length hschema
    have hidxSchemaUids : idx < schemaUids.length := by omega
    obtain ⟨value, hvalue⟩ :=
      attesterLookupNth?_exists (xs := schemaUids) (i := idx) hidxSchemaUids
    rcases huidssShape hvalue with ⟨uids, hvalueArray⟩
    have huids : lookupNth? schemaUids idx = some (.array uids) := by
      simpa [hvalueArray] using hvalue
    rcases hlayout hidxSchemas hschema huids with
      ⟨schemaWord, hschemaWord, _hschemaMload, _hlenMload, _huids⟩
    exact ⟨schemaWord, hschemaWord⟩
  have huidss :
      ∀ {idx value}, lookupNth? schemaUids idx = some value →
        ∃ uids,
          value = .array uids ∧
          (∀ {j uid}, lookupNth? uids j = some uid →
            ∃ uidWord, attesterBytes32ValueWord? uid = some uidWord) := by
    intro idx value hvalue
    have hidxSchemaUids : idx < schemaUids.length := lookupNth?_some_length hvalue
    have hidxSchemas : idx < schemas.length := by omega
    obtain ⟨schema, hschema⟩ :=
      attesterLookupNth?_exists (xs := schemas) (i := idx) hidxSchemas
    rcases huidssShape hvalue with ⟨uids, hvalueArray⟩
    have huids : lookupNth? schemaUids idx = some (.array uids) := by
      simpa [hvalueArray] using hvalue
    rcases hlayout hidxSchemas hschema huids with
      ⟨_schemaWord, _hschemaWord, _hschemaMload, _hlenMload, huidsLayout⟩
    refine ⟨uids, hvalueArray, ?_⟩
    intro j uid huid
    rcases huidsLayout huid with
      ⟨uidWord, huidWord, _huidMload, _hextraMload⟩
    exact ⟨uidWord, huidWord⟩
  exact
    attesterMultiRevokeRequestArrayElemsWords?_some_of_words
      hlen hschemas huidss

theorem attesterMultiRevokeRequestArrayElemsWords?_some_of_readLayoutBounded
    {schemas schemaUids : List Value} {mem : ByteArray}
    {outerBase : UInt256} {contentLo bound : Nat}
    (hlen : schemaUids.length = schemas.length)
    (huidssShape :
      ∀ {idx value}, lookupNth? schemaUids idx = some value →
        ∃ uids, value = .array uids)
    (hlayout :
      AttesterMultiRevokeRequestsReadLayoutBounded
        schemas schemaUids schemas.length mem outerBase contentLo bound) :
    ∃ words,
      attesterMultiRevokeRequestArrayElemsWords? schemas schemaUids = some words := by
  have hschemas :
      ∀ {idx schema}, lookupNth? schemas idx = some schema →
        ∃ schemaWord, attesterBytes32ValueWord? schema = some schemaWord := by
    intro idx schema hschema
    have hidxSchemas : idx < schemas.length := lookupNth?_some_length hschema
    have hidxSchemaUids : idx < schemaUids.length := by omega
    obtain ⟨value, hvalue⟩ :=
      attesterLookupNth?_exists (xs := schemaUids) (i := idx) hidxSchemaUids
    rcases huidssShape hvalue with ⟨uids, hvalueArray⟩
    have huids : lookupNth? schemaUids idx = some (.array uids) := by
      simpa [hvalueArray] using hvalue
    rcases hlayout hidxSchemas hschema huids with
      ⟨schemaWord, _reqPtr, _dataPtr, hschemaWord, _hslot64, _hslotBound,
        _hslotMem, _hslotRead, _hreqLo, _hreqBound, _hreqMem, _hreq32Lo,
        _hreq32Bound, _hreq32Mem, _hschemaRead, _hdataPtrRead, _hdataLo,
        _hdataBound, _hdataMem, _hdataRead, _huidsRead⟩
    exact ⟨schemaWord, hschemaWord⟩
  have huidss :
      ∀ {idx value}, lookupNth? schemaUids idx = some value →
        ∃ uids,
          value = .array uids ∧
          (∀ {j uid}, lookupNth? uids j = some uid →
            ∃ uidWord, attesterBytes32ValueWord? uid = some uidWord) := by
    intro idx value hvalue
    have hidxSchemaUids : idx < schemaUids.length := lookupNth?_some_length hvalue
    have hidxSchemas : idx < schemas.length := by omega
    obtain ⟨schema, hschema⟩ :=
      attesterLookupNth?_exists (xs := schemas) (i := idx) hidxSchemas
    rcases huidssShape hvalue with ⟨uids, hvalueArray⟩
    have huids : lookupNth? schemaUids idx = some (.array uids) := by
      simpa [hvalueArray] using hvalue
    rcases hlayout hidxSchemas hschema huids with
      ⟨_schemaWord, _reqPtr, _dataPtr, _hschemaWord, _hslot64, _hslotBound,
        _hslotMem, _hslotRead, _hreqLo, _hreqBound, _hreqMem, _hreq32Lo,
        _hreq32Bound, _hreq32Mem, _hschemaRead, _hdataPtrRead, _hdataLo,
        _hdataBound, _hdataMem, _hdataRead, huidsRead⟩
    refine ⟨uids, hvalueArray, ?_⟩
    intro j uid huid
    rcases huidsRead huid with
      ⟨uidWord, _elemPtr, huidWord, _helemSlotLo, _helemSlotBound,
        _helemSlotMem, _helemSlotRead, _helemPtrLo, _helemPtrBound,
        _helemPtrMem, _helemPtr32Lo, _helemPtr32Bound, _helemPtr32Mem,
        _helemRead, _helemExtraRead⟩
    exact ⟨uidWord, huidWord⟩
  exact
    attesterMultiRevokeRequestArrayElemsWords?_some_of_words
      hlen hschemas huidss

theorem AttesterMultiRevokeRequestsReadLayoutBounded.to_memoryLayout
    {schemas schemaUids : List Value} {i : Nat}
    {mem : ByteArray} {aw outerBase : UInt256} {contentLo bound : Nat}
    (hactive :
      ∀ {off : UInt256}, off.toNat + 32 ≤ mem.size →
        ¬ off ≥ aw * (⟨32⟩ : UInt256))
    (hread :
      AttesterMultiRevokeRequestsReadLayoutBounded
        schemas schemaUids i mem outerBase contentLo bound) :
    AttesterMultiRevokeRequestsMemoryLayout schemas schemaUids i mem aw outerBase := by
  intro idx hidx
  exact
    AttesterMultiRevokeRequestReadLayoutAt.to_mload hactive
      (AttesterMultiRevokeRequestReadLayoutAtBounded.to_readLayout (hread hidx))

theorem AttesterReadPreservedBefore.trans
    {mem₀ mem₁ mem₂ : ByteArray} {bound : Nat}
    (h₀₁ : AttesterReadPreservedBefore mem₀ mem₁ bound)
    (h₁₂ : AttesterReadPreservedBefore mem₁ mem₂ bound) :
    AttesterReadPreservedBefore mem₀ mem₂ bound := by
  intro read word hmem hread hread64 hbefore
  have hmid := h₀₁ hmem hread hread64 hbefore
  exact h₁₂ hmid.1 hmid.2 hread64 hbefore

theorem AttesterReadPreservedBefore.writeWord_at_or_above
    {mem : ByteArray} {off bound : Nat} {word : UInt256}
    (hbound : bound ≤ off) :
    AttesterReadPreservedBefore mem
      (Reasoning.Theory.writeWord mem off word) bound := by
  intro read w hmem hread _hread64 hbefore
  constructor
  · exact le_trans hmem (attesterWriteWord_size_ge_nat mem off word)
  · rw [attesterWriteWord_read_preserved_len_nat mem off read 32 word
      (Or.inl ⟨le_trans hbefore hbound, hmem⟩) (by norm_num) (by norm_num),
      hread]

theorem AttesterMultiRevokeRequestReadLayoutAtBounded.to_mload_bounded
    {schemas schemaUids : List Value} {mem : ByteArray}
    {aw outerBase : UInt256} {contentLo bound idx : Nat}
    (hcontentLo64 : 64 + 32 ≤ contentLo)
    (hactive :
      ∀ {off : UInt256}, 64 + 32 ≤ off.toNat → off.toNat + 32 ≤ bound →
        ¬ off ≥ aw * (⟨32⟩ : UInt256))
    (hread :
      AttesterMultiRevokeRequestReadLayoutAtBounded
        schemas schemaUids mem outerBase contentLo bound idx) :
    AttesterMultiRevokeRequestMemoryLayoutAt schemas schemaUids mem aw outerBase idx := by
  intro schema uids hschema huids
  rcases hread hschema huids with
    ⟨schemaWord, reqPtr, dataPtr, hschemaWord, hslot64, hslotBound, hslotMem,
      hslotRead, hreqLo, hreqBound, hreqMem, hreq32Lo, hreq32Bound, hreq32Mem,
      hschemaRead, hdataPtrRead, hdataLo, hdataBound, hdataMem, hdataRead,
      huidsRead⟩
  let slot := attesterMultiRevokePostCopyOuterSlotWord outerBase (UInt256.ofNat idx)
  have hreqMload :
      attesterMultiRevokeRequestPtr mem aw outerBase idx = reqPtr := by
    dsimp [attesterMultiRevokeRequestPtr, slot] at hslotMem hslotRead ⊢
    exact attesterMloadWord_of_readWithPadding hslotMem
      (hactive (off := slot) hslot64 hslotBound) hslotRead
  have hreq64 : 64 + 32 ≤ reqPtr.toNat := le_trans hcontentLo64 hreqLo
  have hschemaMload :
      attesterMloadWord mem aw
          (attesterMultiRevokeRequestPtr mem aw outerBase idx) =
        schemaWord := by
    rw [hreqMload]
    exact attesterMloadWord_of_readWithPadding hreqMem
      (hactive (off := reqPtr) hreq64 hreqBound) hschemaRead
  have hreq32_64 : 64 + 32 ≤ ((⟨32⟩ : UInt256) + reqPtr).toNat :=
    le_trans hcontentLo64 hreq32Lo
  have hdataPtrMload :
      attesterMultiRevokeRequestDataPtr mem aw outerBase idx = dataPtr := by
    dsimp [attesterMultiRevokeRequestDataPtr]
    rw [hreqMload]
    exact attesterMloadWord_of_readWithPadding hreq32Mem
      (hactive (off := (⟨32⟩ : UInt256) + reqPtr) hreq32_64 hreq32Bound)
      hdataPtrRead
  have hdata64 : 64 + 32 ≤ dataPtr.toNat := le_trans hcontentLo64 hdataLo
  have hdataLenMload :
      attesterMloadWord mem aw
          (attesterMultiRevokeRequestDataPtr mem aw outerBase idx) =
        UInt256.ofNat uids.length := by
    rw [hdataPtrMload]
    exact attesterMloadWord_of_readWithPadding hdataMem
      (hactive (off := dataPtr) hdata64 hdataBound) hdataRead
  refine ⟨schemaWord, hschemaWord, hschemaMload, hdataLenMload, ?_⟩
  intro j uid huid
  rcases huidsRead huid with
    ⟨uidWord, elemPtr, huidWord, helemSlotLo, helemSlotBound, helemSlotMem,
      helemSlotRead, helemPtrLo, helemPtrBound, helemPtrMem, helemPtr32Lo,
      helemPtr32Bound, helemPtr32Mem, helemRead, helemExtraRead⟩
  let elemSlot := (⟨32⟩ : UInt256) +
    UInt256.mul (⟨32⟩ : UInt256) (UInt256.ofNat j) + dataPtr
  have helemSlot64 : 64 + 32 ≤ elemSlot.toNat :=
    le_trans hcontentLo64 helemSlotLo
  have helemPtrMload :
      attesterMultiRevokeRequestDataElemPtr mem aw outerBase idx j = elemPtr := by
    dsimp [attesterMultiRevokeRequestDataElemPtr, elemSlot]
    rw [hdataPtrMload]
    exact attesterMloadWord_of_readWithPadding helemSlotMem
      (hactive (off := elemSlot) helemSlot64 helemSlotBound) helemSlotRead
  have helemPtr64 : 64 + 32 ≤ elemPtr.toNat :=
    le_trans hcontentLo64 helemPtrLo
  have huidMload :
      attesterMloadWord mem aw
          (attesterMultiRevokeRequestDataElemPtr mem aw outerBase idx j) =
        uidWord := by
    rw [helemPtrMload]
    exact attesterMloadWord_of_readWithPadding helemPtrMem
      (hactive (off := elemPtr) helemPtr64 helemPtrBound) helemRead
  have helemPtr32_64 : 64 + 32 ≤ ((⟨32⟩ : UInt256) + elemPtr).toNat :=
    le_trans hcontentLo64 helemPtr32Lo
  have hextraMload :
      attesterMloadWord mem aw
          ((⟨32⟩ : UInt256) +
            attesterMultiRevokeRequestDataElemPtr mem aw outerBase idx j) =
        (⟨0⟩ : UInt256) := by
    rw [helemPtrMload]
    exact attesterMloadWord_of_readWithPadding helemPtr32Mem
      (hactive (off := (⟨32⟩ : UInt256) + elemPtr) helemPtr32_64
        helemPtr32Bound) helemExtraRead
  exact ⟨uidWord, huidWord, huidMload, hextraMload⟩

theorem AttesterMultiRevokeRequestsReadLayoutBounded.to_memoryLayout_bounded
    {schemas schemaUids : List Value} {i : Nat}
    {mem : ByteArray} {aw outerBase : UInt256} {contentLo bound : Nat}
    (hcontentLo64 : 64 + 32 ≤ contentLo)
    (hactive :
      ∀ {off : UInt256}, 64 + 32 ≤ off.toNat → off.toNat + 32 ≤ bound →
        ¬ off ≥ aw * (⟨32⟩ : UInt256))
    (hread :
      AttesterMultiRevokeRequestsReadLayoutBounded
        schemas schemaUids i mem outerBase contentLo bound) :
    AttesterMultiRevokeRequestsMemoryLayout schemas schemaUids i mem aw outerBase := by
  intro idx hidx
  exact
    AttesterMultiRevokeRequestReadLayoutAtBounded.to_mload_bounded
      hcontentLo64 hactive (hread hidx)

theorem AttesterMultiRevokeRequestReadLayoutAtBounded.preserve_before
    {schemas schemaUids : List Value}
    {mem mem' : ByteArray} {outerBase : UInt256}
    {contentLo bound idx : Nat}
    (hcontentLo64 : 64 + 32 ≤ contentLo)
    (hpres : AttesterReadPreservedBefore mem mem' bound)
    (h :
      AttesterMultiRevokeRequestReadLayoutAtBounded
        schemas schemaUids mem outerBase contentLo bound idx) :
    AttesterMultiRevokeRequestReadLayoutAtBounded
      schemas schemaUids mem' outerBase contentLo bound idx := by
  intro schema uids hschema huids
  rcases h hschema huids with
    ⟨schemaWord, reqPtr, dataPtr, hschemaWord, hslot64, hslotBound, hslotMem,
      hslotRead, hreqLo, hreqBound, hreqMem, hreq32Lo, hreq32Bound, hreq32Mem,
      hschemaRead, hdataPtrRead, hdataLo, hdataBound, hdataMem, hdataRead,
      huidsRead⟩
  have hslotPres := hpres hslotMem hslotRead hslot64 hslotBound
  have hreq64 : 64 + 32 ≤ reqPtr.toNat := le_trans hcontentLo64 hreqLo
  have hreqPres := hpres hreqMem hschemaRead hreq64 hreqBound
  have hreq32_64 : 64 + 32 ≤ ((⟨32⟩ : UInt256) + reqPtr).toNat :=
    le_trans hcontentLo64 hreq32Lo
  have hreq32Pres := hpres hreq32Mem hdataPtrRead hreq32_64 hreq32Bound
  have hdata64 : 64 + 32 ≤ dataPtr.toNat := le_trans hcontentLo64 hdataLo
  have hdataPres := hpres hdataMem hdataRead hdata64 hdataBound
  refine ⟨schemaWord, reqPtr, dataPtr, hschemaWord, hslot64, hslotBound,
    hslotPres.1, hslotPres.2, hreqLo, hreqBound, hreqPres.1, hreq32Lo,
    hreq32Bound, hreq32Pres.1, hreqPres.2, hreq32Pres.2, hdataLo,
    hdataBound, hdataPres.1, hdataPres.2, ?_⟩
  intro j uid huid
  rcases huidsRead huid with
    ⟨uidWord, elemPtr, huidWord, helemSlotLo, helemSlotBound, helemSlotMem,
      helemSlotRead, helemPtrLo, helemPtrBound, helemPtrMem, helemPtr32Lo,
      helemPtr32Bound, helemPtr32Mem, helemRead, helemExtraRead⟩
  let elemSlot := (⟨32⟩ : UInt256) +
    UInt256.mul (⟨32⟩ : UInt256) (UInt256.ofNat j) + dataPtr
  have helemSlot64 : 64 + 32 ≤ elemSlot.toNat :=
    le_trans hcontentLo64 helemSlotLo
  have helemSlotPres :=
    hpres helemSlotMem helemSlotRead helemSlot64 helemSlotBound
  have helemPtr64 : 64 + 32 ≤ elemPtr.toNat :=
    le_trans hcontentLo64 helemPtrLo
  have helemPtrPres := hpres helemPtrMem helemRead helemPtr64 helemPtrBound
  have helemPtr32_64 : 64 + 32 ≤ ((⟨32⟩ : UInt256) + elemPtr).toNat :=
    le_trans hcontentLo64 helemPtr32Lo
  have helemPtr32Pres :=
    hpres helemPtr32Mem helemExtraRead helemPtr32_64 helemPtr32Bound
  exact ⟨uidWord, elemPtr, huidWord, helemSlotLo, helemSlotBound,
    helemSlotPres.1, helemSlotPres.2, helemPtrLo, helemPtrBound,
    helemPtrPres.1, helemPtr32Lo, helemPtr32Bound, helemPtr32Pres.1,
    helemPtrPres.2, helemPtr32Pres.2⟩

theorem AttesterMultiRevokeRequestsReadLayoutBounded.preserve_before
    {schemas schemaUids : List Value} {i : Nat}
    {mem mem' : ByteArray} {outerBase : UInt256} {contentLo bound : Nat}
    (hcontentLo64 : 64 + 32 ≤ contentLo)
    (hpres : AttesterReadPreservedBefore mem mem' bound)
    (h :
      AttesterMultiRevokeRequestsReadLayoutBounded
        schemas schemaUids i mem outerBase contentLo bound) :
    AttesterMultiRevokeRequestsReadLayoutBounded
      schemas schemaUids i mem' outerBase contentLo bound := by
  intro idx hidx
  exact
    AttesterMultiRevokeRequestReadLayoutAtBounded.preserve_before
      hcontentLo64 hpres (h hidx)

set_option maxHeartbeats 1000000 in
theorem attesterEncodeABIDynamicArrayElemsFrom_multiRevokeRequestValues :
    ∀ (schemas schemaUids : List Value) (headSize : Nat)
      (head tail : List UInt256),
      ABI.encodeABIDynamicArrayElemsFrom? multiRevocationRequestTy
          (attesterMultiRevokeRequestValues schemas schemaUids) headSize
          (attesterWordsBytesList head) (attesterWordsBytesList tail) =
        (attesterMultiRevokeRequestArrayElemsWordsFrom?
            headSize schemas schemaUids head tail).bind
          (fun words => some (attesterWordsBytesList words))
  | [], [], headSize, head, tail => by
      simp [attesterMultiRevokeRequestValues,
        attesterMultiRevokeRequestArrayElemsWordsFrom?,
        ABI.encodeABIDynamicArrayElemsFrom?, attesterWordsBytesList_append]
  | [], _ :: _, headSize, head, tail => by
      simp [attesterMultiRevokeRequestValues,
        attesterMultiRevokeRequestArrayElemsWordsFrom?,
        ABI.encodeABIDynamicArrayElemsFrom?, attesterWordsBytesList_append]
  | _ :: _, [], headSize, head, tail => by
      simp [attesterMultiRevokeRequestValues,
        attesterMultiRevokeRequestArrayElemsWordsFrom?,
        ABI.encodeABIDynamicArrayElemsFrom?, attesterWordsBytesList_append]
  | schema :: schemas, value :: schemaUids, headSize, head, tail => by
      cases value with
      | array uids =>
          cases hReq : attesterMultiRevokeRequestEncodedWords? schema uids with
          | none =>
              simp [attesterMultiRevokeRequestValues,
                attesterMultiRevokeRequestArrayElemsWordsFrom?,
                ABI.encodeABIDynamicArrayElemsFrom?,
                attesterEncodeABIValue_multiRevokeRequestValue, hReq]
          | some encoded =>
              have htailLen :
                  (attesterWordsBytesList tail).length = 32 * tail.length :=
                attesterWordsBytesList_length tail
              have hOffset :
                  headSize + (attesterWordsBytesList tail).length =
                    headSize + 32 * tail.length := by
                rw [htailLen]
              simp [attesterMultiRevokeRequestValues,
                attesterMultiRevokeRequestArrayElemsWordsFrom?,
                ABI.encodeABIDynamicArrayElemsFrom?,
                attesterEncodeABIValue_multiRevokeRequestValue, hReq,
                hOffset, attesterNatBytes_eq_toBytesBE]
              simpa [attesterWordBytesList, attesterWordsBytesList,
                attesterWordsBytesList_append, List.append_assoc] using
                attesterEncodeABIDynamicArrayElemsFrom_multiRevokeRequestValues
                  schemas schemaUids headSize
                  (head ++ [UInt256.ofNat (headSize + 32 * tail.length)])
                  (tail ++ encoded)
      | _ =>
          simp [attesterMultiRevokeRequestValues,
            attesterMultiRevokeRequestArrayElemsWordsFrom?,
            ABI.encodeABIDynamicArrayElemsFrom?, attesterWordsBytesList_append]

theorem attesterEncodeABIArrayElems_multiRevokeRequestValues
    (schemas schemaUids : List Value) :
    ABI.encodeABIArrayElems? multiRevocationRequestTy
        (attesterMultiRevokeRequestValues schemas schemaUids) =
      (attesterMultiRevokeRequestArrayElemsWords? schemas schemaUids).bind
        (fun words => some (attesterWordsBytesList words)) := by
  have hdyn :
      ABI.isDynamicABIType multiRevocationRequestTy = true := by
    simp [multiRevocationRequestTy, revocationRequestDataTy, bytes32,
      bytes32Width, uint256, uint256Int, ABI.isDynamicABIType,
      ABI.isDynamicABITypeList]
  rw [show
      ABI.encodeABIArrayElems? multiRevocationRequestTy
          (attesterMultiRevokeRequestValues schemas schemaUids) =
        ABI.encodeABIDynamicArrayElemsFrom? multiRevocationRequestTy
          (attesterMultiRevokeRequestValues schemas schemaUids)
          ((attesterMultiRevokeRequestValues schemas schemaUids).length * 32)
          [] [] by
    simp [ABI.encodeABIArrayElems?, hdyn]]
  simpa [attesterMultiRevokeRequestArrayElemsWords?] using
    attesterEncodeABIDynamicArrayElemsFrom_multiRevokeRequestValues
      schemas schemaUids
      ((attesterMultiRevokeRequestValues schemas schemaUids).length * 32) [] []

theorem attesterEncodeABIValue_multiRevokeRequestArray
    (schemas schemaUids : List Value) :
    ABI.encodeABIValue? (.dynamicArray multiRevocationRequestTy)
        (.array (attesterMultiRevokeRequestValues schemas schemaUids)) =
      (attesterMultiRevokeRequestArrayElemsWords? schemas schemaUids).bind
        (fun words =>
          some (attesterWordsBytesList
            (UInt256.ofNat
              (attesterMultiRevokeRequestValues schemas schemaUids).length ::
              words))) := by
  have hElems := attesterEncodeABIArrayElems_multiRevokeRequestValues schemas schemaUids
  rw [show
      ABI.encodeABIValue? (.dynamicArray multiRevocationRequestTy)
          (.array (attesterMultiRevokeRequestValues schemas schemaUids)) =
        (ABI.encodeABIArrayElems? multiRevocationRequestTy
            (attesterMultiRevokeRequestValues schemas schemaUids)).bind
          (fun encodedElems =>
            some (ABI.natBytes
              (attesterMultiRevokeRequestValues schemas schemaUids).length ++
              encodedElems)) by
    simp [ABI.encodeABIValue?]]
  rw [hElems]
  cases h : attesterMultiRevokeRequestArrayElemsWords? schemas schemaUids with
  | none =>
      simp
  | some words =>
      simp [attesterNatBytes_eq_toBytesBE, attesterWordBytesList,
        attesterWordsBytesList]

theorem attesterEncodeABIValues_multiRevokeRequestArray
    (schemas schemaUids : List Value) :
    ABI.encodeABIValues? [multiRevocationRequestArrayTy]
        [.array (attesterMultiRevokeRequestValues schemas schemaUids)] =
      (attesterMultiRevokeRequestArrayElemsWords? schemas schemaUids).bind
        (fun words =>
          some (attesterWordsBytesList
            [UInt256.ofNat 32,
              UInt256.ofNat
                (attesterMultiRevokeRequestValues schemas schemaUids).length] ++
            attesterWordsBytesList words)) := by
  rw [show
      ABI.encodeABIValues? [multiRevocationRequestArrayTy]
          [.array (attesterMultiRevokeRequestValues schemas schemaUids)] =
        (ABI.encodeABIArrayElems? multiRevocationRequestTy
            (attesterMultiRevokeRequestValues schemas schemaUids)).bind
          (fun encoded =>
            some (ABI.natBytes 32 ++
              (ABI.natBytes
                (attesterMultiRevokeRequestValues schemas schemaUids).length ++
                encoded))) by
    simpa [multiRevocationRequestArrayTy] using
      (attesterEncodeABIValues_single_dynArray
        (elemTy := multiRevocationRequestTy)
        (vs := attesterMultiRevokeRequestValues schemas schemaUids))]
  have hElems := attesterEncodeABIArrayElems_multiRevokeRequestValues schemas schemaUids
  simp [multiRevocationRequestArrayTy] at hElems ⊢
  rw [hElems]
  cases h : attesterMultiRevokeRequestArrayElemsWords? schemas schemaUids with
  | none =>
      simp
  | some words =>
      simp [attesterNatBytes_eq_toBytesBE, attesterWordBytesList,
        attesterWordsBytesList, List.append_assoc]

theorem attesterExternalABIEncode_multiRevokeRequestArray
    (v : AttesterImmutables) (schemas schemaUids : List Value) :
    (config v).externalABI.encode? "multiRevoke"
        [.array (attesterMultiRevokeRequestValues schemas schemaUids)] =
      (attesterMultiRevokeRequestArrayElemsWords? schemas schemaUids).bind
        (fun words =>
          some (multiRevokeSelector ++
            (attesterWordsBytesList
              [UInt256.ofNat 32,
                UInt256.ofNat
                  (attesterMultiRevokeRequestValues schemas schemaUids).length] ++
              attesterWordsBytesList words).toByteArray)) := by
  simp [config, attesterExternalABI, ABI.encodeCallWithSelector?]
  rw [attesterEncodeABIValues_multiRevokeRequestArray]
  cases h : attesterMultiRevokeRequestArrayElemsWords? schemas schemaUids with
  | none =>
      simp [h]
  | some words =>
      simp [h]

end Benchmarks.EAS.Attester
