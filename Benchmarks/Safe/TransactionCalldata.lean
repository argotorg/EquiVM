import Benchmarks.Safe.DynamicCalldata
import Benchmarks.Safe.TransactionArguments

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

abbrev transactionCalldataTypes : List ABIType :=
  [abiAddress, abiUInt256, .bytes, abiUInt8, abiUInt256, abiUInt256, abiUInt256,
    abiAddress, abiAddress, abiUInt256]

abbrev transactionCalldataNames : List Ident :=
  ["to", "value", "data", "operation", "safeTxGas", "baseGas", "gasPrice",
    "gasToken", "refundReceiver", "_nonce"]

def transactionFromCalldata (cd : ByteArray) (payload : ByteArray) : SafeTransaction :=
  { target := AccountAddress.ofNat (calldataWord cd 4).toNat
    value := calldataWord cd 36
    payload := payload
    operation := calldataWord cd 100
    safeTxGas := calldataWord cd 132
    baseGas := calldataWord cd 164
    gasPrice := calldataWord cd 196
    gasToken := AccountAddress.ofNat (calldataWord cd 228).toNat
    refundReceiver := AccountAddress.ofNat (calldataWord cd 260).toNat
    nonce := calldataWord cd 292 }

def transactionCalldataTail (cd : ByteArray) : Option Store := do
  if ¬(calldataWord cd 4).toNat < EVM.addressModulus then none else
  let off := (calldataWord cd 68).toNat
  if solcMaxU64 < off then none else
  let len ← readNat? (cd.toList.drop 4) off
  if solcMaxU64 < len then none else
  let payload ← readBytes? (cd.toList.drop 4) (off + 32) len
  if ¬(calldataWord cd 100).toNat < 256 then none else
  if ¬(calldataWord cd 228).toNat < EVM.addressModulus then none else
  if ¬(calldataWord cd 260).toNat < EVM.addressModulus then none else
  some (transactionArgs (transactionFromCalldata cd ⟨payload.toArray⟩))

set_option maxRecDepth 5000 in
theorem decodeTransactionCalldataCore {cd : ByteArray}
    (hh : 324 ≤ cd.size) (hs : cd.size < 2 ^ 255) :
    decodeCalldata transactionCalldataNames transactionCalldataTypes cd =
      transactionCalldataTail cd := by
  rw [decodeDynamicCalldata (headSize := 320) (by omega) (by decide)
    (by simp [abiTupleHeadSize?, staticABIEncodedSize?, isDynamicABIType, bind]),
    if_neg (by omega), if_neg (by omega)]
  have ha := decodeAddressCalldata (cd := cd) 0 (by omega)
  have hv := decodeUint256Calldata (cd := cd) 32 (by omega)
  have ho := decodeUint8Calldata (cd := cd) 96 (by omega)
  have hsafe := decodeUint256Calldata (cd := cd) 128 (by omega)
  have hbase := decodeUint256Calldata (cd := cd) 160 (by omega)
  have hprice := decodeUint256Calldata (cd := cd) 192 (by omega)
  have hgas := decodeAddressCalldata (cd := cd) 224 (by omega)
  have href := decodeAddressCalldata (cd := cd) 256 (by omega)
  have hnonce := decodeUint256Calldata (cd := cd) 288 hh
  have hn64 := readNat_drop4_at_eq_calldataWord (cd := cd) 64 (by omega)
  rw [decodeABIValues?]
  simp only [Option.bind_some, Option.bind_none, isDynamicABIType, staticABIEncodedSize?, bind,
    Bool.false_eq_true, if_false, Nat.zero_add, Nat.add_zero]
  rw [ha]
  unfold transactionCalldataTail
  by_cases hc : (calldataWord cd 4).toNat < EVM.addressModulus
  swap
  · simp only [Option.bind_some, Option.bind_none, hc, not_false_eq_true, if_true, if_false]
  simp only [Option.bind_some, Option.bind_none, hc, not_true_eq_false, if_false, if_true]
  rw [decodeABIValues?]
  simp only [Option.bind_some, Option.bind_none, isDynamicABIType, staticABIEncodedSize?, bind,
    Bool.false_eq_true, if_false, Nat.zero_add, if_true]
  rw [hv]
  simp only [Option.bind_some, Option.bind_none, bind, if_true]
  rw [decodeABIValues?]
  simp only [Option.bind_some, Option.bind_none, isDynamicABIType, if_true, Nat.zero_add,
    bind, solcMaxLen_modern]
  rw [hn64]
  generalize hoffset : (calldataWord cd 68).toNat = offset at *
  simp only [Option.bind_some, Option.bind_none, bind]
  by_cases hoff : solcMaxU64 < offset
  · simp only [Option.bind_some, Option.bind_none, hoff, if_true]
  simp only [Option.bind_some, Option.bind_none, hoff, if_false]
  rw [decodeABIValue?]
  simp only [Option.bind_some, Option.bind_none, solcMaxLen_modern, bind]
  cases hn : readNat? (cd.toList.drop 4) offset with
  | none => rfl
  | some len =>
    simp only [Option.bind_some, Option.bind_none, ]
    by_cases hlen : solcMaxU64 < len
    · simp only [Option.bind_some, Option.bind_none, hlen, if_true]
    simp only [Option.bind_some, Option.bind_none, hlen, if_false]
    cases hp : readBytes? (cd.toList.drop 4) (offset + 32) len with
    | none => rfl
    | some payload =>
      simp only [Option.bind_some, Option.bind_none, bind]
      rw [decodeABIValues?]
      simp only [Option.bind_some, Option.bind_none, isDynamicABIType, staticABIEncodedSize?, bind,
        Bool.false_eq_true, if_false, Nat.zero_add]
      rw [ho]
      by_cases hop : (calldataWord cd 100).toNat < 256
      swap
      · simp only [Option.bind_some, Option.bind_none, hop, ↓reduceIte, not_false_eq_true, bind]
      simp only [Option.bind_some, Option.bind_none, hop, ↓reduceIte, not_true_eq_false, bind]
      rw [decodeABIValues?]
      simp only [Option.bind_some, Option.bind_none, isDynamicABIType, staticABIEncodedSize?, bind,
        Bool.false_eq_true, if_false, Nat.zero_add, if_true]
      rw [hsafe]
      simp only [Option.bind_some, Option.bind_none, bind, if_true]
      rw [decodeABIValues?]
      simp only [Option.bind_some, Option.bind_none, isDynamicABIType, staticABIEncodedSize?, bind,
        Bool.false_eq_true, if_false, Nat.zero_add, if_true]
      rw [hbase]
      simp only [Option.bind_some, Option.bind_none, bind, if_true]
      rw [decodeABIValues?]
      simp only [Option.bind_some, Option.bind_none, isDynamicABIType, staticABIEncodedSize?, bind,
        Bool.false_eq_true, if_false, Nat.zero_add, if_true]
      rw [hprice]
      simp only [Option.bind_some, Option.bind_none, bind, if_true]
      rw [decodeABIValues?]
      simp only [Option.bind_some, Option.bind_none, isDynamicABIType, staticABIEncodedSize?, bind,
        Bool.false_eq_true, if_false, Nat.zero_add]
      rw [hgas]
      by_cases hgc : (calldataWord cd 228).toNat < EVM.addressModulus
      swap
      · simp only [Option.bind_some, Option.bind_none, hgc, ↓reduceIte, not_false_eq_true, bind]
      simp only [Option.bind_some, Option.bind_none, hgc, ↓reduceIte, not_true_eq_false, bind]
      rw [decodeABIValues?]
      simp only [Option.bind_some, Option.bind_none, isDynamicABIType, staticABIEncodedSize?, bind,
        Bool.false_eq_true, if_false, Nat.zero_add]
      rw [href]
      by_cases hrc : (calldataWord cd 260).toNat < EVM.addressModulus
      swap
      · simp only [Option.bind_some, Option.bind_none, hrc, ↓reduceIte, not_false_eq_true, bind]
      simp only [Option.bind_some, Option.bind_none, hrc, ↓reduceIte, not_true_eq_false, bind]
      rw [decodeABIValues?]
      simp only [Option.bind_some, Option.bind_none, isDynamicABIType, staticABIEncodedSize?, bind,
        Bool.false_eq_true, if_false, Nat.zero_add, if_true]
      rw [hnonce]
      simp only [Option.bind_some, Option.bind_none, bind, if_true]
      rw [decodeABIValues?]
      simp only [Option.bind_some, Option.bind_none, bind, transactionArgs, transactionFromCalldata,
        decodeCalldata.insertValues, transactionCalldataNames]

theorem decodeTransactionCalldataValid {cd : ByteArray} {len : Nat}
    (hh : 324 ≤ cd.size) (hs : cd.size < 2 ^ 255)
    (hc : (calldataWord cd 4).toNat < EVM.addressModulus)
    (hoff : (calldataWord cd 68).toNat ≤ 2 ^ 64 - 1)
    (hw : calldataWord cd (4 + (calldataWord cd 68).toNat) = UInt256.ofNat len)
    (hn : len ≤ 2 ^ 64 - 1) (hin : 4 + (calldataWord cd 68).toNat + 32 + len ≤ cd.size)
    (ho : (calldataWord cd 100).toNat < 256)
    (hgas : (calldataWord cd 228).toNat < EVM.addressModulus)
    (href : (calldataWord cd 260).toNat < EVM.addressModulus) :
    decodeCalldata transactionCalldataNames transactionCalldataTypes cd =
      some (transactionArgs (transactionFromCalldata cd
        (cd.extract (4 + (calldataWord cd 68).toNat + 32)
          (4 + (calldataWord cd 68).toNat + 32 + len)))) := by
  rw [decodeTransactionCalldataCore hh hs]
  have hread := readNat_drop4_at_eq_calldataWord (cd := cd)
    (calldataWord cd 68).toNat (by omega)
  rw [hw, ulit_toNat' len (by change len < 2 ^ 256; omega)] at hread
  have hp := readBytesCalldata (cd := cd) (off := (calldataWord cd 68).toNat + 32)
    (len := len) (by omega)
  unfold transactionCalldataTail
  rw [if_neg (not_not_intro hc), if_neg (show ¬solcMaxU64 < (calldataWord cd 68).toNat by
    change ¬2 ^ 64 - 1 < _; omega), hread]
  dsimp only [bind, Option.bind]
  rw [if_neg (show ¬solcMaxU64 < len by change ¬2 ^ 64 - 1 < len; omega), hp]
  dsimp only [bind, Option.bind]
  rw [if_neg (not_not_intro ho), if_neg (not_not_intro hgas), if_neg (not_not_intro href)]
  simp only [byteArray_toList_eq, Array.toArray_toList, ← Nat.add_assoc]

set_option maxRecDepth 5000 in
theorem decodeTransactionCalldataEvidence {cd : ByteArray} {args : Store}
    (hlong : 4 ≤ cd.size)
    (hd : decodeCalldata transactionCalldataNames transactionCalldataTypes cd = some args) :
    ∃ len, 324 ≤ cd.size ∧ cd.size < 2 ^ 255 ∧
      (calldataWord cd 4).toNat < EVM.addressModulus ∧
      (calldataWord cd 68).toNat ≤ 2 ^ 64 - 1 ∧
      calldataWord cd (4 + (calldataWord cd 68).toNat) = UInt256.ofNat len ∧
      len ≤ 2 ^ 64 - 1 ∧ 4 + (calldataWord cd 68).toNat + 32 + len ≤ cd.size ∧
      (calldataWord cd 100).toNat < 256 ∧
      (calldataWord cd 228).toNat < EVM.addressModulus ∧
      (calldataWord cd 260).toNat < EVM.addressModulus ∧
      args = transactionArgs (transactionFromCalldata cd
        (cd.extract (4 + (calldataWord cd 68).toNat + 32)
          (4 + (calldataWord cd 68).toNat + 32 + len))) := by
  have hg := decodeDynamicCalldata (cd := cd) (names := transactionCalldataNames)
    (ty := abiAddress)
    (types := [abiUInt256, .bytes, abiUInt8, abiUInt256, abiUInt256, abiUInt256,
      abiAddress, abiAddress, abiUInt256]) (headSize := 320) hlong (by decide)
    (by simp [abiTupleHeadSize?, staticABIEncodedSize?, isDynamicABIType, bind, Option.bind])
  have hs : cd.size < 2 ^ 255 := by
    by_contra hbad
    rw [hg, if_pos (by omega)] at hd
    cases hd
  have hh : 324 ≤ cd.size := by
    by_contra hbad
    rw [hg, if_neg (by omega), if_pos (by omega)] at hd
    cases hd
  rw [decodeTransactionCalldataCore hh hs] at hd
  unfold transactionCalldataTail at hd
  by_cases hc : (calldataWord cd 4).toNat < EVM.addressModulus
  swap
  · rw [if_pos hc] at hd; cases hd
  rw [if_neg (not_not_intro hc)] at hd
  by_cases hoff : solcMaxU64 < (calldataWord cd 68).toNat
  · rw [if_pos hoff] at hd; cases hd
  rw [if_neg hoff] at hd
  cases hread : readNat? (cd.toList.drop 4) (calldataWord cd 68).toNat with
  | none => rw [hread] at hd; cases hd
  | some len =>
    rw [hread] at hd
    dsimp only [bind, Option.bind] at hd
    by_cases hn : solcMaxU64 < len
    · rw [if_pos hn] at hd; cases hd
    rw [if_neg hn] at hd
    cases hp : readBytes? (cd.toList.drop 4) ((calldataWord cd 68).toNat + 32) len with
    | none => rw [hp] at hd; cases hd
    | some payload =>
      rw [hp] at hd
      dsimp only [bind, Option.bind] at hd
      by_cases ho : (calldataWord cd 100).toNat < 256
      swap
      · rw [if_pos ho] at hd; cases hd
      rw [if_neg (not_not_intro ho)] at hd
      by_cases hgas : (calldataWord cd 228).toNat < EVM.addressModulus
      swap
      · rw [if_pos hgas] at hd; cases hd
      rw [if_neg (not_not_intro hgas)] at hd
      by_cases href : (calldataWord cd 260).toNat < EVM.addressModulus
      swap
      · rw [if_pos href] at hd; cases hd
      rw [if_neg (not_not_intro href), Option.some.injEq] at hd
      obtain ⟨hword, hin, hbytes⟩ := readCalldataBytesEvidence hlong hread hp
      refine ⟨len, hh, hs, hc, ?_, hword, ?_, hin, ho, hgas, href, ?_⟩
      · change _ ≤ solcMaxU64; omega
      · change len ≤ solcMaxU64; omega
      · rw [← hd, hbytes]
        simp only [byteArray_toList_eq, Array.toArray_toList]

end Benchmarks.Safe
