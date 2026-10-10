import Benchmarks.UniswapV4PoolManager.NarrowWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 3000

structure PoolKeyWords where
  currency0 : UInt256
  currency1 : UInt256
  fee : UInt256
  tickSpacing : UInt256
  hooks : UInt256

def poolKeyTypes : List ABIType := [abiAddress, abiAddress, abiUInt24, abiInt24, abiAddress]
def abiPoolKey : ABIType := .tuple poolKeyTypes
def poolKeyOfCalldata (cd : ByteArray) : PoolKeyWords :=
  ⟨calldataWord cd 4, calldataWord cd 36, calldataWord cd 68, calldataWord cd 100, calldataWord cd 132⟩

def PoolKeyCanonical (key : PoolKeyWords) : Prop :=
  key.currency0.toNat < 2^160 ∧ key.currency1.toNat < 2^160 ∧ key.fee.toNat < 2^24 ∧
  int24Canonical key.tickSpacing ∧ key.hooks.toNat < 2^160
instance (key : PoolKeyWords) : Decidable (PoolKeyCanonical key) := inferInstanceAs (Decidable (_ ∧ _))

def poolKeyValues (key : PoolKeyWords) : List Value :=
  [.address (AccountAddress.ofNat key.currency0.toNat), .address (AccountAddress.ofNat key.currency1.toNat),
   .int (Int.ofNat key.fee.toNat), .int (EVM.signed key.tickSpacing), .address (AccountAddress.ofNat key.hooks.toNat)]

def poolKeyFeeArgs (keyName feeName : Ident) (key : PoolKeyWords) (fee : UInt256) : Store :=
  ((∅ : Store).insert keyName (.tuple (poolKeyValues key))).insert feeName (.int (Int.ofNat fee.toNat))

-- LIBRARY CANDIDATE: word reads from a selector-stripped calldata list.
theorem readWord_drop4 {cd : ByteArray} {off : Nat} (hlen : 4+off+32 ≤ cd.size) :
    readWord? (cd.toList.drop 4) off = some (calldataWord cd (4+off)) := by
  have htake : ((cd.toList.drop (4+off)).take 32).length = 32 := by
    simp only [List.length_take, List.length_drop, byteArray_toList_eq, Array.length_toList]
    change min 32 (cd.size-(4+off)) = 32
    omega
  simp only [readWord?, readBytes?, List.drop_drop, htake, if_true, bind, Option.bind]
  exact congrArg some (decode_word_at_eq_any cd (4+off) hlen)

theorem decodePoolKeyWords {cd : ByteArray} (hlen : 164 ≤ cd.size) :
    decodeScalarWords? poolKeyTypes (cd.toList.drop 4) 0 =
      if PoolKeyCanonical (poolKeyOfCalldata cd) then some (poolKeyValues (poolKeyOfCalldata cd)) else none := by
  have h0 := readWord_drop4 (off := 0) (by omega : 4+0+32 ≤ cd.size)
  have h1 := readWord_drop4 (off := 32) (by omega : 4+32+32 ≤ cd.size)
  have h2 := readWord_drop4 (off := 64) (by omega : 4+64+32 ≤ cd.size)
  have h3 := readWord_drop4 (off := 96) (by omega : 4+96+32 ≤ cd.size)
  have h4 := readWord_drop4 (off := 128) (by omega : 4+128+32 ≤ cd.size)
  simp only [poolKeyTypes, decodeScalarWords?, decodeScalarWord?, h0, h1, h2, h3, h4,
    bind, Option.bind, decodeABIWord_uint24, decodeABIWord_int24]
  simp only [decodeABIWord?, PoolKeyCanonical, poolKeyOfCalldata, poolKeyValues, UInt256.toNat]
  clear h0 h1 h2 h3 h4
  split_ifs <;> simp_all [EVM.addressModulus, EVM.twoPow] <;> omega

theorem decodePoolKey {cd : ByteArray} (hlen : 164 ≤ cd.size) :
    decodeABIValue? abiPoolKey (cd.toList.drop 4) 0 =
      if PoolKeyCanonical (poolKeyOfCalldata cd) then
        some (.tuple (poolKeyValues (poolKeyOfCalldata cd)), 160) else none := by
  rw [abiPoolKey, decodeABIValue?]
  rw [show abiTupleHeadSize? poolKeyTypes = some 160 by native_decide]
  simp only [bind, Option.bind, Nat.zero_add]
  rw [decodeABIValues_scalarWords_eq (by native_decide : poolKeyTypes.all isABIScalarWordType = true)
    (by decide : 0+32*poolKeyTypes.length = 160), decodePoolKeyWords hlen]
  split_ifs <;> rfl

-- GENERALIZES decodeABIWord_uint24 to every unsigned ABI width.
theorem decodeUnsignedWord (bits : BitWidth) (w : UInt256) :
    decodeABIWord? (.elem (.int (.uint bits))) w =
      if w.toNat < EVM.twoPow bits.val then some (.int (Int.ofNat w.toNat)) else none := by
  simp only [decodeABIWord?, if_neg (Nat.ne_of_gt bits.property.1)]
  rfl

-- GENERALIZES the pool-key/uint24 decoder to every unsigned ABI width.
theorem decodePoolKeyUnsignedValues (bits : BitWidth) {cd : ByteArray} (hlen : 196 ≤ cd.size) :
    decodeABIValues? [abiPoolKey, (.elem (.int (.uint bits)))] (cd.toList.drop 4) 0 0 192 192 =
      if PoolKeyCanonical (poolKeyOfCalldata cd) ∧ (calldataWord cd 164).toNat < EVM.twoPow bits.val then
        some ([.tuple (poolKeyValues (poolKeyOfCalldata cd)), .int (Int.ofNat (calldataWord cd 164).toNat)], 192)
      else none := by
  rw [decodeABIValues?]
  rw [show isDynamicABIType abiPoolKey = false by rfl]
  simp only [Bool.false_eq_true, if_false]
  rw [show staticABIEncodedSize? abiPoolKey = some 160 by rfl]
  simp only [bind, Option.bind, Nat.zero_add]
  rw [decodePoolKey (by omega)]
  by_cases hk : PoolKeyCanonical (poolKeyOfCalldata cd)
  · rw [if_pos hk]
    simp only [if_true, max_eq_left (by decide : 160 ≤ 192)]
    rw [decodeABIValues_scalarWords_eq (by rfl : [(.elem (.int (.uint bits)))].all isABIScalarWordType = true)
      (by rfl : 160+32*[(.elem (.int (.uint bits)))].length = 192)]
    simp only [decodeScalarWords?, decodeScalarWord?,
      readWord_drop4 (by omega : 4+160+32 ≤ cd.size), bind, Option.bind, decodeUnsignedWord bits]
    by_cases hf : (calldataWord cd 164).toNat < EVM.twoPow bits.val
    · simp only [hk, hf, true_and, if_true]
    · simp only [hk, hf, and_false, if_false]
  · simp only [hk, false_and, if_false]

private theorem poolKeyUnsignedHeadSize (bits : BitWidth) :
    abiTupleHeadSize? [abiPoolKey, .elem (.int (.uint bits))] = some 192 := by
  simp [abiTupleHeadSize?, isDynamicABIType, isDynamicABITypeList, staticABIEncodedSize?,
    staticABIEncodedSizeList?, abiPoolKey, poolKeyTypes]

theorem decodeCalldata_poolKey_unsigned (bits : BitWidth) {cd : ByteArray} {keyName feeName : Ident}
    (hlen : 196 ≤ cd.size) (hhi : cd.size < calldataLimit) :
    decodeCalldata [keyName, feeName] [abiPoolKey, (.elem (.int (.uint bits)))] cd =
      if PoolKeyCanonical (poolKeyOfCalldata cd) ∧ (calldataWord cd 164).toNat < EVM.twoPow bits.val then
        some (poolKeyFeeArgs keyName feeName (poolKeyOfCalldata cd) (calldataWord cd 164)) else none := by
  have htlen : cd.toList.length = cd.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  unfold decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬cd.toList.length < 4)]
  rw [if_neg (by have h : [abiPoolKey, (.elem (.int (.uint bits)))].any isDynamicABIType = false := by rfl
                 simp only [h, Bool.false_eq_true, false_and, not_false_eq_true])]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; unfold calldataLimit at hhi; omega)]
  rw [if_neg (by simp [solcTotalSizeDynamicGuard])]
  simp only [decodeCalldata.decodeArgs]
  rw [poolKeyUnsignedHeadSize bits]
  simp only [bind, Option.bind]
  rw [if_neg (by rw [List.length_drop, htlen]; omega : ¬(cd.toList.drop 4).length < 192)]
  rw [decodePoolKeyUnsignedValues bits hlen]
  split_ifs <;> rfl

theorem decodeCalldata_poolKey_unsigned_none_short (bits : BitWidth) {cd : ByteArray} {keyName feeName : Ident}
    (h4 : 4 ≤ cd.size) (hlen : cd.size < 196) :
    decodeCalldata [keyName, feeName] [abiPoolKey, (.elem (.int (.uint bits)))] cd = none := by
  have htlen : cd.toList.length = cd.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  unfold decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬cd.toList.length < 4)]
  rw [if_neg (by have h : [abiPoolKey, (.elem (.int (.uint bits)))].any isDynamicABIType = false := by rfl
                 simp only [h, Bool.false_eq_true, false_and, not_false_eq_true])]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [if_neg (by simp [solcTotalSizeDynamicGuard])]
  simp only [decodeCalldata.decodeArgs]
  rw [poolKeyUnsignedHeadSize bits]
  simp only [bind, Option.bind]
  rw [if_pos (by rw [List.length_drop, htlen]; omega : (cd.toList.drop 4).length < 192)]

theorem decodeCalldata_poolKey_unsigned_none_huge (bits : BitWidth) {cd : ByteArray} {keyName feeName : Ident}
    (hlen : calldataLimit ≤ cd.size) :
    decodeCalldata [keyName, feeName] [abiPoolKey, (.elem (.int (.uint bits)))] cd = none := by
  have htlen : cd.toList.length = cd.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  unfold calldataLimit at hlen
  unfold decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬cd.toList.length < 4)]
  rw [if_neg (by have h : [abiPoolKey, (.elem (.int (.uint bits)))].any isDynamicABIType = false := by rfl
                 simp only [h, Bool.false_eq_true, false_and, not_false_eq_true])]
  rw [if_pos ⟨rfl, by rw [List.length_drop, htlen]; omega⟩]

theorem decodePoolKeyFeeValues {cd : ByteArray} (hlen : 196 ≤ cd.size) :
    decodeABIValues? [abiPoolKey, abiUInt24] (cd.toList.drop 4) 0 0 192 192 =
      if PoolKeyCanonical (poolKeyOfCalldata cd) ∧ (calldataWord cd 164).toNat < 2^24 then
        some ([.tuple (poolKeyValues (poolKeyOfCalldata cd)), .int (Int.ofNat (calldataWord cd 164).toNat)], 192)
      else none :=
  decodePoolKeyUnsignedValues ⟨24, by decide⟩ hlen

theorem decodeCalldata_poolKey_uint24 {cd : ByteArray} {keyName feeName : Ident}
    (hlen : 196 ≤ cd.size) (hhi : cd.size < calldataLimit) :
    decodeCalldata [keyName, feeName] [abiPoolKey, abiUInt24] cd =
      if PoolKeyCanonical (poolKeyOfCalldata cd) ∧ (calldataWord cd 164).toNat < 2^24 then
        some (poolKeyFeeArgs keyName feeName (poolKeyOfCalldata cd) (calldataWord cd 164)) else none :=
  decodeCalldata_poolKey_unsigned ⟨24, by decide⟩ hlen hhi

theorem decodeCalldata_poolKey_uint24_none_short {cd : ByteArray} {keyName feeName : Ident}
    (h4 : 4 ≤ cd.size) (hlen : cd.size < 196) :
    decodeCalldata [keyName, feeName] [abiPoolKey, abiUInt24] cd = none :=
  decodeCalldata_poolKey_unsigned_none_short ⟨24, by decide⟩ h4 hlen

theorem decodeCalldata_poolKey_uint24_none_huge {cd : ByteArray} {keyName feeName : Ident}
    (hlen : calldataLimit ≤ cd.size) :
    decodeCalldata [keyName, feeName] [abiPoolKey, abiUInt24] cd = none :=
  decodeCalldata_poolKey_unsigned_none_huge ⟨24, by decide⟩ hlen

end Benchmarks.UniswapV4PoolManager
