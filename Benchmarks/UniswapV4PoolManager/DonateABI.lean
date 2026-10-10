import Benchmarks.UniswapV4PoolManager.PoolKeyABI
import Benchmarks.UniswapV4PoolManager.BytesSliceDecode
import Benchmarks.UniswapV4PoolManager.DynamicHeadDecode

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def donateInputTypes : List ABIType := [abiPoolKey, abiUInt256, abiUInt256, .bytes]
def donateDataStart (cd : ByteArray) : Nat := 4+(calldataWord cd 228).toNat
def donateHookData (cd : ByteArray) : ByteArray := calldataBytesSlice cd (donateDataStart cd)
def donateArgs (cd : ByteArray) : Store :=
  ((((∅ : Store).insert "key" (.tuple (poolKeyValues (poolKeyOfCalldata cd)))).insert "amount0"
    (.int (Int.ofNat (calldataWord cd 164).toNat))).insert "amount1"
    (.int (Int.ofNat (calldataWord cd 196).toNat))).insert "hookData" (.bytes (donateHookData cd))
def DonateValuesBounds (cd : ByteArray) : Prop :=
  PoolKeyCanonical (poolKeyOfCalldata cd) ∧
  (calldataWord cd 228).toNat ≤ solcMaxU64 ∧ BytesSliceBounds cd (donateDataStart cd)
instance (cd : ByteArray) : Decidable (DonateValuesBounds cd) :=
  inferInstanceAs (Decidable (_ ∧ _))
def DonateCalldataBounds (cd : ByteArray) : Prop :=
  260 ≤ cd.size ∧ cd.size < 2^255 ∧ DonateValuesBounds cd
instance (cd : ByteArray) : Decidable (DonateCalldataBounds cd) :=
  inferInstanceAs (Decidable (_ ∧ _))

-- LIBRARY CANDIDATE: decode an unsigned word at a selector-relative offset.
theorem decodeABIValue_uint256_calldata {cd : ByteArray} (off : Nat) (hlen : 4+off+32 ≤ cd.size) :
    decodeABIValue? abiUInt256 (cd.toList.drop 4) off =
      some (.int (Int.ofNat (calldataWord cd (4+off)).toNat), off+32) := by
  simp only [abiUInt256, decodeABIValue?, readWord_drop4 hlen, bind, Option.bind,
    decodeUnsignedWord, EVM.twoPow]
  rw [if_pos (show (calldataWord cd (4+off)).toNat < 2^256 from (calldataWord cd (4+off)).val.isLt)]

theorem decodeDonateValues {cd : ByteArray} (hlen : 260 ≤ cd.size) (hhi : cd.size < 2^255) :
    decodeABIValues? donateInputTypes (cd.toList.drop 4) 0 0 256 256 =
      if DonateValuesBounds cd then
        some ([.tuple (poolKeyValues (poolKeyOfCalldata cd)),
          .int (Int.ofNat (calldataWord cd 164).toNat), .int (Int.ofNat (calldataWord cd 196).toNat),
          .bytes (donateHookData cd)],
          max 256 ((calldataWord cd 228).toNat+32+paddedSize (calldataWord cd (donateDataStart cd)).toNat))
      else none := by
  rw [donateInputTypes, decodeABIValues?]
  simp only [show isDynamicABIType abiPoolKey = false by rfl, Bool.false_eq_true, if_false,
    show staticABIEncodedSize? abiPoolKey = some 160 by rfl, bind, Option.bind, Nat.zero_add]
  rw [decodePoolKey (by omega)]
  by_cases hk : PoolKeyCanonical (poolKeyOfCalldata cd)
  swap
  · rw [if_neg hk, if_neg (fun hh => hk hh.1)]
  rw [if_pos hk]
  simp only [bind, Option.bind, if_true, show max 256 160 = 256 by rfl]
  rw [decodeABIValues?]
  simp only [show isDynamicABIType abiUInt256 = false by rfl, Bool.false_eq_true, if_false,
    show staticABIEncodedSize? abiUInt256 = some 32 by rfl, bind, Option.bind, Nat.zero_add]
  rw [decodeABIValue_uint256_calldata 160 (by omega)]
  simp only [bind, Option.bind, if_true, show max 256 (160+32) = 256 by rfl]
  rw [decodeABIValues?]
  simp only [show isDynamicABIType abiUInt256 = false by rfl, Bool.false_eq_true, if_false,
    show staticABIEncodedSize? abiUInt256 = some 32 by rfl, bind, Option.bind, Nat.zero_add]
  rw [decodeABIValue_uint256_calldata 192 (by omega)]
  simp only [bind, Option.bind, if_true, show max 256 (192+32) = 256 by rfl]
  rw [decodeABIValues?]
  simp only [show isDynamicABIType .bytes = true by rfl, if_true, Nat.zero_add]
  rw [readNat_drop4_at_eq_calldataWord 224 (by omega)]
  simp only [bind, Option.bind, solcMaxLen]
  by_cases ho : (calldataWord cd 228).toNat ≤ solcMaxU64
  swap
  · rw [if_pos (Nat.lt_of_not_ge ho), if_neg (fun hh => ho hh.2.1)]
  rw [if_neg (by omega : ¬solcMaxU64 < (calldataWord cd 228).toNat),
    decodeABIValue_bytes_calldata _ (by omega) hhi]
  by_cases hb : BytesSliceBounds cd (4+(calldataWord cd (4+224)).toNat)
  · rw [if_pos hb, if_pos (show DonateValuesBounds cd from ⟨hk, ho, hb⟩)]
    simp only [decodeABIValues?, bind, Option.bind]
    rfl
  · rw [if_neg hb, if_neg (fun hh => hb hh.2.2)]

theorem decodeCalldata_donate (cd : ByteArray) :
    decodeCalldata ["key", "amount0", "amount1", "hookData"] donateInputTypes cd =
      if DonateCalldataBounds cd then some (donateArgs cd) else none := by
  rw [decodeCalldata_dynamicHead _ _ _ 256 (by rfl) (by native_decide)]
  by_cases hbad : cd.size < 260 ∨ 2^255 ≤ cd.size
  · rw [if_pos hbad, if_neg (by intro hb; rcases hb with ⟨hl, hh, _⟩; omega)]
  · rw [if_neg hbad, decodeDonateValues (by omega) (by omega)]
    by_cases hv : DonateValuesBounds cd
    · rw [if_pos hv, if_pos (show DonateCalldataBounds cd from ⟨by omega, by omega, hv⟩)]
      rfl
    · rw [if_neg hv, if_neg (fun hh => hv hh.2.2)]
      rfl

end Benchmarks.UniswapV4PoolManager
