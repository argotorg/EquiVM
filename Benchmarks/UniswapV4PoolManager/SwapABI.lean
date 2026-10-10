import Benchmarks.UniswapV4PoolManager.SwapParamsDecode
import Benchmarks.UniswapV4PoolManager.BytesSliceDecode
import Benchmarks.UniswapV4PoolManager.DynamicHeadDecode

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def swapInputTypes : List ABIType := [abiPoolKey, abiSwapParams, .bytes]
def swapDataStart (cd : ByteArray) : Nat := 4+(calldataWord cd 260).toNat
def swapHookData (cd : ByteArray) : ByteArray := calldataBytesSlice cd (swapDataStart cd)
def swapArgs (cd : ByteArray) : Store :=
  (((∅ : Store).insert "key" (.tuple (poolKeyValues (poolKeyOfCalldata cd)))).insert "params"
    (.tuple (swapParamsValues (swapParamsOfCalldata cd)))).insert "hookData" (.bytes (swapHookData cd))
def SwapValuesBounds (cd : ByteArray) : Prop :=
  PoolKeyCanonical (poolKeyOfCalldata cd) ∧ SwapParamsBounds cd ∧
  (calldataWord cd 260).toNat ≤ solcMaxU64 ∧ BytesSliceBounds cd (swapDataStart cd)
instance (cd : ByteArray) : Decidable (SwapValuesBounds cd) :=
  inferInstanceAs (Decidable (_ ∧ _))
def SwapCalldataBounds (cd : ByteArray) : Prop :=
  292 ≤ cd.size ∧ cd.size < 2^255 ∧ SwapValuesBounds cd
instance (cd : ByteArray) : Decidable (SwapCalldataBounds cd) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem decodeSwapValues {cd : ByteArray} (hlen : 292 ≤ cd.size) (hhi : cd.size < 2^255) :
    decodeABIValues? swapInputTypes (cd.toList.drop 4) 0 0 288 288 =
      if SwapValuesBounds cd then
        some ([.tuple (poolKeyValues (poolKeyOfCalldata cd)),
          .tuple (swapParamsValues (swapParamsOfCalldata cd)), .bytes (swapHookData cd)],
          max 288 ((calldataWord cd 260).toNat+32+paddedSize (calldataWord cd (swapDataStart cd)).toNat))
      else none := by
  rw [swapInputTypes, decodeABIValues?]
  simp only [show isDynamicABIType abiPoolKey = false by rfl, Bool.false_eq_true, if_false,
    show staticABIEncodedSize? abiPoolKey = some 160 by rfl, bind, Option.bind, Nat.zero_add]
  rw [decodePoolKey (by omega)]
  by_cases hk : PoolKeyCanonical (poolKeyOfCalldata cd)
  swap
  · rw [if_neg hk, if_neg (fun hh => hk hh.1)]
  rw [if_pos hk]
  simp only [bind, Option.bind, if_true, show max 288 160 = 288 by rfl]
  rw [decodeABIValues?]
  simp only [show isDynamicABIType abiSwapParams = false by rfl, Bool.false_eq_true, if_false,
    show staticABIEncodedSize? abiSwapParams = some 96 by rfl, bind, Option.bind, Nat.zero_add]
  rw [decodeSwapParams (by omega)]
  by_cases hp : SwapParamsBounds cd
  swap
  · rw [if_neg hp, if_neg (fun hh => hp hh.2.1)]
  rw [if_pos hp]
  simp only [bind, Option.bind, if_true, show max 288 256 = 288 by rfl]
  rw [decodeABIValues?]
  simp only [show isDynamicABIType .bytes = true by rfl, if_true, Nat.zero_add]
  rw [readNat_drop4_at_eq_calldataWord 256 (by omega)]
  simp only [bind, Option.bind, solcMaxLen]
  by_cases ho : (calldataWord cd 260).toNat ≤ solcMaxU64
  swap
  · rw [if_pos (Nat.lt_of_not_ge ho), if_neg (fun hh => ho hh.2.2.1)]
  rw [if_neg (by omega : ¬solcMaxU64 < (calldataWord cd 260).toNat),
    decodeABIValue_bytes_calldata _ (by omega) hhi]
  by_cases hb : BytesSliceBounds cd (4+(calldataWord cd (4+256)).toNat)
  · rw [if_pos hb, if_pos (show SwapValuesBounds cd from ⟨hk, hp, ho, hb⟩)]
    simp only [decodeABIValues?, bind, Option.bind]
    rfl
  · rw [if_neg hb, if_neg (fun hh => hb hh.2.2.2)]

theorem decodeCalldata_swap (cd : ByteArray) :
    decodeCalldata ["key", "params", "hookData"] swapInputTypes cd =
      if SwapCalldataBounds cd then some (swapArgs cd) else none := by
  rw [decodeCalldata_dynamicHead _ _ _ 288 (by rfl) (by native_decide)]
  by_cases hbad : cd.size < 292 ∨ 2^255 ≤ cd.size
  · rw [if_pos hbad, if_neg (by intro hb; rcases hb with ⟨hl, hh, _⟩; omega)]
  · rw [if_neg hbad, decodeSwapValues (by omega) (by omega)]
    by_cases hv : SwapValuesBounds cd
    · rw [if_pos hv, if_pos (show SwapCalldataBounds cd from ⟨by omega, by omega, hv⟩)]
      rfl
    · rw [if_neg hv, if_neg (fun hh => hv hh.2.2)]
      rfl

end Benchmarks.UniswapV4PoolManager
