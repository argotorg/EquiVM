import Benchmarks.UniswapV4PoolManager.ModifyLiquidityParamsDecode
import Benchmarks.UniswapV4PoolManager.BytesSliceDecode
import Benchmarks.UniswapV4PoolManager.DynamicHeadDecode

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def modifyLiquidityInputTypes : List ABIType := [abiPoolKey, abiModifyLiquidityParams, .bytes]
def modifyLiquidityDataStart (cd : ByteArray) : Nat := 4+(calldataWord cd 292).toNat
def modifyLiquidityHookData (cd : ByteArray) : ByteArray := calldataBytesSlice cd (modifyLiquidityDataStart cd)
def modifyLiquidityArgs (cd : ByteArray) : Store :=
  (((∅ : Store).insert "key" (.tuple (poolKeyValues (poolKeyOfCalldata cd)))).insert "params"
    (.tuple (modifyLiquidityValues (modifyLiquidityOfCalldata cd)))).insert "hookData" (.bytes (modifyLiquidityHookData cd))
def ModifyLiquidityValuesBounds (cd : ByteArray) : Prop :=
  PoolKeyCanonical (poolKeyOfCalldata cd) ∧ ModifyLiquidityCanonical (modifyLiquidityOfCalldata cd) ∧
  (calldataWord cd 292).toNat ≤ solcMaxU64 ∧ BytesSliceBounds cd (modifyLiquidityDataStart cd)
instance (cd : ByteArray) : Decidable (ModifyLiquidityValuesBounds cd) :=
  inferInstanceAs (Decidable (_ ∧ _))
def ModifyLiquidityCalldataBounds (cd : ByteArray) : Prop :=
  324 ≤ cd.size ∧ cd.size < 2^255 ∧ ModifyLiquidityValuesBounds cd
instance (cd : ByteArray) : Decidable (ModifyLiquidityCalldataBounds cd) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem decodeModifyLiquidityValues {cd : ByteArray} (hlen : 324 ≤ cd.size) (hhi : cd.size < 2^255) :
    decodeABIValues? modifyLiquidityInputTypes (cd.toList.drop 4) 0 0 320 320 =
      if ModifyLiquidityValuesBounds cd then
        some ([.tuple (poolKeyValues (poolKeyOfCalldata cd)),
          .tuple (modifyLiquidityValues (modifyLiquidityOfCalldata cd)), .bytes (modifyLiquidityHookData cd)],
          max 320 ((calldataWord cd 292).toNat+32+paddedSize (calldataWord cd (modifyLiquidityDataStart cd)).toNat))
      else none := by
  rw [modifyLiquidityInputTypes, decodeABIValues?]
  simp only [show isDynamicABIType abiPoolKey = false by rfl, Bool.false_eq_true, if_false,
    show staticABIEncodedSize? abiPoolKey = some 160 by rfl, bind, Option.bind, Nat.zero_add]
  rw [decodePoolKey (by omega)]
  by_cases hk : PoolKeyCanonical (poolKeyOfCalldata cd)
  swap
  · rw [if_neg hk, if_neg (fun hh => hk hh.1)]
  rw [if_pos hk]
  simp only [bind, Option.bind, if_true, show max 320 160 = 320 by rfl]
  rw [decodeABIValues?]
  simp only [show isDynamicABIType abiModifyLiquidityParams = false by rfl, Bool.false_eq_true, if_false,
    show staticABIEncodedSize? abiModifyLiquidityParams = some 128 by rfl, bind, Option.bind, Nat.zero_add]
  rw [decodeModifyLiquidityParams (by omega)]
  by_cases hp : ModifyLiquidityCanonical (modifyLiquidityOfCalldata cd)
  swap
  · rw [if_neg hp, if_neg (fun hh => hp hh.2.1)]
  rw [if_pos hp]
  simp only [bind, Option.bind, if_true, show max 320 288 = 320 by rfl]
  rw [decodeABIValues?]
  simp only [show isDynamicABIType .bytes = true by rfl, if_true, Nat.zero_add]
  rw [readNat_drop4_at_eq_calldataWord 288 (by omega)]
  simp only [bind, Option.bind, solcMaxLen]
  by_cases ho : (calldataWord cd 292).toNat ≤ solcMaxU64
  swap
  · rw [if_pos (Nat.lt_of_not_ge ho), if_neg (fun hh => ho hh.2.2.1)]
  rw [if_neg (by omega : ¬solcMaxU64 < (calldataWord cd 292).toNat),
    decodeABIValue_bytes_calldata _ (by omega) hhi]
  by_cases hb : BytesSliceBounds cd (4+(calldataWord cd (4+288)).toNat)
  · rw [if_pos hb, if_pos (show ModifyLiquidityValuesBounds cd from ⟨hk, hp, ho, hb⟩)]
    simp only [decodeABIValues?, bind, Option.bind]
    rfl
  · rw [if_neg hb, if_neg (fun hh => hb hh.2.2.2)]

theorem decodeCalldata_modifyLiquidity (cd : ByteArray) :
    decodeCalldata ["key", "params", "hookData"] modifyLiquidityInputTypes cd =
      if ModifyLiquidityCalldataBounds cd then some (modifyLiquidityArgs cd) else none := by
  rw [decodeCalldata_dynamicHead _ _ _ 320 (by rfl) (by native_decide)]
  by_cases hbad : cd.size < 324 ∨ 2^255 ≤ cd.size
  · rw [if_pos hbad, if_neg (by intro hb; rcases hb with ⟨hl, hh, _⟩; omega)]
  · rw [if_neg hbad, decodeModifyLiquidityValues (by omega) (by omega)]
    by_cases hv : ModifyLiquidityValuesBounds cd
    · rw [if_pos hv, if_pos (show ModifyLiquidityCalldataBounds cd from ⟨by omega, by omega, hv⟩)]
      rfl
    · rw [if_neg hv, if_neg (fun hh => hv hh.2.2)]
      rfl

end Benchmarks.UniswapV4PoolManager
