import Benchmarks.UniswapV4PoolManager.ModifyLiquidityParams
import Benchmarks.UniswapV4PoolManager.SignedBytesDecode

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def modifyLiquidityOfCalldata (cd : ByteArray) : ModifyLiquidityWords :=
  ⟨calldataWord cd 164, calldataWord cd 196, calldataWord cd 228, calldataWord cd 260⟩

def ModifyLiquidityCanonical (p : ModifyLiquidityWords) : Prop :=
  int24Canonical p.lower ∧ int24Canonical p.upper
instance (p : ModifyLiquidityWords) : Decidable (ModifyLiquidityCanonical p) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem decodeModifyLiquidityParams {cd : ByteArray} (hlen : 292 ≤ cd.size) :
    decodeABIValue? abiModifyLiquidityParams (cd.toList.drop 4) 160 =
      if ModifyLiquidityCanonical (modifyLiquidityOfCalldata cd) then
        some (.tuple (modifyLiquidityValues (modifyLiquidityOfCalldata cd)), 288) else none := by
  have h0 := readWord_drop4 (off := 160) (by omega : 4+160+32 ≤ cd.size)
  have h1 := readWord_drop4 (off := 192) (by omega : 4+192+32 ≤ cd.size)
  have h2 := readWord_drop4 (off := 224) (by omega : 4+224+32 ≤ cd.size)
  have hs : decodeABIValue? abiBytes32 (cd.toList.drop 4) 256 =
      some (wordBytes32Value (calldataWord cd 260), 288) := by
    rw [decodeABIValue_bytes32_ok (by
      rw [List.length_take, List.length_drop, List.length_drop, byteArray_toList_eq, Array.length_toList]
      change min 32 (cd.size-4-256) = 32; omega)]
    have ht : ((cd.toList.drop 260).take 32).length = 32 := by
      rw [List.length_take, List.length_drop, byteArray_toList_eq, Array.length_toList]
      change min 32 (cd.size-260) = 32; omega
    have hb := toBytesBE_bytesToWord_of_length ht
    rw [decode_word_at_eq_any cd 260 hlen] at hb
    simp only [List.drop_drop, wordBytes32Value, hb]
  have hd0 := decodeABIValue_scalarWord_eq (bytes := cd.toList.drop 4) (start := 160)
    (by rfl : isABIScalarWordType abiInt24 = true)
  have hd1 := decodeABIValue_scalarWord_eq (bytes := cd.toList.drop 4) (start := 192)
    (by rfl : isABIScalarWordType abiInt24 = true)
  have hd2 := decodeABIValue_scalarWord_eq (bytes := cd.toList.drop 4) (start := 224)
    (by rfl : isABIScalarWordType abiInt256 = true)
  simp only [decodeScalarWord?, h0, h1, h2, bind, Option.bind, decodeABIWord_int24,
    decodeABIWord_signed256] at hd0 hd1 hd2
  rw [abiModifyLiquidityParams, decodeABIValue?]
  rw [show abiTupleHeadSize? modifyLiquidityTypes = some 128 by native_decide]
  by_cases hl : int24Canonical (calldataWord cd 164) <;>
    by_cases hu : int24Canonical (calldataWord cd 196) <;>
    simp only [hl, hu, if_true, if_false] at hd0 hd1 <;>
    simp only [modifyLiquidityTypes, decodeABIValues?,
      show isDynamicABIType abiInt24 = false by rfl,
      show isDynamicABIType abiInt256 = false by rfl,
      show isDynamicABIType abiBytes32 = false by rfl,
      show staticABIEncodedSize? abiInt24 = some 32 by rfl,
      show staticABIEncodedSize? abiInt256 = some 32 by rfl,
      show staticABIEncodedSize? abiBytes32 = some 32 by rfl,
      bind, Option.bind, Bool.false_eq_true, if_false, Nat.add_zero, hd0, hd1, hd2, hs,
      ModifyLiquidityCanonical, modifyLiquidityOfCalldata, hl, hu, true_and, false_and,
      and_false, if_true, modifyLiquidityValues]
  rfl

end Benchmarks.UniswapV4PoolManager
