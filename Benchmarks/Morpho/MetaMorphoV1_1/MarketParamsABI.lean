import Benchmarks.Morpho.MetaMorphoV1_1.MarketParamsCall
import Benchmarks.Morpho.MetaMorphoV1_1.ScalarTupleABI

/-! Exact success and failure conditions for the market-parameter return tuple. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

def marketParamsFieldTypes : List ABIType :=
  [.elem .address, .elem .address, .elem .address, .elem .address, abiUInt256]

def marketParamsFields (out : ByteArray) : List Value :=
  [.address (AccountAddress.ofNat (calldataWord out 0).toNat),
   .address (AccountAddress.ofNat (calldataWord out 32).toNat),
   .address (AccountAddress.ofNat (calldataWord out 64).toNat),
   .address (AccountAddress.ofNat (calldataWord out 96).toNat),
   uint256Value (calldataWord out 128)]

def marketParamsValue (out : ByteArray) : Value :=
  .struct "MarketParams"
    (["loanToken", "collateralToken", "oracle", "irm", "lltv"].zip (marketParamsFields out))

def MarketParamsChecks (out : ByteArray) : Prop :=
  160 ≤ out.size ∧ (calldataWord out 0).toNat < EVM.addressModulus ∧
    (calldataWord out 32).toNat < EVM.addressModulus ∧
    (calldataWord out 64).toNat < EVM.addressModulus ∧
    (calldataWord out 96).toNat < EVM.addressModulus

instance (out : ByteArray) : Decidable (MarketParamsChecks out) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

theorem marketParamsTupleDecode {out : ByteArray} (hhi : out.size < 2 ^ 255) :
    decodeReturnValues? [.tuple marketParamsFieldTypes] out =
      (decodeScalarWords? marketParamsFieldTypes out.toList 0).map (fun vs ↦ [.tuple vs]) :=
  scalarTupleReturnDecode (by decide) hhi

-- LIBRARY CANDIDATE: scalar return-word decoding expressed using calldataWord.
theorem decodeScalarAddress_at {out : ByteArray} {off : Nat} (hin : off + 32 ≤ out.size) :
    decodeScalarWord? (.elem .address) out.toList off =
      if (calldataWord out off).toNat < EVM.addressModulus then
        some (.address (AccountAddress.ofNat (calldataWord out off).toNat), off + 32)
      else none := by
  have hl : ((out.toList.drop off).take 32).length = 32 := by
    simp only [List.length_take, List.length_drop, byteArray_toList_eq, Array.length_toList]
    change min 32 (out.size - off) = 32
    omega
  have hw : bytesToWord ((out.toList.drop off).take 32) = calldataWord out off :=
    decode_word_at_eq_any out off hin
  by_cases hc : (calldataWord out off).toNat < EVM.addressModulus
  · rw [if_pos hc]
    simpa only [hw] using decodeScalarWord_address_ok hl (by rw [hw]; exact hc)
  · rw [if_neg hc]
    exact decodeScalarWord_address_none_noncanon hl (by rw [hw]; exact hc)

theorem marketParamsScalarDecode_long {out : ByteArray} (hlo : 160 ≤ out.size) :
    decodeScalarWords? marketParamsFieldTypes out.toList 0 =
      if MarketParamsChecks out then some (marketParamsFields out) else none := by
  have hu : decodeScalarWord? abiUInt256 out.toList 128 =
      some (uint256Value (calldataWord out 128), 160) := by
    have hl : ((out.toList.drop 128).take 32).length = 32 := by
      simp only [List.length_take, List.length_drop, byteArray_toList_eq, Array.length_toList]
      change min 32 (out.size - 128) = 32
      omega
    simpa only [decode_word_at_eq_any out 128 (by omega)] using decodeScalarWord_uint256_ok hl
  simp only [marketParamsFieldTypes, decodeScalarWords?, Nat.reduceAdd,
    decodeScalarAddress_at (out := out) (off := 0) (by omega),
    decodeScalarAddress_at (out := out) (off := 32) (by omega),
    decodeScalarAddress_at (out := out) (off := 64) (by omega),
    decodeScalarAddress_at (out := out) (off := 96) (by omega), hu]
  by_cases h0 : (calldataWord out 0).toNat < EVM.addressModulus
  · by_cases h32 : (calldataWord out 32).toNat < EVM.addressModulus
    · by_cases h64 : (calldataWord out 64).toNat < EVM.addressModulus
      · by_cases h96 : (calldataWord out 96).toNat < EVM.addressModulus <;>
          simp [h0, h32, h64, h96, MarketParamsChecks, hlo, marketParamsFields]
      · simp [h0, h32, h64, MarketParamsChecks, hlo]
    · simp [h0, h32, MarketParamsChecks, hlo]
  · simp [h0, MarketParamsChecks, hlo]

theorem marketParamsScalarDecode_short {out : ByteArray} (hlo : out.size < 160) :
    decodeScalarWords? marketParamsFieldTypes out.toList 0 = none := by
  cases h : decodeScalarWords? marketParamsFieldTypes out.toList 0 with
  | none => rfl
  | some vs =>
      have hlen := decodeScalarWords?_some_length (by omega) h
      simp only [marketParamsFieldTypes, List.length_cons, List.length_nil, Nat.reduceAdd,
        Nat.reduceMul, Nat.zero_add, byteArray_toList_eq, Array.length_toList] at hlen
      change 160 ≤ out.size at hlen
      omega

theorem marketParamsDecode {out : ByteArray} (hhi : out.size < 2 ^ 255) :
    config.externalABI.decode? "idToMarketParams" out =
      if MarketParamsChecks out then some [marketParamsValue out] else none := by
  change (decodeReturnValues? [.tuple marketParamsFieldTypes] out).bind
    (fun vs ↦ match vs with
      | [.tuple fields] => if fields.length = 5 then
          some [Value.struct "MarketParams"
            (["loanToken", "collateralToken", "oracle", "irm", "lltv"].zip fields)] else none
      | _ => none) = _
  rw [marketParamsTupleDecode hhi]
  by_cases hlo : 160 ≤ out.size
  · rw [marketParamsScalarDecode_long hlo]
    by_cases hc : MarketParamsChecks out <;>
      simp [hc, marketParamsFields, marketParamsValue]
  · rw [marketParamsScalarDecode_short (by omega)]
    simp [MarketParamsChecks, hlo]

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
