import Benchmarks.Morpho.MetaMorphoV1_1.ScalarTupleABI

/-! The six uint128 words returned by Morpho's market reader. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

-- LIBRARY CANDIDATE: bounded unsigned scalar decoding at an arbitrary byte offset.
theorem decodeScalarUint_at {out : ByteArray} {off : Nat} (bits : ABI.BitWidth)
    (hbits : bits.val ≠ 0) (hin : off + 32 ≤ out.size) :
    decodeScalarWord? (.elem (.int (.uint bits))) out.toList off =
      if (calldataWord out off).toNat < 2 ^ bits.val then
        some (uint256Value (calldataWord out off), off + 32) else none := by
  have hl : ((out.toList.drop off).take 32).length = 32 := by
    simp only [List.length_take, List.length_drop, byteArray_toList_eq, Array.length_toList]
    change min 32 (out.size - off) = 32
    omega
  simp only [decodeScalarWord?, readWord?, readBytes?, hl, if_true, bind, Option.bind,
    decode_word_at_eq_any out off hin, decodeABIWord?, hbits, if_false]
  by_cases hc : (calldataWord out off).toNat < 2 ^ bits.val
  · simp only [EVM.twoPow, show (↑(calldataWord out off).val : Nat) =
      (calldataWord out off).toNat from rfl, hc, if_true]
  · simp only [EVM.twoPow, show (↑(calldataWord out off).val : Nat) =
      (calldataWord out off).toNat from rfl, hc, if_false]

def marketUInt128 : ABIType := .elem (.int (.uint ⟨128, by decide⟩))

def marketFields (out : ByteArray) : List Value :=
  [uint256Value (calldataWord out 0), uint256Value (calldataWord out 32),
   uint256Value (calldataWord out 64), uint256Value (calldataWord out 96),
   uint256Value (calldataWord out 128), uint256Value (calldataWord out 160)]

def marketValue (out : ByteArray) : Value :=
  .struct "Market"
    (["totalSupplyAssets", "totalSupplyShares", "totalBorrowAssets", "totalBorrowShares",
      "lastUpdate", "fee"].zip (marketFields out))

def MarketChecks (out : ByteArray) : Prop :=
  192 ≤ out.size ∧ (calldataWord out 0).toNat < 2 ^ 128 ∧
    (calldataWord out 32).toNat < 2 ^ 128 ∧ (calldataWord out 64).toNat < 2 ^ 128 ∧
    (calldataWord out 96).toNat < 2 ^ 128 ∧ (calldataWord out 128).toNat < 2 ^ 128 ∧
    (calldataWord out 160).toNat < 2 ^ 128

instance (out : ByteArray) : Decidable (MarketChecks out) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

theorem marketScalarDecode_long {out : ByteArray} (hl : 192 ≤ out.size) :
    decodeScalarWords? (List.replicate 6 marketUInt128) out.toList 0 =
      if MarketChecks out then some (marketFields out) else none := by
  simp only [List.replicate, decodeScalarWords?, Nat.reduceAdd, marketUInt128,
    decodeScalarUint_at (out := out) (off := 0) ⟨128, by decide⟩ (by decide) (by omega),
    decodeScalarUint_at (out := out) (off := 32) ⟨128, by decide⟩ (by decide) (by omega),
    decodeScalarUint_at (out := out) (off := 64) ⟨128, by decide⟩ (by decide) (by omega),
    decodeScalarUint_at (out := out) (off := 96) ⟨128, by decide⟩ (by decide) (by omega),
    decodeScalarUint_at (out := out) (off := 128) ⟨128, by decide⟩ (by decide) (by omega),
    decodeScalarUint_at (out := out) (off := 160) ⟨128, by decide⟩ (by decide) (by omega)]
  by_cases h0 : (calldataWord out 0).toNat < 2 ^ 128
  · by_cases h32 : (calldataWord out 32).toNat < 2 ^ 128
    · by_cases h64 : (calldataWord out 64).toNat < 2 ^ 128
      · by_cases h96 : (calldataWord out 96).toNat < 2 ^ 128
        · by_cases h128 : (calldataWord out 128).toNat < 2 ^ 128
          · by_cases h160 : (calldataWord out 160).toNat < 2 ^ 128 <;>
              simp [-Nat.reducePow, h0, h32, h64, h96, h128, h160, MarketChecks, hl, marketFields]
          · simp [-Nat.reducePow, h0, h32, h64, h96, h128, MarketChecks, hl]
        · simp [-Nat.reducePow, h0, h32, h64, h96, MarketChecks, hl]
      · simp [-Nat.reducePow, h0, h32, h64, MarketChecks, hl]
    · simp [-Nat.reducePow, h0, h32, MarketChecks, hl]
  · simp [-Nat.reducePow, h0, MarketChecks, hl]

theorem marketScalarDecode_short {out : ByteArray} (hl : out.size < 192) :
    decodeScalarWords? (List.replicate 6 marketUInt128) out.toList 0 = none := by
  cases h : decodeScalarWords? (List.replicate 6 marketUInt128) out.toList 0 with
  | none => rfl
  | some vs =>
      have hlen := decodeScalarWords?_some_length (by omega) h
      simp only [List.length_replicate, Nat.reduceMul, Nat.zero_add,
        byteArray_toList_eq, Array.length_toList] at hlen
      change 192 ≤ out.size at hlen
      omega

theorem marketDecode {out : ByteArray} (hhi : out.size < 2 ^ 255) :
    config.externalABI.decode? "market" out =
      if MarketChecks out then some [marketValue out] else none := by
  change (decodeReturnValues? [.tuple (List.replicate 6 marketUInt128)] out).bind
    (fun vs ↦ match vs with
      | [.tuple fields] => if fields.length = 6 then
          some [Value.struct "Market"
            (["totalSupplyAssets", "totalSupplyShares", "totalBorrowAssets", "totalBorrowShares",
              "lastUpdate", "fee"].zip fields)] else none
      | _ => none) = _
  rw [scalarTupleReturnDecode (by decide) hhi]
  by_cases hl : 192 ≤ out.size
  · rw [marketScalarDecode_long hl]
    by_cases hc : MarketChecks out <;> simp [hc, marketValue, marketFields]
  · rw [marketScalarDecode_short (by omega)]
    simp [MarketChecks, hl]

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
