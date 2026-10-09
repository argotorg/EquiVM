import Benchmarks.Morpho.MorphoBlue.ScalarSliceABI

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000
set_option maxHeartbeats 800000

structure AuthorizationWords where
  authorizer : UInt256
  authorized : UInt256
  enabled : UInt256
  nonce : UInt256
  deadline : UInt256

def authorizationFromCalldata (cd : ByteArray) : AuthorizationWords :=
  ⟨calldataWord cd 4, calldataWord cd 36, calldataWord cd 68,
    calldataWord cd 100, calldataWord cd 132⟩

def AuthorizationWords.Canonical (a : AuthorizationWords) : Prop :=
  a.authorizer.toNat < EVM.addressModulus ∧ a.authorized.toNat < EVM.addressModulus ∧
    (a.enabled = ⟨0⟩ ∨ a.enabled = ⟨1⟩)

instance (a : AuthorizationWords) : Decidable a.Canonical := by
  unfold AuthorizationWords.Canonical
  infer_instance

def AuthorizationWords.value (a : AuthorizationWords) : Value :=
  .tuple [.address (AccountAddress.ofNat a.authorizer.toNat),
    .address (AccountAddress.ofNat a.authorized.toNat), .bool (decide (a.enabled ≠ ⟨0⟩)),
    .int (Int.ofNat a.nonce.toNat), .int (Int.ofNat a.deadline.toNat)]

def authorizationABIFields : List ABIType :=
  [abiAddress, abiAddress, abiBool, abiUInt256, abiUInt256]

def authorizationABIType : ABIType := .tuple authorizationABIFields

theorem decodeAuthorization (cd : ByteArray) (hl : 164 ≤ cd.size) :
    decodeReturnValueWithMode? .modern authorizationABIType (cd.extract 4 164) =
      if (authorizationFromCalldata cd).Canonical then
        some (authorizationFromCalldata cd).value else none := by
  apply decodeReturnValue_static rfl rfl
    (by rw [ByteArray.size_extract]; omega)
  rw [authorizationABIType, decodeABIValue_scalarTuple_eq (by decide)]
  simp only [authorizationABIFields, decodeScalarWords?]
  rw [decodeScalarWord_extract (by decide) hl]
  simp only [show 4 + 0 = 4 from rfl, show 0 + 32 = 32 from rfl]
  by_cases h0 : (calldataWord cd 4).toNat < EVM.addressModulus
  swap
  · simp only [decodeABIWord?, show ¬ (calldataWord cd 4).val.val < EVM.addressModulus from h0,
      ↓reduceIte, Option.map_none, bind, Option.bind_none]
    rw [if_neg (fun hc : (authorizationFromCalldata cd).Canonical ↦ h0 hc.1)]
    rfl
  simp only [decodeABIWord?, show (calldataWord cd 4).val.val < EVM.addressModulus from h0,
    ↓reduceIte, Option.map_some, bind, Option.bind_some]
  rw [decodeScalarWord_extract (by decide) hl]
  by_cases h1 : (calldataWord cd 36).toNat < EVM.addressModulus
  swap
  · simp only [show 4 + 32 = 36 from rfl, decodeABIWord?,
      show ¬ (calldataWord cd 36).val.val < EVM.addressModulus from h1,
      ↓reduceIte, Option.map_none, Option.bind_none]
    rw [if_neg (fun hc : (authorizationFromCalldata cd).Canonical ↦ h1 hc.2.1)]
    rfl
  simp only [show 4 + 32 = 36 from rfl, decodeABIWord?,
    show (calldataWord cd 36).val.val < EVM.addressModulus from h1,
    ↓reduceIte, Option.map_some, Option.bind_some]
  rw [decodeScalarWord_extract (by decide) hl, decodeABIWord_bool_result]
  by_cases hb : calldataWord cd 68 = ⟨0⟩ ∨ calldataWord cd 68 = ⟨1⟩
  swap
  · simp only [show 4 + (32 + 32) = 68 from rfl, hb, ↓reduceIte,
      Option.map_none, Option.bind_none]
    rw [if_neg (fun hc : (authorizationFromCalldata cd).Canonical ↦ hb hc.2.2)]
    rfl
  simp only [show 4 + (32 + 32) = 68 from rfl, hb, ↓reduceIte,
    Option.map_some, Option.bind_some]
  rw [decodeScalarWord_extract (by decide) hl]
  simp only [decodeABIWord?, show (256 : Nat) ≠ 0 from by decide, ↓reduceIte,
    show (calldataWord cd (4 + (32 + 32 + 32))).val.val < EVM.twoPow 256 from
      (calldataWord cd _).val.isLt, Option.map_some, Option.bind_some]
  rw [decodeScalarWord_extract (by decide) hl]
  simp only [decodeABIWord?, show (256 : Nat) ≠ 0 from by decide, ↓reduceIte,
    show (calldataWord cd (4 + (32 + 32 + 32 + 32))).val.val < EVM.twoPow 256 from
      (calldataWord cd _).val.isLt, Option.map_some, Option.bind_some, pure]
  rw [if_pos (show (authorizationFromCalldata cd).Canonical from ⟨h0, h1, hb⟩)]
  rfl

end Benchmarks.Morpho.MorphoBlue
