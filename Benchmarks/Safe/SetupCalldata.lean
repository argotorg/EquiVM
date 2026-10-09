import Benchmarks.Safe.BoundedCalldataWords
import Benchmarks.Safe.BoundedCalldataBytes

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

structure SetupInput where
  owners : List UInt256
  threshold : UInt256
  target : UInt256
  payload : ByteArray
  fallbackHandler : UInt256
  paymentToken : UInt256
  payment : UInt256
  paymentReceiver : UInt256

def SetupInput.args (p : SetupInput) : Store :=
  ((((((((∅ : Store).insert "_owners" (.array (p.owners.map addressArrayValue))).insert
    "_threshold" (uint256Value p.threshold)).insert "to" (addressArrayValue p.target)).insert
    "data" (.bytes p.payload)).insert
    "fallbackHandler" (addressArrayValue p.fallbackHandler)).insert
    "paymentToken" (addressArrayValue p.paymentToken)).insert
    "payment" (uint256Value p.payment)).insert "paymentReceiver" (addressArrayValue
      p.paymentReceiver)

def SetupInput.frame (p : SetupInput) : Frame := { contract := contract, locals := p.args }

def setupInput (cd : ByteArray) (owners : List UInt256) (payload : ByteArray) : SetupInput :=
  { owners := owners
    threshold := calldataWord cd 36
    target := calldataWord cd 68
    payload := payload
    fallbackHandler := calldataWord cd 132
    paymentToken := calldataWord cd 164
    payment := calldataWord cd 196
    paymentReceiver := calldataWord cd 228 }

def setupNames : List Ident :=
  ["_owners", "_threshold", "to", "data", "fallbackHandler", "paymentToken", "payment",
    "paymentReceiver"]

def setupTypes : List ABIType :=
  [.dynamicArray abiAddress, abiUInt256, abiAddress, .bytes, abiAddress, abiAddress,
    abiUInt256, abiAddress]

def setupCalldataTail (cd : ByteArray) : Option Store := do
  if solcMaxU64 < (calldataWord cd 4).toNat then none else
  let owners ← boundedCalldataWords cd (calldataWord cd 4).toNat
  if ¬∀ w ∈ owners, w.toNat < EVM.addressModulus then none else
  if ¬(calldataWord cd 68).toNat < EVM.addressModulus then none else
  if solcMaxU64 < (calldataWord cd 100).toNat then none else
  let payload ← boundedCalldataBytes cd (calldataWord cd 100).toNat
  if ¬(calldataWord cd 132).toNat < EVM.addressModulus then none else
  if ¬(calldataWord cd 164).toNat < EVM.addressModulus then none else
  if ¬(calldataWord cd 228).toNat < EVM.addressModulus then none else
  some (setupInput cd owners payload).args

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem decodeSetupCore {cd : ByteArray} (hh : 260 ≤ cd.size) (hs : cd.size < 2 ^ 255) :
    decodeCalldata setupNames setupTypes cd = setupCalldataTail cd := by
  unfold setupTypes
  rw [decodeDynamicCalldata (headSize := 256) (by omega)
    (by decide +kernel)
    (by simp [abiTupleHeadSize?, staticABIEncodedSize?, isDynamicABIType, bind, Option.bind]),
    if_neg (by omega), if_neg (by omega)]
  simp only [decodeABIValues?, isDynamicABIType, staticABIEncodedSize?, bind, Option.bind,
    Bool.false_eq_true, if_false, if_true, Nat.zero_add, Nat.reduceAdd, Nat.add_zero]
  rw [readNat_drop4_at_eq_calldataWord (cd := cd) 0 (by omega)]
  simp only [Nat.reduceAdd, solcMaxLen_modern]
  unfold setupCalldataTail
  by_cases ho : solcMaxU64 < (calldataWord cd 4).toNat
  · simp only [ho, if_true]
  simp only [ho, if_false]
  rw [decodeBoundedCalldataAddresses]
  cases howners : boundedCalldataWords cd (calldataWord cd 4).toNat with
  | none => rfl
  | some owners =>
      dsimp only [bind, Option.bind]
      by_cases hc : ∀ w ∈ owners, w.toNat < EVM.addressModulus
      swap
      · rw [if_neg hc, if_pos hc]
      rw [if_pos hc, if_neg (not_not_intro hc)]
      dsimp only [bind, Option.bind]
      rw [decodeUint256Calldata (cd := cd) 32 (by omega)]
      simp only [Nat.reduceAdd, ↓reduceIte]
      rw [decodeAddressCalldata (cd := cd) 64 (by omega)]
      simp only [Nat.reduceAdd]
      by_cases ht : (calldataWord cd 68).toNat < EVM.addressModulus
      swap
      · rw [if_neg ht, if_pos ht]
      rw [if_pos ht, if_neg (not_not_intro ht)]
      dsimp only [bind, Option.bind]
      simp only [Nat.reduceAdd, ↓reduceIte]
      rw [readNat_drop4_at_eq_calldataWord (cd := cd) 96 (by omega)]
      simp only [Nat.reduceAdd, solcMaxLen_modern]
      by_cases hd : solcMaxU64 < (calldataWord cd 100).toNat
      · simp only [hd, if_true]
      simp only [hd, if_false]
      rw [decodeBoundedCalldataBytes]
      cases hp : boundedCalldataBytes cd (calldataWord cd 100).toNat with
      | none => rfl
      | some payload =>
          dsimp only [bind, Option.bind]
          rw [decodeAddressCalldata (cd := cd) 128 (by omega)]
          simp only [Nat.reduceAdd]
          by_cases hf : (calldataWord cd 132).toNat < EVM.addressModulus
          swap
          · rw [if_neg hf, if_pos hf]
          rw [if_pos hf, if_neg (not_not_intro hf)]
          dsimp only [bind, Option.bind]
          simp only [Nat.reduceAdd, ↓reduceIte]
          rw [decodeAddressCalldata (cd := cd) 160 (by omega)]
          simp only [Nat.reduceAdd]
          by_cases hk : (calldataWord cd 164).toNat < EVM.addressModulus
          swap
          · rw [if_neg hk, if_pos hk]
          rw [if_pos hk, if_neg (not_not_intro hk)]
          dsimp only [bind, Option.bind]
          simp only [Nat.reduceAdd, ↓reduceIte]
          rw [decodeUint256Calldata (cd := cd) 192 (by omega)]
          simp only [Nat.reduceAdd, ↓reduceIte]
          rw [decodeAddressCalldata (cd := cd) 224 (by omega)]
          simp only [Nat.reduceAdd]
          by_cases hr : (calldataWord cd 228).toNat < EVM.addressModulus
          swap
          · rw [if_neg hr, if_pos hr]
          rw [if_pos hr, if_neg (not_not_intro hr)]
          simp [setupNames, setupInput, SetupInput.args, decodeCalldata.insertValues,
            uint256Value, addressArrayValue]

end Benchmarks.Safe
