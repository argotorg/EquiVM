import Benchmarks.Morpho.MorphoBlue.Bytes32SliceABI

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def signatureABIType : ABIType := .tuple [.elem (.int (.uint ⟨8, by decide⟩)), abiBytes32, abiBytes32]

def signatureRecoveryWord (cd : ByteArray) : UInt256 := calldataWord cd 164

def signatureValue (cd : ByteArray) : Value :=
  .tuple [.int (Int.ofNat (signatureRecoveryWord cd).toNat),
    wordBytes32Value (calldataWord cd 196), wordBytes32Value (calldataWord cd 228)]

theorem decodeSignature (cd : ByteArray) (hl : 260 ≤ cd.size) :
    decodeReturnValueWithMode? .modern signatureABIType (cd.extract 164 260) =
      if (signatureRecoveryWord cd).toNat < 256 then some (signatureValue cd) else none := by
  apply decodeReturnValue_static rfl rfl (by rw [ByteArray.size_extract]; omega)
  rw [signatureABIType, decodeABIValue?]
  simp only [abiTupleHeadSize?, isDynamicABIType, staticABIEncodedSize?,
    bind, Option.bind_some, Bool.false_eq_true, ↓reduceIte, Nat.zero_add, Nat.add_zero]
  rw [decodeABIValues_static_cons rfl rfl, decodeABIValue_scalarWord_eq (by decide),
    decodeScalarWord_extract (by decide) hl]
  by_cases hv : (signatureRecoveryWord cd).toNat < 256
  · simp only [decodeABIWord?, show (8 : Nat) ≠ 0 by decide, ↓reduceIte,
      show (calldataWord cd (164 + (0 + 0))).val.val < EVM.twoPow 8 from hv,
      Option.map_some, Option.bind_some, Nat.zero_add]
    rw [decodeABIValues_static_cons rfl rfl, decodeBytes32_extract (by decide) hl]
    simp only [Option.bind_some, ↓reduceIte]
    rw [decodeABIValues_static_cons rfl rfl, decodeBytes32_extract (by decide) hl]
    simp only [Option.bind_some, ↓reduceIte, hv]
    simp only [decodeABIValues?, Option.map_some, Option.bind_some]; rfl
  · simp only [decodeABIWord?, show (8 : Nat) ≠ 0 by decide, ↓reduceIte,
      show ¬ (calldataWord cd (164 + (0 + 0))).val.val < EVM.twoPow 8 from hv,
      Option.map_none, Option.bind_none, hv]

end Benchmarks.Morpho.MorphoBlue
