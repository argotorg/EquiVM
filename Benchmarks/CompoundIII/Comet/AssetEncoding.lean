import Benchmarks.CompoundIII.Comet.AssetDecode
import Benchmarks.CompoundIII.Comet.StaticReturns
import Reasoning.ABIViews

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

-- LIBRARY CANDIDATE: the outer tuple wrapper does not change static scalar return bytes.
theorem encodeReturn_staticTuple {types : List ABIType} {values : List Value}
    (hs : types.all isABIScalarWordType = true) :
    encodeReturnValues? [.tuple types] [.tuple values] = encodeReturnValues? types values := by
  have hd : isDynamicABIType (.tuple types) = false := (scalarTuple_static hs 0).1
  have hz : staticABIEncodedSize? (.tuple types) = some (32 * types.length) := by
    simpa only [staticABIEncodedSize?, Nat.zero_add] using (scalarTuple_static hs 0).2
  have hh : abiTupleHeadSize? [.tuple types] = some (32 * types.length) := by
    simp [abiTupleHeadSize?, hd, hz]
  simp only [encodeReturnValues?]
  rw [encodeABIValues?, hh]
  simp only [bind, Option.bind]
  rw [encodeABIValuesFrom?, encodeABIValue?]
  cases encodeABIValues? types values <;>
    simp only [bind, Option.bind, hd, Bool.false_eq_true, if_false,
      encodeABIValuesFrom?, List.nil_append, List.append_nil]

-- GENERALIZES the masked-address encoding lemma to an already canonical word.
theorem addressWordEncoding (w : UInt256) (hc : w.toNat < 2^160) :
    encodeABIValue? abiAddress (.address (AccountAddress.ofNat w.toNat)) =
      some (EVM.Word.toBytesBE w) := by
  have he := encodeABIValue_address_word w
  rw [solcAddrMask_clean hc] at he
  rw [word_toBytesBE_eq_toByteArray_toList]
  exact he

def assetWords (out : ByteArray) : List UInt256 :=
  (List.range 8).map fun j ↦ calldataWord out (32 * j)

def assetScalars (out : ByteArray) (hc : AssetCanonical out) : List ScalarReturn :=
  [⟨.int (.uint ⟨8, by decide⟩), .int (calldataWord out 0).toNat,
      calldataWord out 0, uintWordEncoding _ _ (by decide) hc.1⟩,
    ⟨.address, .address (AccountAddress.ofNat (calldataWord out 32).toNat),
      calldataWord out 32, addressWordEncoding _ hc.2.1⟩,
    ⟨.address, .address (AccountAddress.ofNat (calldataWord out 64).toNat),
      calldataWord out 64, addressWordEncoding _ hc.2.2.1⟩,
    ⟨.int (.uint ⟨64, by decide⟩), .int (calldataWord out 96).toNat,
      calldataWord out 96, uintWordEncoding _ _ (by decide) hc.2.2.2.1⟩,
    ⟨.int (.uint ⟨64, by decide⟩), .int (calldataWord out 128).toNat,
      calldataWord out 128, uintWordEncoding _ _ (by decide) hc.2.2.2.2.1⟩,
    ⟨.int (.uint ⟨64, by decide⟩), .int (calldataWord out 160).toNat,
      calldataWord out 160, uintWordEncoding _ _ (by decide) hc.2.2.2.2.2.1⟩,
    ⟨.int (.uint ⟨64, by decide⟩), .int (calldataWord out 192).toNat,
      calldataWord out 192, uintWordEncoding _ _ (by decide) hc.2.2.2.2.2.2.1⟩,
    ⟨.int (.uint ⟨128, by decide⟩), .int (calldataWord out 224).toNat,
      calldataWord out 224, uintWordEncoding _ _ (by decide) hc.2.2.2.2.2.2.2⟩]

theorem assetReturnEncoding {out : ByteArray} (hc : AssetCanonical out) :
    encodeReturnValues? [assetInfoType] [assetTuple out] = some (wordBytes (assetWords out)) := by
  have hs := scalarReturnsEncoding (assetScalars out hc)
  change encodeReturnValues? [.tuple assetInfoTypes]
    [.tuple ((assetScalars out hc).map ScalarReturn.value)] = _
  rw [encodeReturn_staticTuple (by decide)]
  exact hs

end Benchmarks.CompoundIII.Comet
