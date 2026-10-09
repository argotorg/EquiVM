import Benchmarks.Morpho.MorphoBlue.MarketParamsABI
import Benchmarks.Morpho.MorphoBlue.MarketStateCommon
import Benchmarks.Morpho.MorphoBlue.WordBufferCommon
import Reasoning.ABIComposite

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def borrowRateSelector : ByteArray := ⟨#[148, 81, 254, 212]⟩

def borrowRateSelectorWord : UInt256 :=
  UInt256.ofNat 67087174961651252849085867703104089940080361473223925077705643131997698129920

set_option maxHeartbeats 0 in
theorem borrowRateSelectorFact :
    (KEC (ABI.printSignature ⟨"borrowRate", [Syntax.marketParamsABI, Syntax.marketABI]⟩).toUTF8).extract 0 4 =
      borrowRateSelector := by
  have hsig : ABI.printSignature ⟨"borrowRate", [Syntax.marketParamsABI, Syntax.marketABI]⟩ =
      "borrowRate((address,address,address,address,uint256),(uint128,uint128,uint128,uint128,uint128,uint128))" := by
    simp [ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr,
      Syntax.marketParamsABI, Syntax.marketABI, Syntax.addressABI, Syntax.uint256ABI,
      Syntax.uint128ABI, show Nat.repr 256 = "256" by decide +kernel,
      show Nat.repr 128 = "128" by decide +kernel]
    <;> decide +kernel
  rw [hsig]
  decide +kernel

theorem borrowRateSelectorWord_bytes :
    borrowRateSelectorWord.toByteArray.extract 0 4 = borrowRateSelector := by decide +kernel

def borrowRateCalldata (p : MarketParamsWords) (σ : AccountMap) (I : ExecutionEnv)
    (id : UInt256) : ByteArray :=
  borrowRateSelector ++ returnWordBytes (p.toList ++ marketStateWords σ I id)

theorem borrowRateCalldata_size (p : MarketParamsWords) (σ : AccountMap) (I : ExecutionEnv)
    (id : UInt256) : (borrowRateCalldata p σ I id).size = 356 := by
  rw [borrowRateCalldata, ByteArray.size_append, returnWordBytes_size]
  rfl

theorem encodeBorrowRate (p : MarketParamsWords) (hc : p.Canonical)
    (σ : AccountMap) (I : ExecutionEnv) (id : UInt256) :
    config.externalABI.encode? "borrowRate" [p.value, marketStateValue σ I id] =
      some (borrowRateCalldata p σ I id) := by
  have hhead : abiTupleHeadSize? [Syntax.marketParamsABI, Syntax.marketABI] = some 352 := by
    simp [abiTupleHeadSize?, Syntax.marketParamsABI, Syntax.marketABI, Syntax.addressABI,
      Syntax.uint256ABI, Syntax.uint128ABI, staticABIEncodedSize?, staticABIEncodedSizeList?,
      isDynamicABIType, isDynamicABITypeList]
  change (do
    let sig ← Syntax.externalSignature "borrowRate"
    ABI.encodeCallWithSelector? ((KEC (ABI.printSignature sig).toUTF8).extract 0 4)
      sig.paramTypes [p.value, marketStateValue σ I id]) = _
  simp only [Syntax.externalSignature, bind, Option.bind, borrowRateSelectorFact,
    encodeCallWithSelector?, encodeABIValues?, hhead, encodeABIValuesFrom?,
    encodeMarketParams p hc, encodeMarketState, show isDynamicABIType Syntax.marketParamsABI = false from rfl,
    show isDynamicABIType Syntax.marketABI = false from rfl, Bool.false_eq_true, ↓reduceIte,
    List.nil_append, List.append_nil]
  rw [borrowRateCalldata, returnWordBytes_append, MarketParamsWords.bytes]
  congr 2
  rw [List.toByteArray_append, byteArray_toList_toByteArray, byteArray_toList_toByteArray]

theorem borrowRateCalldata_read (p : MarketParamsWords) (σ : AccountMap) (I : ExecutionEnv)
    (id : UInt256) (mem : ByteArray) (off : Nat) (hgap : off - mem.size < USize.size) :
    (staticWordCallMem borrowRateSelectorWord (p.toList ++ marketStateWords σ I id) mem off).readWithPadding
      off 356 = borrowRateCalldata p σ I id := by
  have h := staticWordCallMem_read borrowRateSelectorWord
    (p.toList ++ marketStateWords σ I id) mem off (by simp [MarketParamsWords.toList]) hgap
  rw [borrowRateSelectorWord_bytes] at h
  exact h

theorem decodeBorrowRate_ok {out : ByteArray} (hlen : 32 ≤ out.size)
    (hhi : out.size < 2 ^ 255) :
    config.externalABI.decode? "borrowRate" out =
      some [.int (Int.ofNat (fromByteArrayBigEndian (out.extract 0 32)))] := by
  change (ABI.decodeReturnValue? abiUInt256 out).map (fun v ↦ [v]) = _
  rw [decodeReturnValue?, decodeReturnValues_uint256_ok hlen hhi]
  rfl

theorem decodeBorrowRate_short {out : ByteArray} (hlen : out.size < 32) :
    config.externalABI.decode? "borrowRate" out = none := by
  change (ABI.decodeReturnValue? abiUInt256 out).map (fun v ↦ [v]) = _
  rw [decodeReturnValue?, decodeReturnValues_uint256_none_short hlen]
  rfl

end Benchmarks.Morpho.MorphoBlue
