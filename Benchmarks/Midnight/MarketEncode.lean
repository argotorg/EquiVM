import Benchmarks.Midnight.MarketData

/-! ABI bytes returned by a decoded market, including its collateral array. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem encodeCollateralArray (values : List CollateralData) :
    encodeABIValue? (.dynamicArray Model.collateralABI)
      (.array (values.map CollateralData.value)) =
      some (wordArrayBytes (UInt256.ofNat values.length ::
        values.flatMap CollateralData.words)).toList := by
  rw [encodeABIValue?]
  simp only [encodeABIArrayElems?, show isDynamicABIType Model.collateralABI = false from rfl,
    Bool.false_eq_true, if_false, CollateralData.array_encode, bind, Option.bind,
    List.length_map]
  simp only [natBytes, wordArrayBytes, byteArray_toList_append,
    word_toBytesBE_eq_toByteArray_toList]
  rfl

def MarketData.encodedWords (m : MarketData) : List UInt256 :=
  UInt256.ofNat 32 :: (m.words (UInt256.ofNat 256) ++
    UInt256.ofNat m.collaterals.length :: m.collaterals.flatMap CollateralData.words)

theorem MarketData.encodeValue (m : MarketData) :
    encodeABIValue? Model.marketABI m.value =
      some (wordArrayBytes (m.words (UInt256.ofNat 256) ++
        UInt256.ofNat m.collaterals.length :: m.collaterals.flatMap CollateralData.words)).toList := by
  have hchain := encodeABIValue_uint256 m.chainId
  have hmid := encodeABIValue_accountAddress m.midnight
  have hloan := encodeABIValue_accountAddress m.loanToken
  have hcoll := encodeCollateralArray m.collaterals
  have hmat := encodeABIValue_uint256 m.maturity
  have hrcf := encodeABIValue_uint256 m.rcfThreshold
  have henter := encodeABIValue_accountAddress m.enterGate
  have hliq := encodeABIValue_accountAddress m.liquidatorGate
  rw [Model.marketABI, MarketData.value, encodeABIValue?, encodeABIValues?]
  simp only [abiTupleHeadSize?, Model.u256, Model.addr, isDynamicABIType, staticABIEncodedSize?,
    Bool.false_eq_true, if_false, if_true, bind, Option.bind, encodeABIValuesFrom?,
    hchain, hmid, hloan, hcoll, hmat, hrcf, henter, hliq,
    List.nil_append, List.append_nil, List.length_nil, Nat.add_zero, Nat.reduceAdd]
  simp only [MarketData.words, List.cons_append, List.nil_append, wordArrayBytes,
    byteArray_toList_append, natBytes, word_toBytesBE_eq_toByteArray_toList,
    List.append_assoc]
  rfl

theorem MarketData.encodeReturn (m : MarketData) :
    encodeReturnValues? [Model.marketABI] [m.value] = some (wordArrayBytes m.encodedWords) := by
  simp only [encodeReturnValues?, encodeABIValues?, abiTupleHeadSize?,
    show isDynamicABIType Model.marketABI = true from rfl, if_true, bind, Option.bind,
    encodeABIValuesFrom?, MarketData.encodeValue, List.length_nil, Nat.add_zero,
    List.nil_append, List.append_nil]
  simp only [MarketData.encodedWords, wordArrayBytes, byteArray_toList_append, natBytes,
    word_toBytesBE_eq_toByteArray_toList]
  congr 1
  apply ByteArray.ext
  simp [byteArray_toList_eq]
  rfl

theorem MarketData.encodedWords_length (m : MarketData) :
    m.encodedWords.length = 10 + 4 * m.collaterals.length := by
  have hc : (m.collaterals.flatMap CollateralData.words).length = 4 * m.collaterals.length := by
    induction m.collaterals with
    | nil => rfl
    | cons c cs ih =>
      simp only [List.flatMap_cons, List.length_append, CollateralData.words, List.length_cons,
        List.length_nil, ih]
      omega
  simp only [MarketData.encodedWords, MarketData.words, List.length_cons, List.length_append,
    List.length_nil, hc]
  omega

end Benchmarks.Midnight
