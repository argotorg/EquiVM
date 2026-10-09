import Benchmarks.Morpho.MorphoBlue.AccrueSourceCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def oraclePriceSelector : ByteArray := ⟨#[160, 53, 177, 254]⟩
def oraclePriceSelectorWord : UInt256 :=
  UInt256.ofNat 72464927124685711895252664195178772226123872012682517813167109100718830649344

set_option maxHeartbeats 0 in
theorem oraclePriceSelectorFact :
    (KEC (ABI.printSignature ⟨"price", []⟩).toUTF8).extract 0 4 = oraclePriceSelector := by
  have hs : ABI.printSignature ⟨"price", []⟩ = "price()" := by decide +kernel
  rw [hs]
  decide +kernel

theorem oraclePriceSelectorWord_bytes :
    oraclePriceSelectorWord.toByteArray.extract 0 4 = oraclePriceSelector := by decide +kernel

theorem encodeOraclePrice : config.externalABI.encode? "price" [] = some oraclePriceSelector := by
  change (do
    let sig ← Syntax.externalSignature "price"
    ABI.encodeCallWithSelector? ((KEC (ABI.printSignature sig).toUTF8).extract 0 4) sig.paramTypes []) = _
  simp only [Syntax.externalSignature, bind, Option.bind, oraclePriceSelectorFact,
    encodeCallWithSelector?, encodeABIValues?, abiTupleHeadSize?, encodeABIValuesFrom?,
    pure, List.toByteArray]
  decide +kernel

theorem oraclePriceCallMem_read (mem : ByteArray) (off : Nat) (hgap : off - mem.size < USize.size) :
    (writeWord mem off oraclePriceSelectorWord).readWithPadding off 4 = oraclePriceSelector := by
  have hh := writeWord_read_window mem off 0 4 oraclePriceSelectorWord (by decide) (by decide) (by decide) hgap
  simpa only [Nat.add_zero, Nat.zero_add, oraclePriceSelectorWord_bytes] using hh

theorem decodeOraclePrice_word {out : ByteArray} (hlen : 32 ≤ out.size) (hhi : out.size < 2 ^ 255) :
    config.externalABI.decode? "price" out = some [.int (Int.ofNat (calldataWord out 0).toNat)] :=
  decodeBorrowRate_word hlen hhi

theorem decodeOraclePrice_short {out : ByteArray} (hlen : out.size < 32) :
    config.externalABI.decode? "price" out = none := decodeBorrowRate_short hlen

end Benchmarks.Morpho.MorphoBlue
