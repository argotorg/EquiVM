import Benchmarks.Morpho.MorphoBlue.WordBytesABI

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def supplyCallbackSelector : ByteArray := ⟨#[32, 117, 190, 3]⟩

def supplyCallbackSelectorWord : UInt256 :=
  UInt256.ofNat 14682043673929325603079150921287787843905421430755663564099624249453730332672

set_option maxHeartbeats 0 in
theorem supplyCallbackSelectorFact :
    (KEC (ABI.printSignature ⟨"onMorphoSupply", [abiUInt256, .bytes]⟩).toUTF8).extract 0 4 =
      supplyCallbackSelector := by
  have hs : ABI.printSignature ⟨"onMorphoSupply", [abiUInt256, .bytes]⟩ =
      "onMorphoSupply(uint256,bytes)" := by
    simp [ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr,
      abiUInt256, abiUInt256Int, show Nat.repr 256 = "256" by decide +kernel]
    decide +kernel
  rw [hs]
  decide +kernel

theorem supplyCallbackSelectorWord_bytes :
    supplyCallbackSelectorWord.toByteArray.extract 0 4 = supplyCallbackSelector := by decide +kernel

theorem supplyCallback_encode (word : UInt256) (data : ByteArray) :
    config.externalABI.encode? "onMorphoSupply" [.int (Int.ofNat word.toNat), .bytes data] =
      some (wordBytesCalldata supplyCallbackSelector word data) := by
  change (do
    let sig ← Syntax.externalSignature "onMorphoSupply"
    ABI.encodeCallWithSelector? ((KEC (ABI.printSignature sig).toUTF8).extract 0 4)
      sig.paramTypes [.int (Int.ofNat word.toNat), .bytes data]) = _
  rw [show Syntax.externalSignature "onMorphoSupply" =
    some ⟨"onMorphoSupply", [abiUInt256, ABIType.bytes]⟩ from rfl]
  simp only [bind, Option.bind, supplyCallbackSelectorFact]
  exact encodeCallWithSelector_of_return _ (wordBytesArguments_encode word data)

end Benchmarks.Morpho.MorphoBlue
