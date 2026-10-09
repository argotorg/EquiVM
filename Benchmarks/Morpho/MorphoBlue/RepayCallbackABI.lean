import Benchmarks.Morpho.MorphoBlue.WordBytesABI

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def repayCallbackSelector : ByteArray := ⟨#[5, 180, 89, 28]⟩

def repayCallbackSelectorWord : UInt256 :=
  UInt256.ofNat 2580211724879812161586610295032826124923053499976970674396983989444229988352

set_option maxHeartbeats 0 in
theorem repayCallbackSelectorFact :
    (KEC (ABI.printSignature ⟨"onMorphoRepay", [abiUInt256, .bytes]⟩).toUTF8).extract 0 4 =
      repayCallbackSelector := by
  have hs : ABI.printSignature ⟨"onMorphoRepay", [abiUInt256, .bytes]⟩ =
      "onMorphoRepay(uint256,bytes)" := by
    simp [ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr,
      abiUInt256, abiUInt256Int, show Nat.repr 256 = "256" by decide +kernel]
    decide +kernel
  rw [hs]
  decide +kernel

theorem repayCallbackSelectorWord_bytes :
    repayCallbackSelectorWord.toByteArray.extract 0 4 = repayCallbackSelector := by decide +kernel

theorem repayCallback_encode (word : UInt256) (data : ByteArray) :
    config.externalABI.encode? "onMorphoRepay" [.int (Int.ofNat word.toNat), .bytes data] =
      some (wordBytesCalldata repayCallbackSelector word data) := by
  change (do
    let sig ← Syntax.externalSignature "onMorphoRepay"
    ABI.encodeCallWithSelector? ((KEC (ABI.printSignature sig).toUTF8).extract 0 4)
      sig.paramTypes [.int (Int.ofNat word.toNat), .bytes data]) = _
  rw [show Syntax.externalSignature "onMorphoRepay" =
    some ⟨"onMorphoRepay", [abiUInt256, ABIType.bytes]⟩ from rfl]
  simp only [bind, Option.bind, repayCallbackSelectorFact]
  exact encodeCallWithSelector_of_return _ (wordBytesArguments_encode word data)

end Benchmarks.Morpho.MorphoBlue
