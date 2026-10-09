import Benchmarks.Morpho.MorphoBlue.WordBytesABI

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def flashLoanCallbackSelector : ByteArray := ⟨#[49, 245, 112, 114]⟩

def flashLoanCallbackSelectorWord : UInt256 :=
  UInt256.ofNat 22596983180475517789357921021697479846006262875981638108336662756855948247040

set_option maxHeartbeats 0 in
theorem flashLoanCallbackSelectorFact :
    (KEC (ABI.printSignature ⟨"onMorphoFlashLoan", [abiUInt256, .bytes]⟩).toUTF8).extract 0 4 =
      flashLoanCallbackSelector := by
  have hs : ABI.printSignature ⟨"onMorphoFlashLoan", [abiUInt256, .bytes]⟩ =
      "onMorphoFlashLoan(uint256,bytes)" := by
    simp [ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr,
      abiUInt256, abiUInt256Int, show Nat.repr 256 = "256" by decide +kernel]
    decide +kernel
  rw [hs]
  decide +kernel

theorem flashLoanCallbackSelectorWord_bytes :
    flashLoanCallbackSelectorWord.toByteArray.extract 0 4 = flashLoanCallbackSelector := by decide +kernel

theorem flashLoanCallback_encode (word : UInt256) (data : ByteArray) :
    config.externalABI.encode? "onMorphoFlashLoan" [.int (Int.ofNat word.toNat), .bytes data] =
      some (wordBytesCalldata flashLoanCallbackSelector word data) := by
  change (do
    let sig ← Syntax.externalSignature "onMorphoFlashLoan"
    ABI.encodeCallWithSelector? ((KEC (ABI.printSignature sig).toUTF8).extract 0 4)
      sig.paramTypes [.int (Int.ofNat word.toNat), .bytes data]) = _
  rw [show Syntax.externalSignature "onMorphoFlashLoan" =
    some ⟨"onMorphoFlashLoan", [abiUInt256, ABIType.bytes]⟩ from rfl]
  simp only [bind, Option.bind, flashLoanCallbackSelectorFact]
  exact encodeCallWithSelector_of_return _ (wordBytesArguments_encode word data)

end Benchmarks.Morpho.MorphoBlue
