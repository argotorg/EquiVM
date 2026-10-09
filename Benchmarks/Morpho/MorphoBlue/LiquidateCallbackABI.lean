import Benchmarks.Morpho.MorphoBlue.WordBytesABI

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def liquidateCallbackSelector : ByteArray := ⟨#[207, 126, 161, 150]⟩

def liquidateCallbackSelectorWord : UInt256 :=
  UInt256.ofNat 93852497612052052172171342840208435377766735308355310630824731532202946330624

set_option maxHeartbeats 0 in
theorem liquidateCallbackSelectorFact :
    (KEC (ABI.printSignature ⟨"onMorphoLiquidate", [abiUInt256, .bytes]⟩).toUTF8).extract 0 4 =
      liquidateCallbackSelector := by
  have hs : ABI.printSignature ⟨"onMorphoLiquidate", [abiUInt256, .bytes]⟩ =
      "onMorphoLiquidate(uint256,bytes)" := by
    simp [ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr,
      abiUInt256, abiUInt256Int, show Nat.repr 256 = "256" by decide +kernel]
    decide +kernel
  rw [hs]
  decide +kernel

theorem liquidateCallbackSelectorWord_bytes :
    liquidateCallbackSelectorWord.toByteArray.extract 0 4 = liquidateCallbackSelector := by decide +kernel

theorem liquidateCallback_encode (word : UInt256) (data : ByteArray) :
    config.externalABI.encode? "onMorphoLiquidate" [.int (Int.ofNat word.toNat), .bytes data] =
      some (wordBytesCalldata liquidateCallbackSelector word data) := by
  change (do
    let sig ← Syntax.externalSignature "onMorphoLiquidate"
    ABI.encodeCallWithSelector? ((KEC (ABI.printSignature sig).toUTF8).extract 0 4)
      sig.paramTypes [.int (Int.ofNat word.toNat), .bytes data]) = _
  rw [show Syntax.externalSignature "onMorphoLiquidate" =
    some ⟨"onMorphoLiquidate", [abiUInt256, ABIType.bytes]⟩ from rfl]
  simp only [bind, Option.bind, liquidateCallbackSelectorFact]
  exact encodeCallWithSelector_of_return _ (wordBytesArguments_encode word data)

end Benchmarks.Morpho.MorphoBlue
