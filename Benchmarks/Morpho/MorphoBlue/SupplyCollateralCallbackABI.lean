import Benchmarks.Morpho.MorphoBlue.WordBytesABI

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def supplyCollateralCallbackSelector : ByteArray := ⟨#[177, 2, 47, 223]⟩

def supplyCollateralCallbackSelectorWord : UInt256 :=
  UInt256.ofNat 80063238287514113441828226592934501051780510726226695703038219330117376671744

set_option maxHeartbeats 0 in
theorem supplyCollateralCallbackSelectorFact :
    (KEC (ABI.printSignature ⟨"onMorphoSupplyCollateral", [abiUInt256, .bytes]⟩).toUTF8).extract 0 4 =
      supplyCollateralCallbackSelector := by
  have hs : ABI.printSignature ⟨"onMorphoSupplyCollateral", [abiUInt256, .bytes]⟩ =
      "onMorphoSupplyCollateral(uint256,bytes)" := by
    simp [ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr,
      abiUInt256, abiUInt256Int, show Nat.repr 256 = "256" by decide +kernel]
    decide +kernel
  rw [hs]
  decide +kernel

theorem supplyCollateralCallbackSelectorWord_bytes :
    supplyCollateralCallbackSelectorWord.toByteArray.extract 0 4 = supplyCollateralCallbackSelector := by decide +kernel

theorem supplyCollateralCallback_encode (word : UInt256) (data : ByteArray) :
    config.externalABI.encode? "onMorphoSupplyCollateral" [.int (Int.ofNat word.toNat), .bytes data] =
      some (wordBytesCalldata supplyCollateralCallbackSelector word data) := by
  change (do
    let sig ← Syntax.externalSignature "onMorphoSupplyCollateral"
    ABI.encodeCallWithSelector? ((KEC (ABI.printSignature sig).toUTF8).extract 0 4)
      sig.paramTypes [.int (Int.ofNat word.toNat), .bytes data]) = _
  rw [show Syntax.externalSignature "onMorphoSupplyCollateral" =
    some ⟨"onMorphoSupplyCollateral", [abiUInt256, ABIType.bytes]⟩ from rfl]
  simp only [bind, Option.bind, supplyCollateralCallbackSelectorFact]
  exact encodeCallWithSelector_of_return _ (wordBytesArguments_encode word data)

end Benchmarks.Morpho.MorphoBlue
