import Benchmarks.Dss.End.Common

/-!
# MakerDAO/Sky DSS End selector proofs

The selector theorems connect
the Solm transition signatures to the concrete selector bytes present in `endBytecode`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Dss.End

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- `keccak("wards(address)")[0:4] = 0xbf353dbb`. -/
theorem endWardsSelectorBytes :
    selectorOf wardsTransition = selectorBytes 0xbf 0x35 0x3d 0xbb := by
  simp [selectorOf, transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, wardsTransition, addr]; decide +kernel

/-- `keccak("vat()")[0:4] = 0x36569e77`. -/
theorem endVatSelectorBytes :
    selectorOf vatTransition = selectorBytes 0x36 0x56 0x9e 0x77 := by decide +kernel

/-- `keccak("cat()")[0:4] = 0xe4881813`. -/
theorem endCatSelectorBytes :
    selectorOf catTransition = selectorBytes 0xe4 0x88 0x18 0x13 := by decide +kernel

/-- `keccak("dog()")[0:4] = 0xc3b3ad7f`. -/
theorem endDogSelectorBytes :
    selectorOf dogTransition = selectorBytes 0xc3 0xb3 0xad 0x7f := by decide +kernel

/-- `keccak("vow()")[0:4] = 0x626cb3c5`. -/
theorem endVowSelectorBytes :
    selectorOf vowTransition = selectorBytes 0x62 0x6c 0xb3 0xc5 := by decide +kernel

/-- `keccak("pot()")[0:4] = 0x4ba2363a`. -/
theorem endPotSelectorBytes :
    selectorOf potTransition = selectorBytes 0x4b 0xa2 0x36 0x3a := by decide +kernel

/-- `keccak("spot()")[0:4] = 0x6f265b93`. -/
theorem endSpotSelectorBytes :
    selectorOf spotTransition = selectorBytes 0x6f 0x26 0x5b 0x93 := by decide +kernel

/-- `keccak("cure()")[0:4] = 0x840782ed`. -/
theorem endCureSelectorBytes :
    selectorOf cureTransition = selectorBytes 0x84 0x07 0x82 0xed := by decide +kernel

/-- `keccak("live()")[0:4] = 0x957aa58c`. -/
theorem endLiveSelectorBytes :
    selectorOf liveTransition = selectorBytes 0x95 0x7a 0xa5 0x8c := by decide +kernel

/-- `keccak("when()")[0:4] = 0xe2b0caef`. -/
theorem endWhenSelectorBytes :
    selectorOf whenTransition = selectorBytes 0xe2 0xb0 0xca 0xef := by decide +kernel

/-- `keccak("wait()")[0:4] = 0x64bd7013`. -/
theorem endWaitSelectorBytes :
    selectorOf waitTransition = selectorBytes 0x64 0xbd 0x70 0x13 := by decide +kernel

/-- `keccak("debt()")[0:4] = 0x0dca59c1`. -/
theorem endDebtSelectorBytes :
    selectorOf debtTransition = debtSelector := by decide +kernel

/-- `keccak("tag(bytes32)")[0:4] = 0xee6447b5`. -/
theorem endTagSelectorBytes :
    selectorOf tagTransition = selectorBytes 0xee 0x64 0x47 0xb5 := by
  simp [selectorOf, transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, tagTransition, bytes32]; decide +kernel

/-- `keccak("gap(bytes32)")[0:4] = 0xe6ee62aa`. -/
theorem endGapSelectorBytes :
    selectorOf gapTransition = selectorBytes 0xe6 0xee 0x62 0xaa := by
  simp [selectorOf, transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, gapTransition, bytes32]; decide +kernel

/-- `keccak("Art(bytes32)")[0:4] = 0xe1340a3d`. -/
theorem endArtSelectorBytes :
    selectorOf ArtTransition = selectorBytes 0xe1 0x34 0x0a 0x3d := by
  simp [selectorOf, transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ArtTransition, bytes32]; decide +kernel

/-- `keccak("fix(bytes32)")[0:4] = 0x63fad85e`. -/
theorem endFixSelectorBytes :
    selectorOf fixTransition = selectorBytes 0x63 0xfa 0xd8 0x5e := by
  simp [selectorOf, transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, fixTransition, bytes32]; decide +kernel

/-- `keccak("bag(address)")[0:4] = 0x9255f809`. -/
theorem endBagSelectorBytes :
    selectorOf bagTransition = selectorBytes 0x92 0x55 0xf8 0x09 := by
  simp [selectorOf, transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, bagTransition, addr]; decide +kernel

/-- `keccak("out(bytes32,address)")[0:4] = 0xc939ebfc`. -/
theorem endOutSelectorBytes :
    selectorOf outTransition = selectorBytes 0xc9 0x39 0xeb 0xfc := by
  simp [selectorOf, transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, outTransition, bytes32, addr]; decide +kernel

/-- `keccak("rely(address)")[0:4] = 0x65fae35e`. -/
theorem endRelySelectorBytes :
    selectorOf relyTransition = selectorBytes 0x65 0xfa 0xe3 0x5e := by
  simp [selectorOf, transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, relyTransition, addr]; decide +kernel

/-- `keccak("deny(address)")[0:4] = 0x9c52a7f1`. -/
theorem endDenySelectorBytes :
    selectorOf denyTransition = selectorBytes 0x9c 0x52 0xa7 0xf1 := by
  simp [selectorOf, transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, denyTransition, addr]; decide +kernel

/-- `keccak("file(bytes32,address)")[0:4] = 0xd4e8be83`. -/
theorem endFileAddressSelectorBytes :
    selectorOf fileAddressTransition = selectorBytes 0xd4 0xe8 0xbe 0x83 := by
  simp [selectorOf, transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, fileAddressTransition, bytes32, addr]; decide +kernel

/-- `keccak("file(bytes32,uint256)")[0:4] = 0x29ae8114`. -/
theorem endFileUintSelectorBytes :
    selectorOf fileUintTransition = selectorBytes 0x29 0xae 0x81 0x14 := by
  simp [selectorOf, transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, fileUintTransition, bytes32, uint256]; decide +kernel

/-- `keccak("cage()")[0:4] = 0x69245009`. -/
theorem endCageSelectorBytes :
    selectorOf cageTransition = selectorBytes 0x69 0x24 0x50 0x09 := by decide +kernel

/-- `keccak("cage(bytes32)")[0:4] = 0xe2702fdc`. -/
theorem endCageIlkSelectorBytes :
    selectorOf cageIlkTransition = selectorBytes 0xe2 0x70 0x2f 0xdc := by
  simp [selectorOf, transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, cageIlkTransition, bytes32]; decide +kernel

/-- `keccak("snip(bytes32,uint256)")[0:4] = 0x38c6de40`. -/
theorem endSnipSelectorBytes :
    selectorOf snipTransition = selectorBytes 0x38 0xc6 0xde 0x40 := by
  simp [selectorOf, transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, snipTransition, bytes32, uint256]; decide +kernel

/-- `keccak("skip(bytes32,uint256)")[0:4] = 0x503ecf06`. -/
theorem endSkipSelectorBytes :
    selectorOf skipTransition = selectorBytes 0x50 0x3e 0xcf 0x06 := by
  simp [selectorOf, transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, skipTransition, bytes32, uint256]; decide +kernel

/-- `keccak("skim(bytes32,address)")[0:4] = 0x89ea45d3`. -/
theorem endSkimSelectorBytes :
    selectorOf skimTransition = selectorBytes 0x89 0xea 0x45 0xd3 := by
  simp [selectorOf, transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, skimTransition, bytes32, addr]; decide +kernel

/-- `keccak("free(bytes32)")[0:4] = 0xc83062c6`. -/
theorem endFreeSelectorBytes :
    selectorOf freeTransition = selectorBytes 0xc8 0x30 0x62 0xc6 := by
  simp [selectorOf, transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, freeTransition, bytes32]; decide +kernel

/-- `keccak("thaw()")[0:4] = 0x5920375c`. -/
theorem endThawSelectorBytes :
    selectorOf thawTransition = selectorBytes 0x59 0x20 0x37 0x5c := by decide +kernel

/-- `keccak("flow(bytes32)")[0:4] = 0x4a10eaa6`. -/
theorem endFlowSelectorBytes :
    selectorOf flowTransition = selectorBytes 0x4a 0x10 0xea 0xa6 := by
  simp [selectorOf, transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, flowTransition, bytes32]; decide +kernel

/-- `keccak("pack(uint256)")[0:4] = 0x6ea42555`. -/
theorem endPackSelectorBytes :
    selectorOf packTransition = selectorBytes 0x6e 0xa4 0x25 0x55 := by
  simp [selectorOf, transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, packTransition, uint256]; decide +kernel

/-- `keccak("cash(bytes32,uint256)")[0:4] = 0xfe8507c6`. -/
theorem endCashSelectorBytes :
    selectorOf cashTransition = selectorBytes 0xfe 0x85 0x07 0xc6 := by
  simp [selectorOf, transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, cashTransition, bytes32, uint256]; decide +kernel

end Benchmarks.Dss.End
