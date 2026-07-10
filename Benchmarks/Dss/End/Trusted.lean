import Benchmarks.Dss.End.Common

/-!
# MakerDAO/Sky DSS End trusted selector facts

Lean does not reduce the FFI-backed Keccak computation used by `selectorOf`. These facts connect
the Solm transition signatures to the concrete selector bytes present in `endBytecode`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Dss.End

/-- `keccak("wards(address)")[0:4] = 0xbf353dbb`. -/
axiom endWardsSelectorBytes :
    selectorOf wardsTransition = selectorBytes 0xbf 0x35 0x3d 0xbb

/-- `keccak("vat()")[0:4] = 0x36569e77`. -/
axiom endVatSelectorBytes :
    selectorOf vatTransition = selectorBytes 0x36 0x56 0x9e 0x77

/-- `keccak("cat()")[0:4] = 0xe4881813`. -/
axiom endCatSelectorBytes :
    selectorOf catTransition = selectorBytes 0xe4 0x88 0x18 0x13

/-- `keccak("dog()")[0:4] = 0xc3b3ad7f`. -/
axiom endDogSelectorBytes :
    selectorOf dogTransition = selectorBytes 0xc3 0xb3 0xad 0x7f

/-- `keccak("vow()")[0:4] = 0x626cb3c5`. -/
axiom endVowSelectorBytes :
    selectorOf vowTransition = selectorBytes 0x62 0x6c 0xb3 0xc5

/-- `keccak("pot()")[0:4] = 0x4ba2363a`. -/
axiom endPotSelectorBytes :
    selectorOf potTransition = selectorBytes 0x4b 0xa2 0x36 0x3a

/-- `keccak("spot()")[0:4] = 0x6f265b93`. -/
axiom endSpotSelectorBytes :
    selectorOf spotTransition = selectorBytes 0x6f 0x26 0x5b 0x93

/-- `keccak("cure()")[0:4] = 0x840782ed`. -/
axiom endCureSelectorBytes :
    selectorOf cureTransition = selectorBytes 0x84 0x07 0x82 0xed

/-- `keccak("live()")[0:4] = 0x957aa58c`. -/
axiom endLiveSelectorBytes :
    selectorOf liveTransition = selectorBytes 0x95 0x7a 0xa5 0x8c

/-- `keccak("when()")[0:4] = 0xe2b0caef`. -/
axiom endWhenSelectorBytes :
    selectorOf whenTransition = selectorBytes 0xe2 0xb0 0xca 0xef

/-- `keccak("wait()")[0:4] = 0x64bd7013`. -/
axiom endWaitSelectorBytes :
    selectorOf waitTransition = selectorBytes 0x64 0xbd 0x70 0x13

/-- `keccak("debt()")[0:4] = 0x0dca59c1`. -/
axiom endDebtSelectorBytes :
    selectorOf debtTransition = debtSelector

/-- `keccak("tag(bytes32)")[0:4] = 0xee6447b5`. -/
axiom endTagSelectorBytes :
    selectorOf tagTransition = selectorBytes 0xee 0x64 0x47 0xb5

/-- `keccak("gap(bytes32)")[0:4] = 0xe6ee62aa`. -/
axiom endGapSelectorBytes :
    selectorOf gapTransition = selectorBytes 0xe6 0xee 0x62 0xaa

/-- `keccak("Art(bytes32)")[0:4] = 0xe1340a3d`. -/
axiom endArtSelectorBytes :
    selectorOf ArtTransition = selectorBytes 0xe1 0x34 0x0a 0x3d

/-- `keccak("fix(bytes32)")[0:4] = 0x63fad85e`. -/
axiom endFixSelectorBytes :
    selectorOf fixTransition = selectorBytes 0x63 0xfa 0xd8 0x5e

/-- `keccak("bag(address)")[0:4] = 0x9255f809`. -/
axiom endBagSelectorBytes :
    selectorOf bagTransition = selectorBytes 0x92 0x55 0xf8 0x09

/-- `keccak("out(bytes32,address)")[0:4] = 0xc939ebfc`. -/
axiom endOutSelectorBytes :
    selectorOf outTransition = selectorBytes 0xc9 0x39 0xeb 0xfc

/-- `keccak("rely(address)")[0:4] = 0x65fae35e`. -/
axiom endRelySelectorBytes :
    selectorOf relyTransition = selectorBytes 0x65 0xfa 0xe3 0x5e

/-- `keccak("deny(address)")[0:4] = 0x9c52a7f1`. -/
axiom endDenySelectorBytes :
    selectorOf denyTransition = selectorBytes 0x9c 0x52 0xa7 0xf1

/-- `keccak("file(bytes32,address)")[0:4] = 0xd4e8be83`. -/
axiom endFileAddressSelectorBytes :
    selectorOf fileAddressTransition = selectorBytes 0xd4 0xe8 0xbe 0x83

/-- `keccak("file(bytes32,uint256)")[0:4] = 0x29ae8114`. -/
axiom endFileUintSelectorBytes :
    selectorOf fileUintTransition = selectorBytes 0x29 0xae 0x81 0x14

/-- `keccak("cage()")[0:4] = 0x69245009`. -/
axiom endCageSelectorBytes :
    selectorOf cageTransition = selectorBytes 0x69 0x24 0x50 0x09

/-- `keccak("cage(bytes32)")[0:4] = 0xe2702fdc`. -/
axiom endCageIlkSelectorBytes :
    selectorOf cageIlkTransition = selectorBytes 0xe2 0x70 0x2f 0xdc

/-- `keccak("snip(bytes32,uint256)")[0:4] = 0x38c6de40`. -/
axiom endSnipSelectorBytes :
    selectorOf snipTransition = selectorBytes 0x38 0xc6 0xde 0x40

/-- `keccak("skip(bytes32,uint256)")[0:4] = 0x503ecf06`. -/
axiom endSkipSelectorBytes :
    selectorOf skipTransition = selectorBytes 0x50 0x3e 0xcf 0x06

/-- `keccak("skim(bytes32,address)")[0:4] = 0x89ea45d3`. -/
axiom endSkimSelectorBytes :
    selectorOf skimTransition = selectorBytes 0x89 0xea 0x45 0xd3

/-- `keccak("free(bytes32)")[0:4] = 0xc83062c6`. -/
axiom endFreeSelectorBytes :
    selectorOf freeTransition = selectorBytes 0xc8 0x30 0x62 0xc6

/-- `keccak("thaw()")[0:4] = 0x5920375c`. -/
axiom endThawSelectorBytes :
    selectorOf thawTransition = selectorBytes 0x59 0x20 0x37 0x5c

/-- `keccak("flow(bytes32)")[0:4] = 0x4a10eaa6`. -/
axiom endFlowSelectorBytes :
    selectorOf flowTransition = selectorBytes 0x4a 0x10 0xea 0xa6

/-- `keccak("pack(uint256)")[0:4] = 0x6ea42555`. -/
axiom endPackSelectorBytes :
    selectorOf packTransition = selectorBytes 0x6e 0xa4 0x25 0x55

/-- `keccak("cash(bytes32,uint256)")[0:4] = 0xfe8507c6`. -/
axiom endCashSelectorBytes :
    selectorOf cashTransition = selectorBytes 0xfe 0x85 0x07 0xc6

end Benchmarks.Dss.End
