import Benchmarks.Dss.End.Common

/-!
# MakerDAO/Sky DSS End trusted selector facts

Lean does not reduce the FFI-backed Keccak computation used by `selectorOf`. These facts are the
contract-local selector bytes used to connect Solm dispatch to the runtime dispatcher constants.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.Dss.End

/-- `keccak("wards(address)")[0:4] = 0xbf353dbb`. -/
axiom wardsSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr wardsTransition))).extract 0 4 =
      endSelBytes 0

/-- `keccak("vat()")[0:4] = 0x36569e77`. -/
axiom vatSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr vatTransition))).extract 0 4 =
      endSelBytes 1

/-- `keccak("cat()")[0:4] = 0xe4881813`. -/
axiom catSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr catTransition))).extract 0 4 =
      endSelBytes 2

/-- `keccak("dog()")[0:4] = 0xc3b3ad7f`. -/
axiom dogSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr dogTransition))).extract 0 4 =
      endSelBytes 3

/-- `keccak("vow()")[0:4] = 0x626cb3c5`. -/
axiom vowSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr vowTransition))).extract 0 4 =
      endSelBytes 4

/-- `keccak("pot()")[0:4] = 0x4ba2363a`. -/
axiom potSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr potTransition))).extract 0 4 =
      endSelBytes 5

/-- `keccak("spot()")[0:4] = 0x6f265b93`. -/
axiom spotSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr spotTransition))).extract 0 4 =
      endSelBytes 6

/-- `keccak("cure()")[0:4] = 0x840782ed`. -/
axiom cureSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr cureTransition))).extract 0 4 =
      endSelBytes 7

/-- `keccak("live()")[0:4] = 0x957aa58c`. -/
axiom liveSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr liveTransition))).extract 0 4 =
      endSelBytes 8

/-- `keccak("when()")[0:4] = 0xe2b0caef`. -/
axiom whenSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr whenTransition))).extract 0 4 =
      endSelBytes 9

/-- `keccak("wait()")[0:4] = 0x64bd7013`. -/
axiom waitSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr waitTransition))).extract 0 4 =
      endSelBytes 10

/-- `keccak("debt()")[0:4] = 0x0dca59c1`. -/
axiom debtSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr debtTransition))).extract 0 4 =
      endSelBytes 11

/-- `keccak("tag(bytes32)")[0:4] = 0xee6447b5`. -/
axiom tagSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr tagTransition))).extract 0 4 =
      endSelBytes 12

/-- `keccak("gap(bytes32)")[0:4] = 0xe6ee62aa`. -/
axiom gapSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr gapTransition))).extract 0 4 =
      endSelBytes 13

/-- `keccak("Art(bytes32)")[0:4] = 0xe1340a3d`. -/
axiom ArtSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr ArtTransition))).extract 0 4 =
      endSelBytes 14

/-- `keccak("fix(bytes32)")[0:4] = 0x63fad85e`. -/
axiom fixSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr fixTransition))).extract 0 4 =
      endSelBytes 15

/-- `keccak("bag(address)")[0:4] = 0x9255f809`. -/
axiom bagSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr bagTransition))).extract 0 4 =
      endSelBytes 16

/-- `keccak("out(bytes32,address)")[0:4] = 0xc939ebfc`. -/
axiom outSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr outTransition))).extract 0 4 =
      endSelBytes 17

/-- `keccak("rely(address)")[0:4] = 0x65fae35e`. -/
axiom relySelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr relyTransition))).extract 0 4 =
      endSelBytes 18

/-- `keccak("deny(address)")[0:4] = 0x9c52a7f1`. -/
axiom denySelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr denyTransition))).extract 0 4 =
      endSelBytes 19

/-- `keccak("file(bytes32,address)")[0:4] = 0xd4e8be83`. -/
axiom fileAddressSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr fileAddressTransition))).extract 0 4 =
      endSelBytes 20

/-- `keccak("file(bytes32,uint256)")[0:4] = 0x29ae8114`. -/
axiom fileUintSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr fileUintTransition))).extract 0 4 =
      endSelBytes 21

/-- `keccak("cage()")[0:4] = 0x69245009`. -/
axiom cageSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr cageTransition))).extract 0 4 =
      endSelBytes 22

/-- `keccak("cage(bytes32)")[0:4] = 0xe2702fdc`. -/
axiom cageIlkSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr cageIlkTransition))).extract 0 4 =
      endSelBytes 23

/-- `keccak("snip(bytes32,uint256)")[0:4] = 0x38c6de40`. -/
axiom snipSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr snipTransition))).extract 0 4 =
      endSelBytes 24

/-- `keccak("skip(bytes32,uint256)")[0:4] = 0x503ecf06`. -/
axiom skipSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr skipTransition))).extract 0 4 =
      endSelBytes 25

/-- `keccak("skim(bytes32,address)")[0:4] = 0x89ea45d3`. -/
axiom skimSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr skimTransition))).extract 0 4 =
      endSelBytes 26

/-- `keccak("free(bytes32)")[0:4] = 0xc83062c6`. -/
axiom freeSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr freeTransition))).extract 0 4 =
      endSelBytes 27

/-- `keccak("thaw()")[0:4] = 0x5920375c`. -/
axiom thawSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr thawTransition))).extract 0 4 =
      endSelBytes 28

/-- `keccak("flow(bytes32)")[0:4] = 0x4a10eaa6`. -/
axiom flowSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr flowTransition))).extract 0 4 =
      endSelBytes 29

/-- `keccak("pack(uint256)")[0:4] = 0x6ea42555`. -/
axiom packSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr packTransition))).extract 0 4 =
      endSelBytes 30

/-- `keccak("cash(bytes32,uint256)")[0:4] = 0xfe8507c6`. -/
axiom cashSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr cashTransition))).extract 0 4 =
      endSelBytes 31

end Benchmarks.Dss.End
