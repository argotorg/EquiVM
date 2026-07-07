import Benchmarks.Dss.Spot.Common

/-!
# MakerDAO/Sky DSS Spotter trusted selector facts

Lean does not reduce the FFI-backed Keccak computation used by `selectorOf`. These facts are the
contract-local selector bytes used to connect Solm dispatch to the runtime dispatcher constants.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.Dss.Spot

/-- `keccak("cage()")[0:4] = 0x69245009`. -/
axiom cageSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr cageTransition))).extract 0 4 =
      spotSelBytes 0

/-- `keccak("deny(address)")[0:4] = 0x9c52a7f1`. -/
axiom denySelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr denyTransition))).extract 0 4 =
      spotSelBytes 1

/-- `keccak("file(bytes32,bytes32,uint256)")[0:4] = 0x1a0b287e`. -/
axiom fileMatSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr fileMatTransition))).extract 0 4 =
      spotSelBytes 2

/-- `keccak("file(bytes32,uint256)")[0:4] = 0x29ae8114`. -/
axiom fileParSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr fileParTransition))).extract 0 4 =
      spotSelBytes 3

/-- `keccak("file(bytes32,bytes32,address)")[0:4] = 0xebecb39d`. -/
axiom filePipSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr filePipTransition))).extract 0 4 =
      spotSelBytes 4

/-- `keccak("ilks(bytes32)")[0:4] = 0xd9638d36`. -/
axiom ilksSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr ilksTransition))).extract 0 4 =
      spotSelBytes 5

/-- `keccak("live()")[0:4] = 0x957aa58c`. -/
axiom liveSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr liveTransition))).extract 0 4 =
      spotSelBytes 6

/-- `keccak("par()")[0:4] = 0x495d32cb`. -/
axiom parSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr parTransition))).extract 0 4 =
      spotSelBytes 7

/-- `keccak("poke(bytes32)")[0:4] = 0x1504460f`. -/
axiom pokeSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr pokeTransition))).extract 0 4 =
      spotSelBytes 8

/-- `keccak("rely(address)")[0:4] = 0x65fae35e`. -/
axiom relySelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr relyTransition))).extract 0 4 =
      spotSelBytes 9

/-- `keccak("vat()")[0:4] = 0x36569e77`. -/
axiom vatSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr vatTransition))).extract 0 4 =
      spotSelBytes 10

/-- `keccak("wards(address)")[0:4] = 0xbf353dbb`. -/
axiom wardsSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr wardsTransition))).extract 0 4 =
      spotSelBytes 11

end Benchmarks.Dss.Spot
