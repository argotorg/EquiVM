import Benchmarks.Dss.Jug.Common

/-!
# MakerDAO/Sky DSS Jug trusted selector facts

Lean does not reduce the FFI-backed Keccak computation used by `selectorOf`. These facts are the
contract-local selector bytes used to connect Solm dispatch to the runtime dispatcher constants.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.Dss.Jug

/-- `keccak("base()")[0:4] = 0x5001f3b5`. -/
axiom baseSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr baseTransition))).extract 0 4 =
      jugSelBytes 0

/-- `keccak("deny(address)")[0:4] = 0x9c52a7f1`. -/
axiom denySelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr denyTransition))).extract 0 4 =
      jugSelBytes 1

/-- `keccak("drip(bytes32)")[0:4] = 0x44e2a5a8`. -/
axiom dripSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr dripTransition))).extract 0 4 =
      jugSelBytes 2

/-- `keccak("file(bytes32,uint256)")[0:4] = 0x29ae8114`. -/
axiom fileBaseSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr fileBaseTransition))).extract 0 4 =
      jugSelBytes 3

/-- `keccak("file(bytes32,bytes32,uint256)")[0:4] = 0x1a0b287e`. -/
axiom fileDutySelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr fileDutyTransition))).extract 0 4 =
      jugSelBytes 4

/-- `keccak("file(bytes32,address)")[0:4] = 0xd4e8be83`. -/
axiom fileVowSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr fileVowTransition))).extract 0 4 =
      jugSelBytes 5

/-- `keccak("ilks(bytes32)")[0:4] = 0xd9638d36`. -/
axiom ilksSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr ilksTransition))).extract 0 4 =
      jugSelBytes 6

/-- `keccak("init(bytes32)")[0:4] = 0x3b663195`. -/
axiom initSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr initTransition))).extract 0 4 =
      jugSelBytes 7

/-- `keccak("rely(address)")[0:4] = 0x65fae35e`. -/
axiom relySelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr relyTransition))).extract 0 4 =
      jugSelBytes 8

/-- `keccak("vat()")[0:4] = 0x36569e77`. -/
axiom vatSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr vatTransition))).extract 0 4 =
      jugSelBytes 9

/-- `keccak("vow()")[0:4] = 0x626cb3c5`. -/
axiom vowSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr vowTransition))).extract 0 4 =
      jugSelBytes 10

/-- `keccak("wards(address)")[0:4] = 0xbf353dbb`. -/
axiom wardsSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr wardsTransition))).extract 0 4 =
      jugSelBytes 11

end Benchmarks.Dss.Jug
