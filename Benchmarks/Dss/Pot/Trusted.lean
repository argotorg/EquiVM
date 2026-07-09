import Benchmarks.Dss.Pot.Common

/-!
# MakerDAO/Sky DSS Pot trusted selector facts

Lean does not reduce the FFI-backed Keccak computation used by `selectorOf`. These facts are the
contract-local selector bytes used to connect Solm dispatch to the runtime dispatcher constants.
They are part of the accepted trusted base (selector bytes of each function).
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.Dss.Pot

/-- `keccak("Pie()")[0:4] = 0x2c69ed58`. -/
axiom PieSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr PieTransition))).extract 0 4 =
      potSelBytes 0

/-- `keccak("cage()")[0:4] = 0x69245009`. -/
axiom cageSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr cageTransition))).extract 0 4 =
      potSelBytes 1

/-- `keccak("chi()")[0:4] = 0xc92aecc4`. -/
axiom chiSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr chiTransition))).extract 0 4 =
      potSelBytes 2

/-- `keccak("deny(address)")[0:4] = 0x9c52a7f1`. -/
axiom denySelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr denyTransition))).extract 0 4 =
      potSelBytes 3

/-- `keccak("drip()")[0:4] = 0x9f678cca`. -/
axiom dripSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr dripTransition))).extract 0 4 =
      potSelBytes 4

/-- `keccak("dsr()")[0:4] = 0x487bf082`. -/
axiom dsrSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr dsrTransition))).extract 0 4 =
      potSelBytes 5

/-- `keccak("exit(uint256)")[0:4] = 0x7f8661a1`. -/
axiom exitSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr exitTransition))).extract 0 4 =
      potSelBytes 6

/-- `keccak("file(bytes32,uint256)")[0:4] = 0x29ae8114`. -/
axiom fileDsrSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr fileDsrTransition))).extract 0 4 =
      potSelBytes 7

/-- `keccak("file(bytes32,address)")[0:4] = 0xd4e8be83`. -/
axiom fileVowSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr fileVowTransition))).extract 0 4 =
      potSelBytes 8

/-- `keccak("join(uint256)")[0:4] = 0x049878f3`. -/
axiom joinSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr joinTransition))).extract 0 4 =
      potSelBytes 9

/-- `keccak("live()")[0:4] = 0x957aa58c`. -/
axiom liveSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr liveTransition))).extract 0 4 =
      potSelBytes 10

/-- `keccak("pie(address)")[0:4] = 0x0bebac86`. -/
axiom pieSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr pieTransition))).extract 0 4 =
      potSelBytes 11

/-- `keccak("rely(address)")[0:4] = 0x65fae35e`. -/
axiom relySelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr relyTransition))).extract 0 4 =
      potSelBytes 12

/-- `keccak("rho()")[0:4] = 0x20aba08b`. -/
axiom rhoSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr rhoTransition))).extract 0 4 =
      potSelBytes 13

/-- `keccak("vat()")[0:4] = 0x36569e77`. -/
axiom vatSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr vatTransition))).extract 0 4 =
      potSelBytes 14

/-- `keccak("vow()")[0:4] = 0x626cb3c5`. -/
axiom vowSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr vowTransition))).extract 0 4 =
      potSelBytes 15

/-- `keccak("wards(address)")[0:4] = 0xbf353dbb`. -/
axiom wardsSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr wardsTransition))).extract 0 4 =
      potSelBytes 16

end Benchmarks.Dss.Pot
