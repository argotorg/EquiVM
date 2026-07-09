import Benchmarks.Dss.DaiJoin.Common

/-!
# MakerDAO/Sky DSS DaiJoin trusted selector facts

Lean does not reduce the FFI-backed Keccak computation used by `selectorOf`. These facts are the
contract-local selector bytes used to connect Solm dispatch to the runtime dispatcher constants.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.Dss.DaiJoin

/-- `keccak("cage()")[0:4] = 0x69245009`. -/
axiom cageSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr cageTransition))).extract 0 4 =
      daiJoinSelBytes 0

/-- `keccak("dai()")[0:4] = 0xf4b9fa75`. -/
axiom daiSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr daiTransition))).extract 0 4 =
      daiJoinSelBytes 1

/-- `keccak("deny(address)")[0:4] = 0x9c52a7f1`. -/
axiom denySelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr denyTransition))).extract 0 4 =
      daiJoinSelBytes 2

/-- `keccak("exit(address,uint256)")[0:4] = 0xef693bed`. -/
axiom exitSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr exitTransition))).extract 0 4 =
      daiJoinSelBytes 3

/-- `keccak("join(address,uint256)")[0:4] = 0x3b4da69f`. -/
axiom joinSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr joinTransition))).extract 0 4 =
      daiJoinSelBytes 4

/-- `keccak("live()")[0:4] = 0x957aa58c`. -/
axiom liveSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr liveTransition))).extract 0 4 =
      daiJoinSelBytes 5

/-- `keccak("rely(address)")[0:4] = 0x65fae35e`. -/
axiom relySelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr relyTransition))).extract 0 4 =
      daiJoinSelBytes 6

/-- `keccak("vat()")[0:4] = 0x36569e77`. -/
axiom vatSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr vatTransition))).extract 0 4 =
      daiJoinSelBytes 7

/-- `keccak("wards(address)")[0:4] = 0xbf353dbb`. -/
axiom wardsSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr wardsTransition))).extract 0 4 =
      daiJoinSelBytes 8

end Benchmarks.Dss.DaiJoin
