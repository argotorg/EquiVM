import Benchmarks.Dss.ExponentialDecrease.Common

/-!
# MakerDAO/Sky DSS ExponentialDecrease trusted selector facts

Lean does not reduce the FFI-backed Keccak computation used by `selectorOf`. These facts are the
contract-local selector bytes used to connect Solm dispatch to the runtime dispatcher constants.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.Dss.ExponentialDecrease

/-- `keccak("cut()")[0:4] = 0xe6fd604c`. -/
axiom cutSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr cutTransition))).extract 0 4 =
      stairstepSelBytes 0

/-- `keccak("deny(address)")[0:4] = 0x9c52a7f1`. -/
axiom denySelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr denyTransition))).extract 0 4 =
      stairstepSelBytes 1

/-- `keccak("file(bytes32,uint256)")[0:4] = 0x29ae8114`. -/
axiom fileSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr fileTransition))).extract 0 4 =
      stairstepSelBytes 2

/-- `keccak("price(uint256,uint256)")[0:4] = 0x487a2395`. -/
axiom priceSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr priceTransition))).extract 0 4 =
      stairstepSelBytes 3

/-- `keccak("rely(address)")[0:4] = 0x65fae35e`. -/
axiom relySelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr relyTransition))).extract 0 4 =
      stairstepSelBytes 4

/-- `keccak("wards(address)")[0:4] = 0xbf353dbb`. -/
axiom wardsSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr wardsTransition))).extract 0 4 =
      stairstepSelBytes 5

end Benchmarks.Dss.ExponentialDecrease
