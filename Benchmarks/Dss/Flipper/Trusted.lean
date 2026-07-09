import Benchmarks.Dss.Flipper.Common

/-!
# MakerDAO/Sky DSS Flipper trusted selector facts

Lean does not reduce the FFI-backed Keccak computation used by `selectorOf`. These facts are the
contract-local selector bytes used to connect Solm dispatch to the runtime dispatcher constants.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.Dss.Flipper

/-- `keccak("beg()")[0:4] = 0x7d780d82`. -/
axiom begSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr begTransition))).extract 0 4 =
      flipperSelBytes 0

/-- `keccak("bids(uint256)")[0:4] = 0x4423c5f1`. -/
axiom bidsSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr bidsTransition))).extract 0 4 =
      flipperSelBytes 1

/-- `keccak("cat()")[0:4] = 0xe4881813`. -/
axiom catSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr catTransition))).extract 0 4 =
      flipperSelBytes 2

/-- `keccak("deal(uint256)")[0:4] = 0xc959c42b`. -/
axiom dealSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr dealTransition))).extract 0 4 =
      flipperSelBytes 3

/-- `keccak("dent(uint256,uint256,uint256)")[0:4] = 0x5ff3a382`. -/
axiom dentSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr dentTransition))).extract 0 4 =
      flipperSelBytes 4

/-- `keccak("deny(address)")[0:4] = 0x9c52a7f1`. -/
axiom denySelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr denyTransition))).extract 0 4 =
      flipperSelBytes 5

/-- `keccak("file(bytes32,address)")[0:4] = 0xd4e8be83`. -/
axiom fileAddressSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr fileAddressTransition))).extract 0 4 =
      flipperSelBytes 6

/-- `keccak("file(bytes32,uint256)")[0:4] = 0x29ae8114`. -/
axiom fileUintSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr fileUintTransition))).extract 0 4 =
      flipperSelBytes 7

/-- `keccak("ilk()")[0:4] = 0xc5ce281e`. -/
axiom ilkSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr ilkTransition))).extract 0 4 =
      flipperSelBytes 8

/-- `keccak("kick(address,address,uint256,uint256,uint256)")[0:4] = 0x351de600`. -/
axiom kickSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr kickTransition))).extract 0 4 =
      flipperSelBytes 9

/-- `keccak("kicks()")[0:4] = 0xcfdd3302`. -/
axiom kicksSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr kicksTransition))).extract 0 4 =
      flipperSelBytes 10

/-- `keccak("rely(address)")[0:4] = 0x65fae35e`. -/
axiom relySelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr relyTransition))).extract 0 4 =
      flipperSelBytes 11

/-- `keccak("tau()")[0:4] = 0xcfc4af55`. -/
axiom tauSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr tauTransition))).extract 0 4 =
      flipperSelBytes 12

/-- `keccak("tend(uint256,uint256,uint256)")[0:4] = 0x4b43ed12`. -/
axiom tendSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr tendTransition))).extract 0 4 =
      flipperSelBytes 13

/-- `keccak("tick(uint256)")[0:4] = 0xfc7b6aee`. -/
axiom tickSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr tickTransition))).extract 0 4 =
      flipperSelBytes 14

/-- `keccak("ttl()")[0:4] = 0x4e8b1dd5`. -/
axiom ttlSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr ttlTransition))).extract 0 4 =
      flipperSelBytes 15

/-- `keccak("vat()")[0:4] = 0x36569e77`. -/
axiom vatSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr vatTransition))).extract 0 4 =
      flipperSelBytes 16

/-- `keccak("wards(address)")[0:4] = 0xbf353dbb`. -/
axiom wardsSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr wardsTransition))).extract 0 4 =
      flipperSelBytes 17

/-- `keccak("yank(uint256)")[0:4] = 0x26e027f1`. -/
axiom yankSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr yankTransition))).extract 0 4 =
      flipperSelBytes 18

end Benchmarks.Dss.Flipper
