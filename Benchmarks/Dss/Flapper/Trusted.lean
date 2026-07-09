import Benchmarks.Dss.Flapper.Common

/-!
# MakerDAO/Sky DSS Flapper trusted selector facts

Lean does not reduce the FFI-backed Keccak computation used by `selectorOf`. These facts are the
contract-local selector bytes used to connect Solm dispatch to the runtime dispatcher constants.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.Dss.Flapper

/-- `keccak("beg()")[0:4] = 0x7d780d82`. -/
axiom begSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr begTransition))).extract 0 4 =
      flapperSelBytes 0

/-- `keccak("bids(uint256)")[0:4] = 0x4423c5f1`. -/
axiom bidsSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr bidsTransition))).extract 0 4 =
      flapperSelBytes 1

/-- `keccak("cage(uint256)")[0:4] = 0xa2f91af2`. -/
axiom cageSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr cageTransition))).extract 0 4 =
      flapperSelBytes 2

/-- `keccak("deal(uint256)")[0:4] = 0xc959c42b`. -/
axiom dealSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr dealTransition))).extract 0 4 =
      flapperSelBytes 3

/-- `keccak("deny(address)")[0:4] = 0x9c52a7f1`. -/
axiom denySelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr denyTransition))).extract 0 4 =
      flapperSelBytes 4

/-- `keccak("file(bytes32,uint256)")[0:4] = 0x29ae8114`. -/
axiom fileSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr fileTransition))).extract 0 4 =
      flapperSelBytes 5

/-- `keccak("fill()")[0:4] = 0xd9c55ce1`. -/
axiom fillSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr fillTransition))).extract 0 4 =
      flapperSelBytes 6

/-- `keccak("gem()")[0:4] = 0x7bd2bea7`. -/
axiom gemSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr gemTransition))).extract 0 4 =
      flapperSelBytes 7

/-- `keccak("kick(uint256,uint256)")[0:4] = 0xca40c419`. -/
axiom kickSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr kickTransition))).extract 0 4 =
      flapperSelBytes 8

/-- `keccak("kicks()")[0:4] = 0xcfdd3302`. -/
axiom kicksSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr kicksTransition))).extract 0 4 =
      flapperSelBytes 9

/-- `keccak("lid()")[0:4] = 0x26d2addc`. -/
axiom lidSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr lidTransition))).extract 0 4 =
      flapperSelBytes 10

/-- `keccak("live()")[0:4] = 0x957aa58c`. -/
axiom liveSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr liveTransition))).extract 0 4 =
      flapperSelBytes 11

/-- `keccak("rely(address)")[0:4] = 0x65fae35e`. -/
axiom relySelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr relyTransition))).extract 0 4 =
      flapperSelBytes 12

/-- `keccak("tau()")[0:4] = 0xcfc4af55`. -/
axiom tauSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr tauTransition))).extract 0 4 =
      flapperSelBytes 13

/-- `keccak("tend(uint256,uint256,uint256)")[0:4] = 0x4b43ed12`. -/
axiom tendSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr tendTransition))).extract 0 4 =
      flapperSelBytes 14

/-- `keccak("tick(uint256)")[0:4] = 0xfc7b6aee`. -/
axiom tickSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr tickTransition))).extract 0 4 =
      flapperSelBytes 15

/-- `keccak("ttl()")[0:4] = 0x4e8b1dd5`. -/
axiom ttlSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr ttlTransition))).extract 0 4 =
      flapperSelBytes 16

/-- `keccak("vat()")[0:4] = 0x36569e77`. -/
axiom vatSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr vatTransition))).extract 0 4 =
      flapperSelBytes 17

/-- `keccak("wards(address)")[0:4] = 0xbf353dbb`. -/
axiom wardsSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr wardsTransition))).extract 0 4 =
      flapperSelBytes 18

/-- `keccak("yank(uint256)")[0:4] = 0x26e027f1`. -/
axiom yankSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr yankTransition))).extract 0 4 =
      flapperSelBytes 19

end Benchmarks.Dss.Flapper
