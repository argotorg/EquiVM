import Benchmarks.Dss.Clipper.Common
import Solm.Semantics

/-!
# MakerDAO/Sky DSS Clipper trusted selector facts

Lean does not reduce the FFI-backed Keccak computation used by `selectorOf`. These facts are the
contract-local selector bytes used to connect Solm dispatch to the runtime dispatcher constants.
-/

open Solm ABI Ethereum Ethereum.EVM
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

/-- `keccak("active(uint256)")[0:4] = 0x8033d581`. -/
axiom activeSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr activeTransition))).extract 0 4 =
      clipperSelBytes 0

/-- `keccak("buf()")[0:4] = 0x15232515`. -/
axiom bufSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr bufTransition))).extract 0 4 =
      clipperSelBytes 1

/-- `keccak("calc()")[0:4] = 0x96f1b6be`. -/
axiom calcSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr calcTransition))).extract 0 4 =
      clipperSelBytes 2

/-- `keccak("chip()")[0:4] = 0xb61500e4`. -/
axiom chipSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr chipTransition))).extract 0 4 =
      clipperSelBytes 3

/-- `keccak("chost()")[0:4] = 0xba2cdc75`. -/
axiom chostSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr chostTransition))).extract 0 4 =
      clipperSelBytes 4

/-- `keccak("count()")[0:4] = 0x06661abd`. -/
axiom countSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr countTransition))).extract 0 4 =
      clipperSelBytes 5

/-- `keccak("cusp()")[0:4] = 0x49ed5931`. -/
axiom cuspSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr cuspTransition))).extract 0 4 =
      clipperSelBytes 6

/-- `keccak("deny(address)")[0:4] = 0x9c52a7f1`. -/
axiom denySelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr denyTransition))).extract 0 4 =
      clipperSelBytes 7

/-- `keccak("dog()")[0:4] = 0xc3b3ad7f`. -/
axiom dogSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr dogTransition))).extract 0 4 =
      clipperSelBytes 8

/-- `keccak("file(bytes32,uint256)")[0:4] = 0x29ae8114`. -/
axiom fileUintSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr fileUintTransition))).extract 0 4 =
      clipperSelBytes 9

/-- `keccak("file(bytes32,address)")[0:4] = 0xd4e8be83`. -/
axiom fileAddressSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr fileAddressTransition))).extract 0 4 =
      clipperSelBytes 10

/-- `keccak("getStatus(uint256)")[0:4] = 0x5c622a0e`. -/
axiom getStatusSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr getStatusTransition))).extract 0 4 =
      clipperSelBytes 11

/-- `keccak("ilk()")[0:4] = 0xc5ce281e`. -/
axiom ilkSelectorBytes (v : ClipperImmutables) :
    (ffi.KEC (String.toByteArray (transitionSigStr (ilkTransition v)))).extract 0 4 =
      clipperSelBytes 12

/-- `keccak("kick(uint256,uint256,address,address)")[0:4] = 0x898eb267`. -/
axiom kickSelectorBytes (v : ClipperImmutables) :
    (ffi.KEC (String.toByteArray (transitionSigStr (kickTransition v)))).extract 0 4 =
      clipperSelBytes 13

/-- `keccak("kicks()")[0:4] = 0xcfdd3302`. -/
axiom kicksSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr kicksTransition))).extract 0 4 =
      clipperSelBytes 14

/-- `keccak("list()")[0:4] = 0x0f560cd7`. -/
axiom listSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr listTransition))).extract 0 4 =
      clipperSelBytes 15

/-- `keccak("redo(uint256,address)")[0:4] = 0xd843416d`. -/
axiom redoSelectorBytes (v : ClipperImmutables) :
    (ffi.KEC (String.toByteArray (transitionSigStr (redoTransition v)))).extract 0 4 =
      clipperSelBytes 16

/-- `keccak("rely(address)")[0:4] = 0x65fae35e`. -/
axiom relySelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr relyTransition))).extract 0 4 =
      clipperSelBytes 17

/-- `keccak("sales(uint256)")[0:4] = 0xb5f522f7`. -/
axiom salesSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr salesTransition))).extract 0 4 =
      clipperSelBytes 18

/-- `keccak("spotter()")[0:4] = 0x2e77468d`. -/
axiom spotterSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr spotterTransition))).extract 0 4 =
      clipperSelBytes 19

/-- `keccak("stopped()")[0:4] = 0x75f12b21`. -/
axiom stoppedSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr stoppedTransition))).extract 0 4 =
      clipperSelBytes 20

/-- `keccak("tail()")[0:4] = 0x13d8c840`. -/
axiom tailSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr tailTransition))).extract 0 4 =
      clipperSelBytes 21

/-- `keccak("take(uint256,uint256,uint256,address,bytes)")[0:4] = 0x81a794cb`. -/
axiom takeSelectorBytes (v : ClipperImmutables) :
    (ffi.KEC (String.toByteArray (transitionSigStr (takeTransition v)))).extract 0 4 =
      clipperSelBytes 22

/-- `keccak("tip()")[0:4] = 0x2755cd2d`. -/
axiom tipSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr tipTransition))).extract 0 4 =
      clipperSelBytes 23

/-- `keccak("upchost()")[0:4] = 0x0cbb5862`. -/
axiom upchostSelectorBytes (v : ClipperImmutables) :
    (ffi.KEC (String.toByteArray (transitionSigStr (upchostTransition v)))).extract 0 4 =
      clipperSelBytes 24

/-- `keccak("vat()")[0:4] = 0x36569e77`. -/
axiom vatSelectorBytes (v : ClipperImmutables) :
    (ffi.KEC (String.toByteArray (transitionSigStr (vatTransition v)))).extract 0 4 =
      clipperSelBytes 25

/-- `keccak("vow()")[0:4] = 0x626cb3c5`. -/
axiom vowSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr vowTransition))).extract 0 4 =
      clipperSelBytes 26

/-- `keccak("wards(address)")[0:4] = 0xbf353dbb`. -/
axiom wardsSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr wardsTransition))).extract 0 4 =
      clipperSelBytes 27

/-- `keccak("yank(uint256)")[0:4] = 0x26e027f1`. -/
axiom yankSelectorBytes (v : ClipperImmutables) :
    (ffi.KEC (String.toByteArray (transitionSigStr (yankTransition v)))).extract 0 4 =
      clipperSelBytes 28

end Benchmarks.Dss.Clipper
