import Benchmarks.Dss.Clipper.Common
import Solm.Semantics

/-!
# MakerDAO/Sky DSS Clipper selector proofs

The selector theorems connect Solm signatures to the runtime dispatcher constants.
-/

open Solm ABI Ethereum Ethereum.EVM
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- `keccak256(uint256(11))`, the dynamic-array data slot embedded by solc 0.6.12. -/
theorem activeDataSlot_eq :
    activeDataSlot =
      ⟨660301456019777184113296434797620819555017468543624515662331739614079884729⟩ := by
  decide +kernel

/-- `keccak("active(uint256)")[0:4] = 0x8033d581`. -/
theorem activeSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr activeTransition))).extract 0 4 =
      clipperSelBytes 0 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, activeTransition, uint256]; decide +kernel

/-- `keccak("buf()")[0:4] = 0x15232515`. -/
theorem bufSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr bufTransition))).extract 0 4 =
      clipperSelBytes 1 := by decide +kernel

/-- `keccak("calc()")[0:4] = 0x96f1b6be`. -/
theorem calcSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr calcTransition))).extract 0 4 =
      clipperSelBytes 2 := by decide +kernel

/-- `keccak("chip()")[0:4] = 0xb61500e4`. -/
theorem chipSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr chipTransition))).extract 0 4 =
      clipperSelBytes 3 := by decide +kernel

/-- `keccak("chost()")[0:4] = 0xba2cdc75`. -/
theorem chostSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr chostTransition))).extract 0 4 =
      clipperSelBytes 4 := by decide +kernel

/-- `keccak("count()")[0:4] = 0x06661abd`. -/
theorem countSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr countTransition))).extract 0 4 =
      clipperSelBytes 5 := by decide +kernel

/-- `keccak("cusp()")[0:4] = 0x49ed5931`. -/
theorem cuspSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr cuspTransition))).extract 0 4 =
      clipperSelBytes 6 := by decide +kernel

/-- `keccak("deny(address)")[0:4] = 0x9c52a7f1`. -/
theorem denySelectorBytes :
    (KEC (String.toByteArray (transitionSigStr denyTransition))).extract 0 4 =
      clipperSelBytes 7 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, denyTransition, addr]; decide +kernel

/-- `keccak("dog()")[0:4] = 0xc3b3ad7f`. -/
theorem dogSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr dogTransition))).extract 0 4 =
      clipperSelBytes 8 := by decide +kernel

/-- `keccak("file(bytes32,uint256)")[0:4] = 0x29ae8114`. -/
theorem fileUintSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr fileUintTransition))).extract 0 4 =
      clipperSelBytes 9 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, fileUintTransition, bytes32, uint256]; decide +kernel

/-- `keccak("file(bytes32,address)")[0:4] = 0xd4e8be83`. -/
theorem fileAddressSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr fileAddressTransition))).extract 0 4 =
      clipperSelBytes 10 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, fileAddressTransition, bytes32, addr]; decide +kernel

/-- `keccak("getStatus(uint256)")[0:4] = 0x5c622a0e`. -/
theorem getStatusSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr getStatusTransition))).extract 0 4 =
      clipperSelBytes 11 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, getStatusTransition, uint256]; decide +kernel

/-- `keccak("ilk()")[0:4] = 0xc5ce281e`. -/
theorem ilkSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr ilkTransition))).extract 0 4 =
      clipperSelBytes 12 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ilkTransition]; decide +kernel

/-- `keccak("kick(uint256,uint256,address,address)")[0:4] = 0x898eb267`. -/
theorem kickSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr kickTransition))).extract 0 4 =
      clipperSelBytes 13 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, kickTransition, uint256, addr]; decide +kernel

/-- `keccak("kicks()")[0:4] = 0xcfdd3302`. -/
theorem kicksSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr kicksTransition))).extract 0 4 =
      clipperSelBytes 14 := by decide +kernel

/-- `keccak("list()")[0:4] = 0x0f560cd7`. -/
theorem listSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr listTransition))).extract 0 4 =
      clipperSelBytes 15 := by decide +kernel

/-- `keccak("redo(uint256,address)")[0:4] = 0xd843416d`. -/
theorem redoSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr redoTransition))).extract 0 4 =
      clipperSelBytes 16 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, redoTransition, uint256, addr]; decide +kernel

/-- `keccak("rely(address)")[0:4] = 0x65fae35e`. -/
theorem relySelectorBytes :
    (KEC (String.toByteArray (transitionSigStr relyTransition))).extract 0 4 =
      clipperSelBytes 17 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, relyTransition, addr]; decide +kernel

/-- `keccak("sales(uint256)")[0:4] = 0xb5f522f7`. -/
theorem salesSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr salesTransition))).extract 0 4 =
      clipperSelBytes 18 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, salesTransition, uint256]; decide +kernel

/-- `keccak("spotter()")[0:4] = 0x2e77468d`. -/
theorem spotterSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr spotterTransition))).extract 0 4 =
      clipperSelBytes 19 := by decide +kernel

/-- `keccak("stopped()")[0:4] = 0x75f12b21`. -/
theorem stoppedSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr stoppedTransition))).extract 0 4 =
      clipperSelBytes 20 := by decide +kernel

/-- `keccak("tail()")[0:4] = 0x13d8c840`. -/
theorem tailSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr tailTransition))).extract 0 4 =
      clipperSelBytes 21 := by decide +kernel

/-- `keccak("take(uint256,uint256,uint256,address,bytes)")[0:4] = 0x81a794cb`. -/
theorem takeSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr takeTransition))).extract 0 4 =
      clipperSelBytes 22 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, takeTransition, uint256, addr, bytesDyn]; decide +kernel

/-- `keccak("tip()")[0:4] = 0x2755cd2d`. -/
theorem tipSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr tipTransition))).extract 0 4 =
      clipperSelBytes 23 := by decide +kernel

/-- `keccak("upchost()")[0:4] = 0x0cbb5862`. -/
theorem upchostSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr upchostTransition))).extract 0 4 =
      clipperSelBytes 24 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, upchostTransition]; decide +kernel

/-- `keccak("vat()")[0:4] = 0x36569e77`. -/
theorem vatSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr vatTransition))).extract 0 4 =
      clipperSelBytes 25 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, vatTransition]; decide +kernel

/-- `keccak("vow()")[0:4] = 0x626cb3c5`. -/
theorem vowSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr vowTransition))).extract 0 4 =
      clipperSelBytes 26 := by decide +kernel

/-- `keccak("wards(address)")[0:4] = 0xbf353dbb`. -/
theorem wardsSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr wardsTransition))).extract 0 4 =
      clipperSelBytes 27 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, wardsTransition, addr]; decide +kernel

/-- `keccak("yank(uint256)")[0:4] = 0x26e027f1`. -/
theorem yankSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr yankTransition))).extract 0 4 =
      clipperSelBytes 28 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, yankTransition, uint256]; decide +kernel

end Benchmarks.Dss.Clipper
