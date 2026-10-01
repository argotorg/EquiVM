import Benchmarks.Dss.Vow.Bytecode
import Solm.Semantics

/-!
# MakerDAO/Sky DSS Vow selector proofs

The selector theorems connect Solm signatures to the runtime dispatcher constants.
-/

open Solm Ethereum Ethereum.EVM

namespace Benchmarks.Dss.Vow

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- `keccak("Ash()")[0:4] = 0x2a1d2b3c`. -/
theorem AshSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr AshTransition))).extract 0 4 =
      ⟨#[0x2a, 0x1d, 0x2b, 0x3c]⟩ := by decide +kernel

/-- `keccak("Sin()")[0:4] = 0xd0adc35f`. -/
theorem SinSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr SinTransition))).extract 0 4 =
      ⟨#[0xd0, 0xad, 0xc3, 0x5f]⟩ := by decide +kernel

/-- `keccak("bump()")[0:4] = 0x68110b2f`. -/
theorem bumpSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr bumpTransition))).extract 0 4 =
      ⟨#[0x68, 0x11, 0x0b, 0x2f]⟩ := by decide +kernel

/-- `keccak("cage()")[0:4] = 0x69245009`. -/
theorem cageSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr cageTransition))).extract 0 4 =
      ⟨#[0x69, 0x24, 0x50, 0x09]⟩ := by decide +kernel

/-- `keccak("deny(address)")[0:4] = 0x9c52a7f1`. -/
theorem denySelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr denyTransition))).extract 0 4 =
      ⟨#[0x9c, 0x52, 0xa7, 0xf1]⟩ := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, denyTransition, addr]; decide +kernel

/-- `keccak("dump()")[0:4] = 0xe4330545`. -/
theorem dumpSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr dumpTransition))).extract 0 4 =
      ⟨#[0xe4, 0x33, 0x05, 0x45]⟩ := by decide +kernel

/-- `keccak("fess(uint256)")[0:4] = 0x697efb78`. -/
theorem fessSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr fessTransition))).extract 0 4 =
      ⟨#[0x69, 0x7e, 0xfb, 0x78]⟩ := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, fessTransition, uint256]; decide +kernel

/-- `keccak("file(bytes32,uint256)")[0:4] = 0x29ae8114`. -/
theorem fileUintSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr fileUintTransition))).extract 0 4 =
      ⟨#[0x29, 0xae, 0x81, 0x14]⟩ := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, fileUintTransition, bytes32, uint256]; decide +kernel

/-- `keccak("file(bytes32,address)")[0:4] = 0xd4e8be83`. -/
theorem fileAddressSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr fileAddressTransition))).extract 0 4 =
      ⟨#[0xd4, 0xe8, 0xbe, 0x83]⟩ := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, fileAddressTransition, bytes32, addr]; decide +kernel

/-- `keccak("flap()")[0:4] = 0x0e01198b`. -/
theorem flapSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr flapTransition))).extract 0 4 =
      ⟨#[0x0e, 0x01, 0x19, 0x8b]⟩ := by decide +kernel

/-- `keccak("flapper()")[0:4] = 0x5ca0d723`. -/
theorem flapperSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr flapperTransition))).extract 0 4 =
      ⟨#[0x5c, 0xa0, 0xd7, 0x23]⟩ := by decide +kernel

/-- `keccak("flog(uint256)")[0:4] = 0xd7ee674b`. -/
theorem flogSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr flogTransition))).extract 0 4 =
      ⟨#[0xd7, 0xee, 0x67, 0x4b]⟩ := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, flogTransition, uint256]; decide +kernel

/-- `keccak("flop()")[0:4] = 0xbbbb0d7b`. -/
theorem flopSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr flopTransition))).extract 0 4 =
      ⟨#[0xbb, 0xbb, 0x0d, 0x7b]⟩ := by decide +kernel

/-- `keccak("flopper()")[0:4] = 0x4081d73a`. -/
theorem flopperSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr flopperTransition))).extract 0 4 =
      ⟨#[0x40, 0x81, 0xd7, 0x3a]⟩ := by decide +kernel

/-- `keccak("heal(uint256)")[0:4] = 0xf37ac61c`. -/
theorem healSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr healTransition))).extract 0 4 =
      ⟨#[0xf3, 0x7a, 0xc6, 0x1c]⟩ := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, healTransition, uint256]; decide +kernel

/-- `keccak("hump()")[0:4] = 0x1b8e8cfa`. -/
theorem humpSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr humpTransition))).extract 0 4 =
      ⟨#[0x1b, 0x8e, 0x8c, 0xfa]⟩ := by decide +kernel

/-- `keccak("kiss(uint256)")[0:4] = 0x2506855a`. -/
theorem kissSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr kissTransition))).extract 0 4 =
      ⟨#[0x25, 0x06, 0x85, 0x5a]⟩ := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, kissTransition, uint256]; decide +kernel

/-- `keccak("live()")[0:4] = 0x957aa58c`. -/
theorem liveSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr liveTransition))).extract 0 4 =
      ⟨#[0x95, 0x7a, 0xa5, 0x8c]⟩ := by decide +kernel

/-- `keccak("rely(address)")[0:4] = 0x65fae35e`. -/
theorem relySelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr relyTransition))).extract 0 4 =
      ⟨#[0x65, 0xfa, 0xe3, 0x5e]⟩ := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, relyTransition, addr]; decide +kernel

/-- `keccak("sin(uint256)")[0:4] = 0xcb5cc109`. -/
theorem sinSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr sinTransition))).extract 0 4 =
      ⟨#[0xcb, 0x5c, 0xc1, 0x09]⟩ := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, sinTransition, uint256]; decide +kernel

/-- `keccak("sump()")[0:4] = 0xc349d362`. -/
theorem sumpSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr sumpTransition))).extract 0 4 =
      ⟨#[0xc3, 0x49, 0xd3, 0x62]⟩ := by decide +kernel

/-- `keccak("vat()")[0:4] = 0x36569e77`. -/
theorem vatSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr vatTransition))).extract 0 4 =
      ⟨#[0x36, 0x56, 0x9e, 0x77]⟩ := by decide +kernel

/-- `keccak("wait()")[0:4] = 0x64bd7013`. -/
theorem waitSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr waitTransition))).extract 0 4 =
      ⟨#[0x64, 0xbd, 0x70, 0x13]⟩ := by decide +kernel

/-- `keccak("wards(address)")[0:4] = 0xbf353dbb`. -/
theorem wardsSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr wardsTransition))).extract 0 4 =
      ⟨#[0xbf, 0x35, 0x3d, 0xbb]⟩ := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, wardsTransition, addr]; decide +kernel

end Benchmarks.Dss.Vow
