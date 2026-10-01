import Benchmarks.Dss.Cat.Bytecode
import Solm.Semantics

/-!
# MakerDAO/Sky DSS Cat selector proofs

The selector theorems connect Solm signatures to the runtime dispatcher constants.
-/

open Solm Ethereum Ethereum.EVM

namespace Benchmarks.Dss.Cat

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- `keccak("bite(bytes32,address)")[0:4] = 0x45cf2230`. -/
theorem biteSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr biteTransition))).extract 0 4 =
      ⟨#[0x45, 0xcf, 0x22, 0x30]⟩ := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, biteTransition, bytes32, addr]; decide +kernel

/-- `keccak("box()")[0:4] = 0x754215a1`. -/
theorem boxSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr boxTransition))).extract 0 4 =
      ⟨#[0x75, 0x42, 0x15, 0xa1]⟩ := by decide +kernel

/-- `keccak("cage()")[0:4] = 0x69245009`. -/
theorem cageSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr cageTransition))).extract 0 4 =
      ⟨#[0x69, 0x24, 0x50, 0x09]⟩ := by decide +kernel

/-- `keccak("claw(uint256)")[0:4] = 0xe66d279b`. -/
theorem clawSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr clawTransition))).extract 0 4 =
      ⟨#[0xe6, 0x6d, 0x27, 0x9b]⟩ := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, clawTransition, uint256]; decide +kernel

/-- `keccak("deny(address)")[0:4] = 0x9c52a7f1`. -/
theorem denySelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr denyTransition))).extract 0 4 =
      ⟨#[0x9c, 0x52, 0xa7, 0xf1]⟩ := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, denyTransition, addr]; decide +kernel

/-- `keccak("file(bytes32,address)")[0:4] = 0xd4e8be83`. -/
theorem fileAddressSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr fileAddressTransition))).extract 0 4 =
      ⟨#[0xd4, 0xe8, 0xbe, 0x83]⟩ := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, fileAddressTransition, bytes32, addr]; decide +kernel

/-- `keccak("file(bytes32,bytes32,address)")[0:4] = 0xebecb39d`. -/
theorem fileIlkFlipSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr fileIlkFlipTransition))).extract 0 4 =
      ⟨#[0xeb, 0xec, 0xb3, 0x9d]⟩ := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, fileIlkFlipTransition, bytes32, addr]; decide +kernel

/-- `keccak("file(bytes32,bytes32,uint256)")[0:4] = 0x1a0b287e`. -/
theorem fileIlkUintSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr fileIlkUintTransition))).extract 0 4 =
      ⟨#[0x1a, 0x0b, 0x28, 0x7e]⟩ := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, fileIlkUintTransition, bytes32, uint256]; decide +kernel

/-- `keccak("file(bytes32,uint256)")[0:4] = 0x29ae8114`. -/
theorem fileUintSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr fileUintTransition))).extract 0 4 =
      ⟨#[0x29, 0xae, 0x81, 0x14]⟩ := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, fileUintTransition, bytes32, uint256]; decide +kernel

/-- `keccak("ilks(bytes32)")[0:4] = 0xd9638d36`. -/
theorem ilksSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr ilksTransition))).extract 0 4 =
      ⟨#[0xd9, 0x63, 0x8d, 0x36]⟩ := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ilksTransition, bytes32]; decide +kernel

/-- `keccak("litter()")[0:4] = 0xa4fe8caf`. -/
theorem litterSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr litterTransition))).extract 0 4 =
      ⟨#[0xa4, 0xfe, 0x8c, 0xaf]⟩ := by decide +kernel

/-- `keccak("live()")[0:4] = 0x957aa58c`. -/
theorem liveSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr liveTransition))).extract 0 4 =
      ⟨#[0x95, 0x7a, 0xa5, 0x8c]⟩ := by decide +kernel

/-- `keccak("rely(address)")[0:4] = 0x65fae35e`. -/
theorem relySelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr relyTransition))).extract 0 4 =
      ⟨#[0x65, 0xfa, 0xe3, 0x5e]⟩ := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, relyTransition, addr]; decide +kernel

/-- `keccak("vat()")[0:4] = 0x36569e77`. -/
theorem vatSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr vatTransition))).extract 0 4 =
      ⟨#[0x36, 0x56, 0x9e, 0x77]⟩ := by decide +kernel

/-- `keccak("vow()")[0:4] = 0x626cb3c5`. -/
theorem vowSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr vowTransition))).extract 0 4 =
      ⟨#[0x62, 0x6c, 0xb3, 0xc5]⟩ := by decide +kernel

/-- `keccak("wards(address)")[0:4] = 0xbf353dbb`. -/
theorem wardsSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr wardsTransition))).extract 0 4 =
      ⟨#[0xbf, 0x35, 0x3d, 0xbb]⟩ := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, wardsTransition, addr]; decide +kernel

end Benchmarks.Dss.Cat
