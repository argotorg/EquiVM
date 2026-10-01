import Benchmarks.Dss.Cure.Bytecode
import Solm.Semantics
import Reasoning.Solc

/-!
# MakerDAO/Sky DSS Cure selector proofs

The selector theorems connect Solm signatures to the runtime dispatcher constants.
-/

open Solm Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Dss.Cure

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-! ## Selector bytes -/

/-- `keccak("amt(address)")[0:4] = 0x09615662`. -/
theorem cureAmtSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr amtTransition))).extract 0 4 =
      ⟨#[0x09, 0x61, 0x56, 0x62]⟩ := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, amtTransition, addr]; decide +kernel

/-- `keccak("cage()")[0:4] = 0x69245009`. -/
theorem cureCageSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr cageTransition))).extract 0 4 =
      ⟨#[0x69, 0x24, 0x50, 0x09]⟩ := by decide +kernel

/-- `keccak("deny(address)")[0:4] = 0x9c52a7f1`. -/
theorem cureDenySelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr denyTransition))).extract 0 4 =
      ⟨#[0x9c, 0x52, 0xa7, 0xf1]⟩ := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, denyTransition, addr]; decide +kernel

/-- `keccak("drop(address)")[0:4] = 0x91f2700a`. -/
theorem cureDropSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr dropTransition))).extract 0 4 =
      ⟨#[0x91, 0xf2, 0x70, 0x0a]⟩ := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, dropTransition, addr]; decide +kernel

/-- `keccak("file(bytes32,uint256)")[0:4] = 0x29ae8114`. -/
theorem cureFileSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr fileTransition))).extract 0 4 =
      ⟨#[0x29, 0xae, 0x81, 0x14]⟩ := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, fileTransition, bytes32, uint256]; decide +kernel

/-- `keccak("lCount()")[0:4] = 0x493aa4c7`. -/
theorem cureLCountSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr lCountTransition))).extract 0 4 =
      ⟨#[0x49, 0x3a, 0xa4, 0xc7]⟩ := by decide +kernel

/-- `keccak("lift(address)")[0:4] = 0x3c278bd5`. -/
theorem cureLiftSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr liftTransition))).extract 0 4 =
      ⟨#[0x3c, 0x27, 0x8b, 0xd5]⟩ := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, liftTransition, addr]; decide +kernel

/-- `keccak("list()")[0:4] = 0x0f560cd7`. -/
theorem cureListSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr listTransition))).extract 0 4 =
      ⟨#[0x0f, 0x56, 0x0c, 0xd7]⟩ := by decide +kernel

/-- `keccak("live()")[0:4] = 0x957aa58c`. -/
theorem cureLiveSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr liveTransition))).extract 0 4 =
      ⟨#[0x95, 0x7a, 0xa5, 0x8c]⟩ := by decide +kernel

/-- `keccak("load(address)")[0:4] = 0x2f40e734`. -/
theorem cureLoadSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr loadTransition))).extract 0 4 =
      ⟨#[0x2f, 0x40, 0xe7, 0x34]⟩ := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, loadTransition, addr]; decide +kernel

/-- `keccak("loaded(address)")[0:4] = 0xffa9ca9f`. -/
theorem cureLoadedSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr loadedTransition))).extract 0 4 =
      ⟨#[0xff, 0xa9, 0xca, 0x9f]⟩ := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, loadedTransition, addr]; decide +kernel

/-- `keccak("pos(address)")[0:4] = 0x93d0281c`. -/
theorem curePosSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr posTransition))).extract 0 4 =
      ⟨#[0x93, 0xd0, 0x28, 0x1c]⟩ := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, posTransition, addr]; decide +kernel

/-- `keccak("rely(address)")[0:4] = 0x65fae35e`. -/
theorem cureRelySelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr relyTransition))).extract 0 4 =
      ⟨#[0x65, 0xfa, 0xe3, 0x5e]⟩ := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, relyTransition, addr]; decide +kernel

/-- `keccak("say()")[0:4] = 0x954ab4b2`. -/
theorem cureSaySelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr sayTransition))).extract 0 4 =
      ⟨#[0x95, 0x4a, 0xb4, 0xb2]⟩ := by decide +kernel

/-- `keccak("srcs(uint256)")[0:4] = 0xf381273f`. -/
theorem cureSrcsSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr srcsTransition))).extract 0 4 =
      ⟨#[0xf3, 0x81, 0x27, 0x3f]⟩ := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, srcsTransition, uint256]; decide +kernel

/-- `keccak("tCount()")[0:4] = 0x53f9a873`. -/
theorem cureTCountSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr tCountTransition))).extract 0 4 =
      ⟨#[0x53, 0xf9, 0xa8, 0x73]⟩ := by decide +kernel

/-- `keccak("tell()")[0:4] = 0x53d700e5`. -/
theorem cureTellSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr tellTransition))).extract 0 4 =
      ⟨#[0x53, 0xd7, 0x00, 0xe5]⟩ := by decide +kernel

/-- `keccak("wait()")[0:4] = 0x64bd7013`. -/
theorem cureWaitSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr waitTransition))).extract 0 4 =
      ⟨#[0x64, 0xbd, 0x70, 0x13]⟩ := by decide +kernel

/-- `keccak("wards(address)")[0:4] = 0xbf353dbb`. -/
theorem cureWardsSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr wardsTransition))).extract 0 4 =
      ⟨#[0xbf, 0x35, 0x3d, 0xbb]⟩ := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, wardsTransition, addr]; decide +kernel

/-- `keccak("when()")[0:4] = 0xe2b0caef`. -/
theorem cureWhenSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr whenTransition))).extract 0 4 =
      ⟨#[0xe2, 0xb0, 0xca, 0xef]⟩ := by decide +kernel

end Benchmarks.Dss.Cure
