import Benchmarks.Dss.Pot.Common

/-!
# MakerDAO/Sky DSS Pot selector proofs

The selector theorems connect Solm signatures to the runtime dispatcher constants.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.Dss.Pot

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- `keccak("Pie()")[0:4] = 0x2c69ed58`. -/
theorem PieSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr PieTransition))).extract 0 4 =
      potSelBytes 0 := by decide +kernel

/-- `keccak("cage()")[0:4] = 0x69245009`. -/
theorem cageSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr cageTransition))).extract 0 4 =
      potSelBytes 1 := by decide +kernel

/-- `keccak("chi()")[0:4] = 0xc92aecc4`. -/
theorem chiSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr chiTransition))).extract 0 4 =
      potSelBytes 2 := by decide +kernel

/-- `keccak("deny(address)")[0:4] = 0x9c52a7f1`. -/
theorem denySelectorBytes :
    (KEC (String.toByteArray (transitionSigStr denyTransition))).extract 0 4 =
      potSelBytes 3 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature,
    ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr,
    denyTransition, addr] <;> decide +kernel

/-- `keccak("drip()")[0:4] = 0x9f678cca`. -/
theorem dripSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr dripTransition))).extract 0 4 =
      potSelBytes 4 := by decide +kernel

/-- `keccak("dsr()")[0:4] = 0x487bf082`. -/
theorem dsrSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr dsrTransition))).extract 0 4 =
      potSelBytes 5 := by decide +kernel

/-- `keccak("exit(uint256)")[0:4] = 0x7f8661a1`. -/
theorem exitSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr exitTransition))).extract 0 4 =
      potSelBytes 6 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature,
    ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr,
    exitTransition, uint256] <;> decide +kernel

/-- `keccak("file(bytes32,uint256)")[0:4] = 0x29ae8114`. -/
theorem fileDsrSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr fileDsrTransition))).extract 0 4 =
      potSelBytes 7 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature,
    ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr,
    fileDsrTransition, bytes32, uint256] <;> decide +kernel

/-- `keccak("file(bytes32,address)")[0:4] = 0xd4e8be83`. -/
theorem fileVowSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr fileVowTransition))).extract 0 4 =
      potSelBytes 8 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature,
    ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr,
    fileVowTransition, bytes32, addr] <;> decide +kernel

/-- `keccak("join(uint256)")[0:4] = 0x049878f3`. -/
theorem joinSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr joinTransition))).extract 0 4 =
      potSelBytes 9 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature,
    ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr,
    joinTransition, uint256] <;> decide +kernel

/-- `keccak("live()")[0:4] = 0x957aa58c`. -/
theorem liveSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr liveTransition))).extract 0 4 =
      potSelBytes 10 := by decide +kernel

/-- `keccak("pie(address)")[0:4] = 0x0bebac86`. -/
theorem pieSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr pieTransition))).extract 0 4 =
      potSelBytes 11 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature,
    ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr,
    pieTransition, addr] <;> decide +kernel

/-- `keccak("rely(address)")[0:4] = 0x65fae35e`. -/
theorem relySelectorBytes :
    (KEC (String.toByteArray (transitionSigStr relyTransition))).extract 0 4 =
      potSelBytes 12 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature,
    ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr,
    relyTransition, addr] <;> decide +kernel

/-- `keccak("rho()")[0:4] = 0x20aba08b`. -/
theorem rhoSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr rhoTransition))).extract 0 4 =
      potSelBytes 13 := by decide +kernel

/-- `keccak("vat()")[0:4] = 0x36569e77`. -/
theorem vatSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr vatTransition))).extract 0 4 =
      potSelBytes 14 := by decide +kernel

/-- `keccak("vow()")[0:4] = 0x626cb3c5`. -/
theorem vowSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr vowTransition))).extract 0 4 =
      potSelBytes 15 := by decide +kernel

/-- `keccak("wards(address)")[0:4] = 0xbf353dbb`. -/
theorem wardsSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr wardsTransition))).extract 0 4 =
      potSelBytes 16 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature,
    ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr,
    wardsTransition, addr] <;> decide +kernel

end Benchmarks.Dss.Pot
