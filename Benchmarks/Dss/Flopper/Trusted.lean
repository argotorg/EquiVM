import Benchmarks.Dss.Flopper.Common

/-!
# MakerDAO/Sky DSS Flopper selector proofs

The selector theorems connect Solm signatures to the runtime dispatcher constants.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.Dss.Flopper

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- `keccak("beg()")[0:4] = 0x7d780d82`. -/
theorem begSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr begTransition))).extract 0 4 =
      flopperSelBytes 0 := by decide +kernel

/-- `keccak("bids(uint256)")[0:4] = 0x4423c5f1`. -/
theorem bidsSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr bidsTransition))).extract 0 4 =
      flopperSelBytes 1 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, bidsTransition, uint256]; decide +kernel

/-- `keccak("cage()")[0:4] = 0x69245009`. -/
theorem cageSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr cageTransition))).extract 0 4 =
      flopperSelBytes 2 := by decide +kernel

/-- `keccak("deal(uint256)")[0:4] = 0xc959c42b`. -/
theorem dealSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr dealTransition))).extract 0 4 =
      flopperSelBytes 3 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, dealTransition, uint256]; decide +kernel

/-- `keccak("dent(uint256,uint256,uint256)")[0:4] = 0x5ff3a382`. -/
theorem dentSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr dentTransition))).extract 0 4 =
      flopperSelBytes 4 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, dentTransition, uint256]; decide +kernel

/-- `keccak("deny(address)")[0:4] = 0x9c52a7f1`. -/
theorem denySelectorBytes :
    (KEC (String.toByteArray (transitionSigStr denyTransition))).extract 0 4 =
      flopperSelBytes 5 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, denyTransition, addr]; decide +kernel

/-- `keccak("file(bytes32,uint256)")[0:4] = 0x29ae8114`. -/
theorem fileSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr fileTransition))).extract 0 4 =
      flopperSelBytes 6 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, fileTransition, bytes32, uint256]; decide +kernel

/-- `keccak("gem()")[0:4] = 0x7bd2bea7`. -/
theorem gemSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr gemTransition))).extract 0 4 =
      flopperSelBytes 7 := by decide +kernel

/-- `keccak("kick(address,uint256,uint256)")[0:4] = 0xb7e9cd24`. -/
theorem kickSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr kickTransition))).extract 0 4 =
      flopperSelBytes 8 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, kickTransition, addr, uint256]; decide +kernel

/-- `keccak("kicks()")[0:4] = 0xcfdd3302`. -/
theorem kicksSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr kicksTransition))).extract 0 4 =
      flopperSelBytes 9 := by decide +kernel

/-- `keccak("live()")[0:4] = 0x957aa58c`. -/
theorem liveSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr liveTransition))).extract 0 4 =
      flopperSelBytes 10 := by decide +kernel

/-- `keccak("pad()")[0:4] = 0x9361266c`. -/
theorem padSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr padTransition))).extract 0 4 =
      flopperSelBytes 11 := by decide +kernel

/-- `keccak("rely(address)")[0:4] = 0x65fae35e`. -/
theorem relySelectorBytes :
    (KEC (String.toByteArray (transitionSigStr relyTransition))).extract 0 4 =
      flopperSelBytes 12 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, relyTransition, addr]; decide +kernel

/-- `keccak("tau()")[0:4] = 0xcfc4af55`. -/
theorem tauSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr tauTransition))).extract 0 4 =
      flopperSelBytes 13 := by decide +kernel

/-- `keccak("tick(uint256)")[0:4] = 0xfc7b6aee`. -/
theorem tickSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr tickTransition))).extract 0 4 =
      flopperSelBytes 14 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, tickTransition, uint256]; decide +kernel

/-- `keccak("ttl()")[0:4] = 0x4e8b1dd5`. -/
theorem ttlSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr ttlTransition))).extract 0 4 =
      flopperSelBytes 15 := by decide +kernel

/-- `keccak("vat()")[0:4] = 0x36569e77`. -/
theorem vatSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr vatTransition))).extract 0 4 =
      flopperSelBytes 16 := by decide +kernel

/-- `keccak("vow()")[0:4] = 0x626cb3c5`. -/
theorem vowSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr vowTransition))).extract 0 4 =
      flopperSelBytes 17 := by decide +kernel

/-- `keccak("wards(address)")[0:4] = 0xbf353dbb`. -/
theorem wardsSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr wardsTransition))).extract 0 4 =
      flopperSelBytes 18 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, wardsTransition, addr]; decide +kernel

/-- `keccak("yank(uint256)")[0:4] = 0x26e027f1`. -/
theorem yankSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr yankTransition))).extract 0 4 =
      flopperSelBytes 19 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, yankTransition, uint256]; decide +kernel

end Benchmarks.Dss.Flopper
