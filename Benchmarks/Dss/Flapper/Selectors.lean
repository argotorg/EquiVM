import Benchmarks.Dss.Flapper.Common

/-!
# MakerDAO/Sky DSS Flapper selector proofs

The selector theorems connect Solm signatures to the runtime dispatcher constants.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.Dss.Flapper

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- `keccak("beg()")[0:4] = 0x7d780d82`. -/
theorem begSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr begTransition))).extract 0 4 =
      flapperSelBytes 0 := by decide +kernel

/-- `keccak("bids(uint256)")[0:4] = 0x4423c5f1`. -/
theorem bidsSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr bidsTransition))).extract 0 4 =
      flapperSelBytes 1 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature,
    ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr,
    bidsTransition, uint256] <;> decide +kernel

/-- `keccak("cage(uint256)")[0:4] = 0xa2f91af2`. -/
theorem cageSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr cageTransition))).extract 0 4 =
      flapperSelBytes 2 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature,
    ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr,
    cageTransition, uint256] <;> decide +kernel

/-- `keccak("deal(uint256)")[0:4] = 0xc959c42b`. -/
theorem dealSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr dealTransition))).extract 0 4 =
      flapperSelBytes 3 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature,
    ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr,
    dealTransition, uint256] <;> decide +kernel

/-- `keccak("deny(address)")[0:4] = 0x9c52a7f1`. -/
theorem denySelectorBytes :
    (KEC (String.toByteArray (transitionSigStr denyTransition))).extract 0 4 =
      flapperSelBytes 4 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature,
    ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr,
    denyTransition, addr] <;> decide +kernel

/-- `keccak("file(bytes32,uint256)")[0:4] = 0x29ae8114`. -/
theorem fileSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr fileTransition))).extract 0 4 =
      flapperSelBytes 5 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature,
    ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr,
    fileTransition, bytes32, uint256] <;> decide +kernel

/-- `keccak("fill()")[0:4] = 0xd9c55ce1`. -/
theorem fillSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr fillTransition))).extract 0 4 =
      flapperSelBytes 6 := by decide +kernel

/-- `keccak("gem()")[0:4] = 0x7bd2bea7`. -/
theorem gemSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr gemTransition))).extract 0 4 =
      flapperSelBytes 7 := by decide +kernel

/-- `keccak("kick(uint256,uint256)")[0:4] = 0xca40c419`. -/
theorem kickSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr kickTransition))).extract 0 4 =
      flapperSelBytes 8 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature,
    ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr,
    kickTransition, uint256] <;> decide +kernel

/-- `keccak("kicks()")[0:4] = 0xcfdd3302`. -/
theorem kicksSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr kicksTransition))).extract 0 4 =
      flapperSelBytes 9 := by decide +kernel

/-- `keccak("lid()")[0:4] = 0x26d2addc`. -/
theorem lidSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr lidTransition))).extract 0 4 =
      flapperSelBytes 10 := by decide +kernel

/-- `keccak("live()")[0:4] = 0x957aa58c`. -/
theorem liveSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr liveTransition))).extract 0 4 =
      flapperSelBytes 11 := by decide +kernel

/-- `keccak("rely(address)")[0:4] = 0x65fae35e`. -/
theorem relySelectorBytes :
    (KEC (String.toByteArray (transitionSigStr relyTransition))).extract 0 4 =
      flapperSelBytes 12 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature,
    ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr,
    relyTransition, addr] <;> decide +kernel

/-- `keccak("tau()")[0:4] = 0xcfc4af55`. -/
theorem tauSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr tauTransition))).extract 0 4 =
      flapperSelBytes 13 := by decide +kernel

/-- `keccak("tend(uint256,uint256,uint256)")[0:4] = 0x4b43ed12`. -/
theorem tendSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr tendTransition))).extract 0 4 =
      flapperSelBytes 14 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature,
    ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr,
    tendTransition, uint256] <;> decide +kernel

/-- `keccak("tick(uint256)")[0:4] = 0xfc7b6aee`. -/
theorem tickSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr tickTransition))).extract 0 4 =
      flapperSelBytes 15 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature,
    ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr,
    tickTransition, uint256] <;> decide +kernel

/-- `keccak("ttl()")[0:4] = 0x4e8b1dd5`. -/
theorem ttlSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr ttlTransition))).extract 0 4 =
      flapperSelBytes 16 := by decide +kernel

/-- `keccak("vat()")[0:4] = 0x36569e77`. -/
theorem vatSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr vatTransition))).extract 0 4 =
      flapperSelBytes 17 := by decide +kernel

/-- `keccak("wards(address)")[0:4] = 0xbf353dbb`. -/
theorem wardsSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr wardsTransition))).extract 0 4 =
      flapperSelBytes 18 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature,
    ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr,
    wardsTransition, addr] <;> decide +kernel

/-- `keccak("yank(uint256)")[0:4] = 0x26e027f1`. -/
theorem yankSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr yankTransition))).extract 0 4 =
      flapperSelBytes 19 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature,
    ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr,
    yankTransition, uint256] <;> decide +kernel

end Benchmarks.Dss.Flapper
