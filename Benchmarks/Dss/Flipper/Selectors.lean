import Benchmarks.Dss.Flipper.Common

/-!
# MakerDAO/Sky DSS Flipper selector proofs

The selector theorems connect Solm signatures to the runtime dispatcher constants.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.Dss.Flipper

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- `keccak("beg()")[0:4] = 0x7d780d82`. -/
theorem begSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr begTransition))).extract 0 4 =
      flipperSelBytes 0 := by decide +kernel

/-- `keccak("bids(uint256)")[0:4] = 0x4423c5f1`. -/
theorem bidsSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr bidsTransition))).extract 0 4 =
      flipperSelBytes 1 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, bidsTransition, uint256]; decide +kernel

/-- `keccak("cat()")[0:4] = 0xe4881813`. -/
theorem catSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr catTransition))).extract 0 4 =
      flipperSelBytes 2 := by decide +kernel

/-- `keccak("deal(uint256)")[0:4] = 0xc959c42b`. -/
theorem dealSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr dealTransition))).extract 0 4 =
      flipperSelBytes 3 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, dealTransition, uint256]; decide +kernel

/-- `keccak("dent(uint256,uint256,uint256)")[0:4] = 0x5ff3a382`. -/
theorem dentSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr dentTransition))).extract 0 4 =
      flipperSelBytes 4 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, dentTransition, uint256]; decide +kernel

/-- `keccak("deny(address)")[0:4] = 0x9c52a7f1`. -/
theorem denySelectorBytes :
    (KEC (String.toByteArray (transitionSigStr denyTransition))).extract 0 4 =
      flipperSelBytes 5 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, denyTransition, addr]; decide +kernel

/-- `keccak("file(bytes32,address)")[0:4] = 0xd4e8be83`. -/
theorem fileAddressSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr fileAddressTransition))).extract 0 4 =
      flipperSelBytes 6 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, fileAddressTransition, bytes32, addr]; decide +kernel

/-- `keccak("file(bytes32,uint256)")[0:4] = 0x29ae8114`. -/
theorem fileUintSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr fileUintTransition))).extract 0 4 =
      flipperSelBytes 7 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, fileUintTransition, bytes32, uint256]; decide +kernel

/-- `keccak("ilk()")[0:4] = 0xc5ce281e`. -/
theorem ilkSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr ilkTransition))).extract 0 4 =
      flipperSelBytes 8 := by decide +kernel

/-- `keccak("kick(address,address,uint256,uint256,uint256)")[0:4] = 0x351de600`. -/
theorem kickSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr kickTransition))).extract 0 4 =
      flipperSelBytes 9 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, kickTransition, addr, uint256]; decide +kernel

/-- `keccak("kicks()")[0:4] = 0xcfdd3302`. -/
theorem kicksSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr kicksTransition))).extract 0 4 =
      flipperSelBytes 10 := by decide +kernel

/-- `keccak("rely(address)")[0:4] = 0x65fae35e`. -/
theorem relySelectorBytes :
    (KEC (String.toByteArray (transitionSigStr relyTransition))).extract 0 4 =
      flipperSelBytes 11 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, relyTransition, addr]; decide +kernel

/-- `keccak("tau()")[0:4] = 0xcfc4af55`. -/
theorem tauSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr tauTransition))).extract 0 4 =
      flipperSelBytes 12 := by decide +kernel

/-- `keccak("tend(uint256,uint256,uint256)")[0:4] = 0x4b43ed12`. -/
theorem tendSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr tendTransition))).extract 0 4 =
      flipperSelBytes 13 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, tendTransition, uint256]; decide +kernel

/-- `keccak("tick(uint256)")[0:4] = 0xfc7b6aee`. -/
theorem tickSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr tickTransition))).extract 0 4 =
      flipperSelBytes 14 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, tickTransition, uint256]; decide +kernel

/-- `keccak("ttl()")[0:4] = 0x4e8b1dd5`. -/
theorem ttlSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr ttlTransition))).extract 0 4 =
      flipperSelBytes 15 := by decide +kernel

/-- `keccak("vat()")[0:4] = 0x36569e77`. -/
theorem vatSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr vatTransition))).extract 0 4 =
      flipperSelBytes 16 := by decide +kernel

/-- `keccak("wards(address)")[0:4] = 0xbf353dbb`. -/
theorem wardsSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr wardsTransition))).extract 0 4 =
      flipperSelBytes 17 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, wardsTransition, addr]; decide +kernel

/-- `keccak("yank(uint256)")[0:4] = 0x26e027f1`. -/
theorem yankSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr yankTransition))).extract 0 4 =
      flipperSelBytes 18 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, yankTransition, uint256]; decide +kernel

end Benchmarks.Dss.Flipper
