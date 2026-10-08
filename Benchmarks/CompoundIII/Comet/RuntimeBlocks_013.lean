import Reasoning.Reach
import Reasoning.Immutables
import Benchmarks.CompoundIII.Comet.Bytecode
import Benchmarks.CompoundIII.Comet.ImmutableCode

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace cometWithExtendedAssetListBlocks

open Reasoning.Immutables
set_option maxRecDepth 10000

theorem immutableLayout_sites :
    Benchmarks.CompoundIII.Comet.immutableLayout.sites = [(1592, 32, "governor"), (3441, 32, "governor"), (5137, 32, "governor"), (6161, 32, "governor"), (2168, 32, "pauseGuardian"), (3703, 32, "pauseGuardian"), (2078, 32, "baseToken"), (5008, 32, "baseToken"), (5625, 32, "baseToken"), (6266, 32, "baseToken"), (6450, 32, "baseToken"), (9907, 32, "baseToken"), (12117, 32, "baseToken"), (12429, 32, "baseToken"), (14552, 32, "baseToken"), (15644, 32, "baseToken"), (15869, 32, "baseToken"), (6768, 32, "baseTokenPriceFeed"), (10264, 32, "baseTokenPriceFeed"), (17068, 32, "baseTokenPriceFeed"), (18119, 32, "baseTokenPriceFeed"), (3767, 32, "extensionDelegate"), (18431, 32, "extensionDelegate"), (4926, 32, "supplyKink"), (8616, 32, "supplyKink"), (3925, 32, "supplyPerSecondInterestRateSlopeLow"), (8676, 32, "supplyPerSecondInterestRateSlopeLow"), (8782, 32, "supplyPerSecondInterestRateSlopeLow"), (4196, 32, "supplyPerSecondInterestRateSlopeHigh"), (8830, 32, "supplyPerSecondInterestRateSlopeHigh"), (4550, 32, "supplyPerSecondInterestRateBase"), (8715, 32, "supplyPerSecondInterestRateBase"), (4430, 32, "borrowKink"), (8888, 32, "borrowKink"), (2599, 32, "borrowPerSecondInterestRateSlopeLow"), (8948, 32, "borrowPerSecondInterestRateSlopeLow"), (9054, 32, "borrowPerSecondInterestRateSlopeLow"), (2353, 32, "borrowPerSecondInterestRateSlopeHigh"), (9102, 32, "borrowPerSecondInterestRateSlopeHigh"), (4064, 32, "borrowPerSecondInterestRateBase"), (8987, 32, "borrowPerSecondInterestRateBase"), (1966, 32, "storeFrontPriceFactor"), (18059, 32, "storeFrontPriceFactor"), (3313, 32, "baseScale"), (10302, 32, "baseScale"), (11157, 32, "baseScale"), (17180, 32, "baseScale"), (18175, 32, "baseScale"), (5072, 32, "trackingIndexScale"), (11824, 32, "trackingIndexScale"), (1772, 32, "baseTrackingSupplySpeed"), (8308, 32, "baseTrackingSupplySpeed"), (4610, 32, "baseTrackingBorrowSpeed"), (8188, 32, "baseTrackingBorrowSpeed"), (4490, 32, "baseMinForRewards"), (8046, 32, "baseMinForRewards"), (2721, 32, "baseBorrowMin"), (15134, 32, "baseBorrowMin"), (16028, 32, "baseBorrowMin"), (2844, 32, "targetReserves"), (6688, 32, "targetReserves"), (2783, 32, "decimals"), (4865, 32, "numAssets"), (7501, 32, "numAssets"), (10357, 32, "numAssets"), (10878, 32, "numAssets"), (17114, 32, "numAssets"), (11863, 32, "accrualDescaleFactor"), (6070, 32, "assetList"), (7222, 32, "assetList")] := by native_decide

theorem immutableLayout_inBounds :
    Benchmarks.CompoundIII.Comet.immutableLayout.inBounds Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode = true := by native_decide

theorem immutableTemplate_size64 :
    Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode.size < 2 ^ 64 := by native_decide

theorem immutableRuntime_size (immWords : String → UInt256) :
    (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords).size = Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode.size := by
  exact Layout.runtime_size_of_bounds immutableLayout_inBounds

theorem immutableDecode_1771 (immWords : String → UInt256) :
    decode (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) (⟨1771⟩ : UInt256) =
      some (.Push .PUSH32, some (immWords "baseTrackingSupplySpeed", 32)) := by
  exact Layout.decodeSite (pc := (⟨1771⟩ : UInt256)) (words := immWords)
    1772 "baseTrackingSupplySpeed" [(1592, immWords "governor"), (3441, immWords "governor"), (5137, immWords "governor"), (6161, immWords "governor"), (2168, immWords "pauseGuardian"), (3703, immWords "pauseGuardian"), (2078, immWords "baseToken"), (5008, immWords "baseToken"), (5625, immWords "baseToken"), (6266, immWords "baseToken"), (6450, immWords "baseToken"), (9907, immWords "baseToken"), (12117, immWords "baseToken"), (12429, immWords "baseToken"), (14552, immWords "baseToken"), (15644, immWords "baseToken"), (15869, immWords "baseToken"), (6768, immWords "baseTokenPriceFeed"), (10264, immWords "baseTokenPriceFeed"), (17068, immWords "baseTokenPriceFeed"), (18119, immWords "baseTokenPriceFeed"), (3767, immWords "extensionDelegate"), (18431, immWords "extensionDelegate"), (4926, immWords "supplyKink"), (8616, immWords "supplyKink"), (3925, immWords "supplyPerSecondInterestRateSlopeLow"), (8676, immWords "supplyPerSecondInterestRateSlopeLow"), (8782, immWords "supplyPerSecondInterestRateSlopeLow"), (4196, immWords "supplyPerSecondInterestRateSlopeHigh"), (8830, immWords "supplyPerSecondInterestRateSlopeHigh"), (4550, immWords "supplyPerSecondInterestRateBase"), (8715, immWords "supplyPerSecondInterestRateBase"), (4430, immWords "borrowKink"), (8888, immWords "borrowKink"), (2599, immWords "borrowPerSecondInterestRateSlopeLow"), (8948, immWords "borrowPerSecondInterestRateSlopeLow"), (9054, immWords "borrowPerSecondInterestRateSlopeLow"), (2353, immWords "borrowPerSecondInterestRateSlopeHigh"), (9102, immWords "borrowPerSecondInterestRateSlopeHigh"), (4064, immWords "borrowPerSecondInterestRateBase"), (8987, immWords "borrowPerSecondInterestRateBase"), (1966, immWords "storeFrontPriceFactor"), (18059, immWords "storeFrontPriceFactor"), (3313, immWords "baseScale"), (10302, immWords "baseScale"), (11157, immWords "baseScale"), (17180, immWords "baseScale"), (18175, immWords "baseScale"), (5072, immWords "trackingIndexScale"), (11824, immWords "trackingIndexScale")] [(8308, immWords "baseTrackingSupplySpeed"), (4610, immWords "baseTrackingBorrowSpeed"), (8188, immWords "baseTrackingBorrowSpeed"), (4490, immWords "baseMinForRewards"), (8046, immWords "baseMinForRewards"), (2721, immWords "baseBorrowMin"), (15134, immWords "baseBorrowMin"), (16028, immWords "baseBorrowMin"), (2844, immWords "targetReserves"), (6688, immWords "targetReserves"), (2783, immWords "decimals"), (4865, immWords "numAssets"), (7501, immWords "numAssets"), (10357, immWords "numAssets"), (10878, immWords "numAssets"), (17114, immWords "numAssets"), (11863, immWords "accrualDescaleFactor"), (6070, immWords "assetList"), (7222, immWords "assetList")]
    (by native_decide) (immutableRuntime_size immWords)
    (by native_decide) (by native_decide)
    (by simp [Layout.writes, immutableLayout_sites, WindowDisjointFromWrites,
      UInt256.toNat, UInt256.size]; try native_decide)
    (by native_decide) (by rfl)
    (by
      rw [writeCascade_size]
      · simp [writeCascadeSize]; try native_decide
      · simp [WriteGapsOk]; try native_decide)
    (by simp [WindowDisjointFromWrites]; try native_decide)

/-- Final stack for bytecode block summary `cometWithExtendedAssetList_block_1639_taken`. -/
def cometWithExtendedAssetList_block_1639_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 1639. -/
theorem cometWithExtendedAssetList_block_1639_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 1410) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1639) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1410) (cometWithExtendedAssetList_block_1639_taken_stack (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1639⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pop (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1640⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.callvalue (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1641⟩ : UInt256), UInt8.ofNat 52, .CALLVALUE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1410) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1642⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1410), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1645⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1410)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_1639_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 1410) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1639) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1410) (cometWithExtendedAssetList_block_1639_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_1639_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `cometWithExtendedAssetList_block_1639_fallthrough`. -/
def cometWithExtendedAssetList_block_1639_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 1639. -/
theorem cometWithExtendedAssetList_block_1639_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1639) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1646) (cometWithExtendedAssetList_block_1639_fallthrough_stack (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1639⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pop (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1640⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.callvalue (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1641⟩ : UInt256), UInt8.ofNat 52, .CALLVALUE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1410) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1642⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1410), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiNT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1645⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1646)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_1639_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1639) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1646) (cometWithExtendedAssetList_block_1639_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_1639_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1646. -/
theorem cometWithExtendedAssetList_block_1646_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (UInt256.ofNat 0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 1410) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1646) R mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1410) R mem aw rdata σ (k + 8) (C + ((30))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1646⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.calldatasize (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1648⟩ : UInt256), UInt8.ofNat 54, .CALLDATASIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 3) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1649⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 3), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.not (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1651⟩ : UInt256), UInt8.ofNat 25, .NOT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.add (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1652⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.slt (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1653⟩ : UInt256), UInt8.ofNat 18, .SLT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 1410) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1654⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1410), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.jumpiT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1657⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1410)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_1646_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (UInt256.ofNat 0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 1410) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1646) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1410) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_1646_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1646. -/
theorem cometWithExtendedAssetList_block_1646_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (UInt256.ofNat 0)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1646) R mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1658) R mem aw rdata σ (k + 8) (C + ((30))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1646⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.calldatasize (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1648⟩ : UInt256), UInt8.ofNat 54, .CALLDATASIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 3) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1649⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 3), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.not (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1651⟩ : UInt256), UInt8.ofNat 25, .NOT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.add (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1652⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.slt (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1653⟩ : UInt256), UInt8.ofNat 18, .SLT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 1410) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1654⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1410), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.jumpiNT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1657⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1658)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_1646_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (UInt256.ofNat 0)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1646) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1658) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_1646_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `cometWithExtendedAssetList_block_1658`. -/
def cometWithExtendedAssetList_block_1658_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 1678) :: (UInt256.ofNat 1738) :: (UInt256.ofNat 1000000000000000) :: (UInt256.ofNat 32) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1658. -/
theorem cometWithExtendedAssetList_block_1658 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 7614) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1658) R mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 7614) (cometWithExtendedAssetList_block_1658_stack (R := R)) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1658⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 1000000000000000) (width := 7) (op := .PUSH7) (by decide) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1660⟩ : UInt256), UInt8.ofNat 102, .Push .PUSH7, some ((UInt256.ofNat 1000000000000000), 7), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 1738) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1668⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1738), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1678) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1671⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1678), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 7614) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1674⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 7614), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.jump (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1677⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7614)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_1658_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 7614) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1658) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 7614) (cometWithExtendedAssetList_block_1658_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_1658 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `cometWithExtendedAssetList_block_1678`. -/
def cometWithExtendedAssetList_block_1678_stack {ee : ExecutionEnv} {σ : AccountMap} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (UInt256.land (UInt256.shiftRight (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 1) (⟨0⟩ : UInt256))) (UInt256.ofNat 208)) (UInt256.ofNat 1099511627775)) :: (UInt256.ofNat 1707) :: (UInt256.ofNat 1099511627775) :: (UInt256.ofNat 1713) :: (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 1) (⟨0⟩ : UInt256))) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1678. -/
theorem cometWithExtendedAssetList_block_1678 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 7753) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1678) (x0 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 7753) (cometWithExtendedAssetList_block_1678_stack (ee := ee) (σ := σ) (x0 := x0) (R := R)) mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1678⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 1713) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1679⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1713), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1682⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r4⟩ := RD.sload r3 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1684⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.swap2 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1685⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 1707) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1686⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1707), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.pushConst (UInt256.ofNat 1099511627775) (width := 5) (op := .PUSH5) (by decide) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1689⟩ : UInt256), UInt8.ofNat 100, .Push .PUSH5, some ((UInt256.ofNat 1099511627775), 5), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.swap2 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1695⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.dup3 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1696⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.dup6 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1697⟩ : UInt256), UInt8.ofNat 133, .DUP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 208) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1698⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 208), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.shr (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1700⟩ : UInt256), UInt8.ofNat 28, .SHR, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.and (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1701⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.swap1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1702⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.push2 (UInt256.ofNat 7753) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1703⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 7753), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.jump (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1706⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7753)) r16 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_1678_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 7753) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1678) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 7753) (cometWithExtendedAssetList_block_1678_stack (ee := ee) (σ := σ) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := cometWithExtendedAssetList_block_1678 hstack hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `cometWithExtendedAssetList_block_1707`. -/
def cometWithExtendedAssetList_block_1707_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.land x0 x1) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1707. -/
theorem cometWithExtendedAssetList_block_1707 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 8445) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1707) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 8445) (cometWithExtendedAssetList_block_1707_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 4) (C + ((15))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1707⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.and (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1708⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 8445) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1709⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 8445), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.jump (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1712⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8445)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_1707_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 8445) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1707) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 8445) (cometWithExtendedAssetList_block_1707_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_1707 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `cometWithExtendedAssetList_block_1713`. -/
def cometWithExtendedAssetList_block_1713_stack {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 104)) (UInt256.ofNat 1)) x2) :: (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1)) x1) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1713. -/
theorem cometWithExtendedAssetList_block_1713 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 7799) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1713) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 7799) (cometWithExtendedAssetList_block_1713_stack (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 17) (C + ((53))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1713⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pop (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1714⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1715⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1717⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1719⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.shl (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1721⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.sub (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1722⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.and (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1723⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.swap1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1724⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1725⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1727⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 104) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1729⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 104), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.shl (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1731⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.sub (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1732⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.and (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1733⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.push2 (UInt256.ofNat 7799) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1734⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 7799), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.jump (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1737⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7799)) r17 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_1713_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 7799) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1713) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 7799) (cometWithExtendedAssetList_block_1713_stack (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_1713 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1738. -/
theorem cometWithExtendedAssetList_block_1738 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1738) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RDret (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) g s0 σ (((UInt256.div x0 x1).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32).readWithPadding (memLoad (UInt256.ofNat 64) mem).toNat x2.toNat) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1738⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.div (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1739⟩ : UInt256), UInt8.ofNat 4, .DIV, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1740⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := RD.genMload r3 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1742⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.swap1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1743⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.dup2 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1744⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := RD.genMstore r6 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1745⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact RD.genRet r7 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1746⟩ : UInt256), UInt8.ofNat 243, .RETURN, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

/-- Final stack for bytecode block summary `cometWithExtendedAssetList_block_1747_taken`. -/
def cometWithExtendedAssetList_block_1747_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 1747. -/
theorem cometWithExtendedAssetList_block_1747_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 1410) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1747) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1410) (cometWithExtendedAssetList_block_1747_taken_stack (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1747⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pop (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1748⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.callvalue (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1749⟩ : UInt256), UInt8.ofNat 52, .CALLVALUE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1410) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1750⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1410), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1753⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1410)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_1747_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 1410) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1747) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1410) (cometWithExtendedAssetList_block_1747_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_1747_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `cometWithExtendedAssetList_block_1747_fallthrough`. -/
def cometWithExtendedAssetList_block_1747_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 1747. -/
theorem cometWithExtendedAssetList_block_1747_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1747) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1754) (cometWithExtendedAssetList_block_1747_fallthrough_stack (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1747⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pop (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1748⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.callvalue (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1749⟩ : UInt256), UInt8.ofNat 52, .CALLVALUE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1410) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1750⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1410), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiNT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1753⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1754)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_1747_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1747) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1754) (cometWithExtendedAssetList_block_1747_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_1747_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1754. -/
theorem cometWithExtendedAssetList_block_1754_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (UInt256.ofNat 0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 1410) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1754) R mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1410) R mem aw rdata σ (k + 8) (C + ((30))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1754⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.calldatasize (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1756⟩ : UInt256), UInt8.ofNat 54, .CALLDATASIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 3) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1757⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 3), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.not (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1759⟩ : UInt256), UInt8.ofNat 25, .NOT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.add (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1760⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.slt (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1761⟩ : UInt256), UInt8.ofNat 18, .SLT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 1410) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1762⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1410), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.jumpiT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1765⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1410)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_1754_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (UInt256.ofNat 0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 1410) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1754) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1410) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_1754_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1754. -/
theorem cometWithExtendedAssetList_block_1754_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (UInt256.ofNat 0)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1754) R mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1766) R mem aw rdata σ (k + 8) (C + ((30))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1754⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.calldatasize (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1756⟩ : UInt256), UInt8.ofNat 54, .CALLDATASIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 3) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1757⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 3), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.not (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1759⟩ : UInt256), UInt8.ofNat 25, .NOT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.add (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1760⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.slt (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1761⟩ : UInt256), UInt8.ofNat 18, .SLT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 1410) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1762⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1410), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.jumpiNT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1765⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1766)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_1754_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (UInt256.ofNat 0)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1754) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1766) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_1754_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1766. -/
theorem cometWithExtendedAssetList_block_1766 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1766) R mem aw rdata σ k C)
    : RDret (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) g s0 σ (((immWords "baseTrackingSupplySpeed").toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32).readWithPadding (memLoad (UInt256.ofNat 64) mem).toNat (UInt256.ofNat 32).toNat) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1766⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1768⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := RD.genMload r2 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1770⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.pushConst (immWords "baseTrackingSupplySpeed") (width := 32) (op := .PUSH32) (by decide) (by
    conv_lhs => arg 2; change (⟨1771⟩ : UInt256)
    exact immutableDecode_1771 immWords) (by evm_ov)
  have r5 := r4.dup2 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1804⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := RD.genMstore r5 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1805⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact RD.genRet r6 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1806⟩ : UInt256), UInt8.ofNat 243, .RETURN, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

/-- Final stack for bytecode block summary `cometWithExtendedAssetList_block_1807_taken`. -/
def cometWithExtendedAssetList_block_1807_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 1807. -/
theorem cometWithExtendedAssetList_block_1807_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 1410) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1807) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1410) (cometWithExtendedAssetList_block_1807_taken_stack (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1807⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pop (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1808⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.callvalue (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1809⟩ : UInt256), UInt8.ofNat 52, .CALLVALUE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1410) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1810⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1410), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1813⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1410)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_1807_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 1410) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1807) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1410) (cometWithExtendedAssetList_block_1807_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_1807_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `cometWithExtendedAssetList_block_1807_fallthrough`. -/
def cometWithExtendedAssetList_block_1807_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 1807. -/
theorem cometWithExtendedAssetList_block_1807_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1807) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1814) (cometWithExtendedAssetList_block_1807_fallthrough_stack (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1807⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pop (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1808⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.callvalue (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1809⟩ : UInt256), UInt8.ofNat 52, .CALLVALUE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1410) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1810⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1410), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiNT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1813⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1814)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_1807_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1807) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1814) (cometWithExtendedAssetList_block_1807_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_1807_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `cometWithExtendedAssetList_block_1814_taken`. -/
def cometWithExtendedAssetList_block_1814_taken_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1814. -/
theorem cometWithExtendedAssetList_block_1814_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.ofNat ee.calldata.size) + (UInt256.lnot (UInt256.ofNat 3))) (UInt256.ofNat 0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 1938) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1814) R mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1938) (cometWithExtendedAssetList_block_1814_taken_stack (R := R)) mem aw rdata σ (k + 9) (C + ((33))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1814⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1816⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 3) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1817⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 3), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.not (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1819⟩ : UInt256), UInt8.ofNat 25, .NOT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.calldatasize (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1820⟩ : UInt256), UInt8.ofNat 54, .CALLDATASIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.add (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1821⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.slt (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1822⟩ : UInt256), UInt8.ofNat 18, .SLT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 1938) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1823⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1938), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.jumpiT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1826⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1938)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_1814_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.ofNat ee.calldata.size) + (UInt256.lnot (UInt256.ofNat 3))) (UInt256.ofNat 0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 1938) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1814) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1938) (cometWithExtendedAssetList_block_1814_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_1814_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `cometWithExtendedAssetList_block_1814_fallthrough`. -/
def cometWithExtendedAssetList_block_1814_fallthrough_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1814. -/
theorem cometWithExtendedAssetList_block_1814_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.ofNat ee.calldata.size) + (UInt256.lnot (UInt256.ofNat 3))) (UInt256.ofNat 0)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1814) R mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1827) (cometWithExtendedAssetList_block_1814_fallthrough_stack (R := R)) mem aw rdata σ (k + 9) (C + ((33))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1814⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1816⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 3) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1817⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 3), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.not (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1819⟩ : UInt256), UInt8.ofNat 25, .NOT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.calldatasize (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1820⟩ : UInt256), UInt8.ofNat 54, .CALLDATASIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.add (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1821⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.slt (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1822⟩ : UInt256), UInt8.ofNat 18, .SLT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 1938) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1823⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1938), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.jumpiNT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1826⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1827)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_1814_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.ofNat ee.calldata.size) + (UInt256.lnot (UInt256.ofNat 3))) (UInt256.ofNat 0)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1814) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1827) (cometWithExtendedAssetList_block_1814_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_1814_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `cometWithExtendedAssetList_block_1827_taken`. -/
def cometWithExtendedAssetList_block_1827_taken_stack {ee : ExecutionEnv} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 1) (⟨0⟩ : UInt256))) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1827. -/
theorem cometWithExtendedAssetList_block_1827_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.land (UInt256.shiftRight (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 1) (⟨0⟩ : UInt256))) (UInt256.ofNat 208)) (UInt256.ofNat 1099511627775)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 1921) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1827) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1921) (cometWithExtendedAssetList_block_1827_taken_stack (ee := ee) (σ := σ) (R := R)) mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1827⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r2⟩ := RD.sload r1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1829⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 1099511627775) (width := 5) (op := .PUSH5) (by decide) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1830⟩ : UInt256), UInt8.ofNat 100, .Push .PUSH5, some ((UInt256.ofNat 1099511627775), 5), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup2 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1836⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 208) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1837⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 208), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.shr (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1839⟩ : UInt256), UInt8.ofNat 28, .SHR, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.and (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1840⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 1921) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1841⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1921), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.jumpiT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1844⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1921)) r9 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_1827_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.land (UInt256.shiftRight (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 1) (⟨0⟩ : UInt256))) (UInt256.ofNat 208)) (UInt256.ofNat 1099511627775)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 1921) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1827) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1921) (cometWithExtendedAssetList_block_1827_taken_stack (ee := ee) (σ := σ) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := cometWithExtendedAssetList_block_1827_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `cometWithExtendedAssetList_block_1827_fallthrough`. -/
def cometWithExtendedAssetList_block_1827_fallthrough_stack {ee : ExecutionEnv} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 1) (⟨0⟩ : UInt256))) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1827. -/
theorem cometWithExtendedAssetList_block_1827_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.land (UInt256.shiftRight (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 1) (⟨0⟩ : UInt256))) (UInt256.ofNat 208)) (UInt256.ofNat 1099511627775)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1827) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1845) (cometWithExtendedAssetList_block_1827_fallthrough_stack (ee := ee) (σ := σ) (R := R)) mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1827⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r2⟩ := RD.sload r1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1829⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 1099511627775) (width := 5) (op := .PUSH5) (by decide) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1830⟩ : UInt256), UInt8.ofNat 100, .Push .PUSH5, some ((UInt256.ofNat 1099511627775), 5), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup2 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1836⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 208) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1837⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 208), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.shr (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1839⟩ : UInt256), UInt8.ofNat 28, .SHR, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.and (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1840⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 1921) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1841⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1921), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.jumpiNT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1844⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1845)) r9 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_1827_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.land (UInt256.shiftRight (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 1) (⟨0⟩ : UInt256))) (UInt256.ofNat 208)) (UInt256.ofNat 1099511627775)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1827) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1845) (cometWithExtendedAssetList_block_1827_fallthrough_stack (ee := ee) (σ := σ) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := cometWithExtendedAssetList_block_1827_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

end cometWithExtendedAssetListBlocks
