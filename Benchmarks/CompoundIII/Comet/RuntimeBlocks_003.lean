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

/-- Automatically generated RD summary for bytecode block at pc 229. -/
theorem cometWithExtendedAssetList_block_229_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 927746484) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 1222) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 229) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1222) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨229⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 927746484) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨230⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 927746484), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨235⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1222) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨236⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1222), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨239⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1222)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_229_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 927746484) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 1222) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 229) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1222) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_229_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 229. -/
theorem cometWithExtendedAssetList_block_229_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 927746484) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 229) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 240) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨229⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 927746484) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨230⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 927746484), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨235⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1222) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨236⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1222), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiNT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨239⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 240)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_229_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 927746484) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 229) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 240) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_229_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 240. -/
theorem cometWithExtendedAssetList_block_240_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 950698303) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 1213) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 240) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1213) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨240⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 950698303) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨241⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 950698303), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨246⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1213) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨247⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1213), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨250⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1213)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_240_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 950698303) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 1213) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 240) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1213) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_240_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 240. -/
theorem cometWithExtendedAssetList_block_240_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 950698303) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 240) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 251) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨240⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 950698303) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨241⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 950698303), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨246⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1213) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨247⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1213), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiNT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨250⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 251)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_240_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 950698303) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 240) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 251) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_240_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 251. -/
theorem cometWithExtendedAssetList_block_251_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 993782830) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 1204) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 251) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1204) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨251⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 993782830) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨252⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 993782830), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨257⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1204) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨258⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1204), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨261⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1204)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_251_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 993782830) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 1204) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 251) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1204) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_251_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 251. -/
theorem cometWithExtendedAssetList_block_251_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 993782830) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 251) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 262) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨251⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 993782830) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨252⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 993782830), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨257⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1204) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨258⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1204), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiNT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨261⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 262)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_251_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 993782830) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 251) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 262) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_251_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 262. -/
theorem cometWithExtendedAssetList_block_262_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1100443145) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 1195) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 262) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1195) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨262⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 1100443145) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨263⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 1100443145), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨268⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1195) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨269⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1195), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨272⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1195)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_262_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1100443145) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 1195) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 262) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1195) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_262_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 262. -/
theorem cometWithExtendedAssetList_block_262_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1100443145) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 262) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 273) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨262⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 1100443145) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨263⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 1100443145), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨268⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1195) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨269⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1195), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiNT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨272⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 273)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_262_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1100443145) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 262) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 273) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_262_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 273. -/
theorem cometWithExtendedAssetList_block_273_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1110625635) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 1186) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 273) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1186) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨273⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 1110625635) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨274⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 1110625635), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨279⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1186) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨280⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1186), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨283⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1186)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_273_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1110625635) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 1186) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 273) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1186) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_273_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 273. -/
theorem cometWithExtendedAssetList_block_273_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1110625635) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 273) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 284) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨273⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 1110625635) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨274⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 1110625635), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨279⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1186) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨280⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1186), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiNT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨283⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 284)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_273_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1110625635) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 273) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 284) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_273_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 284. -/
theorem cometWithExtendedAssetList_block_284_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1134440005) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 1177) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 284) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1177) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨284⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 1134440005) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨285⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 1134440005), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨290⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1177) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨291⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1177), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨294⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1177)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_284_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1134440005) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 1177) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 284) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1177) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_284_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 284. -/
theorem cometWithExtendedAssetList_block_284_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1134440005) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 284) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 295) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨284⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 1134440005) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨285⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 1134440005), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨290⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1177) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨291⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1177), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiNT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨294⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 295)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_284_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1134440005) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 284) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 295) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_284_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 295. -/
theorem cometWithExtendedAssetList_block_295_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1153557995) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 1168) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 295) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1168) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨295⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 1153557995) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨296⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 1153557995), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨301⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1168) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨302⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1168), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨305⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1168)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_295_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1153557995) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 1168) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 295) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1168) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_295_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 295. -/
theorem cometWithExtendedAssetList_block_295_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1153557995) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 295) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 306) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨295⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 1153557995) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨296⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 1153557995), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨301⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1168) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨302⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1168), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiNT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨305⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 306)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_295_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1153557995) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 295) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 306) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_295_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 306. -/
theorem cometWithExtendedAssetList_block_306_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1153654023) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 1159) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 306) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1159) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨306⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 1153654023) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨307⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 1153654023), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨312⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1159) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨313⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1159), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨316⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1159)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_306_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1153654023) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 1159) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 306) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1159) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_306_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 306. -/
theorem cometWithExtendedAssetList_block_306_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1153654023) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 306) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 317) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨306⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 1153654023) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨307⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 1153654023), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨312⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1159) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨313⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1159), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiNT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨316⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 317)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_306_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1153654023) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 306) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 317) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_306_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 317. -/
theorem cometWithExtendedAssetList_block_317_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1157571613) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 1150) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 317) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1150) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨317⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 1157571613) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨318⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 1157571613), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨323⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1150) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨324⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1150), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨327⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1150)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_317_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1157571613) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 1150) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 317) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1150) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_317_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 317. -/
theorem cometWithExtendedAssetList_block_317_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1157571613) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 317) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 328) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨317⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 1157571613) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨318⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 1157571613), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨323⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1150) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨324⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1150), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiNT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨327⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 328)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_317_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1157571613) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 317) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 328) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_317_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 328. -/
theorem cometWithExtendedAssetList_block_328_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1507858365) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 1141) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 328) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1141) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨328⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 1507858365) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨329⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 1507858365), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨334⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1141) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨335⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1141), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨338⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1141)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_328_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1507858365) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 1141) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 328) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1141) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_328_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 328. -/
theorem cometWithExtendedAssetList_block_328_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1507858365) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 328) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 339) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨328⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 1507858365) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨329⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 1507858365), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨334⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1141) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨335⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1141), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiNT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨338⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 339)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_328_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1507858365) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 328) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 339) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_328_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

end cometWithExtendedAssetListBlocks
