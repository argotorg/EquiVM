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

/-- Automatically generated RD summary for bytecode block at pc 119. -/
theorem cometWithExtendedAssetList_block_119_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 599290589) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 1312) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 119) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1312) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨119⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 599290589) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨120⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 599290589), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨125⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1312) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨126⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1312), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨129⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1312)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_119_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 599290589) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 1312) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 119) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1312) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_119_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 119. -/
theorem cometWithExtendedAssetList_block_119_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 599290589) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 119) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 130) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨119⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 599290589) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨120⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 599290589), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨125⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1312) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨126⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1312), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiNT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨129⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 130)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_119_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 599290589) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 119) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 130) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_119_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 130. -/
theorem cometWithExtendedAssetList_block_130_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 614716962) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 1303) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 130) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1303) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨130⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 614716962) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨131⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 614716962), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨136⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1303) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨137⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1303), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨140⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1303)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_130_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 614716962) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 1303) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 130) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1303) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_130_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 130. -/
theorem cometWithExtendedAssetList_block_130_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 614716962) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 130) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 141) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨130⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 614716962) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨131⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 614716962), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨136⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1303) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨137⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1303), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiNT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨140⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 141)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_130_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 614716962) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 130) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 141) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_130_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 141. -/
theorem cometWithExtendedAssetList_block_141_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 641995544) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 1294) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 141) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1294) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨141⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 641995544) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨142⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 641995544), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨147⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1294) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨148⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1294), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨151⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1294)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_141_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 641995544) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 1294) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 141) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1294) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_141_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 141. -/
theorem cometWithExtendedAssetList_block_141_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 641995544) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 141) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 152) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨141⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 641995544) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨142⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 641995544), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨147⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1294) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨148⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1294), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiNT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨151⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 152)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_141_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 641995544) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 141) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 152) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_141_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 152. -/
theorem cometWithExtendedAssetList_block_152_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 709414674) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 1285) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 152) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1285) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨152⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 709414674) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨153⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 709414674), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨158⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1285) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨159⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1285), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨162⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1285)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_152_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 709414674) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 1285) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 152) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1285) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_152_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 152. -/
theorem cometWithExtendedAssetList_block_152_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 709414674) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 152) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 163) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨152⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 709414674) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨153⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 709414674), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨158⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1285) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨159⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1285), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiNT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨162⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 163)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_152_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 709414674) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 152) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 163) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_152_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 163. -/
theorem cometWithExtendedAssetList_block_163_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 731029629) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 1276) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 163) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1276) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨163⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 731029629) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨164⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 731029629), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨169⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1276) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨170⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1276), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨173⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1276)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_163_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 731029629) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 1276) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 163) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1276) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_163_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 163. -/
theorem cometWithExtendedAssetList_block_163_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 731029629) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 163) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 174) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨163⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 731029629) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨164⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 731029629), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨169⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1276) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨170⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1276), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiNT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨173⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 174)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_163_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 731029629) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 163) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 174) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_163_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 174. -/
theorem cometWithExtendedAssetList_block_174_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 755328779) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 1267) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 174) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1267) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨174⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 755328779) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨175⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 755328779), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨180⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1267) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨181⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1267), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨184⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1267)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_174_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 755328779) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 1267) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 174) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1267) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_174_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 174. -/
theorem cometWithExtendedAssetList_block_174_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 755328779) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 174) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 185) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨174⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 755328779) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨175⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 755328779), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨180⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1267) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨181⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1267), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiNT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨184⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 185)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_174_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 755328779) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 174) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 185) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_174_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 185. -/
theorem cometWithExtendedAssetList_block_185_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 772061415) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 1258) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 185) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1258) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨185⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 772061415) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨186⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 772061415), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨191⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1258) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨192⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1258), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨195⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1258)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_185_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 772061415) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 1258) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 185) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1258) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_185_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 185. -/
theorem cometWithExtendedAssetList_block_185_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 772061415) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 185) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 196) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨185⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 772061415) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨186⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 772061415), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨191⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1258) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨192⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1258), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiNT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨195⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 196)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_185_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 772061415) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 185) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 196) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_185_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 196. -/
theorem cometWithExtendedAssetList_block_196_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 806251499) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 1249) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 196) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1249) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨196⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 806251499) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨197⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 806251499), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨202⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1249) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨203⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1249), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨206⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1249)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_196_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 806251499) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 1249) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 196) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1249) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_196_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 196. -/
theorem cometWithExtendedAssetList_block_196_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 806251499) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 196) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 207) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨196⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 806251499) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨197⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 806251499), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨202⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1249) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨203⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1249), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiNT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨206⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 207)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_196_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 806251499) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 196) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 207) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_196_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 207. -/
theorem cometWithExtendedAssetList_block_207_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 826074471) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 1240) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 207) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1240) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨207⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 826074471) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨208⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 826074471), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨213⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1240) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨214⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1240), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨217⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1240)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_207_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 826074471) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 1240) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 207) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1240) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_207_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 207. -/
theorem cometWithExtendedAssetList_block_207_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 826074471) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 207) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 218) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨207⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 826074471) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨208⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 826074471), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨213⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1240) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨214⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1240), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiNT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨217⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 218)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_207_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 826074471) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 207) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 218) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_207_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 218. -/
theorem cometWithExtendedAssetList_block_218_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 840395849) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 1231) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 218) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1231) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨218⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 840395849) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨219⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 840395849), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨224⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1231) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨225⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1231), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨228⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1231)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_218_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 840395849) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 1231) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 218) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1231) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_218_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 218. -/
theorem cometWithExtendedAssetList_block_218_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 840395849) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 218) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 229) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨218⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 840395849) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨219⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 840395849), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨224⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1231) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨225⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1231), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiNT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨228⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 229)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_218_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 840395849) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 218) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 229) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_218_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

end cometWithExtendedAssetListBlocks
