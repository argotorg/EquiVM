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

/-- Automatically generated RD summary for bytecode block at pc 559. -/
theorem cometWithExtendedAssetList_block_559_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 2835717307) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 952) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 559) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 952) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨559⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 2835717307) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨560⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 2835717307), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨565⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 952) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨566⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 952), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨569⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 952)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_559_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 2835717307) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 952) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 559) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 952) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_559_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 559. -/
theorem cometWithExtendedAssetList_block_559_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 2835717307) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 559) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 570) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨559⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 2835717307) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨560⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 2835717307), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨565⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 952) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨566⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 952), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiNT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨569⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 570)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_559_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 2835717307) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 559) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 570) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_559_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 570. -/
theorem cometWithExtendedAssetList_block_570_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 2879910238) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 943) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 570) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 943) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨570⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 2879910238) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨571⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 2879910238), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨576⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 943) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨577⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 943), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨580⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 943)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_570_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 2879910238) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 943) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 570) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 943) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_570_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 570. -/
theorem cometWithExtendedAssetList_block_570_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 2879910238) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 570) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 581) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨570⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 2879910238) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨571⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 2879910238), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨576⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 943) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨577⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 943), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiNT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨580⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 581)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_570_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 2879910238) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 570) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 581) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_570_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 581. -/
theorem cometWithExtendedAssetList_block_581_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 2903799676) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 934) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 581) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 934) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨581⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 2903799676) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨582⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 2903799676), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨587⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 934) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨588⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 934), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨591⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 934)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_581_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 2903799676) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 934) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 581) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 934) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_581_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 581. -/
theorem cometWithExtendedAssetList_block_581_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 2903799676) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 581) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 592) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨581⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 2903799676) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨582⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 2903799676), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨587⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 934) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨588⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 934), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiNT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨591⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 592)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_581_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 2903799676) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 581) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 592) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_581_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 592. -/
theorem cometWithExtendedAssetList_block_592_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 3219561613) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 925) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 592) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 925) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨592⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 3219561613) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨593⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 3219561613), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨598⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 925) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨599⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 925), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨602⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 925)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_592_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 3219561613) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 925) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 592) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 925) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_592_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 592. -/
theorem cometWithExtendedAssetList_block_592_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 3219561613) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 592) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 603) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨592⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 3219561613) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨593⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 3219561613), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨598⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 925) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨599⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 925), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiNT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨602⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 603)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_592_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 3219561613) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 592) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 603) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_592_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 603. -/
theorem cometWithExtendedAssetList_block_603_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 3253611544) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 916) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 603) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 916) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨603⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 3253611544) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨604⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 3253611544), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨609⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 916) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨610⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 916), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨613⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 916)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_603_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 3253611544) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 916) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 603) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 916) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_603_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 603. -/
theorem cometWithExtendedAssetList_block_603_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 3253611544) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 603) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 614) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨603⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 3253611544) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨604⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 3253611544), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨609⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 916) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨610⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 916), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiNT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨613⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 614)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_603_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 3253611544) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 603) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 614) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_603_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 614. -/
theorem cometWithExtendedAssetList_block_614_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 3283311230) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 907) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 614) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 907) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨614⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 3283311230) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨615⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 3283311230), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨620⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 907) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨621⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 907), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨624⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 907)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_614_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 3283311230) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 907) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 614) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 907) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_614_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 614. -/
theorem cometWithExtendedAssetList_block_614_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 3283311230) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 614) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 625) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨614⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 3283311230) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨615⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 3283311230), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨620⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 907) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨621⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 907), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiNT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨624⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 625)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_614_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 3283311230) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 614) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 625) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_614_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 625. -/
theorem cometWithExtendedAssetList_block_625_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 3285110738) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 898) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 625) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 898) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨625⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 3285110738) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨626⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 3285110738), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨631⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 898) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨632⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 898), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨635⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 898)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_625_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 3285110738) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 898) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 625) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 898) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_625_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 625. -/
theorem cometWithExtendedAssetList_block_625_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 3285110738) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 625) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 636) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨625⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 3285110738) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨626⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 3285110738), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨631⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 898) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨632⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 898), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiNT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨635⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 636)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_625_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 3285110738) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 625) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 636) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_625_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 636. -/
theorem cometWithExtendedAssetList_block_636_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 3311251043) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 889) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 636) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 889) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨636⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 3311251043) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨637⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 3311251043), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨642⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 889) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨643⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 889), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨646⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 889)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_636_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 3311251043) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 889) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 636) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 889) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_636_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 636. -/
theorem cometWithExtendedAssetList_block_636_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 3311251043) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 636) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 647) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨636⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 3311251043) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨637⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 3311251043), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨642⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 889) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨643⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 889), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiNT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨646⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 647)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_636_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 3311251043) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 636) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 647) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_636_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 647. -/
theorem cometWithExtendedAssetList_block_647_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 3321501135) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 880) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 647) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 880) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨647⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 3321501135) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨648⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 3321501135), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨653⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 880) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨654⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 880), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨657⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 880)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_647_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 3321501135) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 880) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 647) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 880) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_647_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 647. -/
theorem cometWithExtendedAssetList_block_647_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 3321501135) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 647) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 658) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨647⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 3321501135) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨648⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 3321501135), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨653⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 880) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨654⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 880), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiNT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨657⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 658)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_647_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 3321501135) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 647) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 658) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_647_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 658. -/
theorem cometWithExtendedAssetList_block_658_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 3368549995) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 871) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 658) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 871) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨658⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 3368549995) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨659⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 3368549995), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨664⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 871) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨665⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 871), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨668⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 871)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_658_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 3368549995) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 871) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 658) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 871) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_658_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 658. -/
theorem cometWithExtendedAssetList_block_658_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 3368549995) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 658) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 669) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨658⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 3368549995) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨659⟩ : UInt256), UInt8.ofNat 99, .Push .PUSH4, some ((UInt256.ofNat 3368549995), 4), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.eq (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨664⟩ : UInt256), UInt8.ofNat 20, .EQ, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 871) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨665⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 871), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiNT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨668⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 669)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_658_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 3368549995) x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 658) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 669) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_658_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

end cometWithExtendedAssetListBlocks
