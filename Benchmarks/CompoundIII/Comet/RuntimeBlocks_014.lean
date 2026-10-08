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

theorem immutableDecode_1965 (immWords : String → UInt256) :
    decode (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) (⟨1965⟩ : UInt256) =
      some (.Push .PUSH32, some (immWords "storeFrontPriceFactor", 32)) := by
  exact Layout.decodeSite (pc := (⟨1965⟩ : UInt256)) (words := immWords)
    1966 "storeFrontPriceFactor" [(1592, immWords "governor"), (3441, immWords "governor"), (5137, immWords "governor"), (6161, immWords "governor"), (2168, immWords "pauseGuardian"), (3703, immWords "pauseGuardian"), (2078, immWords "baseToken"), (5008, immWords "baseToken"), (5625, immWords "baseToken"), (6266, immWords "baseToken"), (6450, immWords "baseToken"), (9907, immWords "baseToken"), (12117, immWords "baseToken"), (12429, immWords "baseToken"), (14552, immWords "baseToken"), (15644, immWords "baseToken"), (15869, immWords "baseToken"), (6768, immWords "baseTokenPriceFeed"), (10264, immWords "baseTokenPriceFeed"), (17068, immWords "baseTokenPriceFeed"), (18119, immWords "baseTokenPriceFeed"), (3767, immWords "extensionDelegate"), (18431, immWords "extensionDelegate"), (4926, immWords "supplyKink"), (8616, immWords "supplyKink"), (3925, immWords "supplyPerSecondInterestRateSlopeLow"), (8676, immWords "supplyPerSecondInterestRateSlopeLow"), (8782, immWords "supplyPerSecondInterestRateSlopeLow"), (4196, immWords "supplyPerSecondInterestRateSlopeHigh"), (8830, immWords "supplyPerSecondInterestRateSlopeHigh"), (4550, immWords "supplyPerSecondInterestRateBase"), (8715, immWords "supplyPerSecondInterestRateBase"), (4430, immWords "borrowKink"), (8888, immWords "borrowKink"), (2599, immWords "borrowPerSecondInterestRateSlopeLow"), (8948, immWords "borrowPerSecondInterestRateSlopeLow"), (9054, immWords "borrowPerSecondInterestRateSlopeLow"), (2353, immWords "borrowPerSecondInterestRateSlopeHigh"), (9102, immWords "borrowPerSecondInterestRateSlopeHigh"), (4064, immWords "borrowPerSecondInterestRateBase"), (8987, immWords "borrowPerSecondInterestRateBase")] [(18059, immWords "storeFrontPriceFactor"), (3313, immWords "baseScale"), (10302, immWords "baseScale"), (11157, immWords "baseScale"), (17180, immWords "baseScale"), (18175, immWords "baseScale"), (5072, immWords "trackingIndexScale"), (11824, immWords "trackingIndexScale"), (1772, immWords "baseTrackingSupplySpeed"), (8308, immWords "baseTrackingSupplySpeed"), (4610, immWords "baseTrackingBorrowSpeed"), (8188, immWords "baseTrackingBorrowSpeed"), (4490, immWords "baseMinForRewards"), (8046, immWords "baseMinForRewards"), (2721, immWords "baseBorrowMin"), (15134, immWords "baseBorrowMin"), (16028, immWords "baseBorrowMin"), (2844, immWords "targetReserves"), (6688, immWords "targetReserves"), (2783, immWords "decimals"), (4865, immWords "numAssets"), (7501, immWords "numAssets"), (10357, immWords "numAssets"), (10878, immWords "numAssets"), (17114, immWords "numAssets"), (11863, immWords "accrualDescaleFactor"), (6070, immWords "assetList"), (7222, immWords "assetList")]
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

theorem immutableDecode_2077 (immWords : String → UInt256) :
    decode (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) (⟨2077⟩ : UInt256) =
      some (.Push .PUSH32, some (immWords "baseToken", 32)) := by
  exact Layout.decodeSite (pc := (⟨2077⟩ : UInt256)) (words := immWords)
    2078 "baseToken" [(1592, immWords "governor"), (3441, immWords "governor"), (5137, immWords "governor"), (6161, immWords "governor"), (2168, immWords "pauseGuardian"), (3703, immWords "pauseGuardian")] [(5008, immWords "baseToken"), (5625, immWords "baseToken"), (6266, immWords "baseToken"), (6450, immWords "baseToken"), (9907, immWords "baseToken"), (12117, immWords "baseToken"), (12429, immWords "baseToken"), (14552, immWords "baseToken"), (15644, immWords "baseToken"), (15869, immWords "baseToken"), (6768, immWords "baseTokenPriceFeed"), (10264, immWords "baseTokenPriceFeed"), (17068, immWords "baseTokenPriceFeed"), (18119, immWords "baseTokenPriceFeed"), (3767, immWords "extensionDelegate"), (18431, immWords "extensionDelegate"), (4926, immWords "supplyKink"), (8616, immWords "supplyKink"), (3925, immWords "supplyPerSecondInterestRateSlopeLow"), (8676, immWords "supplyPerSecondInterestRateSlopeLow"), (8782, immWords "supplyPerSecondInterestRateSlopeLow"), (4196, immWords "supplyPerSecondInterestRateSlopeHigh"), (8830, immWords "supplyPerSecondInterestRateSlopeHigh"), (4550, immWords "supplyPerSecondInterestRateBase"), (8715, immWords "supplyPerSecondInterestRateBase"), (4430, immWords "borrowKink"), (8888, immWords "borrowKink"), (2599, immWords "borrowPerSecondInterestRateSlopeLow"), (8948, immWords "borrowPerSecondInterestRateSlopeLow"), (9054, immWords "borrowPerSecondInterestRateSlopeLow"), (2353, immWords "borrowPerSecondInterestRateSlopeHigh"), (9102, immWords "borrowPerSecondInterestRateSlopeHigh"), (4064, immWords "borrowPerSecondInterestRateBase"), (8987, immWords "borrowPerSecondInterestRateBase"), (1966, immWords "storeFrontPriceFactor"), (18059, immWords "storeFrontPriceFactor"), (3313, immWords "baseScale"), (10302, immWords "baseScale"), (11157, immWords "baseScale"), (17180, immWords "baseScale"), (18175, immWords "baseScale"), (5072, immWords "trackingIndexScale"), (11824, immWords "trackingIndexScale"), (1772, immWords "baseTrackingSupplySpeed"), (8308, immWords "baseTrackingSupplySpeed"), (4610, immWords "baseTrackingBorrowSpeed"), (8188, immWords "baseTrackingBorrowSpeed"), (4490, immWords "baseMinForRewards"), (8046, immWords "baseMinForRewards"), (2721, immWords "baseBorrowMin"), (15134, immWords "baseBorrowMin"), (16028, immWords "baseBorrowMin"), (2844, immWords "targetReserves"), (6688, immWords "targetReserves"), (2783, immWords "decimals"), (4865, immWords "numAssets"), (7501, immWords "numAssets"), (10357, immWords "numAssets"), (10878, immWords "numAssets"), (17114, immWords "numAssets"), (11863, immWords "accrualDescaleFactor"), (6070, immWords "assetList"), (7222, immWords "assetList")]
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

/-- Final stack for bytecode block summary `cometWithExtendedAssetList_block_1845`. -/
def cometWithExtendedAssetList_block_1845_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 1861) :: (UInt256.shiftLeft (UInt256.ofNat 1099511627775) (UInt256.ofNat 208)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1845. -/
theorem cometWithExtendedAssetList_block_1845 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 7614) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1845) R mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 7614) (cometWithExtendedAssetList_block_1845_stack (R := R)) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.pushConst (UInt256.ofNat 1099511627775) (width := 5) (op := .PUSH5) (by decide) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1845⟩ : UInt256), UInt8.ofNat 100, .Push .PUSH5, some ((UInt256.ofNat 1099511627775), 5), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 208) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1851⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 208), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.shl (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1853⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1861) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1854⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1861), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 7614) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1857⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 7614), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.jump (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1860⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7614)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_1845_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 7614) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1845) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 7614) (cometWithExtendedAssetList_block_1845_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_1845 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1861. -/
theorem cometWithExtendedAssetList_block_1861 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1861) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RDret (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) g s0 (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 1) (UInt256.lor (UInt256.land (UInt256.shiftLeft x0 (UInt256.ofNat 208)) x1) (UInt256.land x2 (UInt256.lnot (UInt256.shiftLeft (UInt256.ofNat 1099511627775) (UInt256.ofNat 208)))))) x3 (UInt256.lor (UInt256.ofNat 18446744073709551617000000000000000) (UInt256.land (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))) ((sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 1) (UInt256.lor (UInt256.land (UInt256.shiftLeft x0 (UInt256.ofNat 208)) x1) (UInt256.land x2 (UInt256.lnot (UInt256.shiftLeft (UInt256.ofNat 1099511627775) (UInt256.ofNat 208)))))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x3 (⟨0⟩ : UInt256)))))) (mem.readWithPadding (memLoad (UInt256.ofNat 64) mem).toNat x3.toNat) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1861⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 1099511627775) (width := 5) (op := .PUSH5) (by decide) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1862⟩ : UInt256), UInt8.ofNat 100, .Push .PUSH5, some ((UInt256.ofNat 1099511627775), 5), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 208) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1868⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 208), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.shl (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1870⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.not (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1871⟩ : UInt256), UInt8.ofNat 25, .NOT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.swap1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1872⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.swap3 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1873⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.and (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1874⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 208) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1875⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 208), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.swap3 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1877⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.swap1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1878⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.swap3 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1879⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.shl (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1880⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.and (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1881⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.or (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1882⟩ : UInt256), UInt8.ofNat 23, .OR, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1883⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r17⟩ := RD.sstore r16 hperm (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1885⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.dup1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1886⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r19⟩ := RD.sload r18 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1887⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1888⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1890⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 128) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1892⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 128), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.shl (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1894⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r24 := r23.sub (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1895⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r25 := r24.not (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1896⟩ : UInt256), UInt8.ofNat 25, .NOT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r26 := r25.and (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1897⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r27 := r26.pushConst (UInt256.ofNat 18446744073709551617000000000000000) (width := 15) (op := .PUSH15) (by decide) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1898⟩ : UInt256), UInt8.ofNat 110, .Push .PUSH15, some ((UInt256.ofNat 18446744073709551617000000000000000), 15), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r28 := r27.or (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1914⟩ : UInt256), UInt8.ofNat 23, .OR, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r29 := r28.dup2 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1915⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r30⟩ := RD.sstore r29 hperm (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1916⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r31 := r30.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1917⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r32 := RD.genMload r31 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1919⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact RD.genRet r32 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1920⟩ : UInt256), UInt8.ofNat 243, .RETURN, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 1921. -/
theorem cometWithExtendedAssetList_block_1921 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1921) R mem aw rdata σ k C)
    : RDrev (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1921⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1922⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := RD.genMload r2 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1924⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.pushConst (UInt256.ofNat 14423199) (width := 3) (op := .PUSH3) (by decide) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1925⟩ : UInt256), UInt8.ofNat 98, .Push .PUSH3, some ((UInt256.ofNat 14423199), 3), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 228) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1929⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 228), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.shl (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1931⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.dup2 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1932⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := RD.genMstore r7 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1933⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 4) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1934⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 4), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.swap1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1936⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact RD.genRev r10 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1937⟩ : UInt256), UInt8.ofNat 253, .REVERT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 1938. -/
theorem cometWithExtendedAssetList_block_1938 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1938) (x0 :: R) mem aw rdata σ k C)
    : RDrev (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1938⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1939⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact RD.genRev r2 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1940⟩ : UInt256), UInt8.ofNat 253, .REVERT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

/-- Final stack for bytecode block summary `cometWithExtendedAssetList_block_1941_taken`. -/
def cometWithExtendedAssetList_block_1941_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 1941. -/
theorem cometWithExtendedAssetList_block_1941_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 1410) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1941) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1410) (cometWithExtendedAssetList_block_1941_taken_stack (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1941⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pop (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1942⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.callvalue (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1943⟩ : UInt256), UInt8.ofNat 52, .CALLVALUE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1410) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1944⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1410), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1947⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1410)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_1941_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 1410) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1941) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1410) (cometWithExtendedAssetList_block_1941_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_1941_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `cometWithExtendedAssetList_block_1941_fallthrough`. -/
def cometWithExtendedAssetList_block_1941_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 1941. -/
theorem cometWithExtendedAssetList_block_1941_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1941) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1948) (cometWithExtendedAssetList_block_1941_fallthrough_stack (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1941⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pop (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1942⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.callvalue (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1943⟩ : UInt256), UInt8.ofNat 52, .CALLVALUE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1410) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1944⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1410), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiNT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1947⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1948)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_1941_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1941) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1948) (cometWithExtendedAssetList_block_1941_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_1941_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1948. -/
theorem cometWithExtendedAssetList_block_1948_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (UInt256.ofNat 0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 1410) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1948) R mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1410) R mem aw rdata σ (k + 8) (C + ((30))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1948⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.calldatasize (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1950⟩ : UInt256), UInt8.ofNat 54, .CALLDATASIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 3) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1951⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 3), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.not (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1953⟩ : UInt256), UInt8.ofNat 25, .NOT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.add (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1954⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.slt (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1955⟩ : UInt256), UInt8.ofNat 18, .SLT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 1410) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1956⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1410), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.jumpiT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1959⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1410)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_1948_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (UInt256.ofNat 0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 1410) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1948) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1410) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_1948_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1948. -/
theorem cometWithExtendedAssetList_block_1948_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (UInt256.ofNat 0)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1948) R mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1960) R mem aw rdata σ (k + 8) (C + ((30))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1948⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.calldatasize (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1950⟩ : UInt256), UInt8.ofNat 54, .CALLDATASIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 3) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1951⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 3), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.not (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1953⟩ : UInt256), UInt8.ofNat 25, .NOT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.add (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1954⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.slt (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1955⟩ : UInt256), UInt8.ofNat 18, .SLT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 1410) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1956⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1410), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.jumpiNT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1959⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1960)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_1948_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (UInt256.ofNat 0)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1948) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1960) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_1948_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1960. -/
theorem cometWithExtendedAssetList_block_1960 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1960) R mem aw rdata σ k C)
    : RDret (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) g s0 σ (((immWords "storeFrontPriceFactor").toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32).readWithPadding (memLoad (UInt256.ofNat 64) mem).toNat (UInt256.ofNat 32).toNat) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1960⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1962⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := RD.genMload r2 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1964⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.pushConst (immWords "storeFrontPriceFactor") (width := 32) (op := .PUSH32) (by decide) (by
    conv_lhs => arg 2; change (⟨1965⟩ : UInt256)
    exact immutableDecode_1965 immWords) (by evm_ov)
  have r5 := r4.dup2 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1998⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := RD.genMstore r5 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨1999⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact RD.genRet r6 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2000⟩ : UInt256), UInt8.ofNat 243, .RETURN, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

/-- Final stack for bytecode block summary `cometWithExtendedAssetList_block_2001_taken`. -/
def cometWithExtendedAssetList_block_2001_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 2001. -/
theorem cometWithExtendedAssetList_block_2001_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 96)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 1410) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 2001) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1410) (cometWithExtendedAssetList_block_2001_taken_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 9) (C + ((32))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2001⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2002⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup2 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2003⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 96) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2004⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 96), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.swap2 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2006⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.sub (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2007⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.slt (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2008⟩ : UInt256), UInt8.ofNat 18, .SLT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 1410) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2009⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1410), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.jumpiT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2012⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1410)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_2001_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 96)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 1410) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 2001) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1410) (cometWithExtendedAssetList_block_2001_taken_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_2001_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `cometWithExtendedAssetList_block_2001_fallthrough`. -/
def cometWithExtendedAssetList_block_2001_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 2001. -/
theorem cometWithExtendedAssetList_block_2001_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 96)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 2001) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 2013) (cometWithExtendedAssetList_block_2001_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 9) (C + ((32))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2001⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2002⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup2 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2003⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 96) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2004⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 96), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.swap2 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2006⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.sub (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2007⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.slt (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2008⟩ : UInt256), UInt8.ofNat 18, .SLT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 1410) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2009⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1410), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.jumpiNT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2012⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2013)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_2001_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 96)) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 2001) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 2013) (cometWithExtendedAssetList_block_2001_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_2001_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `cometWithExtendedAssetList_block_2013`. -/
def cometWithExtendedAssetList_block_2013_stack {ee : ExecutionEnv} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes x0.toNat 32)) :: (UInt256.ofNat 2023) :: (uInt256OfByteArray (ee.calldata.readBytes x0.toNat 32)) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 2013. -/
theorem cometWithExtendedAssetList_block_2013 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 1393) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 2013) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1393) (cometWithExtendedAssetList_block_2013_stack (ee := ee) (x0 := x0) (R := R)) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.dup1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2013⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.calldataload (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2014⟩ : UInt256), UInt8.ofNat 53, .CALLDATALOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 2023) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2015⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 2023), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup2 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2018⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1393) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2019⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1393), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.jump (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2022⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1393)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_2013_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 1393) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 2013) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1393) (cometWithExtendedAssetList_block_2013_stack (ee := ee) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_2013 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `cometWithExtendedAssetList_block_2023`. -/
def cometWithExtendedAssetList_block_2023_stack {ee : ExecutionEnv} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (x1 + (UInt256.ofNat 32)).toNat 32)) :: (UInt256.ofNat 2040) :: (uInt256OfByteArray (ee.calldata.readBytes (x1 + (UInt256.ofNat 32)).toNat 32)) :: (UInt256.ofNat 64) :: x2 :: x1 :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 2023. -/
theorem cometWithExtendedAssetList_block_2023 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 1393) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 2023) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1393) (cometWithExtendedAssetList_block_2023_stack (ee := ee) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 11) (C + ((36))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2023⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap2 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2024⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2025⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2027⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup4 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2029⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.add (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2030⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.calldataload (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2031⟩ : UInt256), UInt8.ofNat 53, .CALLDATALOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 2040) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2032⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 2040), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.dup2 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2035⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 1393) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2036⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1393), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.jump (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2039⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1393)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_2023_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 1393) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 2023) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1393) (cometWithExtendedAssetList_block_2023_stack (ee := ee) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_2023 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `cometWithExtendedAssetList_block_2040`. -/
def cometWithExtendedAssetList_block_2040_stack {ee : ExecutionEnv} {x0 : UInt256} {x1 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (x3 + x1).toNat 32)) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 2040. -/
theorem cometWithExtendedAssetList_block_2040 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains x2 = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 2040) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 x2 (cometWithExtendedAssetList_block_2040_stack (ee := ee) (x0 := x0) (x1 := x1) (x3 := x3) (R := R)) mem aw rdata σ (k + 6) (C + ((21))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2040⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap3 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2041⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.add (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2042⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.calldataload (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2043⟩ : UInt256), UInt8.ofNat 53, .CALLDATALOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.swap1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2044⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.jump (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2045⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  exact RD.normalizeCounters r6 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_2040_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains x2 = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 2040) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 x2 (cometWithExtendedAssetList_block_2040_stack (ee := ee) (x0 := x0) (x1 := x1) (x3 := x3) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_2040 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `cometWithExtendedAssetList_block_2046_taken`. -/
def cometWithExtendedAssetList_block_2046_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 2046. -/
theorem cometWithExtendedAssetList_block_2046_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 1410) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 2046) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1410) (cometWithExtendedAssetList_block_2046_taken_stack (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2046⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pop (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2047⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.callvalue (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2048⟩ : UInt256), UInt8.ofNat 52, .CALLVALUE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1410) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2049⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1410), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2052⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1410)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_2046_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 1410) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 2046) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 1410) (cometWithExtendedAssetList_block_2046_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_2046_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `cometWithExtendedAssetList_block_2046_fallthrough`. -/
def cometWithExtendedAssetList_block_2046_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 2046. -/
theorem cometWithExtendedAssetList_block_2046_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 2046) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 2053) (cometWithExtendedAssetList_block_2046_fallthrough_stack (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2046⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pop (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2047⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.callvalue (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2048⟩ : UInt256), UInt8.ofNat 52, .CALLVALUE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1410) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2049⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1410), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.jumpiNT (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2052⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, immutableLayout_inBounds, immutableTemplate_size64)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2053)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_2046_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 2046) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 2053) (cometWithExtendedAssetList_block_2046_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_2046_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `cometWithExtendedAssetList_block_2053`. -/
def cometWithExtendedAssetList_block_2053_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 4) :: (UInt256.ofNat ee.calldata.size) :: (UInt256.ofNat 2066) :: (UInt256.ofNat 2116) :: R)

/-- Automatically generated RD summary for bytecode block at pc 2053. -/
theorem cometWithExtendedAssetList_block_2053 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 2001) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 2053) R mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 2001) (cometWithExtendedAssetList_block_2053_stack (ee := ee) (R := R)) mem aw rdata σ (k + 6) (C + ((22))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 2116) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2053⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 2116), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 2066) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2056⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 2066), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.calldatasize (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2059⟩ : UInt256), UInt8.ofNat 54, .CALLDATASIZE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 4) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2060⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 4), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 2001) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2062⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 2001), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.jump (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2065⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2001)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_2053_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 2001) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 2053) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 2001) (cometWithExtendedAssetList_block_2053_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_2053 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `cometWithExtendedAssetList_block_2066`. -/
def cometWithExtendedAssetList_block_2066_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 2076) :: x1 :: x2 :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 2066. -/
theorem cometWithExtendedAssetList_block_2066 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 12245) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 2066) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 12245) (cometWithExtendedAssetList_block_2066_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 6) (C + ((21))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2066⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap2 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2067⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.swap1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2068⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 2076) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2069⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 2076), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 12245) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2072⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 12245), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.jump (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2075⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12245)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_2066_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 12245) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 2066) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 12245) (cometWithExtendedAssetList_block_2066_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_2066 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `cometWithExtendedAssetList_block_2076`. -/
def cometWithExtendedAssetList_block_2076_stack {immWords : String → UInt256} {ee : ExecutionEnv} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat ee.source.val) :: x1 :: x0 :: (immWords "baseToken") :: R)

/-- Automatically generated RD summary for bytecode block at pc 2076. -/
theorem cometWithExtendedAssetList_block_2076 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 14496) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 2076) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 14496) (cometWithExtendedAssetList_block_2076_stack (immWords := immWords) (ee := ee) (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 6) (C + ((20))) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2076⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pushConst (immWords "baseToken") (width := 32) (op := .PUSH32) (by decide) (by
    conv_lhs => arg 2; change (⟨2077⟩ : UInt256)
    exact immutableDecode_2077 immWords) (by evm_ov)
  have r3 := r2.swap2 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2110⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.caller (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2111⟩ : UInt256), UInt8.ofNat 51, .CALLER, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 14496) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2112⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 14496), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.jump (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2115⟩ : UInt256), UInt8.ofNat 86, .JUMP, none, immutableLayout_inBounds, immutableTemplate_size64)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14496)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem cometWithExtendedAssetList_block_2076_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) 0).contains (UInt256.ofNat 14496) = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 2076) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 14496) (cometWithExtendedAssetList_block_2076_stack (immWords := immWords) (ee := ee) (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (cometWithExtendedAssetList_block_2076 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 2116. -/
theorem cometWithExtendedAssetList_block_2116 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) ee g s0 (UInt256.ofNat 2116) R mem aw rdata σ k C)
    : RDret (Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords) g s0 (sstoreAccountMap ee.codeOwner σ (memLoad (UInt256.ofNat 0) ((Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords).write (UInt256.ofNat 18514).toNat mem (UInt256.ofNat 0).toNat (UInt256.ofNat 32).toNat)) (UInt256.ofNat 0)) (((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 0) mem).toByteArray.write 0 ((Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords).write (UInt256.ofNat 18514).toNat mem (UInt256.ofNat 0).toNat (UInt256.ofNat 32).toNat) (UInt256.ofNat 0).toNat 32) (memLoad (UInt256.ofNat 64) ((memLoad (UInt256.ofNat 0) mem).toByteArray.write 0 ((Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords).write (UInt256.ofNat 18514).toNat mem (UInt256.ofNat 0).toNat (UInt256.ofNat 32).toNat) (UInt256.ofNat 0).toNat 32)).toNat 32).readWithPadding (memLoad (UInt256.ofNat 64) ((memLoad (UInt256.ofNat 0) mem).toByteArray.write 0 ((Benchmarks.CompoundIII.Comet.immutableLayout.runtime Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode immWords).write (UInt256.ofNat 18514).toNat mem (UInt256.ofNat 0).toNat (UInt256.ofNat 32).toNat) (UInt256.ofNat 0).toNat 32)).toNat (UInt256.ofNat 32).toNat) := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2116⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2117⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2119⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup1 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2121⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := RD.genMload r4 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2122⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2123⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 18514) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2125⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 18514), 2), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.dup4 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2128⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := RD.genCodecopy r8 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2129⟩ : UInt256), UInt8.ofNat 57, .CODECOPY, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.dup2 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2130⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := RD.genMload r10 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2131⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.swap2 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2132⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := RD.genMstore r12 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2133⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r14⟩ := RD.sstore r13 hperm (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2134⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2135⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2137⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := RD.genMload r16 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2139⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2140⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.dup2 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2142⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := RD.genMstore r19 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2143⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact RD.genRet r20 (by immutable_decode(Benchmarks.CompoundIII.Comet.immutableLayout, Benchmarks.CompoundIII.Comet.cometWithExtendedAssetListBytecode, immWords, (⟨2144⟩ : UInt256), UInt8.ofNat 243, .RETURN, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

end cometWithExtendedAssetListBlocks
