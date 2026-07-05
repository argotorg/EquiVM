import Benchmarks.UniswapV3Pool.InitializeGetTickReturn

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.UniswapV3Pool

def getSqrtRatioTickInt24Word (tick : UInt256) : UInt256 :=
  UInt256.signextend ⟨2⟩ tick

def getSqrtRatioTickNegWord (tick : UInt256) : UInt256 :=
  UInt256.slt (getSqrtRatioTickInt24Word tick) ⟨0⟩

def getSqrtRatioAbsTickNegWord (tick : UInt256) : UInt256 :=
  UInt256.sub ⟨0⟩ (getSqrtRatioTickInt24Word tick)

def getSqrtRatioMaxTickWord : UInt256 := ⟨887272⟩

def getSqrtRatioAbsTickInRangeWord (absTick : UInt256) : UInt256 :=
  UInt256.isZero (UInt256.gt absTick getSqrtRatioMaxTickWord)

def getSqrtRatioBit1Word (absTick : UInt256) : UInt256 :=
  UInt256.land absTick ⟨1⟩

def getSqrtRatioInitialEvenWord : UInt256 :=
  UInt256.shiftLeft ⟨1⟩ ⟨128⟩

def getSqrtRatioInitialOddWord : UInt256 :=
  ⟨340265354078544963557816517032075149313⟩

def getSqrtRatioUint136Mask : UInt256 :=
  ⟨87112285931760246646623899502532662132735⟩

def getSqrtRatioRatioMaskedWord (ratio : UInt256) : UInt256 :=
  UInt256.land getSqrtRatioUint136Mask ratio

def getSqrtRatioBit2Word (absTick : UInt256) : UInt256 :=
  UInt256.land absTick ⟨2⟩

def getSqrtRatioFactor2Word : UInt256 :=
  ⟨340248342086729790484326174814286782778⟩

def getSqrtRatioAfterBit2Word (ratio : UInt256) : UInt256 :=
  UInt256.shiftRight (UInt256.mul getSqrtRatioFactor2Word
    (getSqrtRatioRatioMaskedWord ratio)) ⟨128⟩

theorem uniswapV3PoolInitializePatchDisjointGetSqrtRatioAtTick {v : PoolImmutables}
    {pc : UInt256} {n : Nat} (hlo : 11629 ≤ pc.toNat) (hhi : pc.toNat + n ≤ 13989) :
    ∀ p ∈ patches v, pc.toNat + n ≤ p.1 ∨ p.1 + 32 ≤ pc.toNat := by
  intro p hp
  simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup] at hp
  rcases hp with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl
  all_goals omega

private theorem uniswapV3PoolInitializePatchPreservesJumpDest11629 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨11629⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolInitializePatchPreservesJumpDest11652 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨11652⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolInitializePatchPreservesJumpDest11660 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨11660⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolInitializePatchPreservesJumpDest11722 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨11722⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolInitializePatchPreservesJumpDest11742 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨11742⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolInitializePatchPreservesJumpDest11760 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨11760⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolInitializePatchPreservesJumpDest11812 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨11812⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolJumpDestPatched11629 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨11629⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolInitializePatchPreservesJumpDest11629

theorem uniswapV3PoolJumpDestPatched11652 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨11652⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolInitializePatchPreservesJumpDest11652

theorem uniswapV3PoolJumpDestPatched11660 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨11660⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolInitializePatchPreservesJumpDest11660

theorem uniswapV3PoolJumpDestPatched11722 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨11722⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolInitializePatchPreservesJumpDest11722

theorem uniswapV3PoolJumpDestPatched11742 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨11742⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolInitializePatchPreservesJumpDest11742

theorem uniswapV3PoolJumpDestPatched11760 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨11760⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolInitializePatchPreservesJumpDest11760

theorem uniswapV3PoolJumpDestPatched11812 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨11812⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolInitializePatchPreservesJumpDest11812

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetTickAtSqrtRatioSqrtRatioCallSetup {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨14739⟩
      (⟨14786⟩ :: getTickLowEqHiWord ee :: getTickHiWord ee :: getTickLowWord ee ::
        getTickLogSqrt10001Word ee :: getTickLog2After50Word ee :: getTickMsbWord ee ::
          getTickLogRShifted50Word ee :: getTickRatioWord ee :: ⟨0⟩ :: initializeArgWord ee ::
            ⟨10793⟩ :: ⟨0⟩ :: initializeArgWord ee :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k C)
    (heq : getTickLowEqHiWord ee = ⟨0⟩)
    (hov : R.length + 18 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨11629⟩
      (getTickHiWord ee :: ⟨14758⟩ :: initializeArgWord ee ::
        getTickHiWord ee :: getTickLowWord ee :: getTickLogSqrt10001Word ee ::
          getTickLog2After50Word ee :: getTickMsbWord ee :: getTickLogRShifted50Word ee ::
            getTickRatioWord ee :: ⟨0⟩ :: initializeArgWord ee :: ⟨10793⟩ ::
              ⟨0⟩ :: initializeArgWord ee :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 13989 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 15650) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 15650 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetTickAtSqrtRatio hlo hhi)]
  have hd14739 : decode code ⟨14739⟩ = some (.JUMPI, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14740 : decode code ⟨14740⟩ = some (.DUP9, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14741 : decode code ⟨14741⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14743 : decode code ⟨14743⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14745 : decode code ⟨14745⟩ = some (.Push .PUSH1, some (⟨160⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14747 : decode code ⟨14747⟩ = some (.SHL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14748 : decode code ⟨14748⟩ = some (.SUB, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14749 : decode code ⟨14749⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14750 : decode code ⟨14750⟩ = some (.Push .PUSH2, some (⟨14758⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14753 : decode code ⟨14753⟩ = some (.DUP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14754 : decode code ⟨14754⟩ = some (.Push .PUSH2, some (⟨11629⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14757 : decode code ⟨14757⟩ = some (.JUMP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hargClean : UInt256.land (initializeArgWord ee) slot0Uint160Mask =
      initializeArgWord ee := by
    apply slot0Uint160Mask_clean
    rw [initializeArgWord, show initializeUint160Mask = slot0Uint160Mask by native_decide]
    exact slot0Uint160Mask_bound (calldataWord ee.calldata 4)
  have hargCleanR : UInt256.land slot0Uint160Mask (initializeArgWord ee) =
      initializeArgWord ee := by
    rw [u256_land_comm]
    exact hargClean
  have rd14740 := h.jumpiNT hd14739 heq (by
    simp only [List.length_cons]
    omega)
  have rd14741 := by
    simpa using RD.dup9 rd14740 hd14740 (by
      simp only [List.length_cons]
      omega)
  have rd14743 := by
    simpa using rd14741.push1 ⟨1⟩ hd14741 (by
      simp only [List.length_cons]
      omega)
  have rd14745 := by
    simpa using rd14743.push1 ⟨1⟩ hd14743 (by
      simp only [List.length_cons]
      omega)
  have rd14747 := by
    simpa using rd14745.push1 ⟨160⟩ hd14745 (by
      simp only [List.length_cons]
      omega)
  have rd14748 := by
    simpa using rd14747.shl hd14747 (by
      simp only [List.length_cons]
      omega)
  have rd14749 := by
    simpa [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        slot0Uint160Mask by native_decide] using rd14748.sub hd14748 (by
      simp only [List.length_cons]
      omega)
  have rd14750 := by
    simpa [hargCleanR] using rd14749.and hd14749 (by
      simp only [List.length_cons]
      omega)
  have rd14753 := by
    simpa using rd14750.push2 ⟨14758⟩ hd14750 (by
      simp only [List.length_cons]
      omega)
  have rd14754 := by
    simpa using rd14753.dup3 hd14753 (by
      simp only [List.length_cons]
      omega)
  have rd14757 := by
    simpa using rd14754.push2 ⟨11629⟩ hd14754 (by
      simp only [List.length_cons]
      omega)
  have rd11629 := rd14757.jump hd14757 (uniswapV3PoolJumpDestPatched11629 hpatch) (by
    simp only [List.length_cons]
    omega)
  exact ⟨_, _, by simpa using rd11629⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetSqrtRatioAtTickAbsTickNonNeg {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {tick ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨11629⟩ (tick :: ret :: R) mem aw rdata acc k C)
    (hnonneg : getSqrtRatioTickNegWord tick = ⟨0⟩)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨11663⟩
      (getSqrtRatioTickInt24Word tick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 11629 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 13989) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 13989 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetSqrtRatioAtTick hlo hhi)]
  have hd11629 : decode code ⟨11629⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11630 : decode code ⟨11630⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11632 : decode code ⟨11632⟩ = some (.DUP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11633 : decode code ⟨11633⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11635 : decode code ⟨11635⟩ = some (.DUP4, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11636 : decode code ⟨11636⟩ = some (.Push .PUSH1, some (⟨2⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11638 : decode code ⟨11638⟩ = some (.SIGNEXTEND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11639 : decode code ⟨11639⟩ = some (.SLT, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11640 : decode code ⟨11640⟩ = some (.Push .PUSH2, some (⟨11652⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11643 : decode code ⟨11643⟩ = some (.JUMPI, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11644 : decode code ⟨11644⟩ = some (.DUP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11645 : decode code ⟨11645⟩ = some (.Push .PUSH1, some (⟨2⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11647 : decode code ⟨11647⟩ = some (.SIGNEXTEND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11648 : decode code ⟨11648⟩ = some (.Push .PUSH2, some (⟨11660⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11651 : decode code ⟨11651⟩ = some (.JUMP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11660 : decode code ⟨11660⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11661 : decode code ⟨11661⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11662 : decode code ⟨11662⟩ = some (.POP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have rd11630 := by
    simpa using h.jumpdest hd11629 (by
      simp only [List.length_cons]
      omega)
  have rd11632 := by
    simpa using rd11630.push1 ⟨0⟩ hd11630 (by
      simp only [List.length_cons]
      omega)
  have rd11633 := by
    simpa using rd11632.dup1 hd11632 (by
      simp only [List.length_cons]
      omega)
  have rd11635 := by
    simpa using rd11633.push1 ⟨0⟩ hd11633 (by
      simp only [List.length_cons]
      omega)
  have rd11636 := by
    simpa using rd11635.dup4 hd11635 (by
      simp only [List.length_cons]
      omega)
  have rd11638 := by
    simpa using rd11636.push1 ⟨2⟩ hd11636 (by
      simp only [List.length_cons]
      omega)
  have rd11639 := by
    simpa [getSqrtRatioTickInt24Word] using RD.signextend rd11638 hd11638 (by
      simp only [List.length_cons]
      omega)
  have rd11640 := by
    simpa [getSqrtRatioTickNegWord] using rd11639.slt hd11639 (by
      simp only [List.length_cons]
      omega)
  have rd11643 := by
    simpa using rd11640.push2 ⟨11652⟩ hd11640 (by
      simp only [List.length_cons]
      omega)
  have rd11644 := rd11643.jumpiNT hd11643 hnonneg (by
    simp only [List.length_cons]
    omega)
  have rd11645 := by
    simpa using rd11644.dup3 hd11644 (by
      simp only [List.length_cons]
      omega)
  have rd11647 := by
    simpa using rd11645.push1 ⟨2⟩ hd11645 (by
      simp only [List.length_cons]
      omega)
  have rd11648 := by
    simpa [getSqrtRatioTickInt24Word] using RD.signextend rd11647 hd11647 (by
      simp only [List.length_cons]
      omega)
  have rd11651 := by
    simpa using rd11648.push2 ⟨11660⟩ hd11648 (by
      simp only [List.length_cons]
      omega)
  have rd11660 := rd11651.jump hd11651 (uniswapV3PoolJumpDestPatched11660 hpatch) (by
    simp only [List.length_cons]
    omega)
  have rd11661 := by
    simpa using rd11660.jumpdest hd11660 (by
      simp only [List.length_cons]
      omega)
  have rd11662 := by
    simpa using rd11661.swap1 hd11661 (by
      simp only [List.length_cons]
      omega)
  have rd11663 := by
    simpa using rd11662.pop hd11662 (by
      simp only [List.length_cons]
      omega)
  exact ⟨_, _, by simpa using rd11663⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetSqrtRatioAtTickAbsTickNeg {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {tick ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨11629⟩ (tick :: ret :: R) mem aw rdata acc k C)
    (hneg : getSqrtRatioTickNegWord tick ≠ ⟨0⟩)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨11663⟩
      (getSqrtRatioAbsTickNegWord tick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 11629 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 13989) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 13989 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetSqrtRatioAtTick hlo hhi)]
  have hd11629 : decode code ⟨11629⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11630 : decode code ⟨11630⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11632 : decode code ⟨11632⟩ = some (.DUP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11633 : decode code ⟨11633⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11635 : decode code ⟨11635⟩ = some (.DUP4, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11636 : decode code ⟨11636⟩ = some (.Push .PUSH1, some (⟨2⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11638 : decode code ⟨11638⟩ = some (.SIGNEXTEND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11639 : decode code ⟨11639⟩ = some (.SLT, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11640 : decode code ⟨11640⟩ = some (.Push .PUSH2, some (⟨11652⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11643 : decode code ⟨11643⟩ = some (.JUMPI, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11652 : decode code ⟨11652⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11653 : decode code ⟨11653⟩ = some (.DUP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11654 : decode code ⟨11654⟩ = some (.Push .PUSH1, some (⟨2⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11656 : decode code ⟨11656⟩ = some (.SIGNEXTEND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11657 : decode code ⟨11657⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11659 : decode code ⟨11659⟩ = some (.SUB, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11660 : decode code ⟨11660⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11661 : decode code ⟨11661⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11662 : decode code ⟨11662⟩ = some (.POP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have rd11630 := by
    simpa using h.jumpdest hd11629 (by
      simp only [List.length_cons]
      omega)
  have rd11632 := by
    simpa using rd11630.push1 ⟨0⟩ hd11630 (by
      simp only [List.length_cons]
      omega)
  have rd11633 := by
    simpa using rd11632.dup1 hd11632 (by
      simp only [List.length_cons]
      omega)
  have rd11635 := by
    simpa using rd11633.push1 ⟨0⟩ hd11633 (by
      simp only [List.length_cons]
      omega)
  have rd11636 := by
    simpa using rd11635.dup4 hd11635 (by
      simp only [List.length_cons]
      omega)
  have rd11638 := by
    simpa using rd11636.push1 ⟨2⟩ hd11636 (by
      simp only [List.length_cons]
      omega)
  have rd11639 := by
    simpa [getSqrtRatioTickInt24Word] using RD.signextend rd11638 hd11638 (by
      simp only [List.length_cons]
      omega)
  have rd11640 := by
    simpa [getSqrtRatioTickNegWord] using rd11639.slt hd11639 (by
      simp only [List.length_cons]
      omega)
  have rd11643 := by
    simpa using rd11640.push2 ⟨11652⟩ hd11640 (by
      simp only [List.length_cons]
      omega)
  have rd11652 := rd11643.jumpiT hd11643 hneg (uniswapV3PoolJumpDestPatched11652 hpatch) (by
    simp only [List.length_cons]
    omega)
  have rd11653 := by
    simpa using rd11652.jumpdest hd11652 (by
      simp only [List.length_cons]
      omega)
  have rd11654 := by
    simpa using rd11653.dup3 hd11653 (by
      simp only [List.length_cons]
      omega)
  have rd11656 := by
    simpa using rd11654.push1 ⟨2⟩ hd11654 (by
      simp only [List.length_cons]
      omega)
  have rd11657 := by
    simpa [getSqrtRatioTickInt24Word] using RD.signextend rd11656 hd11656 (by
      simp only [List.length_cons]
      omega)
  have rd11659 := by
    simpa using rd11657.push1 ⟨0⟩ hd11657 (by
      simp only [List.length_cons]
      omega)
  have rd11660 := by
    simpa [getSqrtRatioAbsTickNegWord] using rd11659.sub hd11659 (by
      simp only [List.length_cons]
      omega)
  have rd11661 := by
    simpa using rd11660.jumpdest hd11660 (by
      simp only [List.length_cons]
      omega)
  have rd11662 := by
    simpa using rd11661.swap1 hd11661 (by
      simp only [List.length_cons]
      omega)
  have rd11663 := by
    simpa using rd11662.pop hd11662 (by
      simp only [List.length_cons]
      omega)
  exact ⟨_, _, by simpa using rd11663⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetSqrtRatioAtTickRangeOk {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {absTick tick ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨11663⟩ (absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k C)
    (hok : getSqrtRatioAbsTickInRangeWord absTick ≠ ⟨0⟩)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨11722⟩ (absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 11629 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 13989) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 13989 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetSqrtRatioAtTick hlo hhi)]
  have hd11663 : decode code ⟨11663⟩ = some (.Push .PUSH3, some (⟨887272⟩, 3)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11667 : decode code ⟨11667⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11668 : decode code ⟨11668⟩ = some (.GT, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11669 : decode code ⟨11669⟩ = some (.ISZERO, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11670 : decode code ⟨11670⟩ = some (.Push .PUSH2, some (⟨11722⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11673 : decode code ⟨11673⟩ = some (.JUMPI, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have rd11667 := by
    simpa [getSqrtRatioMaxTickWord] using
      h.pushConst (⟨887272⟩ : UInt256) (by native_decide : Operation.POp.PUSH3 ≠ .PUSH0)
        hd11663 (by
          simp only [List.length_cons]
          omega)
  have rd11668 := by
    simpa using rd11667.dup2 hd11667 (by
      simp only [List.length_cons]
      omega)
  have rd11669 := by
    simpa [getSqrtRatioMaxTickWord] using rd11668.gt hd11668 (by
      simp only [List.length_cons]
      omega)
  have rd11670 := by
    simpa [getSqrtRatioAbsTickInRangeWord] using rd11669.iszero hd11669 (by
      simp only [List.length_cons]
      omega)
  have rd11673 := by
    simpa using rd11670.push2 ⟨11722⟩ hd11670 (by
      simp only [List.length_cons]
      omega)
  exact ⟨_, _, rd11673.jumpiT hd11673 hok (uniswapV3PoolJumpDestPatched11722 hpatch) (by
    simp only [List.length_cons]
    omega)⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetSqrtRatioAtTickRatioInitEven {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {absTick tick ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨11722⟩ (absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k C)
    (hbit : getSqrtRatioBit1Word absTick = ⟨0⟩)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨11760⟩
      (getSqrtRatioInitialEvenWord :: ⟨0⟩ :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 11629 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 13989) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 13989 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetSqrtRatioAtTick hlo hhi)]
  have hd11722 : decode code ⟨11722⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11723 : decode code ⟨11723⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11725 : decode code ⟨11725⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11727 : decode code ⟨11727⟩ = some (.DUP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11728 : decode code ⟨11728⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11729 : decode code ⟨11729⟩ = some (.Push .PUSH2, some (⟨11742⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11732 : decode code ⟨11732⟩ = some (.JUMPI, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11733 : decode code ⟨11733⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11735 : decode code ⟨11735⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11737 : decode code ⟨11737⟩ = some (.SHL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11738 : decode code ⟨11738⟩ = some (.Push .PUSH2, some (⟨11760⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11741 : decode code ⟨11741⟩ = some (.JUMP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have rd11723 := by
    simpa using h.jumpdest hd11722 (by
      simp only [List.length_cons]
      omega)
  have rd11725 := by
    simpa using rd11723.push1 ⟨0⟩ hd11723 (by
      simp only [List.length_cons]
      omega)
  have rd11727 := by
    simpa using rd11725.push1 ⟨1⟩ hd11725 (by
      simp only [List.length_cons]
      omega)
  have rd11728 := by
    simpa using rd11727.dup3 hd11727 (by
      simp only [List.length_cons]
      omega)
  have rd11729 := by
    simpa [getSqrtRatioBit1Word] using rd11728.and hd11728 (by
      simp only [List.length_cons]
      omega)
  have rd11732 := by
    simpa using rd11729.push2 ⟨11742⟩ hd11729 (by
      simp only [List.length_cons]
      omega)
  have rd11733 := rd11732.jumpiNT hd11732 hbit (by
    simp only [List.length_cons]
    omega)
  have rd11735 := by
    simpa using rd11733.push1 ⟨1⟩ hd11733 (by
      simp only [List.length_cons]
      omega)
  have rd11737 := by
    simpa using rd11735.push1 ⟨128⟩ hd11735 (by
      simp only [List.length_cons]
      omega)
  have rd11738 := by
    simpa [getSqrtRatioInitialEvenWord] using rd11737.shl hd11737 (by
      simp only [List.length_cons]
      omega)
  have rd11741 := by
    simpa using rd11738.push2 ⟨11760⟩ hd11738 (by
      simp only [List.length_cons]
      omega)
  have rd11760 := rd11741.jump hd11741 (uniswapV3PoolJumpDestPatched11760 hpatch) (by
    simp only [List.length_cons]
    omega)
  exact ⟨_, _, by simpa using rd11760⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetSqrtRatioAtTickRatioInitOdd {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {absTick tick ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨11722⟩ (absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k C)
    (hbit : getSqrtRatioBit1Word absTick ≠ ⟨0⟩)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨11760⟩
      (getSqrtRatioInitialOddWord :: ⟨0⟩ :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 11629 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 13989) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 13989 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetSqrtRatioAtTick hlo hhi)]
  have hd11722 : decode code ⟨11722⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11723 : decode code ⟨11723⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11725 : decode code ⟨11725⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11727 : decode code ⟨11727⟩ = some (.DUP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11728 : decode code ⟨11728⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11729 : decode code ⟨11729⟩ = some (.Push .PUSH2, some (⟨11742⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11732 : decode code ⟨11732⟩ = some (.JUMPI, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11742 : decode code ⟨11742⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11743 :
      decode code ⟨11743⟩ =
        some (.Push .PUSH16, some (⟨340265354078544963557816517032075149313⟩, 16)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have rd11723 := by
    simpa using h.jumpdest hd11722 (by
      simp only [List.length_cons]
      omega)
  have rd11725 := by
    simpa using rd11723.push1 ⟨0⟩ hd11723 (by
      simp only [List.length_cons]
      omega)
  have rd11727 := by
    simpa using rd11725.push1 ⟨1⟩ hd11725 (by
      simp only [List.length_cons]
      omega)
  have rd11728 := by
    simpa using rd11727.dup3 hd11727 (by
      simp only [List.length_cons]
      omega)
  have rd11729 := by
    simpa [getSqrtRatioBit1Word] using rd11728.and hd11728 (by
      simp only [List.length_cons]
      omega)
  have rd11732 := by
    simpa using rd11729.push2 ⟨11742⟩ hd11729 (by
      simp only [List.length_cons]
      omega)
  have rd11742 := rd11732.jumpiT hd11732 hbit (uniswapV3PoolJumpDestPatched11742 hpatch) (by
    simp only [List.length_cons]
    omega)
  have rd11743 := by
    simpa using rd11742.jumpdest hd11742 (by
      simp only [List.length_cons]
      omega)
  have rd11760 := by
    simpa [getSqrtRatioInitialOddWord] using
      rd11743.pushConst (⟨340265354078544963557816517032075149313⟩ : UInt256)
        (by native_decide : Operation.POp.PUSH16 ≠ .PUSH0) hd11743 (by
          simp only [List.length_cons]
          omega)
  exact ⟨_, _, by simpa using rd11760⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetSqrtRatioAtTickBit2Zero {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ratio absTick tick ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨11760⟩ (ratio :: ⟨0⟩ :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k C)
    (hbit : getSqrtRatioBit2Word absTick = ⟨0⟩)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨11812⟩
      (getSqrtRatioRatioMaskedWord ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 11629 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 13989) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 13989 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetSqrtRatioAtTick hlo hhi)]
  have hd11760 : decode code ⟨11760⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11761 :
      decode code ⟨11761⟩ =
        some (.Push .PUSH17, some (⟨87112285931760246646623899502532662132735⟩, 17)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11779 : decode code ⟨11779⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11780 : decode code ⟨11780⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11781 : decode code ⟨11781⟩ = some (.POP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11782 : decode code ⟨11782⟩ = some (.Push .PUSH1, some (⟨2⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11784 : decode code ⟨11784⟩ = some (.DUP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11785 : decode code ⟨11785⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11786 : decode code ⟨11786⟩ = some (.ISZERO, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11787 : decode code ⟨11787⟩ = some (.Push .PUSH2, some (⟨11812⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11790 : decode code ⟨11790⟩ = some (.JUMPI, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hcond : UInt256.isZero (getSqrtRatioBit2Word absTick) ≠ ⟨0⟩ := by
    rw [hbit]
    native_decide
  have rd11761 := by
    simpa using h.jumpdest hd11760 (by
      simp only [List.length_cons]
      omega)
  have rd11779 := by
    simpa [getSqrtRatioUint136Mask] using
      rd11761.pushConst (⟨87112285931760246646623899502532662132735⟩ : UInt256)
        (by native_decide : Operation.POp.PUSH17 ≠ .PUSH0) hd11761 (by
          simp only [List.length_cons]
          omega)
  have rd11780 := by
    simpa [getSqrtRatioRatioMaskedWord, getSqrtRatioUint136Mask] using
      rd11779.and hd11779 (by
        simp only [List.length_cons]
        omega)
  have rd11781 := by
    simpa using rd11780.swap1 hd11780 (by
      simp only [List.length_cons]
      omega)
  have rd11782 := by
    simpa using rd11781.pop hd11781 (by
      simp only [List.length_cons]
      omega)
  have rd11784 := by
    simpa using rd11782.push1 ⟨2⟩ hd11782 (by
      simp only [List.length_cons]
      omega)
  have rd11785 := by
    simpa using rd11784.dup3 hd11784 (by
      simp only [List.length_cons]
      omega)
  have rd11786 := by
    simpa [getSqrtRatioBit2Word] using rd11785.and hd11785 (by
      simp only [List.length_cons]
      omega)
  have rd11787 := by
    simpa using rd11786.iszero hd11786 (by
      simp only [List.length_cons]
      omega)
  have rd11790 := by
    simpa using rd11787.push2 ⟨11812⟩ hd11787 (by
      simp only [List.length_cons]
      omega)
  exact ⟨_, _, rd11790.jumpiT hd11790 hcond (uniswapV3PoolJumpDestPatched11812 hpatch) (by
    simp only [List.length_cons]
    omega)⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetSqrtRatioAtTickBit2Set {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ratio absTick tick ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨11760⟩ (ratio :: ⟨0⟩ :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k C)
    (hbit : getSqrtRatioBit2Word absTick ≠ ⟨0⟩)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨11812⟩
      (getSqrtRatioAfterBit2Word ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 11629 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 13989) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 13989 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetSqrtRatioAtTick hlo hhi)]
  have hd11760 : decode code ⟨11760⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11761 :
      decode code ⟨11761⟩ =
        some (.Push .PUSH17, some (⟨87112285931760246646623899502532662132735⟩, 17)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11779 : decode code ⟨11779⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11780 : decode code ⟨11780⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11781 : decode code ⟨11781⟩ = some (.POP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11782 : decode code ⟨11782⟩ = some (.Push .PUSH1, some (⟨2⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11784 : decode code ⟨11784⟩ = some (.DUP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11785 : decode code ⟨11785⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11786 : decode code ⟨11786⟩ = some (.ISZERO, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11787 : decode code ⟨11787⟩ = some (.Push .PUSH2, some (⟨11812⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11790 : decode code ⟨11790⟩ = some (.JUMPI, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11791 :
      decode code ⟨11791⟩ =
        some (.Push .PUSH16, some (⟨340248342086729790484326174814286782778⟩, 16)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11808 : decode code ⟨11808⟩ = some (.MUL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11809 : decode code ⟨11809⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11811 : decode code ⟨11811⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hcond : UInt256.isZero (getSqrtRatioBit2Word absTick) = ⟨0⟩ :=
    isZero_eq_zero_of_ne hbit
  have rd11761 := by
    simpa using h.jumpdest hd11760 (by
      simp only [List.length_cons]
      omega)
  have rd11779 := by
    simpa [getSqrtRatioUint136Mask] using
      rd11761.pushConst (⟨87112285931760246646623899502532662132735⟩ : UInt256)
        (by native_decide : Operation.POp.PUSH17 ≠ .PUSH0) hd11761 (by
          simp only [List.length_cons]
          omega)
  have rd11780 := by
    simpa [getSqrtRatioRatioMaskedWord, getSqrtRatioUint136Mask] using
      rd11779.and hd11779 (by
        simp only [List.length_cons]
        omega)
  have rd11781 := by
    simpa using rd11780.swap1 hd11780 (by
      simp only [List.length_cons]
      omega)
  have rd11782 := by
    simpa using rd11781.pop hd11781 (by
      simp only [List.length_cons]
      omega)
  have rd11784 := by
    simpa using rd11782.push1 ⟨2⟩ hd11782 (by
      simp only [List.length_cons]
      omega)
  have rd11785 := by
    simpa using rd11784.dup3 hd11784 (by
      simp only [List.length_cons]
      omega)
  have rd11786 := by
    simpa [getSqrtRatioBit2Word] using rd11785.and hd11785 (by
      simp only [List.length_cons]
      omega)
  have rd11787 := by
    simpa using rd11786.iszero hd11786 (by
      simp only [List.length_cons]
      omega)
  have rd11790 := by
    simpa using rd11787.push2 ⟨11812⟩ hd11787 (by
      simp only [List.length_cons]
      omega)
  have rd11791 := rd11790.jumpiNT hd11790 hcond (by
    simp only [List.length_cons]
    omega)
  have rd11808 := by
    simpa [getSqrtRatioFactor2Word] using
      rd11791.pushConst (⟨340248342086729790484326174814286782778⟩ : UInt256)
        (by native_decide : Operation.POp.PUSH16 ≠ .PUSH0) hd11791 (by
          simp only [List.length_cons]
          omega)
  have rd11809 := by
    simpa using rd11808.mul hd11808 (by
      simp only [List.length_cons]
      omega)
  have rd11811 := by
    simpa using rd11809.push1 ⟨128⟩ hd11809 (by
      simp only [List.length_cons]
      omega)
  have rd11812 := by
    simpa [getSqrtRatioAfterBit2Word, getSqrtRatioFactor2Word] using rd11811.shr hd11811
      (by
        simp only [List.length_cons]
        omega)
  exact ⟨_, _, by simpa using rd11812⟩

end Benchmarks.UniswapV3Pool
