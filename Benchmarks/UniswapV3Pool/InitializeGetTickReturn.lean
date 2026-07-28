import Benchmarks.UniswapV3Pool.InitializeGetTickLogCombine

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.UniswapV3Pool

private theorem uniswapV3PoolInitializePatchPreservesJumpDest10793 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨10793⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolInitializePatchPreservesJumpDest14786 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨14786⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolInitializePatchPreservesJumpDest14788 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨14788⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolJumpDestPatched10793 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨10793⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolInitializePatchPreservesJumpDest10793

theorem uniswapV3PoolJumpDestPatched14786 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨14786⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolInitializePatchPreservesJumpDest14786

theorem uniswapV3PoolJumpDestPatched14788 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨14788⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolInitializePatchPreservesJumpDest14788

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetTickAtSqrtRatioReturnCleanup {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {tick a b c d e f gg ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨14788⟩
      (tick :: a :: b :: c :: d :: e :: f :: gg :: ⟨0⟩ :: initializeArgWord ee ::
        ⟨10793⟩ :: ⟨0⟩ :: initializeArgWord ee :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k C)
    (hov : R.length + 18 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨10793⟩
      (tick :: ⟨0⟩ :: initializeArgWord ee :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 13989 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 15650) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 15650 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetTickAtSqrtRatio hlo hhi)]
  have hd14788 : decode code ⟨14788⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14789 : decode code ⟨14789⟩ = some (.SWAP10, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14790 : decode code ⟨14790⟩ = some (.SWAP9, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14791 : decode code ⟨14791⟩ = some (.POP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14792 : decode code ⟨14792⟩ = some (.POP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14793 : decode code ⟨14793⟩ = some (.POP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14794 : decode code ⟨14794⟩ = some (.POP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14795 : decode code ⟨14795⟩ = some (.POP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14796 : decode code ⟨14796⟩ = some (.POP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14797 : decode code ⟨14797⟩ = some (.POP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14798 : decode code ⟨14798⟩ = some (.POP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14799 : decode code ⟨14799⟩ = some (.POP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14800 : decode code ⟨14800⟩ = some (.JUMP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have rd14789 := by
    simpa using h.jumpdest hd14788 (by
      simp only [List.length_cons]
      omega)
  have rd14790 := by
    simpa using rd14789.swap10 hd14789 (by
      simp only [List.length_cons]
      omega)
  have rd14791 := by
    simpa using RD.swap9 rd14790 hd14790 (by
      simp only [List.length_cons]
      omega)
  have rd14792 := by
    simpa using rd14791.pop hd14791 (by
      simp only [List.length_cons]
      omega)
  have rd14793 := by
    simpa using rd14792.pop hd14792 (by
      simp only [List.length_cons]
      omega)
  have rd14794 := by
    simpa using rd14793.pop hd14793 (by
      simp only [List.length_cons]
      omega)
  have rd14795 := by
    simpa using rd14794.pop hd14794 (by
      simp only [List.length_cons]
      omega)
  have rd14796 := by
    simpa using rd14795.pop hd14795 (by
      simp only [List.length_cons]
      omega)
  have rd14797 := by
    simpa using rd14796.pop hd14796 (by
      simp only [List.length_cons]
      omega)
  have rd14798 := by
    simpa using rd14797.pop hd14797 (by
      simp only [List.length_cons]
      omega)
  have rd14799 := by
    simpa using rd14798.pop hd14798 (by
      simp only [List.length_cons]
      omega)
  have rd14800 := by
    simpa using rd14799.pop hd14799 (by
      simp only [List.length_cons]
      omega)
  have rd10793 := rd14800.jump hd14800 (uniswapV3PoolJumpDestPatched10793 hpatch) (by
    simp only [List.length_cons]
    omega)
  exact ⟨_, _, rd10793⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetTickAtSqrtRatioReturnTickLowEq {v : PoolImmutables}
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
    (heq : getTickLowEqHiWord ee ≠ ⟨0⟩)
    (hov : R.length + 18 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨10793⟩
      (getTickLowWord ee :: ⟨0⟩ :: initializeArgWord ee :: ret :: R)
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
  have hd14786 : decode code ⟨14786⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14787 : decode code ⟨14787⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14788 : decode code ⟨14788⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14789 : decode code ⟨14789⟩ = some (.SWAP10, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14790 : decode code ⟨14790⟩ = some (.SWAP9, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14791 : decode code ⟨14791⟩ = some (.POP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14792 : decode code ⟨14792⟩ = some (.POP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14793 : decode code ⟨14793⟩ = some (.POP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14794 : decode code ⟨14794⟩ = some (.POP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14795 : decode code ⟨14795⟩ = some (.POP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14796 : decode code ⟨14796⟩ = some (.POP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14797 : decode code ⟨14797⟩ = some (.POP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14798 : decode code ⟨14798⟩ = some (.POP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14799 : decode code ⟨14799⟩ = some (.POP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14800 : decode code ⟨14800⟩ = some (.JUMP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have rd14786 := h.jumpiT hd14739 heq (uniswapV3PoolJumpDestPatched14786 hpatch) (by
    simp only [List.length_cons]
    omega)
  have rd14787 := by
    simpa using rd14786.jumpdest hd14786 (by
      simp only [List.length_cons]
      omega)
  have rd14788 := by
    simpa using rd14787.dup2 hd14787 (by
      simp only [List.length_cons]
      omega)
  have rd14789 := by
    simpa using rd14788.jumpdest hd14788 (by
      simp only [List.length_cons]
      omega)
  have rd14790 := by
    simpa using rd14789.swap10 hd14789 (by
      simp only [List.length_cons]
      omega)
  have rd14791 := by
    simpa using RD.swap9 rd14790 hd14790 (by
      simp only [List.length_cons]
      omega)
  have rd14792 := by
    simpa using rd14791.pop hd14791 (by
      simp only [List.length_cons]
      omega)
  have rd14793 := by
    simpa using rd14792.pop hd14792 (by
      simp only [List.length_cons]
      omega)
  have rd14794 := by
    simpa using rd14793.pop hd14793 (by
      simp only [List.length_cons]
      omega)
  have rd14795 := by
    simpa using rd14794.pop hd14794 (by
      simp only [List.length_cons]
      omega)
  have rd14796 := by
    simpa using rd14795.pop hd14795 (by
      simp only [List.length_cons]
      omega)
  have rd14797 := by
    simpa using rd14796.pop hd14796 (by
      simp only [List.length_cons]
      omega)
  have rd14798 := by
    simpa using rd14797.pop hd14797 (by
      simp only [List.length_cons]
      omega)
  have rd14799 := by
    simpa using rd14798.pop hd14798 (by
      simp only [List.length_cons]
      omega)
  have rd14800 := by
    simpa using rd14799.pop hd14799 (by
      simp only [List.length_cons]
      omega)
  have rd10793 := rd14800.jump hd14800 (uniswapV3PoolJumpDestPatched10793 hpatch) (by
    simp only [List.length_cons]
    omega)
  exact ⟨_, _, rd10793⟩

end Benchmarks.UniswapV3Pool
