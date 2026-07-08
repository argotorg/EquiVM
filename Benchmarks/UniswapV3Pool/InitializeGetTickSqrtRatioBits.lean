import Benchmarks.UniswapV3Pool.InitializeGetTickSqrtRatio

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.UniswapV3Pool

def getSqrtRatioBit4Word (absTick : UInt256) : UInt256 :=
  UInt256.land absTick ⟨4⟩

def getSqrtRatioFactor4Word : UInt256 :=
  ⟨340214320654664324051920982716015181260⟩

def getSqrtRatioAfterBit4Word (ratio : UInt256) : UInt256 :=
  UInt256.shiftRight (UInt256.mul getSqrtRatioFactor4Word ratio) ⟨128⟩

def getSqrtRatioBit8Word (absTick : UInt256) : UInt256 :=
  UInt256.land absTick ⟨8⟩

def getSqrtRatioFactor8Word : UInt256 :=
  ⟨340146287995602323631171512101879684304⟩

def getSqrtRatioAfterBit8Word (ratio : UInt256) : UInt256 :=
  UInt256.shiftRight (UInt256.mul getSqrtRatioFactor8Word ratio) ⟨128⟩

def getSqrtRatioBit16Word (absTick : UInt256) : UInt256 :=
  UInt256.land absTick ⟨16⟩

def getSqrtRatioFactor16Word : UInt256 :=
  ⟨340010263488231146823593991679159461444⟩

def getSqrtRatioAfterBit16Word (ratio : UInt256) : UInt256 :=
  UInt256.shiftRight (UInt256.mul getSqrtRatioFactor16Word ratio) ⟨128⟩

def getSqrtRatioBit32Word (absTick : UInt256) : UInt256 :=
  UInt256.land absTick ⟨32⟩

def getSqrtRatioFactor32Word : UInt256 :=
  ⟨339738377640345403697157401104375502016⟩

def getSqrtRatioAfterBit32Word (ratio : UInt256) : UInt256 :=
  UInt256.shiftRight (UInt256.mul getSqrtRatioFactor32Word ratio) ⟨128⟩

def getSqrtRatioBit64Word (absTick : UInt256) : UInt256 :=
  UInt256.land absTick ⟨64⟩

def getSqrtRatioFactor64Word : UInt256 :=
  ⟨339195258003219555707034227454543997025⟩

def getSqrtRatioAfterBit64Word (ratio : UInt256) : UInt256 :=
  UInt256.shiftRight (UInt256.mul getSqrtRatioFactor64Word ratio) ⟨128⟩

def getSqrtRatioBit128Word (absTick : UInt256) : UInt256 :=
  UInt256.land absTick ⟨128⟩

def getSqrtRatioFactor128Word : UInt256 :=
  ⟨338111622100601834656805679988414885971⟩

def getSqrtRatioAfterBit128Word (ratio : UInt256) : UInt256 :=
  UInt256.shiftRight (UInt256.mul getSqrtRatioFactor128Word ratio) ⟨128⟩

def getSqrtRatioBit256Word (absTick : UInt256) : UInt256 :=
  UInt256.land absTick ⟨256⟩

def getSqrtRatioFactor256Word : UInt256 :=
  ⟨335954724994790223023589805789778977700⟩

def getSqrtRatioAfterBit256Word (ratio : UInt256) : UInt256 :=
  UInt256.shiftRight (UInt256.mul getSqrtRatioFactor256Word ratio) ⟨128⟩

def getSqrtRatioBit512Word (absTick : UInt256) : UInt256 :=
  UInt256.land absTick ⟨512⟩

def getSqrtRatioFactor512Word : UInt256 :=
  ⟨331682121138379247127172139078559817300⟩

def getSqrtRatioAfterBit512Word (ratio : UInt256) : UInt256 :=
  UInt256.shiftRight (UInt256.mul getSqrtRatioFactor512Word ratio) ⟨128⟩

def getSqrtRatioBit1024Word (absTick : UInt256) : UInt256 :=
  UInt256.land absTick ⟨1024⟩

def getSqrtRatioFactor1024Word : UInt256 :=
  ⟨323299236684853023288211250268160618739⟩

def getSqrtRatioAfterBit1024Word (ratio : UInt256) : UInt256 :=
  UInt256.shiftRight (UInt256.mul getSqrtRatioFactor1024Word ratio) ⟨128⟩

private theorem uniswapV3PoolInitializePatchPreservesJumpDest11843 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨11843⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolInitializePatchPreservesJumpDest11874 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨11874⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolInitializePatchPreservesJumpDest11905 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨11905⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolInitializePatchPreservesJumpDest11936 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨11936⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolInitializePatchPreservesJumpDest11967 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨11967⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolInitializePatchPreservesJumpDest11998 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨11998⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolInitializePatchPreservesJumpDest12030 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨12030⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolInitializePatchPreservesJumpDest12062 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨12062⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolInitializePatchPreservesJumpDest12094 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨12094⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolJumpDestPatched11843 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨11843⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolInitializePatchPreservesJumpDest11843

theorem uniswapV3PoolJumpDestPatched11874 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨11874⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolInitializePatchPreservesJumpDest11874

theorem uniswapV3PoolJumpDestPatched11905 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨11905⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolInitializePatchPreservesJumpDest11905

theorem uniswapV3PoolJumpDestPatched11936 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨11936⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolInitializePatchPreservesJumpDest11936

theorem uniswapV3PoolJumpDestPatched11967 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨11967⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolInitializePatchPreservesJumpDest11967

theorem uniswapV3PoolJumpDestPatched11998 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨11998⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolInitializePatchPreservesJumpDest11998

theorem uniswapV3PoolJumpDestPatched12030 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨12030⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolInitializePatchPreservesJumpDest12030

theorem uniswapV3PoolJumpDestPatched12062 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨12062⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolInitializePatchPreservesJumpDest12062

theorem uniswapV3PoolJumpDestPatched12094 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨12094⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolInitializePatchPreservesJumpDest12094

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetSqrtRatioAtTickBit4Zero {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ratio absTick tick ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨11812⟩ (ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k C)
    (hbit : getSqrtRatioBit4Word absTick = ⟨0⟩)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨11843⟩ (ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 11629 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 13989) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 13989 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetSqrtRatioAtTick hlo hhi)]
  have hd11812 : decode code ⟨11812⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11813 : decode code ⟨11813⟩ = some (.Push .PUSH1, some (⟨4⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11815 : decode code ⟨11815⟩ = some (.DUP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11816 : decode code ⟨11816⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11817 : decode code ⟨11817⟩ = some (.ISZERO, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11818 : decode code ⟨11818⟩ = some (.Push .PUSH2, some (⟨11843⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11821 : decode code ⟨11821⟩ = some (.JUMPI, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hcond : UInt256.isZero (getSqrtRatioBit4Word absTick) ≠ ⟨0⟩ := by
    rw [hbit]
    native_decide
  have rd11813 := by
    simpa using h.jumpdest hd11812 (by
      simp only [List.length_cons]
      omega)
  have rd11815 := by
    simpa using rd11813.push1 ⟨4⟩ hd11813 (by
      simp only [List.length_cons]
      omega)
  have rd11816 := by
    simpa using rd11815.dup3 hd11815 (by
      simp only [List.length_cons]
      omega)
  have rd11817 := by
    simpa [getSqrtRatioBit4Word] using rd11816.and hd11816 (by
      simp only [List.length_cons]
      omega)
  have rd11818 := by
    simpa using rd11817.iszero hd11817 (by
      simp only [List.length_cons]
      omega)
  have rd11821 := by
    simpa using rd11818.push2 ⟨11843⟩ hd11818 (by
      simp only [List.length_cons]
      omega)
  exact ⟨_, _, rd11821.jumpiT hd11821 hcond (uniswapV3PoolJumpDestPatched11843 hpatch) (by
    simp only [List.length_cons]
    omega)⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetSqrtRatioAtTickBit4Set {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ratio absTick tick ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨11812⟩ (ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k C)
    (hbit : getSqrtRatioBit4Word absTick ≠ ⟨0⟩)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨11843⟩
      (getSqrtRatioAfterBit4Word ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 11629 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 13989) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 13989 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetSqrtRatioAtTick hlo hhi)]
  have hd11812 : decode code ⟨11812⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11813 : decode code ⟨11813⟩ = some (.Push .PUSH1, some (⟨4⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11815 : decode code ⟨11815⟩ = some (.DUP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11816 : decode code ⟨11816⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11817 : decode code ⟨11817⟩ = some (.ISZERO, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11818 : decode code ⟨11818⟩ = some (.Push .PUSH2, some (⟨11843⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11821 : decode code ⟨11821⟩ = some (.JUMPI, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11822 :
      decode code ⟨11822⟩ =
        some (.Push .PUSH16, some (⟨340214320654664324051920982716015181260⟩, 16)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11839 : decode code ⟨11839⟩ = some (.MUL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11840 : decode code ⟨11840⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11842 : decode code ⟨11842⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hcond : UInt256.isZero (getSqrtRatioBit4Word absTick) = ⟨0⟩ :=
    isZero_eq_zero_of_ne hbit
  have rd11813 := by
    simpa using h.jumpdest hd11812 (by
      simp only [List.length_cons]
      omega)
  have rd11815 := by
    simpa using rd11813.push1 ⟨4⟩ hd11813 (by
      simp only [List.length_cons]
      omega)
  have rd11816 := by
    simpa using rd11815.dup3 hd11815 (by
      simp only [List.length_cons]
      omega)
  have rd11817 := by
    simpa [getSqrtRatioBit4Word] using rd11816.and hd11816 (by
      simp only [List.length_cons]
      omega)
  have rd11818 := by
    simpa using rd11817.iszero hd11817 (by
      simp only [List.length_cons]
      omega)
  have rd11821 := by
    simpa using rd11818.push2 ⟨11843⟩ hd11818 (by
      simp only [List.length_cons]
      omega)
  have rd11822 := rd11821.jumpiNT hd11821 hcond (by
    simp only [List.length_cons]
    omega)
  have rd11839 := by
    simpa [getSqrtRatioFactor4Word] using
      rd11822.pushConst (⟨340214320654664324051920982716015181260⟩ : UInt256)
        (by native_decide : Operation.POp.PUSH16 ≠ .PUSH0) hd11822 (by
          simp only [List.length_cons]
          omega)
  have rd11840 := by
    simpa using rd11839.mul hd11839 (by
      simp only [List.length_cons]
      omega)
  have rd11842 := by
    simpa using rd11840.push1 ⟨128⟩ hd11840 (by
      simp only [List.length_cons]
      omega)
  have rd11843 := by
    simpa [getSqrtRatioAfterBit4Word, getSqrtRatioFactor4Word] using rd11842.shr hd11842
      (by
        simp only [List.length_cons]
        omega)
  exact ⟨_, _, by simpa using rd11843⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetSqrtRatioAtTickBit8Zero {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ratio absTick tick ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨11843⟩ (ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k C)
    (hbit : getSqrtRatioBit8Word absTick = ⟨0⟩)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨11874⟩ (ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 11629 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 13989) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 13989 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetSqrtRatioAtTick hlo hhi)]
  have hd11843 : decode code ⟨11843⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11844 : decode code ⟨11844⟩ = some (.Push .PUSH1, some (⟨8⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11846 : decode code ⟨11846⟩ = some (.DUP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11847 : decode code ⟨11847⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11848 : decode code ⟨11848⟩ = some (.ISZERO, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11849 : decode code ⟨11849⟩ = some (.Push .PUSH2, some (⟨11874⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11852 : decode code ⟨11852⟩ = some (.JUMPI, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hcond : UInt256.isZero (getSqrtRatioBit8Word absTick) ≠ ⟨0⟩ := by
    rw [hbit]
    native_decide
  have rd11844 := by
    simpa using h.jumpdest hd11843 (by
      simp only [List.length_cons]
      omega)
  have rd11846 := by
    simpa using rd11844.push1 ⟨8⟩ hd11844 (by
      simp only [List.length_cons]
      omega)
  have rd11847 := by
    simpa using rd11846.dup3 hd11846 (by
      simp only [List.length_cons]
      omega)
  have rd11848 := by
    simpa [getSqrtRatioBit8Word] using rd11847.and hd11847 (by
      simp only [List.length_cons]
      omega)
  have rd11849 := by
    simpa using rd11848.iszero hd11848 (by
      simp only [List.length_cons]
      omega)
  have rd11852 := by
    simpa using rd11849.push2 ⟨11874⟩ hd11849 (by
      simp only [List.length_cons]
      omega)
  exact ⟨_, _, rd11852.jumpiT hd11852 hcond (uniswapV3PoolJumpDestPatched11874 hpatch) (by
    simp only [List.length_cons]
    omega)⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetSqrtRatioAtTickBit8Set {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ratio absTick tick ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨11843⟩ (ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k C)
    (hbit : getSqrtRatioBit8Word absTick ≠ ⟨0⟩)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨11874⟩
      (getSqrtRatioAfterBit8Word ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 11629 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 13989) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 13989 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetSqrtRatioAtTick hlo hhi)]
  have hd11843 : decode code ⟨11843⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11844 : decode code ⟨11844⟩ = some (.Push .PUSH1, some (⟨8⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11846 : decode code ⟨11846⟩ = some (.DUP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11847 : decode code ⟨11847⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11848 : decode code ⟨11848⟩ = some (.ISZERO, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11849 : decode code ⟨11849⟩ = some (.Push .PUSH2, some (⟨11874⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11852 : decode code ⟨11852⟩ = some (.JUMPI, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11853 :
      decode code ⟨11853⟩ =
        some (.Push .PUSH16, some (⟨340146287995602323631171512101879684304⟩, 16)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11870 : decode code ⟨11870⟩ = some (.MUL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11871 : decode code ⟨11871⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11873 : decode code ⟨11873⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hcond : UInt256.isZero (getSqrtRatioBit8Word absTick) = ⟨0⟩ :=
    isZero_eq_zero_of_ne hbit
  have rd11844 := by
    simpa using h.jumpdest hd11843 (by
      simp only [List.length_cons]
      omega)
  have rd11846 := by
    simpa using rd11844.push1 ⟨8⟩ hd11844 (by
      simp only [List.length_cons]
      omega)
  have rd11847 := by
    simpa using rd11846.dup3 hd11846 (by
      simp only [List.length_cons]
      omega)
  have rd11848 := by
    simpa [getSqrtRatioBit8Word] using rd11847.and hd11847 (by
      simp only [List.length_cons]
      omega)
  have rd11849 := by
    simpa using rd11848.iszero hd11848 (by
      simp only [List.length_cons]
      omega)
  have rd11852 := by
    simpa using rd11849.push2 ⟨11874⟩ hd11849 (by
      simp only [List.length_cons]
      omega)
  have rd11853 := rd11852.jumpiNT hd11852 hcond (by
    simp only [List.length_cons]
    omega)
  have rd11870 := by
    simpa [getSqrtRatioFactor8Word] using
      rd11853.pushConst (⟨340146287995602323631171512101879684304⟩ : UInt256)
        (by native_decide : Operation.POp.PUSH16 ≠ .PUSH0) hd11853 (by
          simp only [List.length_cons]
          omega)
  have rd11871 := by
    simpa using rd11870.mul hd11870 (by
      simp only [List.length_cons]
      omega)
  have rd11873 := by
    simpa using rd11871.push1 ⟨128⟩ hd11871 (by
      simp only [List.length_cons]
      omega)
  have rd11874 := by
    simpa [getSqrtRatioAfterBit8Word, getSqrtRatioFactor8Word] using rd11873.shr hd11873
      (by
        simp only [List.length_cons]
        omega)
  exact ⟨_, _, by simpa using rd11874⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetSqrtRatioAtTickBit16Zero {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ratio absTick tick ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨11874⟩ (ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k C)
    (hbit : getSqrtRatioBit16Word absTick = ⟨0⟩)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨11905⟩ (ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 11629 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 13989) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 13989 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetSqrtRatioAtTick hlo hhi)]
  have hd11874 : decode code ⟨11874⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11875 : decode code ⟨11875⟩ = some (.Push .PUSH1, some (⟨16⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11877 : decode code ⟨11877⟩ = some (.DUP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11878 : decode code ⟨11878⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11879 : decode code ⟨11879⟩ = some (.ISZERO, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11880 : decode code ⟨11880⟩ = some (.Push .PUSH2, some (⟨11905⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11883 : decode code ⟨11883⟩ = some (.JUMPI, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hcond : UInt256.isZero (getSqrtRatioBit16Word absTick) ≠ ⟨0⟩ := by
    rw [hbit]
    native_decide
  have rd11875 := by
    simpa using h.jumpdest hd11874 (by
      simp only [List.length_cons]
      omega)
  have rd11877 := by
    simpa using rd11875.push1 ⟨16⟩ hd11875 (by
      simp only [List.length_cons]
      omega)
  have rd11878 := by
    simpa using rd11877.dup3 hd11877 (by
      simp only [List.length_cons]
      omega)
  have rd11879 := by
    simpa [getSqrtRatioBit16Word] using rd11878.and hd11878 (by
      simp only [List.length_cons]
      omega)
  have rd11880 := by
    simpa using rd11879.iszero hd11879 (by
      simp only [List.length_cons]
      omega)
  have rd11883 := by
    simpa using rd11880.push2 ⟨11905⟩ hd11880 (by
      simp only [List.length_cons]
      omega)
  exact ⟨_, _, rd11883.jumpiT hd11883 hcond (uniswapV3PoolJumpDestPatched11905 hpatch) (by
    simp only [List.length_cons]
    omega)⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetSqrtRatioAtTickBit16Set {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ratio absTick tick ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨11874⟩ (ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k C)
    (hbit : getSqrtRatioBit16Word absTick ≠ ⟨0⟩)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨11905⟩
      (getSqrtRatioAfterBit16Word ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 11629 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 13989) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 13989 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetSqrtRatioAtTick hlo hhi)]
  have hd11874 : decode code ⟨11874⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11875 : decode code ⟨11875⟩ = some (.Push .PUSH1, some (⟨16⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11877 : decode code ⟨11877⟩ = some (.DUP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11878 : decode code ⟨11878⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11879 : decode code ⟨11879⟩ = some (.ISZERO, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11880 : decode code ⟨11880⟩ = some (.Push .PUSH2, some (⟨11905⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11883 : decode code ⟨11883⟩ = some (.JUMPI, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11884 :
      decode code ⟨11884⟩ =
        some (.Push .PUSH16, some (⟨340010263488231146823593991679159461444⟩, 16)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11901 : decode code ⟨11901⟩ = some (.MUL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11902 : decode code ⟨11902⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11904 : decode code ⟨11904⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hcond : UInt256.isZero (getSqrtRatioBit16Word absTick) = ⟨0⟩ :=
    isZero_eq_zero_of_ne hbit
  have rd11875 := by
    simpa using h.jumpdest hd11874 (by
      simp only [List.length_cons]
      omega)
  have rd11877 := by
    simpa using rd11875.push1 ⟨16⟩ hd11875 (by
      simp only [List.length_cons]
      omega)
  have rd11878 := by
    simpa using rd11877.dup3 hd11877 (by
      simp only [List.length_cons]
      omega)
  have rd11879 := by
    simpa [getSqrtRatioBit16Word] using rd11878.and hd11878 (by
      simp only [List.length_cons]
      omega)
  have rd11880 := by
    simpa using rd11879.iszero hd11879 (by
      simp only [List.length_cons]
      omega)
  have rd11883 := by
    simpa using rd11880.push2 ⟨11905⟩ hd11880 (by
      simp only [List.length_cons]
      omega)
  have rd11884 := rd11883.jumpiNT hd11883 hcond (by
    simp only [List.length_cons]
    omega)
  have rd11901 := by
    simpa [getSqrtRatioFactor16Word] using
      rd11884.pushConst (⟨340010263488231146823593991679159461444⟩ : UInt256)
        (by native_decide : Operation.POp.PUSH16 ≠ .PUSH0) hd11884 (by
          simp only [List.length_cons]
          omega)
  have rd11902 := by
    simpa using rd11901.mul hd11901 (by
      simp only [List.length_cons]
      omega)
  have rd11904 := by
    simpa using rd11902.push1 ⟨128⟩ hd11902 (by
      simp only [List.length_cons]
      omega)
  have rd11905 := by
    simpa [getSqrtRatioAfterBit16Word, getSqrtRatioFactor16Word] using
      rd11904.shr hd11904 (by
        simp only [List.length_cons]
        omega)
  exact ⟨_, _, by simpa using rd11905⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetSqrtRatioAtTickBit32Zero {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ratio absTick tick ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨11905⟩ (ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k C)
    (hbit : getSqrtRatioBit32Word absTick = ⟨0⟩)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨11936⟩ (ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 11629 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 13989) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 13989 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetSqrtRatioAtTick hlo hhi)]
  have hd11905 : decode code ⟨11905⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11906 : decode code ⟨11906⟩ = some (.Push .PUSH1, some (⟨32⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11908 : decode code ⟨11908⟩ = some (.DUP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11909 : decode code ⟨11909⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11910 : decode code ⟨11910⟩ = some (.ISZERO, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11911 : decode code ⟨11911⟩ = some (.Push .PUSH2, some (⟨11936⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11914 : decode code ⟨11914⟩ = some (.JUMPI, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hcond : UInt256.isZero (getSqrtRatioBit32Word absTick) ≠ ⟨0⟩ := by
    rw [hbit]
    native_decide
  have rd11906 := by
    simpa using h.jumpdest hd11905 (by
      simp only [List.length_cons]
      omega)
  have rd11908 := by
    simpa using rd11906.push1 ⟨32⟩ hd11906 (by
      simp only [List.length_cons]
      omega)
  have rd11909 := by
    simpa using rd11908.dup3 hd11908 (by
      simp only [List.length_cons]
      omega)
  have rd11910 := by
    simpa [getSqrtRatioBit32Word] using rd11909.and hd11909 (by
      simp only [List.length_cons]
      omega)
  have rd11911 := by
    simpa using rd11910.iszero hd11910 (by
      simp only [List.length_cons]
      omega)
  have rd11914 := by
    simpa using rd11911.push2 ⟨11936⟩ hd11911 (by
      simp only [List.length_cons]
      omega)
  exact ⟨_, _, rd11914.jumpiT hd11914 hcond (uniswapV3PoolJumpDestPatched11936 hpatch) (by
    simp only [List.length_cons]
    omega)⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetSqrtRatioAtTickBit32Set {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ratio absTick tick ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨11905⟩ (ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k C)
    (hbit : getSqrtRatioBit32Word absTick ≠ ⟨0⟩)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨11936⟩
      (getSqrtRatioAfterBit32Word ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 11629 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 13989) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 13989 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetSqrtRatioAtTick hlo hhi)]
  have hd11905 : decode code ⟨11905⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11906 : decode code ⟨11906⟩ = some (.Push .PUSH1, some (⟨32⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11908 : decode code ⟨11908⟩ = some (.DUP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11909 : decode code ⟨11909⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11910 : decode code ⟨11910⟩ = some (.ISZERO, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11911 : decode code ⟨11911⟩ = some (.Push .PUSH2, some (⟨11936⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11914 : decode code ⟨11914⟩ = some (.JUMPI, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11915 :
      decode code ⟨11915⟩ =
        some (.Push .PUSH16, some (⟨339738377640345403697157401104375502016⟩, 16)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11932 : decode code ⟨11932⟩ = some (.MUL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11933 : decode code ⟨11933⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11935 : decode code ⟨11935⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hcond : UInt256.isZero (getSqrtRatioBit32Word absTick) = ⟨0⟩ :=
    isZero_eq_zero_of_ne hbit
  have rd11906 := by
    simpa using h.jumpdest hd11905 (by
      simp only [List.length_cons]
      omega)
  have rd11908 := by
    simpa using rd11906.push1 ⟨32⟩ hd11906 (by
      simp only [List.length_cons]
      omega)
  have rd11909 := by
    simpa using rd11908.dup3 hd11908 (by
      simp only [List.length_cons]
      omega)
  have rd11910 := by
    simpa [getSqrtRatioBit32Word] using rd11909.and hd11909 (by
      simp only [List.length_cons]
      omega)
  have rd11911 := by
    simpa using rd11910.iszero hd11910 (by
      simp only [List.length_cons]
      omega)
  have rd11914 := by
    simpa using rd11911.push2 ⟨11936⟩ hd11911 (by
      simp only [List.length_cons]
      omega)
  have rd11915 := rd11914.jumpiNT hd11914 hcond (by
    simp only [List.length_cons]
    omega)
  have rd11932 := by
    simpa [getSqrtRatioFactor32Word] using
      rd11915.pushConst (⟨339738377640345403697157401104375502016⟩ : UInt256)
        (by native_decide : Operation.POp.PUSH16 ≠ .PUSH0) hd11915 (by
          simp only [List.length_cons]
          omega)
  have rd11933 := by
    simpa using rd11932.mul hd11932 (by
      simp only [List.length_cons]
      omega)
  have rd11935 := by
    simpa using rd11933.push1 ⟨128⟩ hd11933 (by
      simp only [List.length_cons]
      omega)
  have rd11936 := by
    simpa [getSqrtRatioAfterBit32Word, getSqrtRatioFactor32Word] using
      rd11935.shr hd11935 (by
        simp only [List.length_cons]
        omega)
  exact ⟨_, _, by simpa using rd11936⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetSqrtRatioAtTickBit64Zero {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ratio absTick tick ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨11936⟩ (ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k C)
    (hbit : getSqrtRatioBit64Word absTick = ⟨0⟩)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨11967⟩ (ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 11629 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 13989) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 13989 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetSqrtRatioAtTick hlo hhi)]
  have hd11936 : decode code ⟨11936⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11937 : decode code ⟨11937⟩ = some (.Push .PUSH1, some (⟨64⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11939 : decode code ⟨11939⟩ = some (.DUP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11940 : decode code ⟨11940⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11941 : decode code ⟨11941⟩ = some (.ISZERO, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11942 : decode code ⟨11942⟩ = some (.Push .PUSH2, some (⟨11967⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11945 : decode code ⟨11945⟩ = some (.JUMPI, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hcond : UInt256.isZero (getSqrtRatioBit64Word absTick) ≠ ⟨0⟩ := by
    rw [hbit]
    native_decide
  have rd11937 := by
    simpa using h.jumpdest hd11936 (by
      simp only [List.length_cons]
      omega)
  have rd11939 := by
    simpa using rd11937.push1 ⟨64⟩ hd11937 (by
      simp only [List.length_cons]
      omega)
  have rd11940 := by
    simpa using rd11939.dup3 hd11939 (by
      simp only [List.length_cons]
      omega)
  have rd11941 := by
    simpa [getSqrtRatioBit64Word] using rd11940.and hd11940 (by
      simp only [List.length_cons]
      omega)
  have rd11942 := by
    simpa using rd11941.iszero hd11941 (by
      simp only [List.length_cons]
      omega)
  have rd11945 := by
    simpa using rd11942.push2 ⟨11967⟩ hd11942 (by
      simp only [List.length_cons]
      omega)
  exact ⟨_, _, rd11945.jumpiT hd11945 hcond (uniswapV3PoolJumpDestPatched11967 hpatch) (by
    simp only [List.length_cons]
    omega)⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetSqrtRatioAtTickBit64Set {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ratio absTick tick ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨11936⟩ (ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k C)
    (hbit : getSqrtRatioBit64Word absTick ≠ ⟨0⟩)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨11967⟩
      (getSqrtRatioAfterBit64Word ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 11629 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 13989) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 13989 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetSqrtRatioAtTick hlo hhi)]
  have hd11936 : decode code ⟨11936⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11937 : decode code ⟨11937⟩ = some (.Push .PUSH1, some (⟨64⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11939 : decode code ⟨11939⟩ = some (.DUP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11940 : decode code ⟨11940⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11941 : decode code ⟨11941⟩ = some (.ISZERO, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11942 : decode code ⟨11942⟩ = some (.Push .PUSH2, some (⟨11967⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11945 : decode code ⟨11945⟩ = some (.JUMPI, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11946 :
      decode code ⟨11946⟩ =
        some (.Push .PUSH16, some (⟨339195258003219555707034227454543997025⟩, 16)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11963 : decode code ⟨11963⟩ = some (.MUL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11964 : decode code ⟨11964⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11966 : decode code ⟨11966⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hcond : UInt256.isZero (getSqrtRatioBit64Word absTick) = ⟨0⟩ :=
    isZero_eq_zero_of_ne hbit
  have rd11937 := by
    simpa using h.jumpdest hd11936 (by
      simp only [List.length_cons]
      omega)
  have rd11939 := by
    simpa using rd11937.push1 ⟨64⟩ hd11937 (by
      simp only [List.length_cons]
      omega)
  have rd11940 := by
    simpa using rd11939.dup3 hd11939 (by
      simp only [List.length_cons]
      omega)
  have rd11941 := by
    simpa [getSqrtRatioBit64Word] using rd11940.and hd11940 (by
      simp only [List.length_cons]
      omega)
  have rd11942 := by
    simpa using rd11941.iszero hd11941 (by
      simp only [List.length_cons]
      omega)
  have rd11945 := by
    simpa using rd11942.push2 ⟨11967⟩ hd11942 (by
      simp only [List.length_cons]
      omega)
  have rd11946 := rd11945.jumpiNT hd11945 hcond (by
    simp only [List.length_cons]
    omega)
  have rd11963 := by
    simpa [getSqrtRatioFactor64Word] using
      rd11946.pushConst (⟨339195258003219555707034227454543997025⟩ : UInt256)
        (by native_decide : Operation.POp.PUSH16 ≠ .PUSH0) hd11946 (by
          simp only [List.length_cons]
          omega)
  have rd11964 := by
    simpa using rd11963.mul hd11963 (by
      simp only [List.length_cons]
      omega)
  have rd11966 := by
    simpa using rd11964.push1 ⟨128⟩ hd11964 (by
      simp only [List.length_cons]
      omega)
  have rd11967 := by
    simpa [getSqrtRatioAfterBit64Word, getSqrtRatioFactor64Word] using
      rd11966.shr hd11966 (by
        simp only [List.length_cons]
        omega)
  exact ⟨_, _, by simpa using rd11967⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetSqrtRatioAtTickBit128Zero {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ratio absTick tick ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨11967⟩ (ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k C)
    (hbit : getSqrtRatioBit128Word absTick = ⟨0⟩)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨11998⟩ (ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 11629 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 13989) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 13989 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetSqrtRatioAtTick hlo hhi)]
  have hd11967 : decode code ⟨11967⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11968 : decode code ⟨11968⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11970 : decode code ⟨11970⟩ = some (.DUP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11971 : decode code ⟨11971⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11972 : decode code ⟨11972⟩ = some (.ISZERO, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11973 : decode code ⟨11973⟩ = some (.Push .PUSH2, some (⟨11998⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11976 : decode code ⟨11976⟩ = some (.JUMPI, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hcond : UInt256.isZero (getSqrtRatioBit128Word absTick) ≠ ⟨0⟩ := by
    rw [hbit]
    native_decide
  have rd11968 := by
    simpa using h.jumpdest hd11967 (by
      simp only [List.length_cons]
      omega)
  have rd11970 := by
    simpa using rd11968.push1 ⟨128⟩ hd11968 (by
      simp only [List.length_cons]
      omega)
  have rd11971 := by
    simpa using rd11970.dup3 hd11970 (by
      simp only [List.length_cons]
      omega)
  have rd11972 := by
    simpa [getSqrtRatioBit128Word] using rd11971.and hd11971 (by
      simp only [List.length_cons]
      omega)
  have rd11973 := by
    simpa using rd11972.iszero hd11972 (by
      simp only [List.length_cons]
      omega)
  have rd11976 := by
    simpa using rd11973.push2 ⟨11998⟩ hd11973 (by
      simp only [List.length_cons]
      omega)
  exact ⟨_, _, rd11976.jumpiT hd11976 hcond (uniswapV3PoolJumpDestPatched11998 hpatch) (by
    simp only [List.length_cons]
    omega)⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetSqrtRatioAtTickBit128Set {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ratio absTick tick ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨11967⟩ (ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k C)
    (hbit : getSqrtRatioBit128Word absTick ≠ ⟨0⟩)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨11998⟩
      (getSqrtRatioAfterBit128Word ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 11629 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 13989) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 13989 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetSqrtRatioAtTick hlo hhi)]
  have hd11967 : decode code ⟨11967⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11968 : decode code ⟨11968⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11970 : decode code ⟨11970⟩ = some (.DUP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11971 : decode code ⟨11971⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11972 : decode code ⟨11972⟩ = some (.ISZERO, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11973 : decode code ⟨11973⟩ = some (.Push .PUSH2, some (⟨11998⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11976 : decode code ⟨11976⟩ = some (.JUMPI, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11977 :
      decode code ⟨11977⟩ =
        some (.Push .PUSH16, some (⟨338111622100601834656805679988414885971⟩, 16)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11994 : decode code ⟨11994⟩ = some (.MUL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11995 : decode code ⟨11995⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11997 : decode code ⟨11997⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hcond : UInt256.isZero (getSqrtRatioBit128Word absTick) = ⟨0⟩ :=
    isZero_eq_zero_of_ne hbit
  have rd11968 := by
    simpa using h.jumpdest hd11967 (by
      simp only [List.length_cons]
      omega)
  have rd11970 := by
    simpa using rd11968.push1 ⟨128⟩ hd11968 (by
      simp only [List.length_cons]
      omega)
  have rd11971 := by
    simpa using rd11970.dup3 hd11970 (by
      simp only [List.length_cons]
      omega)
  have rd11972 := by
    simpa [getSqrtRatioBit128Word] using rd11971.and hd11971 (by
      simp only [List.length_cons]
      omega)
  have rd11973 := by
    simpa using rd11972.iszero hd11972 (by
      simp only [List.length_cons]
      omega)
  have rd11976 := by
    simpa using rd11973.push2 ⟨11998⟩ hd11973 (by
      simp only [List.length_cons]
      omega)
  have rd11977 := rd11976.jumpiNT hd11976 hcond (by
    simp only [List.length_cons]
    omega)
  have rd11994 := by
    simpa [getSqrtRatioFactor128Word] using
      rd11977.pushConst (⟨338111622100601834656805679988414885971⟩ : UInt256)
        (by native_decide : Operation.POp.PUSH16 ≠ .PUSH0) hd11977 (by
          simp only [List.length_cons]
          omega)
  have rd11995 := by
    simpa using rd11994.mul hd11994 (by
      simp only [List.length_cons]
      omega)
  have rd11997 := by
    simpa using rd11995.push1 ⟨128⟩ hd11995 (by
      simp only [List.length_cons]
      omega)
  have rd11998 := by
    simpa [getSqrtRatioAfterBit128Word, getSqrtRatioFactor128Word] using
      rd11997.shr hd11997 (by
        simp only [List.length_cons]
        omega)
  exact ⟨_, _, by simpa using rd11998⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetSqrtRatioAtTickBit256Zero {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ratio absTick tick ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨11998⟩ (ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k C)
    (hbit : getSqrtRatioBit256Word absTick = ⟨0⟩)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨12030⟩ (ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 11629 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 13989) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 13989 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetSqrtRatioAtTick hlo hhi)]
  have hd11998 : decode code ⟨11998⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11999 : decode code ⟨11999⟩ = some (.Push .PUSH2, some (⟨256⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12002 : decode code ⟨12002⟩ = some (.DUP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12003 : decode code ⟨12003⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12004 : decode code ⟨12004⟩ = some (.ISZERO, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12005 : decode code ⟨12005⟩ = some (.Push .PUSH2, some (⟨12030⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12008 : decode code ⟨12008⟩ = some (.JUMPI, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hcond : UInt256.isZero (getSqrtRatioBit256Word absTick) ≠ ⟨0⟩ := by
    rw [hbit]
    native_decide
  have rd11999 := by
    simpa using h.jumpdest hd11998 (by
      simp only [List.length_cons]
      omega)
  have rd12002 := by
    simpa using rd11999.push2 ⟨256⟩ hd11999 (by
      simp only [List.length_cons]
      omega)
  have rd12003 := by
    simpa using rd12002.dup3 hd12002 (by
      simp only [List.length_cons]
      omega)
  have rd12004 := by
    simpa [getSqrtRatioBit256Word] using rd12003.and hd12003 (by
      simp only [List.length_cons]
      omega)
  have rd12005 := by
    simpa using rd12004.iszero hd12004 (by
      simp only [List.length_cons]
      omega)
  have rd12008 := by
    simpa using rd12005.push2 ⟨12030⟩ hd12005 (by
      simp only [List.length_cons]
      omega)
  exact ⟨_, _, rd12008.jumpiT hd12008 hcond (uniswapV3PoolJumpDestPatched12030 hpatch) (by
    simp only [List.length_cons]
    omega)⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetSqrtRatioAtTickBit256Set {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ratio absTick tick ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨11998⟩ (ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k C)
    (hbit : getSqrtRatioBit256Word absTick ≠ ⟨0⟩)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨12030⟩
      (getSqrtRatioAfterBit256Word ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 11629 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 13989) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 13989 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetSqrtRatioAtTick hlo hhi)]
  have hd11998 : decode code ⟨11998⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd11999 : decode code ⟨11999⟩ = some (.Push .PUSH2, some (⟨256⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12002 : decode code ⟨12002⟩ = some (.DUP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12003 : decode code ⟨12003⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12004 : decode code ⟨12004⟩ = some (.ISZERO, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12005 : decode code ⟨12005⟩ = some (.Push .PUSH2, some (⟨12030⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12008 : decode code ⟨12008⟩ = some (.JUMPI, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12009 :
      decode code ⟨12009⟩ =
        some (.Push .PUSH16, some (⟨335954724994790223023589805789778977700⟩, 16)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12026 : decode code ⟨12026⟩ = some (.MUL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12027 : decode code ⟨12027⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12029 : decode code ⟨12029⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hcond : UInt256.isZero (getSqrtRatioBit256Word absTick) = ⟨0⟩ :=
    isZero_eq_zero_of_ne hbit
  have rd11999 := by
    simpa using h.jumpdest hd11998 (by
      simp only [List.length_cons]
      omega)
  have rd12002 := by
    simpa using rd11999.push2 ⟨256⟩ hd11999 (by
      simp only [List.length_cons]
      omega)
  have rd12003 := by
    simpa using rd12002.dup3 hd12002 (by
      simp only [List.length_cons]
      omega)
  have rd12004 := by
    simpa [getSqrtRatioBit256Word] using rd12003.and hd12003 (by
      simp only [List.length_cons]
      omega)
  have rd12005 := by
    simpa using rd12004.iszero hd12004 (by
      simp only [List.length_cons]
      omega)
  have rd12008 := by
    simpa using rd12005.push2 ⟨12030⟩ hd12005 (by
      simp only [List.length_cons]
      omega)
  have rd12009 := rd12008.jumpiNT hd12008 hcond (by
    simp only [List.length_cons]
    omega)
  have rd12026 := by
    simpa [getSqrtRatioFactor256Word] using
      rd12009.pushConst (⟨335954724994790223023589805789778977700⟩ : UInt256)
        (by native_decide : Operation.POp.PUSH16 ≠ .PUSH0) hd12009 (by
          simp only [List.length_cons]
          omega)
  have rd12027 := by
    simpa using rd12026.mul hd12026 (by
      simp only [List.length_cons]
      omega)
  have rd12029 := by
    simpa using rd12027.push1 ⟨128⟩ hd12027 (by
      simp only [List.length_cons]
      omega)
  have rd12030 := by
    simpa [getSqrtRatioAfterBit256Word, getSqrtRatioFactor256Word] using
      rd12029.shr hd12029 (by
        simp only [List.length_cons]
        omega)
  exact ⟨_, _, by simpa using rd12030⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetSqrtRatioAtTickBit512Zero {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ratio absTick tick ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨12030⟩ (ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k C)
    (hbit : getSqrtRatioBit512Word absTick = ⟨0⟩)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨12062⟩ (ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 11629 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 13989) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 13989 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetSqrtRatioAtTick hlo hhi)]
  have hd12030 : decode code ⟨12030⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12031 : decode code ⟨12031⟩ = some (.Push .PUSH2, some (⟨512⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12034 : decode code ⟨12034⟩ = some (.DUP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12035 : decode code ⟨12035⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12036 : decode code ⟨12036⟩ = some (.ISZERO, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12037 : decode code ⟨12037⟩ = some (.Push .PUSH2, some (⟨12062⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12040 : decode code ⟨12040⟩ = some (.JUMPI, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hcond : UInt256.isZero (getSqrtRatioBit512Word absTick) ≠ ⟨0⟩ := by
    rw [hbit]
    native_decide
  have rd12031 := by
    simpa using h.jumpdest hd12030 (by
      simp only [List.length_cons]
      omega)
  have rd12034 := by
    simpa using rd12031.push2 ⟨512⟩ hd12031 (by
      simp only [List.length_cons]
      omega)
  have rd12035 := by
    simpa using rd12034.dup3 hd12034 (by
      simp only [List.length_cons]
      omega)
  have rd12036 := by
    simpa [getSqrtRatioBit512Word] using rd12035.and hd12035 (by
      simp only [List.length_cons]
      omega)
  have rd12037 := by
    simpa using rd12036.iszero hd12036 (by
      simp only [List.length_cons]
      omega)
  have rd12040 := by
    simpa using rd12037.push2 ⟨12062⟩ hd12037 (by
      simp only [List.length_cons]
      omega)
  exact ⟨_, _, rd12040.jumpiT hd12040 hcond (uniswapV3PoolJumpDestPatched12062 hpatch) (by
    simp only [List.length_cons]
    omega)⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetSqrtRatioAtTickBit512Set {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ratio absTick tick ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨12030⟩ (ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k C)
    (hbit : getSqrtRatioBit512Word absTick ≠ ⟨0⟩)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨12062⟩
      (getSqrtRatioAfterBit512Word ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 11629 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 13989) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 13989 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetSqrtRatioAtTick hlo hhi)]
  have hd12030 : decode code ⟨12030⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12031 : decode code ⟨12031⟩ = some (.Push .PUSH2, some (⟨512⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12034 : decode code ⟨12034⟩ = some (.DUP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12035 : decode code ⟨12035⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12036 : decode code ⟨12036⟩ = some (.ISZERO, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12037 : decode code ⟨12037⟩ = some (.Push .PUSH2, some (⟨12062⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12040 : decode code ⟨12040⟩ = some (.JUMPI, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12041 :
      decode code ⟨12041⟩ =
        some (.Push .PUSH16, some (⟨331682121138379247127172139078559817300⟩, 16)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12058 : decode code ⟨12058⟩ = some (.MUL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12059 : decode code ⟨12059⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12061 : decode code ⟨12061⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hcond : UInt256.isZero (getSqrtRatioBit512Word absTick) = ⟨0⟩ :=
    isZero_eq_zero_of_ne hbit
  have rd12031 := by
    simpa using h.jumpdest hd12030 (by
      simp only [List.length_cons]
      omega)
  have rd12034 := by
    simpa using rd12031.push2 ⟨512⟩ hd12031 (by
      simp only [List.length_cons]
      omega)
  have rd12035 := by
    simpa using rd12034.dup3 hd12034 (by
      simp only [List.length_cons]
      omega)
  have rd12036 := by
    simpa [getSqrtRatioBit512Word] using rd12035.and hd12035 (by
      simp only [List.length_cons]
      omega)
  have rd12037 := by
    simpa using rd12036.iszero hd12036 (by
      simp only [List.length_cons]
      omega)
  have rd12040 := by
    simpa using rd12037.push2 ⟨12062⟩ hd12037 (by
      simp only [List.length_cons]
      omega)
  have rd12041 := rd12040.jumpiNT hd12040 hcond (by
    simp only [List.length_cons]
    omega)
  have rd12058 := by
    simpa [getSqrtRatioFactor512Word] using
      rd12041.pushConst (⟨331682121138379247127172139078559817300⟩ : UInt256)
        (by native_decide : Operation.POp.PUSH16 ≠ .PUSH0) hd12041 (by
          simp only [List.length_cons]
          omega)
  have rd12059 := by
    simpa using rd12058.mul hd12058 (by
      simp only [List.length_cons]
      omega)
  have rd12061 := by
    simpa using rd12059.push1 ⟨128⟩ hd12059 (by
      simp only [List.length_cons]
      omega)
  have rd12062 := by
    simpa [getSqrtRatioAfterBit512Word, getSqrtRatioFactor512Word] using
      rd12061.shr hd12061 (by
        simp only [List.length_cons]
        omega)
  exact ⟨_, _, by simpa using rd12062⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetSqrtRatioAtTickBit1024Zero {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ratio absTick tick ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨12062⟩ (ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k C)
    (hbit : getSqrtRatioBit1024Word absTick = ⟨0⟩)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨12094⟩ (ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 11629 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 13989) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 13989 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetSqrtRatioAtTick hlo hhi)]
  have hd12062 : decode code ⟨12062⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12063 : decode code ⟨12063⟩ = some (.Push .PUSH2, some (⟨1024⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12066 : decode code ⟨12066⟩ = some (.DUP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12067 : decode code ⟨12067⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12068 : decode code ⟨12068⟩ = some (.ISZERO, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12069 : decode code ⟨12069⟩ = some (.Push .PUSH2, some (⟨12094⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12072 : decode code ⟨12072⟩ = some (.JUMPI, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hcond : UInt256.isZero (getSqrtRatioBit1024Word absTick) ≠ ⟨0⟩ := by
    rw [hbit]
    native_decide
  have rd12063 := by
    simpa using h.jumpdest hd12062 (by
      simp only [List.length_cons]
      omega)
  have rd12066 := by
    simpa using rd12063.push2 ⟨1024⟩ hd12063 (by
      simp only [List.length_cons]
      omega)
  have rd12067 := by
    simpa using rd12066.dup3 hd12066 (by
      simp only [List.length_cons]
      omega)
  have rd12068 := by
    simpa [getSqrtRatioBit1024Word] using rd12067.and hd12067 (by
      simp only [List.length_cons]
      omega)
  have rd12069 := by
    simpa using rd12068.iszero hd12068 (by
      simp only [List.length_cons]
      omega)
  have rd12072 := by
    simpa using rd12069.push2 ⟨12094⟩ hd12069 (by
      simp only [List.length_cons]
      omega)
  exact ⟨_, _, rd12072.jumpiT hd12072 hcond (uniswapV3PoolJumpDestPatched12094 hpatch) (by
    simp only [List.length_cons]
    omega)⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetSqrtRatioAtTickBit1024Set {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ratio absTick tick ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨12062⟩ (ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k C)
    (hbit : getSqrtRatioBit1024Word absTick ≠ ⟨0⟩)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨12094⟩
      (getSqrtRatioAfterBit1024Word ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 11629 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 13989) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 13989 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetSqrtRatioAtTick hlo hhi)]
  have hd12062 : decode code ⟨12062⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12063 : decode code ⟨12063⟩ = some (.Push .PUSH2, some (⟨1024⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12066 : decode code ⟨12066⟩ = some (.DUP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12067 : decode code ⟨12067⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12068 : decode code ⟨12068⟩ = some (.ISZERO, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12069 : decode code ⟨12069⟩ = some (.Push .PUSH2, some (⟨12094⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12072 : decode code ⟨12072⟩ = some (.JUMPI, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12073 :
      decode code ⟨12073⟩ =
        some (.Push .PUSH16, some (⟨323299236684853023288211250268160618739⟩, 16)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12090 : decode code ⟨12090⟩ = some (.MUL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12091 : decode code ⟨12091⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12093 : decode code ⟨12093⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hcond : UInt256.isZero (getSqrtRatioBit1024Word absTick) = ⟨0⟩ :=
    isZero_eq_zero_of_ne hbit
  have rd12063 := by
    simpa using h.jumpdest hd12062 (by
      simp only [List.length_cons]
      omega)
  have rd12066 := by
    simpa using rd12063.push2 ⟨1024⟩ hd12063 (by
      simp only [List.length_cons]
      omega)
  have rd12067 := by
    simpa using rd12066.dup3 hd12066 (by
      simp only [List.length_cons]
      omega)
  have rd12068 := by
    simpa [getSqrtRatioBit1024Word] using rd12067.and hd12067 (by
      simp only [List.length_cons]
      omega)
  have rd12069 := by
    simpa using rd12068.iszero hd12068 (by
      simp only [List.length_cons]
      omega)
  have rd12072 := by
    simpa using rd12069.push2 ⟨12094⟩ hd12069 (by
      simp only [List.length_cons]
      omega)
  have rd12073 := rd12072.jumpiNT hd12072 hcond (by
    simp only [List.length_cons]
    omega)
  have rd12090 := by
    simpa [getSqrtRatioFactor1024Word] using
      rd12073.pushConst (⟨323299236684853023288211250268160618739⟩ : UInt256)
        (by native_decide : Operation.POp.PUSH16 ≠ .PUSH0) hd12073 (by
          simp only [List.length_cons]
          omega)
  have rd12091 := by
    simpa using rd12090.mul hd12090 (by
      simp only [List.length_cons]
      omega)
  have rd12093 := by
    simpa using rd12091.push1 ⟨128⟩ hd12091 (by
      simp only [List.length_cons]
      omega)
  have rd12094 := by
    simpa [getSqrtRatioAfterBit1024Word, getSqrtRatioFactor1024Word] using
      rd12093.shr hd12093 (by
        simp only [List.length_cons]
        omega)
  exact ⟨_, _, by simpa using rd12094⟩

end Benchmarks.UniswapV3Pool
