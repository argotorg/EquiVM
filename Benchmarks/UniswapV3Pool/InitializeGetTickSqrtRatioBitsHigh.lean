import Benchmarks.UniswapV3Pool.InitializeGetTickSqrtRatioBits

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.UniswapV3Pool

def getSqrtRatioBit2048Word (absTick : UInt256) : UInt256 :=
  UInt256.land absTick ⟨2048⟩

def getSqrtRatioFactor2048Word : UInt256 :=
  ⟨307163716377032989948697243942600083929⟩

def getSqrtRatioAfterBit2048Word (ratio : UInt256) : UInt256 :=
  UInt256.shiftRight (UInt256.mul getSqrtRatioFactor2048Word ratio) ⟨128⟩

def getSqrtRatioBit4096Word (absTick : UInt256) : UInt256 :=
  UInt256.land absTick ⟨4096⟩

def getSqrtRatioFactor4096Word : UInt256 :=
  ⟨277268403626896220162999269216087595045⟩

def getSqrtRatioAfterBit4096Word (ratio : UInt256) : UInt256 :=
  UInt256.shiftRight (UInt256.mul getSqrtRatioFactor4096Word ratio) ⟨128⟩

def getSqrtRatioBit8192Word (absTick : UInt256) : UInt256 :=
  UInt256.land absTick ⟨8192⟩

def getSqrtRatioFactor8192Word : UInt256 :=
  ⟨225923453940442621947126027127485391333⟩

def getSqrtRatioAfterBit8192Word (ratio : UInt256) : UInt256 :=
  UInt256.shiftRight (UInt256.mul getSqrtRatioFactor8192Word ratio) ⟨128⟩

def getSqrtRatioBit16384Word (absTick : UInt256) : UInt256 :=
  UInt256.land absTick ⟨16384⟩

def getSqrtRatioFactor16384Word : UInt256 :=
  ⟨149997214084966997727330242082538205943⟩

def getSqrtRatioAfterBit16384Word (ratio : UInt256) : UInt256 :=
  UInt256.shiftRight (UInt256.mul getSqrtRatioFactor16384Word ratio) ⟨128⟩

def getSqrtRatioBit32768Word (absTick : UInt256) : UInt256 :=
  UInt256.land absTick ⟨32768⟩

def getSqrtRatioFactor32768Word : UInt256 :=
  ⟨66119101136024775622716233608466517926⟩

def getSqrtRatioAfterBit32768Word (ratio : UInt256) : UInt256 :=
  UInt256.shiftRight (UInt256.mul getSqrtRatioFactor32768Word ratio) ⟨128⟩

def getSqrtRatioBit65536Word (absTick : UInt256) : UInt256 :=
  UInt256.land absTick ⟨65536⟩

def getSqrtRatioFactor65536Word : UInt256 :=
  ⟨12847376061809297530290974190478138313⟩

def getSqrtRatioAfterBit65536Word (ratio : UInt256) : UInt256 :=
  UInt256.shiftRight (UInt256.mul getSqrtRatioFactor65536Word ratio) ⟨128⟩

def getSqrtRatioBit131072Word (absTick : UInt256) : UInt256 :=
  UInt256.land absTick ⟨131072⟩

def getSqrtRatioFactor131072Word : UInt256 :=
  ⟨485053260817066172746253684029974020⟩

def getSqrtRatioAfterBit131072Word (ratio : UInt256) : UInt256 :=
  UInt256.shiftRight (UInt256.mul getSqrtRatioFactor131072Word ratio) ⟨128⟩

def getSqrtRatioBit262144Word (absTick : UInt256) : UInt256 :=
  UInt256.land absTick ⟨262144⟩

def getSqrtRatioFactor262144Word : UInt256 :=
  ⟨691415978906521570653435304214168⟩

def getSqrtRatioAfterBit262144Word (ratio : UInt256) : UInt256 :=
  UInt256.shiftRight (UInt256.mul getSqrtRatioFactor262144Word ratio) ⟨128⟩

def getSqrtRatioBit524288Word (absTick : UInt256) : UInt256 :=
  UInt256.land absTick ⟨524288⟩

def getSqrtRatioFactor524288Word : UInt256 :=
  ⟨1404880482679654955896180642⟩

def getSqrtRatioAfterBit524288Word (ratio : UInt256) : UInt256 :=
  UInt256.shiftRight (UInt256.mul getSqrtRatioFactor524288Word ratio) ⟨128⟩

private theorem uniswapV3PoolInitializePatchPreservesJumpDest12126 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨12126⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolInitializePatchPreservesJumpDest12158 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨12158⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolInitializePatchPreservesJumpDest12190 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨12190⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolInitializePatchPreservesJumpDest12222 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨12222⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolInitializePatchPreservesJumpDest12254 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨12254⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolInitializePatchPreservesJumpDest12287 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨12287⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolInitializePatchPreservesJumpDest12319 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨12319⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolInitializePatchPreservesJumpDest12350 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨12350⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolInitializePatchPreservesJumpDest12379 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨12379⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolJumpDestPatched12126 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨12126⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolInitializePatchPreservesJumpDest12126

theorem uniswapV3PoolJumpDestPatched12158 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨12158⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolInitializePatchPreservesJumpDest12158

theorem uniswapV3PoolJumpDestPatched12190 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨12190⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolInitializePatchPreservesJumpDest12190

theorem uniswapV3PoolJumpDestPatched12222 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨12222⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolInitializePatchPreservesJumpDest12222

theorem uniswapV3PoolJumpDestPatched12254 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨12254⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolInitializePatchPreservesJumpDest12254

theorem uniswapV3PoolJumpDestPatched12287 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨12287⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolInitializePatchPreservesJumpDest12287

theorem uniswapV3PoolJumpDestPatched12319 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨12319⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolInitializePatchPreservesJumpDest12319

theorem uniswapV3PoolJumpDestPatched12350 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨12350⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolInitializePatchPreservesJumpDest12350

theorem uniswapV3PoolJumpDestPatched12379 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨12379⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolInitializePatchPreservesJumpDest12379

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetSqrtRatioAtTickBit2048Zero {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ratio absTick tick ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨12094⟩ (ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k C)
    (hbit : getSqrtRatioBit2048Word absTick = ⟨0⟩)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨12126⟩ (ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 11629 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 13989) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 13989 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetSqrtRatioAtTick hlo hhi)]
  have hd12094 : decode code ⟨12094⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12095 : decode code ⟨12095⟩ = some (.Push .PUSH2, some (⟨2048⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12098 : decode code ⟨12098⟩ = some (.DUP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12099 : decode code ⟨12099⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12100 : decode code ⟨12100⟩ = some (.ISZERO, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12101 : decode code ⟨12101⟩ = some (.Push .PUSH2, some (⟨12126⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12104 : decode code ⟨12104⟩ = some (.JUMPI, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hcond : UInt256.isZero (getSqrtRatioBit2048Word absTick) ≠ ⟨0⟩ := by
    rw [hbit]
    native_decide
  have rd12095 := by
    simpa using h.jumpdest hd12094 (by
      simp only [List.length_cons]
      omega)
  have rd12098 := by
    simpa using rd12095.push2 ⟨2048⟩ hd12095 (by
      simp only [List.length_cons]
      omega)
  have rd12099 := by
    simpa using rd12098.dup3 hd12098 (by
      simp only [List.length_cons]
      omega)
  have rd12100 := by
    simpa [getSqrtRatioBit2048Word] using rd12099.and hd12099 (by
      simp only [List.length_cons]
      omega)
  have rd12101 := by
    simpa using rd12100.iszero hd12100 (by
      simp only [List.length_cons]
      omega)
  have rd12104 := by
    simpa using rd12101.push2 ⟨12126⟩ hd12101 (by
      simp only [List.length_cons]
      omega)
  exact ⟨_, _, rd12104.jumpiT hd12104 hcond (uniswapV3PoolJumpDestPatched12126 hpatch) (by
    simp only [List.length_cons]
    omega)⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetSqrtRatioAtTickBit2048Set {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ratio absTick tick ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨12094⟩ (ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k C)
    (hbit : getSqrtRatioBit2048Word absTick ≠ ⟨0⟩)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨12126⟩
      (getSqrtRatioAfterBit2048Word ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 11629 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 13989) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 13989 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetSqrtRatioAtTick hlo hhi)]
  have hd12094 : decode code ⟨12094⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12095 : decode code ⟨12095⟩ = some (.Push .PUSH2, some (⟨2048⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12098 : decode code ⟨12098⟩ = some (.DUP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12099 : decode code ⟨12099⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12100 : decode code ⟨12100⟩ = some (.ISZERO, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12101 : decode code ⟨12101⟩ = some (.Push .PUSH2, some (⟨12126⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12104 : decode code ⟨12104⟩ = some (.JUMPI, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12105 :
      decode code ⟨12105⟩ =
        some (.Push .PUSH16, some (⟨307163716377032989948697243942600083929⟩, 16)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12122 : decode code ⟨12122⟩ = some (.MUL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12123 : decode code ⟨12123⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12125 : decode code ⟨12125⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hcond : UInt256.isZero (getSqrtRatioBit2048Word absTick) = ⟨0⟩ :=
    isZero_eq_zero_of_ne hbit
  have rd12095 := by
    simpa using h.jumpdest hd12094 (by
      simp only [List.length_cons]
      omega)
  have rd12098 := by
    simpa using rd12095.push2 ⟨2048⟩ hd12095 (by
      simp only [List.length_cons]
      omega)
  have rd12099 := by
    simpa using rd12098.dup3 hd12098 (by
      simp only [List.length_cons]
      omega)
  have rd12100 := by
    simpa [getSqrtRatioBit2048Word] using rd12099.and hd12099 (by
      simp only [List.length_cons]
      omega)
  have rd12101 := by
    simpa using rd12100.iszero hd12100 (by
      simp only [List.length_cons]
      omega)
  have rd12104 := by
    simpa using rd12101.push2 ⟨12126⟩ hd12101 (by
      simp only [List.length_cons]
      omega)
  have rd12105 := rd12104.jumpiNT hd12104 hcond (by
    simp only [List.length_cons]
    omega)
  have rd12122 := by
    simpa [getSqrtRatioFactor2048Word] using
      rd12105.pushConst (⟨307163716377032989948697243942600083929⟩ : UInt256)
        (by native_decide : Operation.POp.PUSH16 ≠ .PUSH0) hd12105 (by
          simp only [List.length_cons]
          omega)
  have rd12123 := by
    simpa using rd12122.mul hd12122 (by
      simp only [List.length_cons]
      omega)
  have rd12125 := by
    simpa using rd12123.push1 ⟨128⟩ hd12123 (by
      simp only [List.length_cons]
      omega)
  have rd12126 := by
    simpa [getSqrtRatioAfterBit2048Word, getSqrtRatioFactor2048Word] using
      rd12125.shr hd12125 (by
        simp only [List.length_cons]
        omega)
  exact ⟨_, _, by simpa using rd12126⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetSqrtRatioAtTickBit4096Zero {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ratio absTick tick ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨12126⟩ (ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k C)
    (hbit : getSqrtRatioBit4096Word absTick = ⟨0⟩)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨12158⟩ (ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 11629 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 13989) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 13989 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetSqrtRatioAtTick hlo hhi)]
  have hd12126 : decode code ⟨12126⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12127 : decode code ⟨12127⟩ = some (.Push .PUSH2, some (⟨4096⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12130 : decode code ⟨12130⟩ = some (.DUP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12131 : decode code ⟨12131⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12132 : decode code ⟨12132⟩ = some (.ISZERO, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12133 : decode code ⟨12133⟩ = some (.Push .PUSH2, some (⟨12158⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12136 : decode code ⟨12136⟩ = some (.JUMPI, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hcond : UInt256.isZero (getSqrtRatioBit4096Word absTick) ≠ ⟨0⟩ := by
    rw [hbit]
    native_decide
  have rd12127 := by
    simpa using h.jumpdest hd12126 (by
      simp only [List.length_cons]
      omega)
  have rd12130 := by
    simpa using rd12127.push2 ⟨4096⟩ hd12127 (by
      simp only [List.length_cons]
      omega)
  have rd12131 := by
    simpa using rd12130.dup3 hd12130 (by
      simp only [List.length_cons]
      omega)
  have rd12132 := by
    simpa [getSqrtRatioBit4096Word] using rd12131.and hd12131 (by
      simp only [List.length_cons]
      omega)
  have rd12133 := by
    simpa using rd12132.iszero hd12132 (by
      simp only [List.length_cons]
      omega)
  have rd12136 := by
    simpa using rd12133.push2 ⟨12158⟩ hd12133 (by
      simp only [List.length_cons]
      omega)
  exact ⟨_, _, rd12136.jumpiT hd12136 hcond (uniswapV3PoolJumpDestPatched12158 hpatch) (by
    simp only [List.length_cons]
    omega)⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetSqrtRatioAtTickBit4096Set {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ratio absTick tick ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨12126⟩ (ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k C)
    (hbit : getSqrtRatioBit4096Word absTick ≠ ⟨0⟩)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨12158⟩
      (getSqrtRatioAfterBit4096Word ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 11629 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 13989) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 13989 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetSqrtRatioAtTick hlo hhi)]
  have hd12126 : decode code ⟨12126⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12127 : decode code ⟨12127⟩ = some (.Push .PUSH2, some (⟨4096⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12130 : decode code ⟨12130⟩ = some (.DUP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12131 : decode code ⟨12131⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12132 : decode code ⟨12132⟩ = some (.ISZERO, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12133 : decode code ⟨12133⟩ = some (.Push .PUSH2, some (⟨12158⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12136 : decode code ⟨12136⟩ = some (.JUMPI, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12137 :
      decode code ⟨12137⟩ =
        some (.Push .PUSH16, some (⟨277268403626896220162999269216087595045⟩, 16)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12154 : decode code ⟨12154⟩ = some (.MUL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12155 : decode code ⟨12155⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12157 : decode code ⟨12157⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hcond : UInt256.isZero (getSqrtRatioBit4096Word absTick) = ⟨0⟩ :=
    isZero_eq_zero_of_ne hbit
  have rd12127 := by
    simpa using h.jumpdest hd12126 (by
      simp only [List.length_cons]
      omega)
  have rd12130 := by
    simpa using rd12127.push2 ⟨4096⟩ hd12127 (by
      simp only [List.length_cons]
      omega)
  have rd12131 := by
    simpa using rd12130.dup3 hd12130 (by
      simp only [List.length_cons]
      omega)
  have rd12132 := by
    simpa [getSqrtRatioBit4096Word] using rd12131.and hd12131 (by
      simp only [List.length_cons]
      omega)
  have rd12133 := by
    simpa using rd12132.iszero hd12132 (by
      simp only [List.length_cons]
      omega)
  have rd12136 := by
    simpa using rd12133.push2 ⟨12158⟩ hd12133 (by
      simp only [List.length_cons]
      omega)
  have rd12137 := rd12136.jumpiNT hd12136 hcond (by
    simp only [List.length_cons]
    omega)
  have rd12154 := by
    simpa [getSqrtRatioFactor4096Word] using
      rd12137.pushConst (⟨277268403626896220162999269216087595045⟩ : UInt256)
        (by native_decide : Operation.POp.PUSH16 ≠ .PUSH0) hd12137 (by
          simp only [List.length_cons]
          omega)
  have rd12155 := by
    simpa using rd12154.mul hd12154 (by
      simp only [List.length_cons]
      omega)
  have rd12157 := by
    simpa using rd12155.push1 ⟨128⟩ hd12155 (by
      simp only [List.length_cons]
      omega)
  have rd12158 := by
    simpa [getSqrtRatioAfterBit4096Word, getSqrtRatioFactor4096Word] using
      rd12157.shr hd12157 (by
        simp only [List.length_cons]
        omega)
  exact ⟨_, _, by simpa using rd12158⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetSqrtRatioAtTickBit8192Zero {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ratio absTick tick ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨12158⟩ (ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k C)
    (hbit : getSqrtRatioBit8192Word absTick = ⟨0⟩)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨12190⟩ (ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 11629 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 13989) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 13989 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetSqrtRatioAtTick hlo hhi)]
  have hd12158 : decode code ⟨12158⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12159 : decode code ⟨12159⟩ = some (.Push .PUSH2, some (⟨8192⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12162 : decode code ⟨12162⟩ = some (.DUP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12163 : decode code ⟨12163⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12164 : decode code ⟨12164⟩ = some (.ISZERO, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12165 : decode code ⟨12165⟩ = some (.Push .PUSH2, some (⟨12190⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12168 : decode code ⟨12168⟩ = some (.JUMPI, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hcond : UInt256.isZero (getSqrtRatioBit8192Word absTick) ≠ ⟨0⟩ := by
    rw [hbit]
    native_decide
  have rd12159 := by
    simpa using h.jumpdest hd12158 (by
      simp only [List.length_cons]
      omega)
  have rd12162 := by
    simpa using rd12159.push2 ⟨8192⟩ hd12159 (by
      simp only [List.length_cons]
      omega)
  have rd12163 := by
    simpa using rd12162.dup3 hd12162 (by
      simp only [List.length_cons]
      omega)
  have rd12164 := by
    simpa [getSqrtRatioBit8192Word] using rd12163.and hd12163 (by
      simp only [List.length_cons]
      omega)
  have rd12165 := by
    simpa using rd12164.iszero hd12164 (by
      simp only [List.length_cons]
      omega)
  have rd12168 := by
    simpa using rd12165.push2 ⟨12190⟩ hd12165 (by
      simp only [List.length_cons]
      omega)
  exact ⟨_, _, rd12168.jumpiT hd12168 hcond (uniswapV3PoolJumpDestPatched12190 hpatch) (by
    simp only [List.length_cons]
    omega)⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetSqrtRatioAtTickBit8192Set {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ratio absTick tick ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨12158⟩ (ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k C)
    (hbit : getSqrtRatioBit8192Word absTick ≠ ⟨0⟩)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨12190⟩
      (getSqrtRatioAfterBit8192Word ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 11629 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 13989) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 13989 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetSqrtRatioAtTick hlo hhi)]
  have hd12158 : decode code ⟨12158⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12159 : decode code ⟨12159⟩ = some (.Push .PUSH2, some (⟨8192⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12162 : decode code ⟨12162⟩ = some (.DUP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12163 : decode code ⟨12163⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12164 : decode code ⟨12164⟩ = some (.ISZERO, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12165 : decode code ⟨12165⟩ = some (.Push .PUSH2, some (⟨12190⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12168 : decode code ⟨12168⟩ = some (.JUMPI, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12169 :
      decode code ⟨12169⟩ =
        some (.Push .PUSH16, some (⟨225923453940442621947126027127485391333⟩, 16)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12186 : decode code ⟨12186⟩ = some (.MUL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12187 : decode code ⟨12187⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12189 : decode code ⟨12189⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hcond : UInt256.isZero (getSqrtRatioBit8192Word absTick) = ⟨0⟩ :=
    isZero_eq_zero_of_ne hbit
  have rd12159 := by
    simpa using h.jumpdest hd12158 (by
      simp only [List.length_cons]
      omega)
  have rd12162 := by
    simpa using rd12159.push2 ⟨8192⟩ hd12159 (by
      simp only [List.length_cons]
      omega)
  have rd12163 := by
    simpa using rd12162.dup3 hd12162 (by
      simp only [List.length_cons]
      omega)
  have rd12164 := by
    simpa [getSqrtRatioBit8192Word] using rd12163.and hd12163 (by
      simp only [List.length_cons]
      omega)
  have rd12165 := by
    simpa using rd12164.iszero hd12164 (by
      simp only [List.length_cons]
      omega)
  have rd12168 := by
    simpa using rd12165.push2 ⟨12190⟩ hd12165 (by
      simp only [List.length_cons]
      omega)
  have rd12169 := rd12168.jumpiNT hd12168 hcond (by
    simp only [List.length_cons]
    omega)
  have rd12186 := by
    simpa [getSqrtRatioFactor8192Word] using
      rd12169.pushConst (⟨225923453940442621947126027127485391333⟩ : UInt256)
        (by native_decide : Operation.POp.PUSH16 ≠ .PUSH0) hd12169 (by
          simp only [List.length_cons]
          omega)
  have rd12187 := by
    simpa using rd12186.mul hd12186 (by
      simp only [List.length_cons]
      omega)
  have rd12189 := by
    simpa using rd12187.push1 ⟨128⟩ hd12187 (by
      simp only [List.length_cons]
      omega)
  have rd12190 := by
    simpa [getSqrtRatioAfterBit8192Word, getSqrtRatioFactor8192Word] using
      rd12189.shr hd12189 (by
        simp only [List.length_cons]
        omega)
  exact ⟨_, _, by simpa using rd12190⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetSqrtRatioAtTickBit16384Zero {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ratio absTick tick ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨12190⟩ (ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k C)
    (hbit : getSqrtRatioBit16384Word absTick = ⟨0⟩)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨12222⟩ (ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 11629 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 13989) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 13989 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetSqrtRatioAtTick hlo hhi)]
  have hd12190 : decode code ⟨12190⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12191 : decode code ⟨12191⟩ = some (.Push .PUSH2, some (⟨16384⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12194 : decode code ⟨12194⟩ = some (.DUP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12195 : decode code ⟨12195⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12196 : decode code ⟨12196⟩ = some (.ISZERO, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12197 : decode code ⟨12197⟩ = some (.Push .PUSH2, some (⟨12222⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12200 : decode code ⟨12200⟩ = some (.JUMPI, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hcond : UInt256.isZero (getSqrtRatioBit16384Word absTick) ≠ ⟨0⟩ := by
    rw [hbit]
    native_decide
  have rd12191 := by
    simpa using h.jumpdest hd12190 (by
      simp only [List.length_cons]
      omega)
  have rd12194 := by
    simpa using rd12191.push2 ⟨16384⟩ hd12191 (by
      simp only [List.length_cons]
      omega)
  have rd12195 := by
    simpa using rd12194.dup3 hd12194 (by
      simp only [List.length_cons]
      omega)
  have rd12196 := by
    simpa [getSqrtRatioBit16384Word] using rd12195.and hd12195 (by
      simp only [List.length_cons]
      omega)
  have rd12197 := by
    simpa using rd12196.iszero hd12196 (by
      simp only [List.length_cons]
      omega)
  have rd12200 := by
    simpa using rd12197.push2 ⟨12222⟩ hd12197 (by
      simp only [List.length_cons]
      omega)
  exact ⟨_, _, rd12200.jumpiT hd12200 hcond (uniswapV3PoolJumpDestPatched12222 hpatch) (by
    simp only [List.length_cons]
    omega)⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetSqrtRatioAtTickBit16384Set {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ratio absTick tick ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨12190⟩ (ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k C)
    (hbit : getSqrtRatioBit16384Word absTick ≠ ⟨0⟩)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨12222⟩
      (getSqrtRatioAfterBit16384Word ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 11629 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 13989) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 13989 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetSqrtRatioAtTick hlo hhi)]
  have hd12190 : decode code ⟨12190⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12191 : decode code ⟨12191⟩ = some (.Push .PUSH2, some (⟨16384⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12194 : decode code ⟨12194⟩ = some (.DUP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12195 : decode code ⟨12195⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12196 : decode code ⟨12196⟩ = some (.ISZERO, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12197 : decode code ⟨12197⟩ = some (.Push .PUSH2, some (⟨12222⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12200 : decode code ⟨12200⟩ = some (.JUMPI, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12201 :
      decode code ⟨12201⟩ =
        some (.Push .PUSH16, some (⟨149997214084966997727330242082538205943⟩, 16)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12218 : decode code ⟨12218⟩ = some (.MUL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12219 : decode code ⟨12219⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12221 : decode code ⟨12221⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hcond : UInt256.isZero (getSqrtRatioBit16384Word absTick) = ⟨0⟩ :=
    isZero_eq_zero_of_ne hbit
  have rd12191 := by
    simpa using h.jumpdest hd12190 (by
      simp only [List.length_cons]
      omega)
  have rd12194 := by
    simpa using rd12191.push2 ⟨16384⟩ hd12191 (by
      simp only [List.length_cons]
      omega)
  have rd12195 := by
    simpa using rd12194.dup3 hd12194 (by
      simp only [List.length_cons]
      omega)
  have rd12196 := by
    simpa [getSqrtRatioBit16384Word] using rd12195.and hd12195 (by
      simp only [List.length_cons]
      omega)
  have rd12197 := by
    simpa using rd12196.iszero hd12196 (by
      simp only [List.length_cons]
      omega)
  have rd12200 := by
    simpa using rd12197.push2 ⟨12222⟩ hd12197 (by
      simp only [List.length_cons]
      omega)
  have rd12201 := rd12200.jumpiNT hd12200 hcond (by
    simp only [List.length_cons]
    omega)
  have rd12218 := by
    simpa [getSqrtRatioFactor16384Word] using
      rd12201.pushConst (⟨149997214084966997727330242082538205943⟩ : UInt256)
        (by native_decide : Operation.POp.PUSH16 ≠ .PUSH0) hd12201 (by
          simp only [List.length_cons]
          omega)
  have rd12219 := by
    simpa using rd12218.mul hd12218 (by
      simp only [List.length_cons]
      omega)
  have rd12221 := by
    simpa using rd12219.push1 ⟨128⟩ hd12219 (by
      simp only [List.length_cons]
      omega)
  have rd12222 := by
    simpa [getSqrtRatioAfterBit16384Word, getSqrtRatioFactor16384Word] using
      rd12221.shr hd12221 (by
        simp only [List.length_cons]
        omega)
  exact ⟨_, _, by simpa using rd12222⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetSqrtRatioAtTickBit32768Zero {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ratio absTick tick ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨12222⟩ (ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k C)
    (hbit : getSqrtRatioBit32768Word absTick = ⟨0⟩)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨12254⟩ (ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 11629 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 13989) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 13989 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetSqrtRatioAtTick hlo hhi)]
  have hd12222 : decode code ⟨12222⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12223 : decode code ⟨12223⟩ = some (.Push .PUSH2, some (⟨32768⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12226 : decode code ⟨12226⟩ = some (.DUP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12227 : decode code ⟨12227⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12228 : decode code ⟨12228⟩ = some (.ISZERO, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12229 : decode code ⟨12229⟩ = some (.Push .PUSH2, some (⟨12254⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12232 : decode code ⟨12232⟩ = some (.JUMPI, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hcond : UInt256.isZero (getSqrtRatioBit32768Word absTick) ≠ ⟨0⟩ := by
    rw [hbit]
    native_decide
  have rd12223 := by
    simpa using h.jumpdest hd12222 (by
      simp only [List.length_cons]
      omega)
  have rd12226 := by
    simpa using rd12223.push2 ⟨32768⟩ hd12223 (by
      simp only [List.length_cons]
      omega)
  have rd12227 := by
    simpa using rd12226.dup3 hd12226 (by
      simp only [List.length_cons]
      omega)
  have rd12228 := by
    simpa [getSqrtRatioBit32768Word] using rd12227.and hd12227 (by
      simp only [List.length_cons]
      omega)
  have rd12229 := by
    simpa using rd12228.iszero hd12228 (by
      simp only [List.length_cons]
      omega)
  have rd12232 := by
    simpa using rd12229.push2 ⟨12254⟩ hd12229 (by
      simp only [List.length_cons]
      omega)
  exact ⟨_, _, rd12232.jumpiT hd12232 hcond (uniswapV3PoolJumpDestPatched12254 hpatch) (by
    simp only [List.length_cons]
    omega)⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetSqrtRatioAtTickBit32768Set {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ratio absTick tick ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨12222⟩ (ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k C)
    (hbit : getSqrtRatioBit32768Word absTick ≠ ⟨0⟩)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨12254⟩
      (getSqrtRatioAfterBit32768Word ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 11629 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 13989) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 13989 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetSqrtRatioAtTick hlo hhi)]
  have hd12222 : decode code ⟨12222⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12223 : decode code ⟨12223⟩ = some (.Push .PUSH2, some (⟨32768⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12226 : decode code ⟨12226⟩ = some (.DUP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12227 : decode code ⟨12227⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12228 : decode code ⟨12228⟩ = some (.ISZERO, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12229 : decode code ⟨12229⟩ = some (.Push .PUSH2, some (⟨12254⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12232 : decode code ⟨12232⟩ = some (.JUMPI, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12233 :
      decode code ⟨12233⟩ =
        some (.Push .PUSH16, some (⟨66119101136024775622716233608466517926⟩, 16)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12250 : decode code ⟨12250⟩ = some (.MUL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12251 : decode code ⟨12251⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12253 : decode code ⟨12253⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hcond : UInt256.isZero (getSqrtRatioBit32768Word absTick) = ⟨0⟩ :=
    isZero_eq_zero_of_ne hbit
  have rd12223 := by
    simpa using h.jumpdest hd12222 (by
      simp only [List.length_cons]
      omega)
  have rd12226 := by
    simpa using rd12223.push2 ⟨32768⟩ hd12223 (by
      simp only [List.length_cons]
      omega)
  have rd12227 := by
    simpa using rd12226.dup3 hd12226 (by
      simp only [List.length_cons]
      omega)
  have rd12228 := by
    simpa [getSqrtRatioBit32768Word] using rd12227.and hd12227 (by
      simp only [List.length_cons]
      omega)
  have rd12229 := by
    simpa using rd12228.iszero hd12228 (by
      simp only [List.length_cons]
      omega)
  have rd12232 := by
    simpa using rd12229.push2 ⟨12254⟩ hd12229 (by
      simp only [List.length_cons]
      omega)
  have rd12233 := rd12232.jumpiNT hd12232 hcond (by
    simp only [List.length_cons]
    omega)
  have rd12250 := by
    simpa [getSqrtRatioFactor32768Word] using
      rd12233.pushConst (⟨66119101136024775622716233608466517926⟩ : UInt256)
        (by native_decide : Operation.POp.PUSH16 ≠ .PUSH0) hd12233 (by
          simp only [List.length_cons]
          omega)
  have rd12251 := by
    simpa using rd12250.mul hd12250 (by
      simp only [List.length_cons]
      omega)
  have rd12253 := by
    simpa using rd12251.push1 ⟨128⟩ hd12251 (by
      simp only [List.length_cons]
      omega)
  have rd12254 := by
    simpa [getSqrtRatioAfterBit32768Word, getSqrtRatioFactor32768Word] using
      rd12253.shr hd12253 (by
        simp only [List.length_cons]
        omega)
  exact ⟨_, _, by simpa using rd12254⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetSqrtRatioAtTickBit65536Zero {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ratio absTick tick ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨12254⟩ (ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k C)
    (hbit : getSqrtRatioBit65536Word absTick = ⟨0⟩)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨12287⟩ (ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 11629 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 13989) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 13989 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetSqrtRatioAtTick hlo hhi)]
  have hd12254 : decode code ⟨12254⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12255 : decode code ⟨12255⟩ = some (.Push .PUSH3, some (⟨65536⟩, 3)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12259 : decode code ⟨12259⟩ = some (.DUP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12260 : decode code ⟨12260⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12261 : decode code ⟨12261⟩ = some (.ISZERO, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12262 : decode code ⟨12262⟩ = some (.Push .PUSH2, some (⟨12287⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12265 : decode code ⟨12265⟩ = some (.JUMPI, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hcond : UInt256.isZero (getSqrtRatioBit65536Word absTick) ≠ ⟨0⟩ := by
    rw [hbit]
    native_decide
  have rd12255 := by
    simpa using h.jumpdest hd12254 (by
      simp only [List.length_cons]
      omega)
  have rd12259 := by
    simpa using
      rd12255.pushConst (⟨65536⟩ : UInt256)
        (by native_decide : Operation.POp.PUSH3 ≠ .PUSH0) hd12255 (by
          simp only [List.length_cons]
          omega)
  have rd12260 := by
    simpa using rd12259.dup3 hd12259 (by
      simp only [List.length_cons]
      omega)
  have rd12261 := by
    simpa [getSqrtRatioBit65536Word] using rd12260.and hd12260 (by
      simp only [List.length_cons]
      omega)
  have rd12262 := by
    simpa using rd12261.iszero hd12261 (by
      simp only [List.length_cons]
      omega)
  have rd12265 := by
    simpa using rd12262.push2 ⟨12287⟩ hd12262 (by
      simp only [List.length_cons]
      omega)
  exact ⟨_, _, rd12265.jumpiT hd12265 hcond (uniswapV3PoolJumpDestPatched12287 hpatch) (by
    simp only [List.length_cons]
    omega)⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetSqrtRatioAtTickBit65536Set {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ratio absTick tick ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨12254⟩ (ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k C)
    (hbit : getSqrtRatioBit65536Word absTick ≠ ⟨0⟩)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨12287⟩
      (getSqrtRatioAfterBit65536Word ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 11629 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 13989) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 13989 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetSqrtRatioAtTick hlo hhi)]
  have hd12254 : decode code ⟨12254⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12255 : decode code ⟨12255⟩ = some (.Push .PUSH3, some (⟨65536⟩, 3)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12259 : decode code ⟨12259⟩ = some (.DUP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12260 : decode code ⟨12260⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12261 : decode code ⟨12261⟩ = some (.ISZERO, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12262 : decode code ⟨12262⟩ = some (.Push .PUSH2, some (⟨12287⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12265 : decode code ⟨12265⟩ = some (.JUMPI, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12266 :
      decode code ⟨12266⟩ =
        some (.Push .PUSH16, some (⟨12847376061809297530290974190478138313⟩, 16)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12283 : decode code ⟨12283⟩ = some (.MUL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12284 : decode code ⟨12284⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12286 : decode code ⟨12286⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hcond : UInt256.isZero (getSqrtRatioBit65536Word absTick) = ⟨0⟩ :=
    isZero_eq_zero_of_ne hbit
  have rd12255 := by
    simpa using h.jumpdest hd12254 (by
      simp only [List.length_cons]
      omega)
  have rd12259 := by
    simpa using
      rd12255.pushConst (⟨65536⟩ : UInt256)
        (by native_decide : Operation.POp.PUSH3 ≠ .PUSH0) hd12255 (by
          simp only [List.length_cons]
          omega)
  have rd12260 := by
    simpa using rd12259.dup3 hd12259 (by
      simp only [List.length_cons]
      omega)
  have rd12261 := by
    simpa [getSqrtRatioBit65536Word] using rd12260.and hd12260 (by
      simp only [List.length_cons]
      omega)
  have rd12262 := by
    simpa using rd12261.iszero hd12261 (by
      simp only [List.length_cons]
      omega)
  have rd12265 := by
    simpa using rd12262.push2 ⟨12287⟩ hd12262 (by
      simp only [List.length_cons]
      omega)
  have rd12266 := rd12265.jumpiNT hd12265 hcond (by
    simp only [List.length_cons]
    omega)
  have rd12283 := by
    simpa [getSqrtRatioFactor65536Word] using
      rd12266.pushConst (⟨12847376061809297530290974190478138313⟩ : UInt256)
        (by native_decide : Operation.POp.PUSH16 ≠ .PUSH0) hd12266 (by
          simp only [List.length_cons]
          omega)
  have rd12284 := by
    simpa using rd12283.mul hd12283 (by
      simp only [List.length_cons]
      omega)
  have rd12286 := by
    simpa using rd12284.push1 ⟨128⟩ hd12284 (by
      simp only [List.length_cons]
      omega)
  have rd12287 := by
    simpa [getSqrtRatioAfterBit65536Word, getSqrtRatioFactor65536Word] using
      rd12286.shr hd12286 (by
        simp only [List.length_cons]
        omega)
  exact ⟨_, _, by simpa using rd12287⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetSqrtRatioAtTickBit131072Zero {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ratio absTick tick ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨12287⟩ (ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k C)
    (hbit : getSqrtRatioBit131072Word absTick = ⟨0⟩)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨12319⟩ (ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 11629 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 13989) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 13989 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetSqrtRatioAtTick hlo hhi)]
  have hd12287 : decode code ⟨12287⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12288 : decode code ⟨12288⟩ = some (.Push .PUSH3, some (⟨131072⟩, 3)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12292 : decode code ⟨12292⟩ = some (.DUP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12293 : decode code ⟨12293⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12294 : decode code ⟨12294⟩ = some (.ISZERO, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12295 : decode code ⟨12295⟩ = some (.Push .PUSH2, some (⟨12319⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12298 : decode code ⟨12298⟩ = some (.JUMPI, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hcond : UInt256.isZero (getSqrtRatioBit131072Word absTick) ≠ ⟨0⟩ := by
    rw [hbit]
    native_decide
  have rd12288 := by
    simpa using h.jumpdest hd12287 (by
      simp only [List.length_cons]
      omega)
  have rd12292 := by
    simpa using
      rd12288.pushConst (⟨131072⟩ : UInt256)
        (by native_decide : Operation.POp.PUSH3 ≠ .PUSH0) hd12288 (by
          simp only [List.length_cons]
          omega)
  have rd12293 := by
    simpa using rd12292.dup3 hd12292 (by
      simp only [List.length_cons]
      omega)
  have rd12294 := by
    simpa [getSqrtRatioBit131072Word] using rd12293.and hd12293 (by
      simp only [List.length_cons]
      omega)
  have rd12295 := by
    simpa using rd12294.iszero hd12294 (by
      simp only [List.length_cons]
      omega)
  have rd12298 := by
    simpa using rd12295.push2 ⟨12319⟩ hd12295 (by
      simp only [List.length_cons]
      omega)
  exact ⟨_, _, rd12298.jumpiT hd12298 hcond (uniswapV3PoolJumpDestPatched12319 hpatch) (by
    simp only [List.length_cons]
    omega)⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetSqrtRatioAtTickBit131072Set {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ratio absTick tick ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨12287⟩ (ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k C)
    (hbit : getSqrtRatioBit131072Word absTick ≠ ⟨0⟩)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨12319⟩
      (getSqrtRatioAfterBit131072Word ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 11629 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 13989) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 13989 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetSqrtRatioAtTick hlo hhi)]
  have hd12287 : decode code ⟨12287⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12288 : decode code ⟨12288⟩ = some (.Push .PUSH3, some (⟨131072⟩, 3)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12292 : decode code ⟨12292⟩ = some (.DUP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12293 : decode code ⟨12293⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12294 : decode code ⟨12294⟩ = some (.ISZERO, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12295 : decode code ⟨12295⟩ = some (.Push .PUSH2, some (⟨12319⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12298 : decode code ⟨12298⟩ = some (.JUMPI, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12299 :
      decode code ⟨12299⟩ =
        some (.Push .PUSH15, some (⟨485053260817066172746253684029974020⟩, 15)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12315 : decode code ⟨12315⟩ = some (.MUL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12316 : decode code ⟨12316⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12318 : decode code ⟨12318⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hcond : UInt256.isZero (getSqrtRatioBit131072Word absTick) = ⟨0⟩ :=
    isZero_eq_zero_of_ne hbit
  have rd12288 := by
    simpa using h.jumpdest hd12287 (by
      simp only [List.length_cons]
      omega)
  have rd12292 := by
    simpa using
      rd12288.pushConst (⟨131072⟩ : UInt256)
        (by native_decide : Operation.POp.PUSH3 ≠ .PUSH0) hd12288 (by
          simp only [List.length_cons]
          omega)
  have rd12293 := by
    simpa using rd12292.dup3 hd12292 (by
      simp only [List.length_cons]
      omega)
  have rd12294 := by
    simpa [getSqrtRatioBit131072Word] using rd12293.and hd12293 (by
      simp only [List.length_cons]
      omega)
  have rd12295 := by
    simpa using rd12294.iszero hd12294 (by
      simp only [List.length_cons]
      omega)
  have rd12298 := by
    simpa using rd12295.push2 ⟨12319⟩ hd12295 (by
      simp only [List.length_cons]
      omega)
  have rd12299 := rd12298.jumpiNT hd12298 hcond (by
    simp only [List.length_cons]
    omega)
  have rd12315 := by
    simpa [getSqrtRatioFactor131072Word] using
      rd12299.pushConst (⟨485053260817066172746253684029974020⟩ : UInt256)
        (by native_decide : Operation.POp.PUSH15 ≠ .PUSH0) hd12299 (by
          simp only [List.length_cons]
          omega)
  have rd12316 := by
    simpa using rd12315.mul hd12315 (by
      simp only [List.length_cons]
      omega)
  have rd12318 := by
    simpa using rd12316.push1 ⟨128⟩ hd12316 (by
      simp only [List.length_cons]
      omega)
  have rd12319 := by
    simpa [getSqrtRatioAfterBit131072Word, getSqrtRatioFactor131072Word] using
      rd12318.shr hd12318 (by
        simp only [List.length_cons]
        omega)
  exact ⟨_, _, by simpa using rd12319⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetSqrtRatioAtTickBit262144Zero {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ratio absTick tick ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨12319⟩ (ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k C)
    (hbit : getSqrtRatioBit262144Word absTick = ⟨0⟩)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨12350⟩ (ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 11629 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 13989) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 13989 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetSqrtRatioAtTick hlo hhi)]
  have hd12319 : decode code ⟨12319⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12320 : decode code ⟨12320⟩ = some (.Push .PUSH3, some (⟨262144⟩, 3)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12324 : decode code ⟨12324⟩ = some (.DUP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12325 : decode code ⟨12325⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12326 : decode code ⟨12326⟩ = some (.ISZERO, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12327 : decode code ⟨12327⟩ = some (.Push .PUSH2, some (⟨12350⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12330 : decode code ⟨12330⟩ = some (.JUMPI, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hcond : UInt256.isZero (getSqrtRatioBit262144Word absTick) ≠ ⟨0⟩ := by
    rw [hbit]
    native_decide
  have rd12320 := by
    simpa using h.jumpdest hd12319 (by
      simp only [List.length_cons]
      omega)
  have rd12324 := by
    simpa using
      rd12320.pushConst (⟨262144⟩ : UInt256)
        (by native_decide : Operation.POp.PUSH3 ≠ .PUSH0) hd12320 (by
          simp only [List.length_cons]
          omega)
  have rd12325 := by
    simpa using rd12324.dup3 hd12324 (by
      simp only [List.length_cons]
      omega)
  have rd12326 := by
    simpa [getSqrtRatioBit262144Word] using rd12325.and hd12325 (by
      simp only [List.length_cons]
      omega)
  have rd12327 := by
    simpa using rd12326.iszero hd12326 (by
      simp only [List.length_cons]
      omega)
  have rd12330 := by
    simpa using rd12327.push2 ⟨12350⟩ hd12327 (by
      simp only [List.length_cons]
      omega)
  exact ⟨_, _, rd12330.jumpiT hd12330 hcond (uniswapV3PoolJumpDestPatched12350 hpatch) (by
    simp only [List.length_cons]
    omega)⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetSqrtRatioAtTickBit262144Set {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ratio absTick tick ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨12319⟩ (ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k C)
    (hbit : getSqrtRatioBit262144Word absTick ≠ ⟨0⟩)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨12350⟩
      (getSqrtRatioAfterBit262144Word ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 11629 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 13989) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 13989 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetSqrtRatioAtTick hlo hhi)]
  have hd12319 : decode code ⟨12319⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12320 : decode code ⟨12320⟩ = some (.Push .PUSH3, some (⟨262144⟩, 3)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12324 : decode code ⟨12324⟩ = some (.DUP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12325 : decode code ⟨12325⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12326 : decode code ⟨12326⟩ = some (.ISZERO, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12327 : decode code ⟨12327⟩ = some (.Push .PUSH2, some (⟨12350⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12330 : decode code ⟨12330⟩ = some (.JUMPI, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12331 :
      decode code ⟨12331⟩ =
        some (.Push .PUSH14, some (⟨691415978906521570653435304214168⟩, 14)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12346 : decode code ⟨12346⟩ = some (.MUL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12347 : decode code ⟨12347⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12349 : decode code ⟨12349⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hcond : UInt256.isZero (getSqrtRatioBit262144Word absTick) = ⟨0⟩ :=
    isZero_eq_zero_of_ne hbit
  have rd12320 := by
    simpa using h.jumpdest hd12319 (by
      simp only [List.length_cons]
      omega)
  have rd12324 := by
    simpa using
      rd12320.pushConst (⟨262144⟩ : UInt256)
        (by native_decide : Operation.POp.PUSH3 ≠ .PUSH0) hd12320 (by
          simp only [List.length_cons]
          omega)
  have rd12325 := by
    simpa using rd12324.dup3 hd12324 (by
      simp only [List.length_cons]
      omega)
  have rd12326 := by
    simpa [getSqrtRatioBit262144Word] using rd12325.and hd12325 (by
      simp only [List.length_cons]
      omega)
  have rd12327 := by
    simpa using rd12326.iszero hd12326 (by
      simp only [List.length_cons]
      omega)
  have rd12330 := by
    simpa using rd12327.push2 ⟨12350⟩ hd12327 (by
      simp only [List.length_cons]
      omega)
  have rd12331 := rd12330.jumpiNT hd12330 hcond (by
    simp only [List.length_cons]
    omega)
  have rd12346 := by
    simpa [getSqrtRatioFactor262144Word] using
      rd12331.pushConst (⟨691415978906521570653435304214168⟩ : UInt256)
        (by native_decide : Operation.POp.PUSH14 ≠ .PUSH0) hd12331 (by
          simp only [List.length_cons]
          omega)
  have rd12347 := by
    simpa using rd12346.mul hd12346 (by
      simp only [List.length_cons]
      omega)
  have rd12349 := by
    simpa using rd12347.push1 ⟨128⟩ hd12347 (by
      simp only [List.length_cons]
      omega)
  have rd12350 := by
    simpa [getSqrtRatioAfterBit262144Word, getSqrtRatioFactor262144Word] using
      rd12349.shr hd12349 (by
        simp only [List.length_cons]
        omega)
  exact ⟨_, _, by simpa using rd12350⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetSqrtRatioAtTickBit524288Zero {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ratio absTick tick ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨12350⟩ (ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k C)
    (hbit : getSqrtRatioBit524288Word absTick = ⟨0⟩)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨12379⟩ (ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 11629 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 13989) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 13989 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetSqrtRatioAtTick hlo hhi)]
  have hd12350 : decode code ⟨12350⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12351 : decode code ⟨12351⟩ = some (.Push .PUSH3, some (⟨524288⟩, 3)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12355 : decode code ⟨12355⟩ = some (.DUP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12356 : decode code ⟨12356⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12357 : decode code ⟨12357⟩ = some (.ISZERO, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12358 : decode code ⟨12358⟩ = some (.Push .PUSH2, some (⟨12379⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12361 : decode code ⟨12361⟩ = some (.JUMPI, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hcond : UInt256.isZero (getSqrtRatioBit524288Word absTick) ≠ ⟨0⟩ := by
    rw [hbit]
    native_decide
  have rd12351 := by
    simpa using h.jumpdest hd12350 (by
      simp only [List.length_cons]
      omega)
  have rd12355 := by
    simpa using
      rd12351.pushConst (⟨524288⟩ : UInt256)
        (by native_decide : Operation.POp.PUSH3 ≠ .PUSH0) hd12351 (by
          simp only [List.length_cons]
          omega)
  have rd12356 := by
    simpa using rd12355.dup3 hd12355 (by
      simp only [List.length_cons]
      omega)
  have rd12357 := by
    simpa [getSqrtRatioBit524288Word] using rd12356.and hd12356 (by
      simp only [List.length_cons]
      omega)
  have rd12358 := by
    simpa using rd12357.iszero hd12357 (by
      simp only [List.length_cons]
      omega)
  have rd12361 := by
    simpa using rd12358.push2 ⟨12379⟩ hd12358 (by
      simp only [List.length_cons]
      omega)
  exact ⟨_, _, rd12361.jumpiT hd12361 hcond (uniswapV3PoolJumpDestPatched12379 hpatch) (by
    simp only [List.length_cons]
    omega)⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetSqrtRatioAtTickBit524288Set {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ratio absTick tick ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨12350⟩ (ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k C)
    (hbit : getSqrtRatioBit524288Word absTick ≠ ⟨0⟩)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨12379⟩
      (getSqrtRatioAfterBit524288Word ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 11629 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 13989) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 13989 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetSqrtRatioAtTick hlo hhi)]
  have hd12350 : decode code ⟨12350⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12351 : decode code ⟨12351⟩ = some (.Push .PUSH3, some (⟨524288⟩, 3)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12355 : decode code ⟨12355⟩ = some (.DUP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12356 : decode code ⟨12356⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12357 : decode code ⟨12357⟩ = some (.ISZERO, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12358 : decode code ⟨12358⟩ = some (.Push .PUSH2, some (⟨12379⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12361 : decode code ⟨12361⟩ = some (.JUMPI, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12362 :
      decode code ⟨12362⟩ =
        some (.Push .PUSH12, some (⟨1404880482679654955896180642⟩, 12)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12375 : decode code ⟨12375⟩ = some (.MUL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12376 : decode code ⟨12376⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12378 : decode code ⟨12378⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hcond : UInt256.isZero (getSqrtRatioBit524288Word absTick) = ⟨0⟩ :=
    isZero_eq_zero_of_ne hbit
  have rd12351 := by
    simpa using h.jumpdest hd12350 (by
      simp only [List.length_cons]
      omega)
  have rd12355 := by
    simpa using
      rd12351.pushConst (⟨524288⟩ : UInt256)
        (by native_decide : Operation.POp.PUSH3 ≠ .PUSH0) hd12351 (by
          simp only [List.length_cons]
          omega)
  have rd12356 := by
    simpa using rd12355.dup3 hd12355 (by
      simp only [List.length_cons]
      omega)
  have rd12357 := by
    simpa [getSqrtRatioBit524288Word] using rd12356.and hd12356 (by
      simp only [List.length_cons]
      omega)
  have rd12358 := by
    simpa using rd12357.iszero hd12357 (by
      simp only [List.length_cons]
      omega)
  have rd12361 := by
    simpa using rd12358.push2 ⟨12379⟩ hd12358 (by
      simp only [List.length_cons]
      omega)
  have rd12362 := rd12361.jumpiNT hd12361 hcond (by
    simp only [List.length_cons]
    omega)
  have rd12375 := by
    simpa [getSqrtRatioFactor524288Word] using
      rd12362.pushConst (⟨1404880482679654955896180642⟩ : UInt256)
        (by native_decide : Operation.POp.PUSH12 ≠ .PUSH0) hd12362 (by
          simp only [List.length_cons]
          omega)
  have rd12376 := by
    simpa using rd12375.mul hd12375 (by
      simp only [List.length_cons]
      omega)
  have rd12378 := by
    simpa using rd12376.push1 ⟨128⟩ hd12376 (by
      simp only [List.length_cons]
      omega)
  have rd12379 := by
    simpa [getSqrtRatioAfterBit524288Word, getSqrtRatioFactor524288Word] using
      rd12378.shr hd12378 (by
        simp only [List.length_cons]
        omega)
  exact ⟨_, _, by simpa using rd12379⟩

end Benchmarks.UniswapV3Pool
