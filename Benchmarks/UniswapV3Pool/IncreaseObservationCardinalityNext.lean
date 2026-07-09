import Benchmarks.UniswapV3Pool.IncreaseObservationCardinalityNextGrowLoop

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.UniswapV3Pool

private theorem uniswapV3PoolPatchPreservesJumpDest5404 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨5404⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolJumpDestPatched5404 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨5404⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest5404

private theorem uniswapV3PoolPatchPreservesJumpDest5472 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨5472⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolPatchPreservesJumpDest16053 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨16053⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolPatchPreservesJumpDest5521 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨5521⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolPatchPreservesJumpDest5630 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨5630⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolIncreaseObservationCardinalityNextPatchPreservesJumpDest857 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨857⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolPatchPreservesJumpDest13186 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨13186⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolPatchPreservesJumpDest16115 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨16115⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolJumpDestPatched5472 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨5472⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest5472

theorem uniswapV3PoolJumpDestPatched16053 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨16053⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest16053

theorem uniswapV3PoolJumpDestPatched5521 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨5521⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest5521

theorem uniswapV3PoolJumpDestPatched5630 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨5630⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest5630

theorem uniswapV3PoolIncreaseObservationCardinalityNextJumpDestPatched857
    {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨857⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolIncreaseObservationCardinalityNextPatchPreservesJumpDest857

theorem uniswapV3PoolJumpDestPatched13186 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨13186⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest13186

theorem uniswapV3PoolJumpDestPatched16115 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨16115⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest16115

private theorem uniswapV3PoolIncreaseObservationCardinalityNextPatchDisjoint
    {v : PoolImmutables} {pc : UInt256} (hlo : 5404 ≤ pc.toNat)
    (hhi : pc.toNat + 33 ≤ 6603) :
    ∀ p ∈ patches v, pc.toNat + 33 ≤ p.1 ∨ p.1 + 32 ≤ pc.toNat := by
  intro p hp
  simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup] at hp
  rcases hp with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;>
    omega

private theorem uniswapV3PoolIncreaseObservationCardinalityNextGrowPatchDisjoint
    {v : PoolImmutables} {pc : UInt256} (hlo : 16053 ≤ pc.toNat)
    (hhi : pc.toNat + 33 ≤ 19295) :
    ∀ p ∈ patches v, pc.toNat + 33 ≤ p.1 ∨ p.1 + 32 ≤ pc.toNat := by
  intro p hp
  simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup] at hp
  rcases hp with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;>
    omega

private theorem uniswapV3PoolIncreaseObservationCardinalityNextMidPatchDisjoint
    {v : PoolImmutables} {pc : UInt256} (hlo : 11291 ≤ pc.toNat)
    (hhi : pc.toNat + 33 ≤ 15650) :
    ∀ p ∈ patches v, pc.toNat + 33 ≤ p.1 ∨ p.1 + 32 ≤ pc.toNat := by
  intro p hp
  simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup] at hp
  rcases hp with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;>
    omega

private theorem uniswapV3PoolIncreaseObservationCardinalityNextLockEnterOk
    {v : PoolImmutables} {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨5404⟩ R mem aw rdata (cA, σ) k C)
    (hperm : ee.perm = true)
    (hunlocked : increaseObservationCardinalityNextUnlockedByte σ ee ≠ ⟨0⟩)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨5486⟩ R mem aw rdata
      (cA, sstoreAccountMap ee.codeOwner σ ⟨0⟩
        (increaseObservationCardinalityNextLockedSlotWord σ ee)) k' C' := by
  have hdecode {pc : UInt256} (hlo : 5404 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 6603) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 6603 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolIncreaseObservationCardinalityNextPatchDisjoint hlo hhi)]
  have hd5404 : decode code ⟨5404⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5405 : decode code ⟨5405⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5407 : decode code ⟨5407⟩ = some (.SLOAD, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5408 : decode code ⟨5408⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5410 : decode code ⟨5410⟩ = some (.Push .PUSH1, some (⟨240⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5412 : decode code ⟨5412⟩ = some (.SHL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5413 : decode code ⟨5413⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5414 : decode code ⟨5414⟩ = some (.DIV, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5415 : decode code ⟨5415⟩ = some (.Push .PUSH1, some (⟨255⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5417 : decode code ⟨5417⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5418 : decode code ⟨5418⟩ = some (.Push .PUSH2, some (⟨5472⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5421 : decode code ⟨5421⟩ = some (.JUMPI, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5472 : decode code ⟨5472⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5473 : decode code ⟨5473⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5475 : decode code ⟨5475⟩ = some (.DUP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5476 : decode code ⟨5476⟩ = some (.SLOAD, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5477 : decode code ⟨5477⟩ = some (.Push .PUSH1, some (⟨255⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5479 : decode code ⟨5479⟩ = some (.Push .PUSH1, some (⟨240⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5481 : decode code ⟨5481⟩ = some (.SHL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5482 : decode code ⟨5482⟩ = some (.NOT, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5483 : decode code ⟨5483⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5484 : decode code ⟨5484⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5485 : decode code ⟨5485⟩ = some (.SSTORE, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have rd5405 : RD code ee g s0 ⟨5405⟩ R mem aw rdata (cA, σ) (k + 1) (C + 1) := by
    simpa using h.jumpdest hd5404 (by evm_ov)
  have rd5407 : RD code ee g s0 ⟨5407⟩ (⟨0⟩ :: R) mem aw rdata (cA, σ)
      (k + 1 + 1) (C + 1 + 3) := by
    simpa using rd5405.push1 ⟨0⟩ hd5405 (by evm_ov)
  obtain ⟨_, _, rd5408₀⟩ := rd5407.sload hd5407 (by evm_ov)
  have rd5408 := by
    simpa [solcSlotWord] using rd5408₀
  have rd5410 := by
    simpa using rd5408.push1 ⟨1⟩ hd5408 (by evm_ov)
  have rd5412 := by
    simpa using rd5410.push1 ⟨240⟩ hd5410 (by evm_ov)
  have rd5413 := by
    simpa [increaseObservationCardinalityNextUnlockedShift] using
      rd5412.shl hd5412 (by evm_ov)
  have rd5414 := by
    simpa using rd5413.swap1 hd5413 (by evm_ov)
  have rd5415 := by
    simpa using rd5414.div hd5414 (by evm_ov)
  have rd5417 := by
    simpa [increaseObservationCardinalityNextUint8Mask] using
      rd5415.push1 ⟨255⟩ hd5415 (by evm_ov)
  have rd5418 := by
    simpa [increaseObservationCardinalityNextUnlockedByte] using rd5417.and hd5417
      (by evm_ov)
  have rd5421 := by
    simpa using rd5418.push2 ⟨5472⟩ hd5418 (by evm_ov)
  have rd5472 := rd5421.jumpiT hd5421 hunlocked
    (uniswapV3PoolJumpDestPatched5472 hpatch) (by evm_ov)
  have rd5473 := by
    simpa using rd5472.jumpdest hd5472 (by evm_ov)
  have rd5475 := by
    simpa using rd5473.push1 ⟨0⟩ hd5473 (by evm_ov)
  have rd5476 := by
    simpa using rd5475.dup1 hd5475 (by evm_ov)
  obtain ⟨_, _, rd5477₀⟩ := rd5476.sload hd5476 (by evm_ov)
  have rd5477 := by
    simpa [solcSlotWord] using rd5477₀
  have rd5479 := by
    simpa [increaseObservationCardinalityNextUint8Mask] using
      rd5477.push1 ⟨255⟩ hd5477 (by evm_ov)
  have rd5481 := by
    simpa using rd5479.push1 ⟨240⟩ hd5479 (by evm_ov)
  have rd5482 := by
    simpa using rd5481.shl hd5481 (by evm_ov)
  have rd5483 := by
    simpa [increaseObservationCardinalityNextUnlockedClearMask] using rd5482.not
      hd5482 (by evm_ov)
  have rd5484 := by
    simpa [increaseObservationCardinalityNextLockedSlotWord] using rd5483.and hd5483
      (by evm_ov)
  have rd5485 := by
    simpa using rd5484.swap1 hd5484 (by evm_ov)
  exact rd5485.sstore hperm hd5485 (by
    omega)

private theorem uniswapV3PoolIncreaseObservationCardinalityNextLockedRevertTailWf
    {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    solcErrorStringRevertTailWf code ⟨5422⟩ ⟨3⟩ ⟨5001035⟩ ⟨232⟩ .PUSH3 3 := by
  have hdecode {pc : UInt256} (hlo : 5404 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 6603) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 6603 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolIncreaseObservationCardinalityNextPatchDisjoint hlo hhi)]
  dsimp [solcErrorStringRevertTailWf]
  repeat' constructor
  all_goals
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide

private theorem uniswapV3PoolIncreaseObservationCardinalityNextLockEnterLockedRevert
    {v : PoolImmutables} {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨5404⟩ R solcFreePtrMem (UInt256.ofNat 3) rdata
      (cA, σ) k C)
    (hlocked : increaseObservationCardinalityNextUnlockedByte σ ee = ⟨0⟩)
    (hov : R.length + 6 ≤ 1024) :
    RDrev code g s0 := by
  have hdecode {pc : UInt256} (hlo : 5404 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 6603) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 6603 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolIncreaseObservationCardinalityNextPatchDisjoint hlo hhi)]
  have hd5404 : decode code ⟨5404⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5405 : decode code ⟨5405⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5407 : decode code ⟨5407⟩ = some (.SLOAD, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5408 : decode code ⟨5408⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5410 : decode code ⟨5410⟩ = some (.Push .PUSH1, some (⟨240⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5412 : decode code ⟨5412⟩ = some (.SHL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5413 : decode code ⟨5413⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5414 : decode code ⟨5414⟩ = some (.DIV, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5415 : decode code ⟨5415⟩ = some (.Push .PUSH1, some (⟨255⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5417 : decode code ⟨5417⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5418 : decode code ⟨5418⟩ = some (.Push .PUSH2, some (⟨5472⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd5421 : decode code ⟨5421⟩ = some (.JUMPI, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have rd5405 : RD code ee g s0 ⟨5405⟩ R solcFreePtrMem (UInt256.ofNat 3) rdata
      (cA, σ) (k + 1) (C + 1) := by
    simpa using h.jumpdest hd5404 (by evm_ov)
  have rd5407 : RD code ee g s0 ⟨5407⟩ (⟨0⟩ :: R) solcFreePtrMem
      (UInt256.ofNat 3) rdata (cA, σ) (k + 1 + 1) (C + 1 + 3) := by
    simpa using rd5405.push1 ⟨0⟩ hd5405 (by evm_ov)
  obtain ⟨_, _, rd5408₀⟩ := rd5407.sload hd5407 (by evm_ov)
  have rd5408 := by
    simpa [solcSlotWord] using rd5408₀
  have rd5410 := by
    simpa using rd5408.push1 ⟨1⟩ hd5408 (by evm_ov)
  have rd5412 := by
    simpa using rd5410.push1 ⟨240⟩ hd5410 (by evm_ov)
  have rd5413 := by
    simpa [increaseObservationCardinalityNextUnlockedShift] using
      rd5412.shl hd5412 (by evm_ov)
  have rd5414 := by
    simpa using rd5413.swap1 hd5413 (by evm_ov)
  have rd5415 := by
    simpa using rd5414.div hd5414 (by evm_ov)
  have rd5417 := by
    simpa [increaseObservationCardinalityNextUint8Mask] using
      rd5415.push1 ⟨255⟩ hd5415 (by evm_ov)
  have rd5418 := by
    simpa [increaseObservationCardinalityNextUnlockedByte] using rd5417.and hd5417
      (by evm_ov)
  have rd5421 := by
    simpa using rd5418.push2 ⟨5472⟩ hd5418 (by evm_ov)
  have rd5422 := rd5421.jumpiNT hd5421 hlocked (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨5422⟩) (len := ⟨3⟩) (rawWord := ⟨5001035⟩) (shift := ⟨232⟩)
    (word := UInt256.shiftLeft ⟨5001035⟩ ⟨232⟩) (op := .PUSH3) (width := 3)
    rd5422
    (uniswapV3PoolIncreaseObservationCardinalityNextLockedRevertTailWf hpatch)
    (by native_decide)
    rfl
    solcFreePtrMem_size
    solcFreePtrMem_read64
    (by omega)

private theorem uniswapV3PoolIncreaseObservationCardinalityNextOldZeroRevertTailWf
    {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    solcErrorStringRevertTailWf code ⟨16067⟩ ⟨1⟩ ⟨73⟩ ⟨248⟩ .PUSH1 1 := by
  have hdecode {pc : UInt256} (hlo : 16053 ≤ pc.toNat)
      (hhi : pc.toNat + 33 ≤ 19295) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 19295 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolIncreaseObservationCardinalityNextGrowPatchDisjoint hlo hhi)]
  dsimp [solcErrorStringRevertTailWf]
  repeat' constructor
  all_goals
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide

private theorem uniswapV3PoolIncreaseObservationCardinalityNextAfterNoDelegateOldZeroRevert
    {v : PoolImmutables} {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨5493⟩
      (increaseObservationCardinalityNextArgWord ee :: ⟨857⟩ :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hzero : increaseObservationCardinalityNextOldWord σ ee = ⟨0⟩)
    (hov : R.length + 14 ≤ 1024) :
    RDrev code g s0 := by
  have hdecodeBody {pc : UInt256} (hlo : 5404 ≤ pc.toNat)
      (hhi : pc.toNat + 33 ≤ 6603) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 6603 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolIncreaseObservationCardinalityNextPatchDisjoint hlo hhi)]
  have hdecodeGrow {pc : UInt256} (hlo : 16053 ≤ pc.toNat)
      (hhi : pc.toNat + 33 ≤ 19295) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 19295 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolIncreaseObservationCardinalityNextGrowPatchDisjoint hlo hhi)]
  have hd5493 : decode code ⟨5493⟩ = some (.JUMPDEST, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]
    native_decide
  have hd5494 : decode code ⟨5494⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]
    native_decide
  have hd5496 : decode code ⟨5496⟩ = some (.DUP1, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]
    native_decide
  have hd5497 : decode code ⟨5497⟩ = some (.SLOAD, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]
    native_decide
  have hd5498 : decode code ⟨5498⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]
    native_decide
  have hd5500 : decode code ⟨5500⟩ = some (.Push .PUSH1, some (⟨216⟩, 1)) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]
    native_decide
  have hd5502 : decode code ⟨5502⟩ = some (.SHL, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]
    native_decide
  have hd5503 : decode code ⟨5503⟩ = some (.SWAP1, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]
    native_decide
  have hd5504 : decode code ⟨5504⟩ = some (.DIV, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]
    native_decide
  have hd5505 : decode code ⟨5505⟩ = some (.Push .PUSH2, some (⟨65535⟩, 2)) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]
    native_decide
  have hd5508 : decode code ⟨5508⟩ = some (.AND, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]
    native_decide
  have hd5509 : decode code ⟨5509⟩ = some (.SWAP1, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]
    native_decide
  have hd5510 : decode code ⟨5510⟩ = some (.Push .PUSH2, some (⟨5521⟩, 2)) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]
    native_decide
  have hd5513 : decode code ⟨5513⟩ = some (.Push .PUSH1, some (⟨8⟩, 1)) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]
    native_decide
  have hd5515 : decode code ⟨5515⟩ = some (.DUP4, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]
    native_decide
  have hd5516 : decode code ⟨5516⟩ = some (.DUP6, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]
    native_decide
  have hd5517 : decode code ⟨5517⟩ = some (.Push .PUSH2, some (⟨16053⟩, 2)) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]
    native_decide
  have hd5520 : decode code ⟨5520⟩ = some (.JUMP, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]
    native_decide
  have hd16053 : decode code ⟨16053⟩ = some (.JUMPDEST, .none) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]
    native_decide
  have hd16054 : decode code ⟨16054⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]
    native_decide
  have hd16056 : decode code ⟨16056⟩ = some (.DUP1, .none) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]
    native_decide
  have hd16057 : decode code ⟨16057⟩ = some (.DUP4, .none) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]
    native_decide
  have hd16058 : decode code ⟨16058⟩ = some (.Push .PUSH2, some (⟨65535⟩, 2)) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]
    native_decide
  have hd16061 : decode code ⟨16061⟩ = some (.AND, .none) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]
    native_decide
  have hd16062 : decode code ⟨16062⟩ = some (.GT, .none) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]
    native_decide
  have hd16063 : decode code ⟨16063⟩ = some (.Push .PUSH2, some (⟨16115⟩, 2)) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]
    native_decide
  have hd16066 : decode code ⟨16066⟩ = some (.JUMPI, .none) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]
    native_decide
  have hshift :
      UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨216⟩ = slot0ShiftBytes 27 := by
    native_decide
  have hmask : increaseObservationCardinalityNextUint16Mask = slot0Uint16Mask := by
    native_decide
  have holdCleanL :
      UInt256.land slot0Uint16Mask (increaseObservationCardinalityNextOldWord σ ee) =
        increaseObservationCardinalityNextOldWord σ ee := by
    exact slot0Uint16Mask_clean_left
      (slot0Uint16Mask_bound (UInt256.div (slot0SlotWord σ ee) (slot0ShiftBytes 27)))
  have holdCleanR :
      UInt256.land (increaseObservationCardinalityNextOldWord σ ee) slot0Uint16Mask =
        increaseObservationCardinalityNextOldWord σ ee := by
    rw [u256_land_comm, holdCleanL]
  have holdInner :
      UInt256.land slot0Uint16Mask
          (UInt256.div (solcSlotWord σ ee ⟨0⟩) (slot0ShiftBytes 27)) =
        increaseObservationCardinalityNextOldWord σ ee := by
    rw [increaseObservationCardinalityNextOldWord, slot0ObservationCardinalityNextWord,
      slot0SlotWord, u256_land_comm]
  have hmaskedOldZero :
      UInt256.land slot0Uint16Mask
          (UInt256.land slot0Uint16Mask
            (UInt256.div (solcSlotWord σ ee ⟨0⟩) (slot0ShiftBytes 27))) =
        ⟨0⟩ := by
    rw [holdInner, holdCleanL, hzero]
  have hgtMaskedOldZero :
      UInt256.gt
          (UInt256.land (⟨65535⟩ : UInt256)
            (UInt256.land (⟨65535⟩ : UInt256)
              (UInt256.div (solcSlotWord σ ee ⟨0⟩) (slot0ShiftBytes 27))))
          ⟨0⟩ =
        ⟨0⟩ := by
    have hraw :
        UInt256.land (⟨65535⟩ : UInt256)
            (UInt256.land (⟨65535⟩ : UInt256)
              (UInt256.div (solcSlotWord σ ee ⟨0⟩) (slot0ShiftBytes 27))) =
          ⟨0⟩ := by
      simpa [slot0Uint16Mask] using hmaskedOldZero
    rw [hraw]
    native_decide
  have rd5494 := by
    simpa using h.jumpdest hd5493 (by evm_ov)
  have rd5496 := by
    simpa using rd5494.push1 ⟨0⟩ hd5494 (by evm_ov)
  have rd5497 := by
    simpa using rd5496.dup1 hd5496 (by evm_ov)
  obtain ⟨_, _, rd5498₀⟩ := rd5497.sload hd5497 (by evm_ov)
  have rd5498 := by
    simpa [solcSlotWord] using rd5498₀
  have rd5500 := by
    simpa using rd5498.push1 ⟨1⟩ hd5498 (by evm_ov)
  have rd5502 := by
    simpa using rd5500.push1 ⟨216⟩ hd5500 (by evm_ov)
  have rd5503 := by
    simpa using rd5502.shl hd5502 (by evm_ov)
  have rd5504 := by
    simpa using rd5503.swap1 hd5503 (by evm_ov)
  have rd5505 := by
    simpa [hshift] using rd5504.div hd5504 (by evm_ov)
  have rd5508 := by
    simpa [increaseObservationCardinalityNextUint16Mask, hmask,
      increaseObservationCardinalityNextOldWord, slot0ObservationCardinalityNextWord,
      slot0SlotWord, solcSlotWord] using rd5505.push2 ⟨65535⟩ hd5505 (by evm_ov)
  have rd5509 := by
    simpa [increaseObservationCardinalityNextOldWord, slot0ObservationCardinalityNextWord,
      slot0SlotWord, solcSlotWord, hmask] using rd5508.and hd5508 (by
        simp only [List.length_cons]
        omega)
  have rd5510 := by
    simpa using rd5509.swap1 hd5509 (by evm_ov)
  have rd5513 := by
    simpa using rd5510.push2 ⟨5521⟩ hd5510 (by
      simp only [List.length_cons]
      omega)
  have rd5515 := by
    simpa using rd5513.push1 ⟨8⟩ hd5513 (by
      simp only [List.length_cons]
      omega)
  have rd5516 := by
    simpa using rd5515.dup4 hd5515 (by
      simp only [List.length_cons]
      omega)
  have rd5517 := by
    simpa using rd5516.dup6 hd5516 (by
      simp only [List.length_cons]
      omega)
  have rd5520 := by
    simpa using rd5517.push2 ⟨16053⟩ hd5517 (by
      simp only [List.length_cons]
      omega)
  have rd16053 := rd5520.jump hd5520 (uniswapV3PoolJumpDestPatched16053 hpatch)
    (by simp only [List.length_cons]; omega)
  have rd16054 := by
    simpa using rd16053.jumpdest hd16053 (by
      simp only [List.length_cons]
      omega)
  have rd16056 := by
    simpa using rd16054.push1 ⟨0⟩ hd16054 (by
      simp only [List.length_cons]
      omega)
  have rd16057 := by
    simpa using rd16056.dup1 hd16056 (by
      simp only [List.length_cons]
      omega)
  have rd16058 := by
    simpa using rd16057.dup4 hd16057 (by
      simp only [List.length_cons]
      omega)
  have rd16061 := by
    simpa [hmask, holdCleanL, holdCleanR] using rd16058.push2 ⟨65535⟩ hd16058 (by
      simp only [List.length_cons]
      omega)
  have rd16062 := by
    simpa [hmask, holdCleanL, holdCleanR] using rd16061.and hd16061 (by
      simp only [List.length_cons]
      omega)
  have rd16063 := by
    simpa [hmask, solcSlotWord, hmaskedOldZero] using rd16062.gt hd16062 (by
      simp only [List.length_cons]
      omega)
  have rd16066 := by
    simpa using rd16063.push2 ⟨16115⟩ hd16063 (by
      simp only [List.length_cons]
      omega)
  have rd16067 := rd16066.jumpiNT hd16066 (by
      simpa [solcSlotWord] using hgtMaskedOldZero)
    (by simp only [List.length_cons]; omega)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨16067⟩) (len := ⟨1⟩) (rawWord := ⟨73⟩) (shift := ⟨248⟩)
    (word := UInt256.shiftLeft ⟨73⟩ ⟨248⟩) (op := .PUSH1) (width := 1)
    rd16067
    (uniswapV3PoolIncreaseObservationCardinalityNextOldZeroRevertTailWf hpatch)
    (by native_decide)
    rfl
    solcFreePtrMem_size
    solcFreePtrMem_read64
    (by simp only [List.length_cons]; omega)

private theorem uniswapV3PoolIncreaseObservationCardinalityNextAfterNoDelegateNoGrowReturn
    {v : PoolImmutables} {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨5493⟩
      (increaseObservationCardinalityNextArgWord ee :: ⟨857⟩ :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (holdNonzero : increaseObservationCardinalityNextOldWord σ ee ≠ ⟨0⟩)
    (hnewLe : UInt256.gt (increaseObservationCardinalityNextArgWord ee)
        (increaseObservationCardinalityNextOldWord σ ee) = ⟨0⟩)
    (hov : R.length + 14 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨5521⟩
      (increaseObservationCardinalityNextOldWord σ ee :: ⟨0⟩ ::
        increaseObservationCardinalityNextOldWord σ ee ::
        increaseObservationCardinalityNextArgWord ee :: ⟨857⟩ :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  have hdecodeBody {pc : UInt256} (hlo : 5404 ≤ pc.toNat)
      (hhi : pc.toNat + 33 ≤ 6603) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 6603 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolIncreaseObservationCardinalityNextPatchDisjoint hlo hhi)]
  have hdecodeGrow {pc : UInt256} (hlo : 16053 ≤ pc.toNat)
      (hhi : pc.toNat + 33 ≤ 19295) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 19295 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolIncreaseObservationCardinalityNextGrowPatchDisjoint hlo hhi)]
  have hdecodeMid {pc : UInt256} (hlo : 11291 ≤ pc.toNat)
      (hhi : pc.toNat + 33 ≤ 15650) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 15650 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolIncreaseObservationCardinalityNextMidPatchDisjoint hlo hhi)]
  have hd5493 : decode code ⟨5493⟩ = some (.JUMPDEST, .none) := by rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5494 : decode code ⟨5494⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5496 : decode code ⟨5496⟩ = some (.DUP1, .none) := by rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5497 : decode code ⟨5497⟩ = some (.SLOAD, .none) := by rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5498 : decode code ⟨5498⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5500 : decode code ⟨5500⟩ = some (.Push .PUSH1, some (⟨216⟩, 1)) := by rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5502 : decode code ⟨5502⟩ = some (.SHL, .none) := by rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5503 : decode code ⟨5503⟩ = some (.SWAP1, .none) := by rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5504 : decode code ⟨5504⟩ = some (.DIV, .none) := by rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5505 : decode code ⟨5505⟩ = some (.Push .PUSH2, some (⟨65535⟩, 2)) := by rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5508 : decode code ⟨5508⟩ = some (.AND, .none) := by rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5509 : decode code ⟨5509⟩ = some (.SWAP1, .none) := by rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5510 : decode code ⟨5510⟩ = some (.Push .PUSH2, some (⟨5521⟩, 2)) := by rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5513 : decode code ⟨5513⟩ = some (.Push .PUSH1, some (⟨8⟩, 1)) := by rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5515 : decode code ⟨5515⟩ = some (.DUP4, .none) := by rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5516 : decode code ⟨5516⟩ = some (.DUP6, .none) := by rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5517 : decode code ⟨5517⟩ = some (.Push .PUSH2, some (⟨16053⟩, 2)) := by rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5520 : decode code ⟨5520⟩ = some (.JUMP, .none) := by rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd16053 : decode code ⟨16053⟩ = some (.JUMPDEST, .none) := by rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16054 : decode code ⟨16054⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16056 : decode code ⟨16056⟩ = some (.DUP1, .none) := by rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16057 : decode code ⟨16057⟩ = some (.DUP4, .none) := by rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16058 : decode code ⟨16058⟩ = some (.Push .PUSH2, some (⟨65535⟩, 2)) := by rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16061 : decode code ⟨16061⟩ = some (.AND, .none) := by rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16062 : decode code ⟨16062⟩ = some (.GT, .none) := by rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16063 : decode code ⟨16063⟩ = some (.Push .PUSH2, some (⟨16115⟩, 2)) := by rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16066 : decode code ⟨16066⟩ = some (.JUMPI, .none) := by rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16115 : decode code ⟨16115⟩ = some (.JUMPDEST, .none) := by rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16116 : decode code ⟨16116⟩ = some (.DUP3, .none) := by rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16117 : decode code ⟨16117⟩ = some (.Push .PUSH2, some (⟨65535⟩, 2)) := by rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16120 : decode code ⟨16120⟩ = some (.AND, .none) := by rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16121 : decode code ⟨16121⟩ = some (.DUP3, .none) := by rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16122 : decode code ⟨16122⟩ = some (.Push .PUSH2, some (⟨65535⟩, 2)) := by rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16125 : decode code ⟨16125⟩ = some (.AND, .none) := by rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16126 : decode code ⟨16126⟩ = some (.GT, .none) := by rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16127 : decode code ⟨16127⟩ = some (.Push .PUSH2, some (⟨16137⟩, 2)) := by rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16130 : decode code ⟨16130⟩ = some (.JUMPI, .none) := by rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16131 : decode code ⟨16131⟩ = some (.POP, .none) := by rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16132 : decode code ⟨16132⟩ = some (.DUP2, .none) := by rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16133 : decode code ⟨16133⟩ = some (.Push .PUSH2, some (⟨13186⟩, 2)) := by rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16136 : decode code ⟨16136⟩ = some (.JUMP, .none) := by rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd13186 : decode code ⟨13186⟩ = some (.JUMPDEST, .none) := by rw [hdecodeMid (by native_decide) (by native_decide)]; native_decide
  have hd13187 : decode code ⟨13187⟩ = some (.SWAP4, .none) := by rw [hdecodeMid (by native_decide) (by native_decide)]; native_decide
  have hd13188 : decode code ⟨13188⟩ = some (.SWAP3, .none) := by rw [hdecodeMid (by native_decide) (by native_decide)]; native_decide
  have hd13189 : decode code ⟨13189⟩ = some (.POP, .none) := by rw [hdecodeMid (by native_decide) (by native_decide)]; native_decide
  have hd13190 : decode code ⟨13190⟩ = some (.POP, .none) := by rw [hdecodeMid (by native_decide) (by native_decide)]; native_decide
  have hd13191 : decode code ⟨13191⟩ = some (.POP, .none) := by rw [hdecodeMid (by native_decide) (by native_decide)]; native_decide
  have hd13192 : decode code ⟨13192⟩ = some (.JUMP, .none) := by rw [hdecodeMid (by native_decide) (by native_decide)]; native_decide
  have hshift :
      UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨216⟩ = slot0ShiftBytes 27 := by
    native_decide
  have hmask : increaseObservationCardinalityNextUint16Mask = slot0Uint16Mask := by
    native_decide
  have holdCleanL :
      UInt256.land slot0Uint16Mask (increaseObservationCardinalityNextOldWord σ ee) =
        increaseObservationCardinalityNextOldWord σ ee := by
    exact slot0Uint16Mask_clean_left
      (slot0Uint16Mask_bound (UInt256.div (slot0SlotWord σ ee) (slot0ShiftBytes 27)))
  have holdCleanR :
      UInt256.land (increaseObservationCardinalityNextOldWord σ ee) slot0Uint16Mask =
        increaseObservationCardinalityNextOldWord σ ee := by
    rw [u256_land_comm, holdCleanL]
  have hnewCanon :
      (increaseObservationCardinalityNextArgWord ee).toNat < EVM.twoPow 16 := by
    simpa [increaseObservationCardinalityNextArgWord, hmask] using
      slot0Uint16Mask_bound (calldataWord ee.calldata 4)
  have hnewCleanL :
      UInt256.land slot0Uint16Mask (increaseObservationCardinalityNextArgWord ee) =
        increaseObservationCardinalityNextArgWord ee := by
    exact slot0Uint16Mask_clean_left hnewCanon
  have hnewCleanR :
      UInt256.land (increaseObservationCardinalityNextArgWord ee) slot0Uint16Mask =
        increaseObservationCardinalityNextArgWord ee := by
    rw [u256_land_comm, hnewCleanL]
  have holdInner :
      UInt256.land slot0Uint16Mask
          (UInt256.div (solcSlotWord σ ee ⟨0⟩) (slot0ShiftBytes 27)) =
        increaseObservationCardinalityNextOldWord σ ee := by
    rw [increaseObservationCardinalityNextOldWord, slot0ObservationCardinalityNextWord,
      slot0SlotWord, u256_land_comm]
  have hmaskedOld :
      UInt256.land slot0Uint16Mask
          (UInt256.land slot0Uint16Mask
            (UInt256.div (solcSlotWord σ ee ⟨0⟩) (slot0ShiftBytes 27))) =
        increaseObservationCardinalityNextOldWord σ ee := by
    rw [holdInner, holdCleanL]
  have holdRaw :
      UInt256.land (⟨65535⟩ : UInt256)
          (UInt256.div (solcSlotWord σ ee ⟨0⟩) (slot0ShiftBytes 27)) =
        increaseObservationCardinalityNextOldWord σ ee := by
    simpa [slot0Uint16Mask] using holdInner
  have hgtMaskedOldZero :
      UInt256.gt
          (UInt256.land (⟨65535⟩ : UInt256)
            (UInt256.land (⟨65535⟩ : UInt256)
              (UInt256.div (solcSlotWord σ ee ⟨0⟩) (slot0ShiftBytes 27))))
          ⟨0⟩ ≠
        ⟨0⟩ := by
    have hraw :
        UInt256.land (⟨65535⟩ : UInt256)
            (UInt256.land (⟨65535⟩ : UInt256)
              (UInt256.div (solcSlotWord σ ee ⟨0⟩) (slot0ShiftBytes 27))) =
          increaseObservationCardinalityNextOldWord σ ee := by
      simpa [slot0Uint16Mask] using hmaskedOld
    have holdPos : 0 < (increaseObservationCardinalityNextOldWord σ ee).toNat := by
      exact Nat.pos_of_ne_zero (by
        intro hz
        apply holdNonzero
        apply u256_inj
        simpa using hz)
    have hgtOne :
        UInt256.gt (increaseObservationCardinalityNextOldWord σ ee) ⟨0⟩ = ⟨1⟩ := by
      exact ugt_one (by simpa using holdPos)
    rw [hraw, hgtOne]
    native_decide
  have hnewLeRaw :
      UInt256.gt
          (UInt256.land (⟨65535⟩ : UInt256) (increaseObservationCardinalityNextArgWord ee))
          (UInt256.land (⟨65535⟩ : UInt256)
            (UInt256.land (⟨65535⟩ : UInt256)
              (UInt256.div (solcSlotWord σ ee ⟨0⟩) (slot0ShiftBytes 27)))) =
        ⟨0⟩ := by
    have hrawOld :
        UInt256.land (⟨65535⟩ : UInt256)
            (UInt256.land (⟨65535⟩ : UInt256)
              (UInt256.div (solcSlotWord σ ee ⟨0⟩) (slot0ShiftBytes 27))) =
          increaseObservationCardinalityNextOldWord σ ee := by
      simpa [slot0Uint16Mask] using hmaskedOld
    have hrawNew :
        UInt256.land (⟨65535⟩ : UInt256) (increaseObservationCardinalityNextArgWord ee) =
          increaseObservationCardinalityNextArgWord ee := by
      simpa [slot0Uint16Mask] using hnewCleanL
    rw [hrawNew, hrawOld]
    exact hnewLe
  have rd5494 := by
    simpa using h.jumpdest hd5493 (by evm_ov)
  have rd5496 := by
    simpa using rd5494.push1 ⟨0⟩ hd5494 (by evm_ov)
  have rd5497 := by
    simpa using rd5496.dup1 hd5496 (by evm_ov)
  obtain ⟨_, _, rd5498₀⟩ := rd5497.sload hd5497 (by evm_ov)
  have rd5498 := by
    simpa [solcSlotWord] using rd5498₀
  have rd5500 := by
    simpa using rd5498.push1 ⟨1⟩ hd5498 (by evm_ov)
  have rd5502 := by
    simpa using rd5500.push1 ⟨216⟩ hd5500 (by evm_ov)
  have rd5503 := by
    simpa using rd5502.shl hd5502 (by evm_ov)
  have rd5504 := by
    simpa using rd5503.swap1 hd5503 (by evm_ov)
  have rd5505 := by
    simpa [hshift] using rd5504.div hd5504 (by evm_ov)
  have rd5508 := by
    simpa [increaseObservationCardinalityNextUint16Mask, hmask,
      increaseObservationCardinalityNextOldWord, slot0ObservationCardinalityNextWord,
      slot0SlotWord, solcSlotWord] using rd5505.push2 ⟨65535⟩ hd5505 (by evm_ov)
  have rd5509 := by
    simpa [increaseObservationCardinalityNextOldWord, slot0ObservationCardinalityNextWord,
      slot0SlotWord, solcSlotWord, hmask] using rd5508.and hd5508 (by
        simp only [List.length_cons]
        omega)
  have rd5510 := by
    simpa using rd5509.swap1 hd5509 (by evm_ov)
  have rd5513 := by
    simpa using rd5510.push2 ⟨5521⟩ hd5510 (by
      simp only [List.length_cons]
      omega)
  have rd5515 := by
    simpa using rd5513.push1 ⟨8⟩ hd5513 (by
      simp only [List.length_cons]
      omega)
  have rd5516 := by
    simpa using rd5515.dup4 hd5515 (by
      simp only [List.length_cons]
      omega)
  have rd5517 := by
    simpa using rd5516.dup6 hd5516 (by
      simp only [List.length_cons]
      omega)
  have rd5520 := by
    simpa using rd5517.push2 ⟨16053⟩ hd5517 (by
      simp only [List.length_cons]
      omega)
  have rd16053 := rd5520.jump hd5520 (uniswapV3PoolJumpDestPatched16053 hpatch)
    (by simp only [List.length_cons]; omega)
  have rd16054 := by
    simpa using rd16053.jumpdest hd16053 (by
      simp only [List.length_cons]
      omega)
  have rd16056 := by
    simpa using rd16054.push1 ⟨0⟩ hd16054 (by
      simp only [List.length_cons]
      omega)
  have rd16057 := by
    simpa using rd16056.dup1 hd16056 (by
      simp only [List.length_cons]
      omega)
  have rd16058 := by
    simpa using rd16057.dup4 hd16057 (by
      simp only [List.length_cons]
      omega)
  have rd16061 := by
    simpa [hmask, holdCleanL, holdCleanR] using rd16058.push2 ⟨65535⟩ hd16058 (by
      simp only [List.length_cons]
      omega)
  have rd16062 := by
    simpa [hmask, holdCleanL, holdCleanR] using rd16061.and hd16061 (by
      simp only [List.length_cons]
      omega)
  have rd16063 := by
    simpa [hmask, solcSlotWord, hmaskedOld] using rd16062.gt hd16062 (by
      simp only [List.length_cons]
      omega)
  have rd16066 := by
    simpa using rd16063.push2 ⟨16115⟩ hd16063 (by
      simp only [List.length_cons]
      omega)
  have rd16115 := rd16066.jumpiT hd16066 (by
      simpa [solcSlotWord] using hgtMaskedOldZero)
    (uniswapV3PoolJumpDestPatched16115 hpatch)
    (by simp only [List.length_cons]; omega)
  have rd16116 := by
    simpa using rd16115.jumpdest hd16115 (by
      simp only [List.length_cons]
      omega)
  have rd16117 := by
    simpa using rd16116.dup3 hd16116 (by
      simp only [List.length_cons]
      omega)
  have rd16120 := by
    simpa using rd16117.push2 ⟨65535⟩ hd16117 (by
      simp only [List.length_cons]
      omega)
  have rd16121 := by
    simpa [hmask, holdCleanL, holdCleanR] using rd16120.and hd16120 (by
      simp only [List.length_cons]
      omega)
  have rd16122 := by
    simpa using rd16121.dup3 hd16121 (by
      simp only [List.length_cons]
      omega)
  have rd16125 := by
    simpa using rd16122.push2 ⟨65535⟩ hd16122 (by
      simp only [List.length_cons]
      omega)
  have rd16126 := by
    simpa [hmask, hnewCleanL, hnewCleanR] using rd16125.and hd16125 (by
      simp only [List.length_cons]
      omega)
  have rd16127 := by
    simpa using rd16126.gt hd16126 (by
      simp only [List.length_cons]
      omega)
  have rd16130 := by
    simpa using rd16127.push2 ⟨16137⟩ hd16127 (by
      simp only [List.length_cons]
      omega)
  have rd16131 := rd16130.jumpiNT hd16130 hnewLeRaw (by
    simp only [List.length_cons]
    omega)
  have rd16132 := by
    simpa using rd16131.pop hd16131 (by
      simp only [List.length_cons]
      omega)
  have rd16133 := by
    simpa using rd16132.dup2 hd16132 (by
      simp only [List.length_cons]
      omega)
  have rd16136 := by
    simpa using rd16133.push2 ⟨13186⟩ hd16133 (by
      simp only [List.length_cons]
      omega)
  have rd13186 := rd16136.jump hd16136 (uniswapV3PoolJumpDestPatched13186 hpatch)
    (by simp only [List.length_cons]; omega)
  have rd13187 := by
    simpa using rd13186.jumpdest hd13186 (by
      simp only [List.length_cons]
      omega)
  have rd13188 := by
    simpa using rd13187.swap4 hd13187 (by
      simp only [List.length_cons]
      omega)
  have rd13189 := by
    simpa using rd13188.swap3 hd13188 (by
      simp only [List.length_cons]
      omega)
  have rd13190 := by
    simpa using rd13189.pop hd13189 (by
      simp only [List.length_cons]
      omega)
  have rd13191 := by
    simpa using rd13190.pop hd13190 (by
      simp only [List.length_cons]
      omega)
  have rd13192 := by
    simpa using rd13191.pop hd13191 (by
      simp only [List.length_cons]
      omega)
  have rd5521 := rd13192.jump hd13192 (uniswapV3PoolJumpDestPatched5521 hpatch)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, by
    simpa [solcSlotWord, holdRaw] using rd5521⟩

set_option maxHeartbeats 1000000 in
private theorem uniswapV3PoolIncreaseObservationCardinalityNextNoGrowTailReturn
    {v : PoolImmutables} {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨5521⟩
      (increaseObservationCardinalityNextOldWord σ ee :: ⟨0⟩ ::
        increaseObservationCardinalityNextOldWord σ ee ::
        increaseObservationCardinalityNextArgWord ee :: ⟨857⟩ :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hperm : ee.perm = true)
    (hov : R.length + 12 ≤ 1024) :
    RDret code g s0
      (cA, sstoreAccountMap ee.codeOwner
        (sstoreAccountMap ee.codeOwner σ ⟨0⟩
          (increaseObservationCardinalityNextEvmNoGrowObsNextSlotWord σ ee))
        ⟨0⟩
        (increaseObservationCardinalityNextEvmUnlockedTrueSlotWord
          (sstoreAccountMap ee.codeOwner σ ⟨0⟩
            (increaseObservationCardinalityNextEvmNoGrowObsNextSlotWord σ ee)) ee))
      ByteArray.empty := by
  have hdecodeBody {pc : UInt256} (hlo : 5404 ≤ pc.toNat)
      (hhi : pc.toNat + 33 ≤ 6603) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 6603 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolIncreaseObservationCardinalityNextPatchDisjoint hlo hhi)]
  have hd5521 : decode code ⟨5521⟩ = some (.JUMPDEST, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5522 : decode code ⟨5522⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5524 : decode code ⟨5524⟩ = some (.DUP1, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5525 : decode code ⟨5525⟩ = some (.SLOAD, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5526 : decode code ⟨5526⟩ = some (.Push .PUSH2, some (⟨65535⟩, 2)) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5529 : decode code ⟨5529⟩ = some (.DUP1, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5530 : decode code ⟨5530⟩ = some (.DUP5, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5531 : decode code ⟨5531⟩ = some (.AND, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5532 : decode code ⟨5532⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5534 : decode code ⟨5534⟩ = some (.Push .PUSH1, some (⟨216⟩, 1)) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5536 : decode code ⟨5536⟩ = some (.SHL, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5537 : decode code ⟨5537⟩ = some (.DUP2, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5538 : decode code ⟨5538⟩ = some (.MUL, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5539 : decode code ⟨5539⟩ = some (.Push .PUSH2, some (⟨65535⟩, 2)) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5542 : decode code ⟨5542⟩ = some (.Push .PUSH1, some (⟨216⟩, 1)) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5544 : decode code ⟨5544⟩ = some (.SHL, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5545 : decode code ⟨5545⟩ = some (.NOT, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5546 : decode code ⟨5546⟩ = some (.SWAP1, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5547 : decode code ⟨5547⟩ = some (.SWAP4, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5548 : decode code ⟨5548⟩ = some (.AND, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5549 : decode code ⟨5549⟩ = some (.SWAP3, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5550 : decode code ⟨5550⟩ = some (.SWAP1, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5551 : decode code ⟨5551⟩ = some (.SWAP3, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5552 : decode code ⟨5552⟩ = some (.OR, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5553 : decode code ⟨5553⟩ = some (.SWAP1, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5554 : decode code ⟨5554⟩ = some (.SWAP3, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5555 : decode code ⟨5555⟩ = some (.SSTORE, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5556 : decode code ⟨5556⟩ = some (.SWAP2, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5557 : decode code ⟨5557⟩ = some (.SWAP3, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5558 : decode code ⟨5558⟩ = some (.POP, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5559 : decode code ⟨5559⟩ = some (.DUP4, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5560 : decode code ⟨5560⟩ = some (.AND, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5561 : decode code ⟨5561⟩ = some (.EQ, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5562 : decode code ⟨5562⟩ = some (.Push .PUSH2, some (⟨5630⟩, 2)) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5565 : decode code ⟨5565⟩ = some (.JUMPI, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5630 : decode code ⟨5630⟩ = some (.JUMPDEST, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5631 : decode code ⟨5631⟩ = some (.POP, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5632 : decode code ⟨5632⟩ = some (.POP, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5633 : decode code ⟨5633⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5635 : decode code ⟨5635⟩ = some (.DUP1, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5636 : decode code ⟨5636⟩ = some (.SLOAD, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5637 : decode code ⟨5637⟩ = some (.Push .PUSH1, some (⟨255⟩, 1)) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5639 : decode code ⟨5639⟩ = some (.Push .PUSH1, some (⟨240⟩, 1)) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5641 : decode code ⟨5641⟩ = some (.SHL, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5642 : decode code ⟨5642⟩ = some (.NOT, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5643 : decode code ⟨5643⟩ = some (.AND, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5644 : decode code ⟨5644⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5646 : decode code ⟨5646⟩ = some (.Push .PUSH1, some (⟨240⟩, 1)) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5648 : decode code ⟨5648⟩ = some (.SHL, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5649 : decode code ⟨5649⟩ = some (.OR, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5650 : decode code ⟨5650⟩ = some (.SWAP1, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5651 : decode code ⟨5651⟩ = some (.SSTORE, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5652 : decode code ⟨5652⟩ = some (.POP, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5653 : decode code ⟨5653⟩ = some (.JUMP, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd857 : decode code ⟨857⟩ = some (.JUMPDEST, .none) := by
    rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
    native_decide
  have hd858 : decode code ⟨858⟩ = some (.STOP, .none) := by
    rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
    native_decide
  have rd5525 := evm_run h with [
    raw jumpdest hd5521 (by evm_ov),
    raw push1 ⟨0⟩ hd5522 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw dup1 hd5524 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega)]
  obtain ⟨_, _, rd5526₀⟩ := rd5525.sload hd5525 (by
    have h := hov
    simp only [List.length_cons] at h ⊢
    omega)
  have rd5555 := evm_run rd5526₀ with [
    raw push2 ⟨65535⟩ hd5526 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw dup1 hd5529 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw dup5 hd5530 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw and hd5531 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw push1 ⟨1⟩ hd5532 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw push1 ⟨216⟩ hd5534 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw shl hd5536 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw dup2 hd5537 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw mul hd5538 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw push2 ⟨65535⟩ hd5539 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw push1 ⟨216⟩ hd5542 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw shl hd5544 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw not hd5545 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw swap1 hd5546 (by evm_ov),
    raw swap4 hd5547 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw and hd5548 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw swap3 hd5549 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw swap1 hd5550 (by evm_ov),
    raw swap3 hd5551 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw lor hd5552 (by evm_ov),
    raw swap1 hd5553 (by evm_ov),
    raw swap3 hd5554 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega)]
  obtain ⟨_, _, rd5556₀⟩ := rd5555.sstore hperm hd5555 (by evm_ov)
  have rd5556 := by
    simpa [increaseObservationCardinalityNextEvmNoGrowObsNextSlotWord,
      codeOwnerStorageWord] using rd5556₀
  have rd5565 := evm_run rd5556 with [
    raw swap2 hd5556 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw swap3 hd5557 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw pop hd5558 (by evm_ov),
    raw dup4 hd5559 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw and hd5560 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw eq hd5561 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw push2 ⟨5630⟩ hd5562 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega)]
  have rd5630 := rd5565.jumpiT hd5565 (by
      rw [u256_eq_refl]
      exact one_ne_zero_uint)
    (uniswapV3PoolJumpDestPatched5630 hpatch)
    (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega)
  have rd5636 := evm_run rd5630 with [
    raw jumpdest hd5630 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw pop hd5631 (by evm_ov),
    raw pop hd5632 (by evm_ov),
    raw push1 ⟨0⟩ hd5633 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw dup1 hd5635 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega)]
  obtain ⟨_, _, rd5637₀⟩ := rd5636.sload hd5636 (by
    have h := hov
    simp only [List.length_cons] at h ⊢
    omega)
  have rd5651 := evm_run rd5637₀ with [
    raw push1 ⟨255⟩ hd5637 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw push1 ⟨240⟩ hd5639 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw shl hd5641 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw not hd5642 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw and hd5643 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw push1 ⟨1⟩ hd5644 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw push1 ⟨240⟩ hd5646 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw shl hd5648 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw lor hd5649 (by evm_ov),
    raw swap1 hd5650 (by evm_ov)]
  obtain ⟨_, _, rd5652₀⟩ := rd5651.sstore hperm hd5651 (by evm_ov)
  have rd5652 := by
    simpa [increaseObservationCardinalityNextEvmUnlockedTrueSlotWord,
      slot0UnlockedClearMask, codeOwnerStorageWord] using rd5652₀
  have rd5653 := evm_run rd5652 with [
    raw pop hd5652 (by evm_ov)]
  have rd857 := rd5653.jump hd5653
    (uniswapV3PoolIncreaseObservationCardinalityNextJumpDestPatched857 hpatch)
    (by evm_ov)
  have rd858 := rd857.jumpdest hd857 (by evm_ov)
  have hpc858 : (⟨857⟩ : UInt256) + ⟨1⟩ = ⟨858⟩ := by
    native_decide
  obtain ⟨_, _, rd858'⟩ : ∃ k' C', RD code ee g s0 ⟨858⟩ R solcFreePtrMem
      (UInt256.ofNat 3) rdata
      (cA, sstoreAccountMap ee.codeOwner
        (sstoreAccountMap ee.codeOwner σ ⟨0⟩
          (increaseObservationCardinalityNextEvmNoGrowObsNextSlotWord σ ee))
        ⟨0⟩
        (increaseObservationCardinalityNextEvmUnlockedTrueSlotWord
          (sstoreAccountMap ee.codeOwner σ ⟨0⟩
            (increaseObservationCardinalityNextEvmNoGrowObsNextSlotWord σ ee)) ee))
      k' C' := by
    exact ⟨_, _, by
      simpa [increaseObservationCardinalityNextEvmNoGrowObsNextSlotWord,
        increaseObservationCardinalityNextEvmUnlockedTrueSlotWord, slot0UnlockedClearMask,
        codeOwnerStorageWord, hpc858] using rd858⟩
  exact rd858'.stop hd858 (by
    have h := hov
    omega)

private theorem uniswapV3PoolIncreaseObservationCardinalityNextDecodedReachRoutine
    {v : PoolImmutables} {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {de ret : UInt256} {R : List UInt256} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨846⟩ (de :: ⟨4⟩ :: ret :: R) mem aw rdata acc k C)
    (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨5404⟩
      (increaseObservationCardinalityNextArgWord ee :: ret :: R) mem aw rdata acc k' C' := by
  have harg :
      UInt256.land increaseObservationCardinalityNextUint16Mask (calldataWord ee.calldata 4) =
        increaseObservationCardinalityNextArgWord ee := by
    rw [increaseObservationCardinalityNextArgWord, u256_land_comm]
  have rd847 : RD code ee g s0 ⟨847⟩ (de :: ⟨4⟩ :: ret :: R)
      mem aw rdata acc (k + 1) (C + 1) := by
    simpa using h.jumpdest
      (by
        rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
        native_decide)
      (by evm_ov)
  have rd848 : RD code ee g s0 ⟨848⟩ (⟨4⟩ :: ret :: R)
      mem aw rdata acc (k + 1 + 1) (C + 1 + 2) := by
    simpa using rd847.pop
      (by
        rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
        native_decide)
      (by evm_ov)
  have rd849 : RD code ee g s0 ⟨849⟩ (calldataWord ee.calldata 4 :: ret :: R)
      mem aw rdata acc (k + 1 + 1 + 1) (C + 1 + 2 + 3) := by
    simpa [calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide] using
      (rd848.calldataload
        (by
          rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
          native_decide)
        (by evm_ov))
  have rd852 : RD code ee g s0 ⟨852⟩
      (increaseObservationCardinalityNextUint16Mask :: calldataWord ee.calldata 4 :: ret :: R)
      mem aw rdata acc (k + 1 + 1 + 1 + 1) (C + 1 + 2 + 3 + 3) := by
    simpa [increaseObservationCardinalityNextUint16Mask] using rd849.push2 ⟨65535⟩
      (by
        rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
        native_decide)
      (by evm_ov)
  have rd853 : RD code ee g s0 ⟨853⟩
      (increaseObservationCardinalityNextArgWord ee :: ret :: R)
      mem aw rdata acc (k + 1 + 1 + 1 + 1 + 1) (C + 1 + 2 + 3 + 3 + 3) := by
    simpa [harg] using rd852.and
      (by
        rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
        native_decide)
      (by
        simp only [List.length_cons]
        omega)
  have rd856 : RD code ee g s0 ⟨856⟩
      (⟨5404⟩ :: increaseObservationCardinalityNextArgWord ee :: ret :: R)
      mem aw rdata acc (k + 1 + 1 + 1 + 1 + 1 + 1) (C + 1 + 2 + 3 + 3 + 3 + 3) := by
    simpa using rd853.push2 ⟨5404⟩
      (by
        rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
        native_decide)
      (by evm_ov)
  exact ⟨_, _, rd856.jump
    (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide)
    (uniswapV3PoolJumpDestPatched5404 hpatch)
    (by evm_ov)⟩

set_option maxHeartbeats 3000000 in
private theorem uniswapV3PoolIncreaseObservationCardinalityNextExternalLenOk
    {v : PoolImmutables} {code : ByteArray} {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hreach : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨824⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨846⟩
      (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩ :: ⟨4⟩ :: ⟨857⟩ ::
        [solcSelectorWord I])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  exact RD.solcExternalStaticArgsLenOk (need := ⟨32⟩)
    (entry := ⟨824⟩) (ret := ⟨857⟩) (decoded := ⟨846⟩) hreach
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (uniswapV3PoolJumpDestPatched2258 hpatch (by native_decide))
    (solcDecodeLenCheckOkUnsigned (by simpa using hsz36) hsize)

theorem uniswapV3PoolIncreaseObservationCardinalityNextEvmDecodeShort
    {v : PoolImmutables} {code : ByteArray} {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : (uniswapV3PoolSelBytes 5 == I.calldata.extract 0 4) = true)
    (hshort : I.calldata.size < 36) :
    RDrev code g (initState cA gh bl σ σ₀ g A I) := by
  have hreach := uniswapV3PoolIncreaseObservationCardinalityNextReachEntry
    (v := v) (code := code) (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hpatch hcode hwv hsz hsize hsel
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by
      rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]
      omega) hsize]
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
    rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]
    omega
  exact RD.solcExternalStaticArgsShortReverts (need := ⟨32⟩)
    (entry := ⟨824⟩) (ret := ⟨857⟩) (decoded := ⟨846⟩) hreach
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    hlt

theorem uniswapV3PoolIncreaseObservationCardinalityNextBodyCore {v : PoolImmutables}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsel : (uniswapV3PoolSelBytes 5 == I.calldata.extract 0 4) = true) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdispatch :=
    uniswapV3PoolDispatch_increaseObservationCardinalityNext (v := v) (cd := I.calldata) hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · have hdecode :=
      uniswapV3PoolIncreaseObservationCardinalityNextDecodeOk (v := v) (I := I) hsz36
    have hreach := uniswapV3PoolIncreaseObservationCardinalityNextReachEntry
      (v := v) (code := code) (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hpatch hcode hwv hsz
      hsize hsel
    obtain ⟨_, _, hdecoded⟩ :=
      uniswapV3PoolIncreaseObservationCardinalityNextExternalLenOk
        (v := v) (code := code) (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
        (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hpatch hreach
        hsz36 hsize
    obtain ⟨_, _, hbodyEntry⟩ :=
      uniswapV3PoolIncreaseObservationCardinalityNextDecodedReachRoutine
        (v := v) (code := code) (ee := I) (g := Sat256.ofUInt256 g)
        (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (de := UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) (ret := ⟨857⟩)
        (R := [solcSelectorWord I]) (mem := solcFreePtrMem) (aw := UInt256.ofNat 3)
        (rdata := ByteArray.empty) (acc := (cA, σ_evm)) hpatch hdecoded
        (by simp only [List.length_singleton]; omega)
    by_cases hunlocked : increaseObservationCardinalityNextUnlockedByte σ_evm I ≠ ⟨0⟩
    · have hlockProgress :
          ∃ k C, RD code I (Sat256.ofUInt256 g)
            (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨5486⟩
            (increaseObservationCardinalityNextArgWord I :: ⟨857⟩ :: [solcSelectorWord I])
            solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
            (cA, sstoreAccountMap I.codeOwner σ_evm ⟨0⟩
              (increaseObservationCardinalityNextLockedSlotWord σ_evm I)) k C :=
        uniswapV3PoolIncreaseObservationCardinalityNextLockEnterOk
          (v := v) (code := code) (ee := I) (g := Sat256.ofUInt256 g)
          (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
          (R := increaseObservationCardinalityNextArgWord I :: ⟨857⟩ :: [solcSelectorWord I])
          (mem := solcFreePtrMem) (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
          (cA := cA) (σ := σ_evm) hpatch hbodyEntry _hperm hunlocked
          (by norm_num)
      have hunlockedSolm :
          increaseObservationCardinalityNextUnlockedByte σ_solm I ≠ ⟨0⟩ := by
        rw [increaseObservationCardinalityNextUnlockedByte_transport
          (σ_evm := σ_evm) (σ_solm := σ_solm) hAccounts]
        exact hunlocked
      have hsourceLock :=
        uniswapV3PoolIncreaseObservationCardinalityNextSourceLockPrefixExact (v := v)
          (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A)
          (I := I) (g := Sat256.ofUInt256 g) hwv hunlockedSolm
      have hlockedWord :
          increaseObservationCardinalityNextLockedSlotWord σ_solm I =
            increaseObservationCardinalityNextLockedSlotWord σ_evm I :=
        increaseObservationCardinalityNextLockedSlotWord_transport (σ_evm := σ_evm)
          (σ_solm := σ_solm) hAccounts
      have hAccountsAfterLock :
          accountMapEquiv
            (sstoreAccountMap I.codeOwner σ_evm ⟨0⟩
              (increaseObservationCardinalityNextLockedSlotWord σ_evm I))
            (sstoreAccountMap I.codeOwner σ_solm ⟨0⟩
              (increaseObservationCardinalityNextLockedSlotWord σ_solm I)) := by
        rw [hlockedWord]
        exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨0⟩
          (increaseObservationCardinalityNextLockedSlotWord σ_evm I) hAccounts
      have hsourceLockState :
          Solm.EVM.storageStore (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              I.codeOwner ⟨0⟩
              (increaseObservationCardinalityNextLockedSlotWord σ_solm I) =
            initState cA gh bl
              (sstoreAccountMap I.codeOwner σ_solm ⟨0⟩
                (increaseObservationCardinalityNextLockedSlotWord σ_solm I))
              σ₀ (Sat256.ofUInt256 g) A I := by
        unfold Solm.EVM.storageStore State.lookupAccount sstoreAccountMap
        cases hlookup : σ_solm.find? I.codeOwner with
        | none =>
            simp [initState, Option.option, hlookup]
        | some _ =>
            simp [initState, State.setAccount, Account.updateStorage, Option.option, hlookup]
      have hsourceLockInit :
          ExecBlock (config v)
            { contract := contract v, locals := increaseObservationCardinalityNextStore I }
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
              .require (.storage (slot0F "unlocked")),
              .assign .storage (slot0F "unlocked") (.boolLit false) ]
            (.ok { contract := contract v, locals := increaseObservationCardinalityNextStore I }
              (initState cA gh bl
                (sstoreAccountMap I.codeOwner σ_solm ⟨0⟩
                  (increaseObservationCardinalityNextLockedSlotWord σ_solm I))
                σ₀ (Sat256.ofUInt256 g) A I)) := by
        simpa [hsourceLockState] using hsourceLock
      obtain ⟨kLock, CLock, hrdAfterLock⟩ := hlockProgress
      by_cases hnoDelegate : uniswapV3PoolNoDelegateCallGuard v I ≠ ⟨0⟩
      · obtain ⟨kNoDelegate, CNoDelegate, hrdNoDelegate⟩ :=
          uniswapV3PoolNoDelegateCallOk (v := v) (code := code) (ee := I)
            (g := Sat256.ofUInt256 g)
            (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
            (R := increaseObservationCardinalityNextArgWord I :: ⟨857⟩ :: [solcSelectorWord I])
            (mem := solcFreePtrMem) (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
            (acc := (cA, sstoreAccountMap I.codeOwner σ_evm ⟨0⟩
              (increaseObservationCardinalityNextLockedSlotWord σ_evm I)))
            hpatch hrdAfterLock hnoDelegate (by norm_num)
        have hsourceNoDelegate :
            ExecBlock (config v)
              { contract := contract v, locals := increaseObservationCardinalityNextStore I }
              (initState cA gh bl
                (sstoreAccountMap I.codeOwner σ_solm ⟨0⟩
                  (increaseObservationCardinalityNextLockedSlotWord σ_solm I))
                σ₀ (Sat256.ofUInt256 g) A I)
              [ .require (.binary .eq (.env .this) (addrLit v.original)) ]
              (.ok { contract := contract v, locals := increaseObservationCardinalityNextStore I }
                (initState cA gh bl
                  (sstoreAccountMap I.codeOwner σ_solm ⟨0⟩
                    (increaseObservationCardinalityNextLockedSlotWord σ_solm I))
                  σ₀ (Sat256.ofUInt256 g) A I)) := by
          exact ExecBlock.consNormal
            (ExecStmt.requireTrue (uniswapV3PoolNoDelegateCallEvalTrue
              (v := v) (cA := cA) (gh := gh) (bl := bl)
              (σ := sstoreAccountMap I.codeOwner σ_solm ⟨0⟩
                (increaseObservationCardinalityNextLockedSlotWord σ_solm I))
              (σ₀ := σ₀) (A := A) (I := I)
              (L := increaseObservationCardinalityNextStore I)
              (g := Sat256.ofUInt256 g) hnoDelegate))
            ExecBlock.nil
        by_cases holdZeroEvm :
            increaseObservationCardinalityNextOldWord
              (sstoreAccountMap I.codeOwner σ_evm ⟨0⟩
                (increaseObservationCardinalityNextLockedSlotWord σ_evm I)) I = ⟨0⟩
        · have hrd :=
            uniswapV3PoolIncreaseObservationCardinalityNextAfterNoDelegateOldZeroRevert
              (v := v) (code := code) (ee := I) (g := Sat256.ofUInt256 g)
              (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
              (R := [solcSelectorWord I]) (rdata := ByteArray.empty) (cA := cA)
              (σ := sstoreAccountMap I.codeOwner σ_evm ⟨0⟩
                (increaseObservationCardinalityNextLockedSlotWord σ_evm I))
              hpatch hrdNoDelegate holdZeroEvm (by norm_num)
          have holdZeroSolm :
              increaseObservationCardinalityNextOldWord
                (sstoreAccountMap I.codeOwner σ_solm ⟨0⟩
                  (increaseObservationCardinalityNextLockedSlotWord σ_solm I)) I = ⟨0⟩ := by
            rw [increaseObservationCardinalityNextOldWord_transport hAccountsAfterLock]
            exact holdZeroEvm
          have hsourceOldZero :
              ExecBlock (config v)
                { contract := contract v, locals := increaseObservationCardinalityNextStore I }
                (initState cA gh bl
                  (sstoreAccountMap I.codeOwner σ_solm ⟨0⟩
                    (increaseObservationCardinalityNextLockedSlotWord σ_solm I))
                  σ₀ (Sat256.ofUInt256 g) A I)
                [ .letDecl "observationCardinalityNextOld" (some uint16)
                    (.storage (slot0F "observationCardinalityNext")),
                  .letDecl "observationCardinalityNextNew" (some uint16)
                    (.var "observationCardinalityNext"),
                  .require (gtE (.var "observationCardinalityNextOld") (.intLit 0)),
                  Stmt.ite (leE (.var "observationCardinalityNextNew")
                      (.var "observationCardinalityNextOld"))
                    [ .assign .localVar (varRef "observationCardinalityNextNew")
                        (.var "observationCardinalityNextOld") ]
                    [ .letDecl "i" (some uint16) (.var "observationCardinalityNextOld"),
                      .while (ltE (.var "i") (.var "observationCardinalityNextNew"))
                      [ .assign .storage (observationsRawF (.var "i") "blockTimestamp")
                            (.intLit 1),
                          .assign .localVar (varRef "i") (addE (.var "i") (.intLit 1)) ] ],
                  .assign .storage (slot0F "observationCardinalityNext")
                    (.var "observationCardinalityNextNew"),
                  .assign .storage (slot0F "unlocked") (.boolLit true) ] .reverted := by
            exact uniswapV3PoolIncreaseObservationCardinalityNextSourceOldZeroReverts
              (v := v)
              (evm := initState cA gh bl
                (sstoreAccountMap I.codeOwner σ_solm ⟨0⟩
                  (increaseObservationCardinalityNextLockedSlotWord σ_solm I))
                σ₀ (Sat256.ofUInt256 g) A I)
              (I := I)
              (by simp [initState])
              (by simpa [initState] using holdZeroSolm)
          have hsourceFail :
              ExecBlock (config v)
                { contract := contract v, locals := increaseObservationCardinalityNextStore I }
                (initState cA gh bl
                  (sstoreAccountMap I.codeOwner σ_solm ⟨0⟩
                    (increaseObservationCardinalityNextLockedSlotWord σ_solm I))
                  σ₀ (Sat256.ofUInt256 g) A I)
                [ .require (.binary .eq (.env .this) (addrLit v.original)),
                  .letDecl "observationCardinalityNextOld" (some uint16)
                    (.storage (slot0F "observationCardinalityNext")),
                  .letDecl "observationCardinalityNextNew" (some uint16)
                    (.var "observationCardinalityNext"),
                  .require (gtE (.var "observationCardinalityNextOld") (.intLit 0)),
                  Stmt.ite (leE (.var "observationCardinalityNextNew")
                      (.var "observationCardinalityNextOld"))
                    [ .assign .localVar (varRef "observationCardinalityNextNew")
                        (.var "observationCardinalityNextOld") ]
                    [ .letDecl "i" (some uint16) (.var "observationCardinalityNextOld"),
                      .while (ltE (.var "i") (.var "observationCardinalityNextNew"))
                      [ .assign .storage (observationsRawF (.var "i") "blockTimestamp")
                            (.intLit 1),
                          .assign .localVar (varRef "i") (addE (.var "i") (.intLit 1)) ] ],
                  .assign .storage (slot0F "observationCardinalityNext")
                    (.var "observationCardinalityNextNew"),
                  .assign .storage (slot0F "unlocked") (.boolLit true) ] .reverted := by
            simpa using execBlock_append hsourceNoDelegate hsourceOldZero
          have hbody :
              ExecTransitionBody (config v) (contract v)
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                (increaseObservationCardinalityNextStore I)
                (increaseobservationcardinalitynextTransition v).body .reverted := by
            change ExecTransitionBody (config v) (contract v)
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                (increaseObservationCardinalityNextStore I)
                [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
                  .require (.storage (slot0F "unlocked")),
                  .assign .storage (slot0F "unlocked") (.boolLit false),
                  .require (.binary .eq (.env .this) (addrLit v.original)),
                  .letDecl "observationCardinalityNextOld" (some uint16)
                    (.storage (slot0F "observationCardinalityNext")),
                  .letDecl "observationCardinalityNextNew" (some uint16)
                    (.var "observationCardinalityNext"),
                  .require (gtE (.var "observationCardinalityNextOld") (.intLit 0)),
                  Stmt.ite (leE (.var "observationCardinalityNextNew")
                      (.var "observationCardinalityNextOld"))
                    [ .assign .localVar (varRef "observationCardinalityNextNew")
                        (.var "observationCardinalityNextOld") ]
                    [ .letDecl "i" (some uint16) (.var "observationCardinalityNextOld"),
                      .while (ltE (.var "i") (.var "observationCardinalityNextNew"))
                      [ .assign .storage (observationsRawF (.var "i") "blockTimestamp")
                            (.intLit 1),
                          .assign .localVar (varRef "i") (addE (.var "i") (.intLit 1)) ] ],
                  .assign .storage (slot0F "observationCardinalityNext")
                    (.var "observationCardinalityNextNew"),
                  .assign .storage (slot0F "unlocked") (.boolLit true) ] .reverted
            exact ExecFuncBody.execBlockRevert <| by
              simpa using execBlock_append hsourceLockInit hsourceFail
          exact hrd.reEquivExecutionRevert hcode hdispatch hdecode hbody
        · have holdNonzeroEvm :
              increaseObservationCardinalityNextOldWord
                (sstoreAccountMap I.codeOwner σ_evm ⟨0⟩
                  (increaseObservationCardinalityNextLockedSlotWord σ_evm I)) I ≠ ⟨0⟩ :=
            holdZeroEvm
          have holdNonzeroSolm :
              increaseObservationCardinalityNextOldWord
                (sstoreAccountMap I.codeOwner σ_solm ⟨0⟩
                  (increaseObservationCardinalityNextLockedSlotWord σ_solm I)) I ≠ ⟨0⟩ := by
            rw [increaseObservationCardinalityNextOldWord_transport hAccountsAfterLock]
            exact holdNonzeroEvm
          have hnoGrowPrefix :
              UInt256.gt (increaseObservationCardinalityNextArgWord I)
                    (increaseObservationCardinalityNextOldWord
                      (sstoreAccountMap I.codeOwner σ_evm ⟨0⟩
                        (increaseObservationCardinalityNextLockedSlotWord σ_evm I)) I) = ⟨0⟩ →
                ∃ k C, RD code I (Sat256.ofUInt256 g)
                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨5521⟩
                  (increaseObservationCardinalityNextOldWord
                      (sstoreAccountMap I.codeOwner σ_evm ⟨0⟩
                        (increaseObservationCardinalityNextLockedSlotWord σ_evm I)) I ::
                    ⟨0⟩ ::
                    increaseObservationCardinalityNextOldWord
                      (sstoreAccountMap I.codeOwner σ_evm ⟨0⟩
                        (increaseObservationCardinalityNextLockedSlotWord σ_evm I)) I ::
                    increaseObservationCardinalityNextArgWord I :: ⟨857⟩ :: [solcSelectorWord I])
                  solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
                  (cA, sstoreAccountMap I.codeOwner σ_evm ⟨0⟩
                    (increaseObservationCardinalityNextLockedSlotWord σ_evm I)) k C := by
            intro hnewLeEvm
            exact uniswapV3PoolIncreaseObservationCardinalityNextAfterNoDelegateNoGrowReturn
              (v := v) (code := code) (ee := I) (g := Sat256.ofUInt256 g)
              (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
              (R := [solcSelectorWord I]) (rdata := ByteArray.empty) (cA := cA)
              (σ := sstoreAccountMap I.codeOwner σ_evm ⟨0⟩
                (increaseObservationCardinalityNextLockedSlotWord σ_evm I))
              hpatch hrdNoDelegate holdNonzeroEvm hnewLeEvm (by norm_num)
          have hnewLeSolm :
              ∀ hnewLeEvm :
                UInt256.gt (increaseObservationCardinalityNextArgWord I)
                  (increaseObservationCardinalityNextOldWord
                    (sstoreAccountMap I.codeOwner σ_evm ⟨0⟩
                      (increaseObservationCardinalityNextLockedSlotWord σ_evm I)) I) = ⟨0⟩,
                UInt256.gt (increaseObservationCardinalityNextArgWord I)
                  (increaseObservationCardinalityNextOldWord
                    (sstoreAccountMap I.codeOwner σ_solm ⟨0⟩
                      (increaseObservationCardinalityNextLockedSlotWord σ_solm I)) I) = ⟨0⟩ := by
            intro hnewLeEvm
            rw [increaseObservationCardinalityNextOldWord_transport hAccountsAfterLock]
            exact hnewLeEvm
          have hsourceNoGrowReturns :
              ∀ hnewLeEvm :
                UInt256.gt (increaseObservationCardinalityNextArgWord I)
                  (increaseObservationCardinalityNextOldWord
                    (sstoreAccountMap I.codeOwner σ_evm ⟨0⟩
                      (increaseObservationCardinalityNextLockedSlotWord σ_evm I)) I) = ⟨0⟩,
                ExecBlock (config v)
                  { contract := contract v, locals := increaseObservationCardinalityNextStore I }
                  (initState cA gh bl
                    (sstoreAccountMap I.codeOwner σ_solm ⟨0⟩
                      (increaseObservationCardinalityNextLockedSlotWord σ_solm I))
                    σ₀ (Sat256.ofUInt256 g) A I)
                  [ .letDecl "observationCardinalityNextOld" (some uint16)
                      (.storage (slot0F "observationCardinalityNext")),
                    .letDecl "observationCardinalityNextNew" (some uint16)
                      (.var "observationCardinalityNext"),
                    .require (gtE (.var "observationCardinalityNextOld") (.intLit 0)),
                    Stmt.ite (leE (.var "observationCardinalityNextNew")
                        (.var "observationCardinalityNextOld"))
                      [ .assign .localVar (varRef "observationCardinalityNextNew")
                          (.var "observationCardinalityNextOld") ]
                      [ .letDecl "i" (some uint16) (.var "observationCardinalityNextOld"),
                        .while (ltE (.var "i") (.var "observationCardinalityNextNew"))
                        [ .assign .storage (observationsRawF (.var "i") "blockTimestamp")
                              (.intLit 1),
                            .assign .localVar (varRef "i") (addE (.var "i") (.intLit 1)) ] ],
                    .assign .storage (slot0F "observationCardinalityNext")
                      (.var "observationCardinalityNextNew"),
                    .assign .storage (slot0F "unlocked") (.boolLit true) ]
                  (.ok
                    { contract := contract v,
                      locals := increaseObservationCardinalityNextStoreWithOldNewNoGrow
                        (sstoreAccountMap I.codeOwner σ_solm ⟨0⟩
                          (increaseObservationCardinalityNextLockedSlotWord σ_solm I)) I }
                    (slot0AfterUnlockState
                      (increaseObservationCardinalityNextAfterNoGrowObsNextState
                        (initState cA gh bl
                          (sstoreAccountMap I.codeOwner σ_solm ⟨0⟩
                            (increaseObservationCardinalityNextLockedSlotWord σ_solm I))
                          σ₀ (Sat256.ofUInt256 g) A I) I))) := by
            intro hnewLeEvm
            exact uniswapV3PoolIncreaseObservationCardinalityNextSourceNoGrowReturns
              (v := v)
              (evm := initState cA gh bl
                (sstoreAccountMap I.codeOwner σ_solm ⟨0⟩
                  (increaseObservationCardinalityNextLockedSlotWord σ_solm I))
                σ₀ (Sat256.ofUInt256 g) A I)
              (I := I)
              (by simp [initState])
              (by simpa [initState] using holdNonzeroSolm)
              (by simpa [initState] using hnewLeSolm hnewLeEvm)
          by_cases hnewLeEvm :
              UInt256.gt (increaseObservationCardinalityNextArgWord I)
                (increaseObservationCardinalityNextOldWord
                  (sstoreAccountMap I.codeOwner σ_evm ⟨0⟩
                    (increaseObservationCardinalityNextLockedSlotWord σ_evm I)) I) = ⟨0⟩
          · obtain ⟨_, _, hrd5521⟩ := hnoGrowPrefix hnewLeEvm
            have hrdRet :=
              uniswapV3PoolIncreaseObservationCardinalityNextNoGrowTailReturn
                (v := v) (code := code) (ee := I) (g := Sat256.ofUInt256 g)
                (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                (R := [solcSelectorWord I]) (rdata := ByteArray.empty) (cA := cA)
                (σ := sstoreAccountMap I.codeOwner σ_evm ⟨0⟩
                  (increaseObservationCardinalityNextLockedSlotWord σ_evm I))
                hpatch hrd5521 _hperm (by norm_num)
            have hsourceSuccess :=
              execBlock_append hsourceNoDelegate (hsourceNoGrowReturns hnewLeEvm)
            have hbody :
                ExecTransitionBody (config v) (contract v)
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                  (increaseObservationCardinalityNextStore I)
                  (increaseobservationcardinalitynextTransition v).body
                  (.returned
                    { contract := contract v,
                      locals := increaseObservationCardinalityNextStoreWithOldNewNoGrow
                        (sstoreAccountMap I.codeOwner σ_solm ⟨0⟩
                          (increaseObservationCardinalityNextLockedSlotWord σ_solm I)) I }
                    (slot0AfterUnlockState
                      (increaseObservationCardinalityNextAfterNoGrowObsNextState
                        (initState cA gh bl
                          (sstoreAccountMap I.codeOwner σ_solm ⟨0⟩
                            (increaseObservationCardinalityNextLockedSlotWord σ_solm I))
                          σ₀ (Sat256.ofUInt256 g) A I) I))
                    none)
                  := by
              refine ExecFuncBody.execBlockOK ?_
              simpa [increaseobservationcardinalitynextTransition] using
                execBlock_append hsourceLockInit hsourceSuccess
            exact hrdRet.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
              (by
                simp [slot0AfterUnlockState,
                  increaseObservationCardinalityNextAfterNoGrowObsNextState,
                  storageStore_createdAccounts, initState])
              (by
                exact increaseObservationCardinalityNextFinalNoGrowAccountMapEquiv
                  (evmOwner := initState cA gh bl
                    (sstoreAccountMap I.codeOwner σ_solm ⟨0⟩
                      (increaseObservationCardinalityNextLockedSlotWord σ_solm I))
                    σ₀ (Sat256.ofUInt256 g) A I)
                  (σOwnerEvm := sstoreAccountMap I.codeOwner σ_evm ⟨0⟩
                    (increaseObservationCardinalityNextLockedSlotWord σ_evm I))
                  (I := I)
                  (by simpa [initState] using hAccountsAfterLock)
                  (by simp [initState]))
              (by
                rw [show (increaseobservationcardinalitynextTransition v).returnType = []
                  from rfl]
                exact returnEquiv.fallthrough rfl rfl (by native_decide))
          · exact uniswapV3PoolIncreaseObservationCardinalityNextGrowBranch
              (v := v) (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
              (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
              (code := code) hpatch hcode hdispatch hdecode hsourceLockInit
              hsourceNoDelegate hrdNoDelegate hAccountsAfterLock holdNonzeroEvm
              holdNonzeroSolm hnewLeEvm _hperm
      · have hnoDelegateZero : uniswapV3PoolNoDelegateCallGuard v I = ⟨0⟩ := by
          by_contra hne
          exact hnoDelegate hne
        have hrd :=
          uniswapV3PoolNoDelegateCallRevert (v := v) (code := code) (ee := I)
            (g := Sat256.ofUInt256 g)
            (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
            (R := increaseObservationCardinalityNextArgWord I :: ⟨857⟩ :: [solcSelectorWord I])
            (mem := solcFreePtrMem) (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
            (acc := (cA, sstoreAccountMap I.codeOwner σ_evm ⟨0⟩
              (increaseObservationCardinalityNextLockedSlotWord σ_evm I)))
            hpatch hrdAfterLock hnoDelegateZero (by norm_num)
        have hsourceFail :
            ExecBlock (config v)
              { contract := contract v, locals := increaseObservationCardinalityNextStore I }
              (initState cA gh bl
                (sstoreAccountMap I.codeOwner σ_solm ⟨0⟩
                  (increaseObservationCardinalityNextLockedSlotWord σ_solm I))
                σ₀ (Sat256.ofUInt256 g) A I)
              [ .require (.binary .eq (.env .this) (addrLit v.original)),
                .letDecl "observationCardinalityNextOld" (some uint16)
                  (.storage (slot0F "observationCardinalityNext")),
                .letDecl "observationCardinalityNextNew" (some uint16)
                  (.var "observationCardinalityNext"),
                .require (gtE (.var "observationCardinalityNextOld") (.intLit 0)),
                Stmt.ite (leE (.var "observationCardinalityNextNew")
                    (.var "observationCardinalityNextOld"))
                  [ .assign .localVar (varRef "observationCardinalityNextNew")
                      (.var "observationCardinalityNextOld") ]
                  [ .letDecl "i" (some uint16) (.var "observationCardinalityNextOld"),
                    .while (ltE (.var "i") (.var "observationCardinalityNextNew"))
                      [ .assign .storage (observationsRawF (.var "i") "blockTimestamp") (.intLit 1),
                        .assign .localVar (varRef "i") (addE (.var "i") (.intLit 1)) ] ],
                .assign .storage (slot0F "observationCardinalityNext")
                  (.var "observationCardinalityNextNew"),
                .assign .storage (slot0F "unlocked") (.boolLit true) ] .reverted := by
          exact ExecBlock.consRevert
            (ExecStmt.requireFalse (uniswapV3PoolNoDelegateCallEvalFalse
              (v := v) (cA := cA) (gh := gh) (bl := bl)
              (σ := sstoreAccountMap I.codeOwner σ_solm ⟨0⟩
                (increaseObservationCardinalityNextLockedSlotWord σ_solm I))
              (σ₀ := σ₀) (A := A) (I := I)
              (L := increaseObservationCardinalityNextStore I)
              (g := Sat256.ofUInt256 g) hnoDelegateZero))
        have hbody :
            ExecTransitionBody (config v) (contract v)
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              (increaseObservationCardinalityNextStore I)
              (increaseobservationcardinalitynextTransition v).body .reverted := by
          change ExecTransitionBody (config v) (contract v)
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              (increaseObservationCardinalityNextStore I)
              [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
                .require (.storage (slot0F "unlocked")),
                .assign .storage (slot0F "unlocked") (.boolLit false),
                .require (.binary .eq (.env .this) (addrLit v.original)),
                .letDecl "observationCardinalityNextOld" (some uint16)
                  (.storage (slot0F "observationCardinalityNext")),
                .letDecl "observationCardinalityNextNew" (some uint16)
                  (.var "observationCardinalityNext"),
                .require (gtE (.var "observationCardinalityNextOld") (.intLit 0)),
                Stmt.ite (leE (.var "observationCardinalityNextNew")
                    (.var "observationCardinalityNextOld"))
                  [ .assign .localVar (varRef "observationCardinalityNextNew")
                      (.var "observationCardinalityNextOld") ]
                  [ .letDecl "i" (some uint16) (.var "observationCardinalityNextOld"),
                    .while (ltE (.var "i") (.var "observationCardinalityNextNew"))
                      [ .assign .storage (observationsRawF (.var "i") "blockTimestamp") (.intLit 1),
                        .assign .localVar (varRef "i") (addE (.var "i") (.intLit 1)) ] ],
                .assign .storage (slot0F "observationCardinalityNext")
                  (.var "observationCardinalityNextNew"),
                .assign .storage (slot0F "unlocked") (.boolLit true) ] .reverted
          exact ExecFuncBody.execBlockRevert <| by
            simpa using execBlock_append hsourceLockInit hsourceFail
        exact hrd.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · have hlockedEvm : increaseObservationCardinalityNextUnlockedByte σ_evm I = ⟨0⟩ := by
        by_contra hne
        exact hunlocked hne
      have hlockedSolm :
          increaseObservationCardinalityNextUnlockedByte σ_solm I = ⟨0⟩ := by
        rw [increaseObservationCardinalityNextUnlockedByte_transport
          (σ_evm := σ_evm) (σ_solm := σ_solm) hAccounts]
        exact hlockedEvm
      have hbody :=
        uniswapV3PoolIncreaseObservationCardinalityNextSourceLockedReverts (v := v)
          (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A)
          (I := I) (g := Sat256.ofUInt256 g) hwv hlockedSolm
      have hrd :=
        uniswapV3PoolIncreaseObservationCardinalityNextLockEnterLockedRevert
          (v := v) (code := code) (ee := I) (g := Sat256.ofUInt256 g)
          (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
          (R := increaseObservationCardinalityNextArgWord I :: ⟨857⟩ :: [solcSelectorWord I])
          (rdata := ByteArray.empty) (cA := cA) (σ := σ_evm) hpatch hbodyEntry
          hlockedEvm (by norm_num)
      exact hrd.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · have hshort : I.calldata.size < 36 := by omega
    have hdecode :=
      uniswapV3PoolIncreaseObservationCardinalityNextDecodeShort (v := v) (I := I) hshort
    have hrd := uniswapV3PoolIncreaseObservationCardinalityNextEvmDecodeShort
      (v := v) (code := code) (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hpatch hcode hwv hsz
      hsize hsel hshort
    exact hrd.reEquivDecodingFailed hcode hdispatch hdecode

end Benchmarks.UniswapV3Pool
