import Benchmarks.UniswapV3Pool.IncreaseObservationCardinalityNextBase

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.UniswapV3Pool

private theorem uniswapV3PoolIncreaseObservationCardinalityNextGrowPatchPreservesJumpDest16053 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨16053⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolIncreaseObservationCardinalityNextGrowPatchPreservesJumpDest16115 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨16115⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolIncreaseObservationCardinalityNextGrowPatchPreservesJumpDest16137 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨16137⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolIncreaseObservationCardinalityNextGrowPatchPreservesJumpDest16139 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨16139⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolIncreaseObservationCardinalityNextGrowPatchPreservesJumpDest16207 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨16207⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolIncreaseObservationCardinalityNextGrowPatchPreservesJumpDest5521 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨5521⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolIncreaseObservationCardinalityNextGrowPatchPreservesJumpDest5630 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨5630⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolIncreaseObservationCardinalityNextGrowPatchPreservesJumpDest857 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨857⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolIncreaseObservationCardinalityNextGrowJumpDestPatched16053
    {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨16053⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolIncreaseObservationCardinalityNextGrowPatchPreservesJumpDest16053

theorem uniswapV3PoolIncreaseObservationCardinalityNextGrowJumpDestPatched16115
    {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨16115⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolIncreaseObservationCardinalityNextGrowPatchPreservesJumpDest16115

theorem uniswapV3PoolIncreaseObservationCardinalityNextGrowJumpDestPatched16137
    {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨16137⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolIncreaseObservationCardinalityNextGrowPatchPreservesJumpDest16137

theorem uniswapV3PoolIncreaseObservationCardinalityNextGrowJumpDestPatched16139
    {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨16139⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolIncreaseObservationCardinalityNextGrowPatchPreservesJumpDest16139

theorem uniswapV3PoolIncreaseObservationCardinalityNextGrowJumpDestPatched16207
    {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨16207⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolIncreaseObservationCardinalityNextGrowPatchPreservesJumpDest16207

theorem uniswapV3PoolIncreaseObservationCardinalityNextGrowJumpDestPatched5521
    {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨5521⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolIncreaseObservationCardinalityNextGrowPatchPreservesJumpDest5521

theorem uniswapV3PoolIncreaseObservationCardinalityNextGrowJumpDestPatched5630
    {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨5630⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolIncreaseObservationCardinalityNextGrowPatchPreservesJumpDest5630

theorem uniswapV3PoolIncreaseObservationCardinalityNextGrowJumpDestPatched857
    {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨857⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolIncreaseObservationCardinalityNextGrowPatchPreservesJumpDest857

abbrev increaseObservationCardinalityNextEvmObsNextSlotWord
    (σ : AccountMap) (I : ExecutionEnv) (obsNext : UInt256) : UInt256 :=
  UInt256.lor
    (UInt256.land
      (codeOwnerStorageWord I σ ⟨0⟩)
      (UInt256.lnot (UInt256.shiftLeft (⟨65535⟩ : UInt256) ⟨216⟩)))
    (UInt256.mul
      (UInt256.land obsNext (⟨65535⟩ : UInt256))
      (UInt256.shiftLeft ⟨1⟩ ⟨216⟩))

abbrev increaseObservationCardinalityNextGrowObservationSlot (i : UInt256) : UInt256 :=
  UInt256.land (⟨65535⟩ : UInt256) i + ⟨8⟩

abbrev increaseObservationCardinalityNextGrowObservationWord
    (σ : AccountMap) (I : ExecutionEnv) (i : UInt256) : UInt256 :=
  UInt256.lor
    (UInt256.land (⟨4294967295⟩ : UInt256) (⟨1⟩ : UInt256))
    (UInt256.land
      (UInt256.lnot (⟨4294967295⟩ : UInt256))
      (codeOwnerStorageWord I σ (increaseObservationCardinalityNextGrowObservationSlot i)))

abbrev increaseObservationCardinalityNextEventTopic : UInt256 :=
  ⟨77928370965229736361680894451701302466328135445772690950750693029892640871002⟩

def increaseObservationCardinalityNextEventMem0 (old : UInt256) : ByteArray :=
  (UInt256.toByteArray (UInt256.land old (⟨65535⟩ : UInt256))).write 0 solcFreePtrMem 128 32

def increaseObservationCardinalityNextEventMem (old obsNext : UInt256) : ByteArray :=
  (UInt256.toByteArray (UInt256.land obsNext (⟨65535⟩ : UInt256))).write 0
    (increaseObservationCardinalityNextEventMem0 old) 160 32

theorem increaseObservationCardinalityNextEventMem0_size (old : UInt256) :
    (increaseObservationCardinalityNextEventMem0 old).size = 160 := by
  unfold increaseObservationCardinalityNextEventMem0
  rw [toByteArray_write_eq _ _ _ (by rw [solcFreePtrMem_size]; omega)
      (by rw [solcFreePtrMem_size]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, solcFreePtrMem_size, ByteArray_zeroes_size,
    show (USize.ofNat (128 - 96)).toNat = 32 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
    toByteArray_size]

theorem increaseObservationCardinalityNextEventMem_size (old obsNext : UInt256) :
    (increaseObservationCardinalityNextEventMem old obsNext).size = 192 := by
  unfold increaseObservationCardinalityNextEventMem
  rw [toByteArray_write_eq _ _ _ (by rw [increaseObservationCardinalityNextEventMem0_size])
      (by rw [increaseObservationCardinalityNextEventMem0_size]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, increaseObservationCardinalityNextEventMem0_size,
    ByteArray_zeroes_size,
    show (USize.ofNat (160 - 160)).toNat = 0 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
    toByteArray_size]

theorem increaseObservationCardinalityNextEventMem_read64 (old obsNext : UInt256) :
    (increaseObservationCardinalityNextEventMem old obsNext).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold increaseObservationCardinalityNextEventMem
  rw [write32_read_below _ _ 160 64 (by rw [toByteArray_size])
    (by rw [increaseObservationCardinalityNextEventMem0_size]) (by omega)]
  unfold increaseObservationCardinalityNextEventMem0
  rw [toByteArray_write_read_below_of_gap _ _ 128 64
    (by rw [solcFreePtrMem_size]) (by omega)
    (by rw [solcFreePtrMem_size]; exact lt_usize _ (by norm_num))]
  exact solcFreePtrMem_read64

theorem increaseObservationCardinalityNextEventMem_mload64 (old obsNext : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (increaseObservationCardinalityNextEventMem old obsNext).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((increaseObservationCardinalityNextEventMem old obsNext).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ :=
  mloadFreePtrValue (by rw [increaseObservationCardinalityNextEventMem_size]; decide)
    (by decide) (increaseObservationCardinalityNextEventMem_read64 old obsNext)

private theorem uniswapV3PoolIncreaseObservationCardinalityNextGrowBodyPatchDisjoint
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

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolIncreaseObservationCardinalityNextGrowPrefix
    {v : PoolImmutables} {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨5493⟩
      (increaseObservationCardinalityNextArgWord ee :: ⟨857⟩ :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (holdNonzero : increaseObservationCardinalityNextOldWord σ ee ≠ ⟨0⟩)
    (hnewGt : UInt256.gt (increaseObservationCardinalityNextArgWord ee)
        (increaseObservationCardinalityNextOldWord σ ee) ≠ ⟨0⟩)
    (hov : R.length + 14 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨16137⟩
      (⟨0⟩ :: increaseObservationCardinalityNextArgWord ee ::
        increaseObservationCardinalityNextOldWord σ ee :: ⟨8⟩ :: ⟨5521⟩ :: ⟨0⟩ ::
        increaseObservationCardinalityNextOldWord σ ee ::
        increaseObservationCardinalityNextArgWord ee :: ⟨857⟩ :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  have hdecodeBody {pc : UInt256} (hlo : 5404 ≤ pc.toNat)
      (hhi : pc.toNat + 33 ≤ 6603) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 6603 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolIncreaseObservationCardinalityNextGrowBodyPatchDisjoint hlo hhi)]
  have hdecodeGrow {pc : UInt256} (hlo : 16053 ≤ pc.toNat)
      (hhi : pc.toNat + 33 ≤ 19295) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 19295 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolIncreaseObservationCardinalityNextGrowPatchDisjoint hlo hhi)]
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
  have hnewGtRaw :
      UInt256.gt
          (UInt256.land (⟨65535⟩ : UInt256) (increaseObservationCardinalityNextArgWord ee))
          (UInt256.land (⟨65535⟩ : UInt256)
            (UInt256.land (⟨65535⟩ : UInt256)
              (UInt256.div (solcSlotWord σ ee ⟨0⟩) (slot0ShiftBytes 27)))) ≠
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
    exact hnewGt
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
  have rd16053 := rd5520.jump hd5520
    (uniswapV3PoolIncreaseObservationCardinalityNextGrowJumpDestPatched16053 hpatch)
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
    (uniswapV3PoolIncreaseObservationCardinalityNextGrowJumpDestPatched16115 hpatch)
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
  have rd16137 := rd16130.jumpiT hd16130 hnewGtRaw
    (uniswapV3PoolIncreaseObservationCardinalityNextGrowJumpDestPatched16137 hpatch)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, by
    simpa [solcSlotWord, holdRaw] using rd16137⟩

theorem uniswapV3PoolIncreaseObservationCardinalityNextGrowEnterLoopHeader
    {v : PoolImmutables} {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {obsNext old arg ret : UInt256} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨16137⟩
      (⟨0⟩ :: obsNext :: old :: ⟨8⟩ :: ⟨5521⟩ :: ⟨0⟩ :: old :: arg :: ret :: R)
      mem aw rdata acc k C)
    (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨16139⟩
      (old :: ⟨0⟩ :: obsNext :: old :: ⟨8⟩ :: ⟨5521⟩ :: ⟨0⟩ :: old :: arg :: ret :: R)
      mem aw rdata acc k' C' := by
  have hdecodeGrow {pc : UInt256} (hlo : 16053 ≤ pc.toNat)
      (hhi : pc.toNat + 33 ≤ 19295) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 19295 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolIncreaseObservationCardinalityNextGrowPatchDisjoint hlo hhi)]
  have hd16137 : decode code ⟨16137⟩ = some (.JUMPDEST, .none) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16138 : decode code ⟨16138⟩ = some (.DUP3, .none) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have rd16138 := by
    simpa using h.jumpdest hd16137 (by
      simp only [List.length_cons]
      omega)
  have rd16139 := by
    simpa using rd16138.dup3 hd16138 (by
      simp only [List.length_cons]
      omega)
  exact ⟨_, _, rd16139⟩

theorem uniswapV3PoolIncreaseObservationCardinalityNextGrowLoopExitToTail
    {v : PoolImmutables} {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {i obsNext old arg ret : UInt256} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨16139⟩
      (i :: ⟨0⟩ :: obsNext :: old :: ⟨8⟩ :: ⟨5521⟩ :: ⟨0⟩ :: old :: arg :: ret :: R)
      mem aw rdata acc k C)
    (hdone : UInt256.isZero
        (UInt256.lt
          (UInt256.land (⟨65535⟩ : UInt256) i)
          (UInt256.land (⟨65535⟩ : UInt256) obsNext)) ≠ ⟨0⟩)
    (hov : R.length + 14 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨5521⟩
      (obsNext :: ⟨0⟩ :: old :: arg :: ret :: R) mem aw rdata acc k' C' := by
  have hdecodeGrow {pc : UInt256} (hlo : 16053 ≤ pc.toNat)
      (hhi : pc.toNat + 33 ≤ 19295) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 19295 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolIncreaseObservationCardinalityNextGrowPatchDisjoint hlo hhi)]
  have hd16139 : decode code ⟨16139⟩ = some (.JUMPDEST, .none) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16140 : decode code ⟨16140⟩ = some (.DUP3, .none) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16141 : decode code ⟨16141⟩ = some (.Push .PUSH2, some (⟨65535⟩, 2)) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16144 : decode code ⟨16144⟩ = some (.AND, .none) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16145 : decode code ⟨16145⟩ = some (.DUP2, .none) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16146 : decode code ⟨16146⟩ = some (.Push .PUSH2, some (⟨65535⟩, 2)) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16149 : decode code ⟨16149⟩ = some (.AND, .none) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16150 : decode code ⟨16150⟩ = some (.LT, .none) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16151 : decode code ⟨16151⟩ = some (.ISZERO, .none) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16152 : decode code ⟨16152⟩ = some (.Push .PUSH2, some (⟨16207⟩, 2)) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16155 : decode code ⟨16155⟩ = some (.JUMPI, .none) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16207 : decode code ⟨16207⟩ = some (.JUMPDEST, .none) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16208 : decode code ⟨16208⟩ = some (.POP, .none) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16209 : decode code ⟨16209⟩ = some (.SWAP1, .none) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16210 : decode code ⟨16210⟩ = some (.SWAP4, .none) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16211 : decode code ⟨16211⟩ = some (.SWAP3, .none) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16212 : decode code ⟨16212⟩ = some (.POP, .none) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16213 : decode code ⟨16213⟩ = some (.POP, .none) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16214 : decode code ⟨16214⟩ = some (.POP, .none) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16215 : decode code ⟨16215⟩ = some (.JUMP, .none) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have rd16140 := by
    simpa using h.jumpdest hd16139 (by
      simp only [List.length_cons]
      omega)
  have rd16141 := by
    simpa using rd16140.dup3 hd16140 (by
      simp only [List.length_cons]
      omega)
  have rd16144 := by
    simpa using rd16141.push2 ⟨65535⟩ hd16141 (by
      simp only [List.length_cons]
      omega)
  have rd16145 := by
    simpa using rd16144.and hd16144 (by
      simp only [List.length_cons]
      omega)
  have rd16146 := by
    simpa using rd16145.dup2 hd16145 (by
      simp only [List.length_cons]
      omega)
  have rd16149 := by
    simpa using rd16146.push2 ⟨65535⟩ hd16146 (by
      simp only [List.length_cons]
      omega)
  have rd16150 := by
    simpa using rd16149.and hd16149 (by
      simp only [List.length_cons]
      omega)
  have rd16151 := by
    simpa using rd16150.lt hd16150 (by
      simp only [List.length_cons]
      omega)
  have rd16152 := by
    simpa using rd16151.iszero hd16151 (by
      simp only [List.length_cons]
      omega)
  have rd16155 := by
    simpa using rd16152.push2 ⟨16207⟩ hd16152 (by
      simp only [List.length_cons]
      omega)
  have rd16207 := rd16155.jumpiT hd16155 hdone
    (uniswapV3PoolIncreaseObservationCardinalityNextGrowJumpDestPatched16207 hpatch)
    (by simp only [List.length_cons]; omega)
  have rd16208 := by
    simpa using rd16207.jumpdest hd16207 (by
      simp only [List.length_cons]
      omega)
  have rd16209 := by
    simpa using rd16208.pop hd16208 (by
      simp only [List.length_cons]
      omega)
  have rd16210 := by
    simpa using rd16209.swap1 hd16209 (by
      simp only [List.length_cons]
      omega)
  have rd16211 := by
    simpa using rd16210.swap4 hd16210 (by
      simp only [List.length_cons]
      omega)
  have rd16212 := by
    simpa using rd16211.swap3 hd16211 (by
      simp only [List.length_cons]
      omega)
  have rd16213 := by
    simpa using rd16212.pop hd16212 (by
      simp only [List.length_cons]
      omega)
  have rd16214 := by
    simpa using rd16213.pop hd16213 (by
      simp only [List.length_cons]
      omega)
  have rd16215 := by
    simpa using rd16214.pop hd16214 (by
      simp only [List.length_cons]
      omega)
  have rd5521 := rd16215.jump hd16215
    (uniswapV3PoolIncreaseObservationCardinalityNextGrowJumpDestPatched5521 hpatch)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, by
    simpa using rd5521⟩

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolIncreaseObservationCardinalityNextGrowLoopBodyStep
    {v : PoolImmutables} {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare}
    {σ : AccountMap} {i obsNext old arg ret : UInt256} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨16139⟩
      (i :: ⟨0⟩ :: obsNext :: old :: ⟨8⟩ :: ⟨5521⟩ :: ⟨0⟩ :: old :: arg :: ret :: R)
      mem aw rdata (cA, σ) k C)
    (hloop : UInt256.isZero
        (UInt256.lt
          (UInt256.land (⟨65535⟩ : UInt256) i)
          (UInt256.land (⟨65535⟩ : UInt256) obsNext)) = ⟨0⟩)
    (hincOk : UInt256.lt (UInt256.land (⟨65535⟩ : UInt256) i)
        (⟨65535⟩ : UInt256) ≠ ⟨0⟩)
    (hperm : ee.perm = true)
    (hov : R.length + 15 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨16139⟩
      (((⟨1⟩ : UInt256) + i) :: ⟨0⟩ :: obsNext :: old :: ⟨8⟩ :: ⟨5521⟩ ::
        ⟨0⟩ :: old :: arg :: ret :: R)
      mem aw rdata
      (cA, sstoreAccountMap ee.codeOwner σ
        (increaseObservationCardinalityNextGrowObservationSlot i)
        (increaseObservationCardinalityNextGrowObservationWord σ ee i)) k' C' := by
  have hdecodeGrow {pc : UInt256} (hlo : 16053 ≤ pc.toNat)
      (hhi : pc.toNat + 33 ≤ 19295) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 19295 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolIncreaseObservationCardinalityNextGrowPatchDisjoint hlo hhi)]
  have hd16139 : decode code ⟨16139⟩ = some (.JUMPDEST, .none) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16140 : decode code ⟨16140⟩ = some (.DUP3, .none) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16141 : decode code ⟨16141⟩ = some (.Push .PUSH2, some (⟨65535⟩, 2)) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16144 : decode code ⟨16144⟩ = some (.AND, .none) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16145 : decode code ⟨16145⟩ = some (.DUP2, .none) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16146 : decode code ⟨16146⟩ = some (.Push .PUSH2, some (⟨65535⟩, 2)) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16149 : decode code ⟨16149⟩ = some (.AND, .none) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16150 : decode code ⟨16150⟩ = some (.LT, .none) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16151 : decode code ⟨16151⟩ = some (.ISZERO, .none) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16152 : decode code ⟨16152⟩ = some (.Push .PUSH2, some (⟨16207⟩, 2)) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16155 : decode code ⟨16155⟩ = some (.JUMPI, .none) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16156 : decode code ⟨16156⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16158 : decode code ⟨16158⟩ = some (.DUP6, .none) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16159 : decode code ⟨16159⟩ = some (.DUP3, .none) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16160 : decode code ⟨16160⟩ = some (.Push .PUSH2, some (⟨65535⟩, 2)) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16163 : decode code ⟨16163⟩ = some (.AND, .none) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16164 : decode code ⟨16164⟩ = some (.Push .PUSH2, some (⟨65535⟩, 2)) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16167 : decode code ⟨16167⟩ = some (.DUP2, .none) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16168 : decode code ⟨16168⟩ = some (.LT, .none) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16169 : decode code ⟨16169⟩ = some (.Push .PUSH2, some (⟨16174⟩, 2)) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16172 : decode code ⟨16172⟩ = some (.JUMPI, .none) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16174 : decode code ⟨16174⟩ = some (.JUMPDEST, .none) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16175 : decode code ⟨16175⟩ = some (.ADD, .none) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16176 : decode code ⟨16176⟩ = some (.DUP1, .none) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16177 : decode code ⟨16177⟩ = some (.SLOAD, .none) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16178 : decode code ⟨16178⟩ = some (.Push .PUSH4, some (⟨4294967295⟩, 4)) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16183 : decode code ⟨16183⟩ = some (.NOT, .none) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16184 : decode code ⟨16184⟩ = some (.AND, .none) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16185 : decode code ⟨16185⟩ = some (.Push .PUSH4, some (⟨4294967295⟩, 4)) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16190 : decode code ⟨16190⟩ = some (.SWAP3, .none) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16191 : decode code ⟨16191⟩ = some (.SWAP1, .none) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16192 : decode code ⟨16192⟩ = some (.SWAP3, .none) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16193 : decode code ⟨16193⟩ = some (.AND, .none) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16194 : decode code ⟨16194⟩ = some (.SWAP2, .none) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16195 : decode code ⟨16195⟩ = some (.SWAP1, .none) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16196 : decode code ⟨16196⟩ = some (.SWAP2, .none) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16197 : decode code ⟨16197⟩ = some (.OR, .none) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16198 : decode code ⟨16198⟩ = some (.SWAP1, .none) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16199 : decode code ⟨16199⟩ = some (.SSTORE, .none) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16200 : decode code ⟨16200⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16202 : decode code ⟨16202⟩ = some (.ADD, .none) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16203 : decode code ⟨16203⟩ = some (.Push .PUSH2, some (⟨16139⟩, 2)) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have hd16206 : decode code ⟨16206⟩ = some (.JUMP, .none) := by
    rw [hdecodeGrow (by native_decide) (by native_decide)]; native_decide
  have rd16140 := by
    simpa using h.jumpdest hd16139 (by
      simp only [List.length_cons]
      omega)
  have rd16141 := by
    simpa using rd16140.dup3 hd16140 (by
      simp only [List.length_cons]
      omega)
  have rd16144 := by
    simpa using rd16141.push2 ⟨65535⟩ hd16141 (by
      simp only [List.length_cons]
      omega)
  have rd16145 := by
    simpa using rd16144.and hd16144 (by
      simp only [List.length_cons]
      omega)
  have rd16146 := by
    simpa using rd16145.dup2 hd16145 (by
      simp only [List.length_cons]
      omega)
  have rd16149 := by
    simpa using rd16146.push2 ⟨65535⟩ hd16146 (by
      simp only [List.length_cons]
      omega)
  have rd16150 := by
    simpa using rd16149.and hd16149 (by
      simp only [List.length_cons]
      omega)
  have rd16151 := by
    simpa using rd16150.lt hd16150 (by
      simp only [List.length_cons]
      omega)
  have rd16152 := by
    simpa using rd16151.iszero hd16151 (by
      simp only [List.length_cons]
      omega)
  have rd16155 := by
    simpa using rd16152.push2 ⟨16207⟩ hd16152 (by
      simp only [List.length_cons]
      omega)
  have rd16156 := rd16155.jumpiNT hd16155 hloop (by
    simp only [List.length_cons]
    omega)
  have rd16158 := by
    simpa using rd16156.push1 ⟨1⟩ hd16156 (by
      simp only [List.length_cons]
      omega)
  have rd16159 := by
    simpa using rd16158.dup6 hd16158 (by
      simp only [List.length_cons]
      omega)
  have rd16160 := by
    simpa using rd16159.dup3 hd16159 (by
      simp only [List.length_cons]
      omega)
  have rd16163 := by
    simpa using rd16160.push2 ⟨65535⟩ hd16160 (by
      simp only [List.length_cons]
      omega)
  have rd16164 := by
    simpa using rd16163.and hd16163 (by
      simp only [List.length_cons]
      omega)
  have rd16167 := by
    simpa using rd16164.push2 ⟨65535⟩ hd16164 (by
      simp only [List.length_cons]
      omega)
  have rd16168 := by
    simpa using rd16167.dup2 hd16167 (by
      simp only [List.length_cons]
      omega)
  have rd16169 := by
    simpa using rd16168.lt hd16168 (by
      simp only [List.length_cons]
      omega)
  have rd16172 := by
    simpa using rd16169.push2 ⟨16174⟩ hd16169 (by
      simp only [List.length_cons]
      omega)
  have rd16174 := rd16172.jumpiT hd16172 hincOk
    (by
      exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
        (uniswapV3PoolPatchOffsetMem v)
        (by native_decide :
          D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
            ⟨16174⟩ 0 = true))
    (by simp only [List.length_cons]; omega)
  have rd16175 := by
    simpa using rd16174.jumpdest hd16174 (by
      simp only [List.length_cons]
      omega)
  have rd16176 := by
    simpa [increaseObservationCardinalityNextGrowObservationSlot] using
      rd16175.add hd16175 (by
        simp only [List.length_cons]
        omega)
  have rd16177 := by
    simpa using rd16176.dup1 hd16176 (by
      simp only [List.length_cons]
      omega)
  obtain ⟨_, _, rd16178₀⟩ := rd16177.sload hd16177 (by
    simp only [List.length_cons]
    omega)
  have rd16178 := by
    simpa [increaseObservationCardinalityNextGrowObservationSlot, codeOwnerStorageWord]
      using rd16178₀
  have rd16183 := by
    simpa using rd16178.pushConst ⟨4294967295⟩
      (by native_decide : Operation.POp.PUSH4 ≠ .PUSH0) hd16178 (by
        simp only [List.length_cons]
        omega)
  have rd16184 := by
    simpa using rd16183.not hd16183 (by
      simp only [List.length_cons]
      omega)
  have rd16185 := by
    simpa using rd16184.and hd16184 (by
      simp only [List.length_cons]
      omega)
  have rd16190 := by
    simpa using rd16185.pushConst ⟨4294967295⟩
      (by native_decide : Operation.POp.PUSH4 ≠ .PUSH0) hd16185 (by
        simp only [List.length_cons]
        omega)
  have rd16191 := by
    simpa using rd16190.swap3 hd16190 (by
      simp only [List.length_cons]
      omega)
  have rd16192 := by
    simpa using rd16191.swap1 hd16191 (by
      simp only [List.length_cons]
      omega)
  have rd16193 := by
    simpa using rd16192.swap3 hd16192 (by
      simp only [List.length_cons]
      omega)
  have rd16194 := by
    simpa using rd16193.and hd16193 (by
      simp only [List.length_cons]
      omega)
  have rd16195 := by
    simpa using rd16194.swap2 hd16194 (by
      simp only [List.length_cons]
      omega)
  have rd16196 := by
    simpa using rd16195.swap1 hd16195 (by
      simp only [List.length_cons]
      omega)
  have rd16197 := by
    simpa using rd16196.swap2 hd16196 (by
      simp only [List.length_cons]
      omega)
  have rd16198 := by
    simpa [increaseObservationCardinalityNextGrowObservationWord] using
      rd16197.lor hd16197 (by
        simp only [List.length_cons]
        omega)
  have rd16199 := by
    simpa using rd16198.swap1 hd16198 (by
      simp only [List.length_cons]
      omega)
  obtain ⟨_, _, rd16200₀⟩ := rd16199.sstore hperm hd16199 (by
    simp only [List.length_cons]
    omega)
  have rd16200 := by
    simpa [increaseObservationCardinalityNextGrowObservationSlot,
      increaseObservationCardinalityNextGrowObservationWord, codeOwnerStorageWord]
      using rd16200₀
  have rd16202 := by
    simpa using rd16200.push1 ⟨1⟩ hd16200 (by
      simp only [List.length_cons]
      omega)
  have rd16203 := by
    simpa using rd16202.add hd16202 (by
      simp only [List.length_cons]
      omega)
  have rd16206 := by
    simpa using rd16203.push2 ⟨16139⟩ hd16203 (by
      simp only [List.length_cons]
      omega)
  have rd16139 := rd16206.jump hd16206
    (uniswapV3PoolIncreaseObservationCardinalityNextGrowJumpDestPatched16139 hpatch)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, by
    simpa [increaseObservationCardinalityNextGrowObservationSlot,
      increaseObservationCardinalityNextGrowObservationWord, codeOwnerStorageWord]
      using rd16139⟩

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolIncreaseObservationCardinalityNextTailReturn
    {v : PoolImmutables} {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {R : List UInt256} {rdata : ByteArray} {obsNext : UInt256}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨5521⟩
      (obsNext :: ⟨0⟩ :: increaseObservationCardinalityNextOldWord σ ee ::
        increaseObservationCardinalityNextArgWord ee :: ⟨857⟩ :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hperm : ee.perm = true)
    (heqObsNext :
      UInt256.land (increaseObservationCardinalityNextOldWord σ ee) (⟨65535⟩ : UInt256) =
        UInt256.land obsNext (⟨65535⟩ : UInt256))
    (hov : R.length + 12 ≤ 1024) :
    RDret code g s0
      (cA, sstoreAccountMap ee.codeOwner
        (sstoreAccountMap ee.codeOwner σ ⟨0⟩
          (increaseObservationCardinalityNextEvmObsNextSlotWord σ ee obsNext))
        ⟨0⟩
        (increaseObservationCardinalityNextEvmUnlockedTrueSlotWord
          (sstoreAccountMap ee.codeOwner σ ⟨0⟩
            (increaseObservationCardinalityNextEvmObsNextSlotWord σ ee obsNext)) ee))
      ByteArray.empty := by
  have hdecodeBody {pc : UInt256} (hlo : 5404 ≤ pc.toNat)
      (hhi : pc.toNat + 33 ≤ 6603) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 6603 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolIncreaseObservationCardinalityNextGrowBodyPatchDisjoint hlo hhi)]
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
    simpa [increaseObservationCardinalityNextEvmObsNextSlotWord,
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
      rw [heqObsNext, u256_eq_refl]
      exact one_ne_zero_uint)
    (uniswapV3PoolIncreaseObservationCardinalityNextGrowJumpDestPatched5630 hpatch)
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
    (uniswapV3PoolIncreaseObservationCardinalityNextGrowJumpDestPatched857 hpatch)
    (by evm_ov)
  have rd858 := rd857.jumpdest hd857 (by evm_ov)
  have hpc858 : (⟨857⟩ : UInt256) + ⟨1⟩ = ⟨858⟩ := by
    native_decide
  obtain ⟨_, _, rd858'⟩ : ∃ k' C', RD code ee g s0 ⟨858⟩ R solcFreePtrMem
      (UInt256.ofNat 3) rdata
      (cA, sstoreAccountMap ee.codeOwner
        (sstoreAccountMap ee.codeOwner σ ⟨0⟩
          (increaseObservationCardinalityNextEvmObsNextSlotWord σ ee obsNext))
        ⟨0⟩
        (increaseObservationCardinalityNextEvmUnlockedTrueSlotWord
          (sstoreAccountMap ee.codeOwner σ ⟨0⟩
            (increaseObservationCardinalityNextEvmObsNextSlotWord σ ee obsNext)) ee))
      k' C' := by
    exact ⟨_, _, by
      simpa [increaseObservationCardinalityNextEvmObsNextSlotWord,
        increaseObservationCardinalityNextEvmUnlockedTrueSlotWord, slot0UnlockedClearMask,
        codeOwnerStorageWord, hpc858] using rd858⟩
  exact rd858'.stop hd858 (by
    have h := hov
    omega)

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolIncreaseObservationCardinalityNextUnlockReturnFrom5630
    {v : PoolImmutables} {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {obsNext old arg : UInt256}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨5630⟩
      (obsNext :: old :: arg :: ⟨857⟩ :: R)
      mem aw rdata (cA, σ) k C)
    (hperm : ee.perm = true)
    (hov : R.length + 6 ≤ 1024) :
    RDret code g s0
      (cA, sstoreAccountMap ee.codeOwner σ ⟨0⟩
        (increaseObservationCardinalityNextEvmUnlockedTrueSlotWord σ ee))
      ByteArray.empty := by
  have hdecodeBody {pc : UInt256} (hlo : 5404 ≤ pc.toNat)
      (hhi : pc.toNat + 33 ≤ 6603) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 6603 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolIncreaseObservationCardinalityNextGrowBodyPatchDisjoint hlo hhi)]
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
  have rd5636 := evm_run h with [
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
    (uniswapV3PoolIncreaseObservationCardinalityNextGrowJumpDestPatched857 hpatch)
    (by evm_ov)
  have rd858 := rd857.jumpdest hd857 (by evm_ov)
  have hpc858 : (⟨857⟩ : UInt256) + ⟨1⟩ = ⟨858⟩ := by
    native_decide
  obtain ⟨_, _, rd858'⟩ : ∃ k' C', RD code ee g s0 ⟨858⟩ R mem aw rdata
      (cA, sstoreAccountMap ee.codeOwner σ ⟨0⟩
        (increaseObservationCardinalityNextEvmUnlockedTrueSlotWord σ ee))
      k' C' := by
    exact ⟨_, _, by
      simpa [increaseObservationCardinalityNextEvmUnlockedTrueSlotWord,
        slot0UnlockedClearMask, codeOwnerStorageWord, hpc858] using rd858⟩
  exact rd858'.stop hd858 (by
    have h := hov
    omega)

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolIncreaseObservationCardinalityNextGrowEventTailReturn
    {v : PoolImmutables} {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {R : List UInt256} {rdata : ByteArray} {obsNext old arg : UInt256}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨5565⟩
      (⟨5630⟩ :: UInt256.eq (UInt256.land old (⟨65535⟩ : UInt256))
        (UInt256.land obsNext (⟨65535⟩ : UInt256)) ::
        obsNext :: old :: arg :: ⟨857⟩ :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hperm : ee.perm = true)
    (hchanged :
      UInt256.land old (⟨65535⟩ : UInt256) ≠
        UInt256.land obsNext (⟨65535⟩ : UInt256))
    (hov : R.length + 12 ≤ 1024) :
    RDret code g s0
      (cA, sstoreAccountMap ee.codeOwner σ ⟨0⟩
        (increaseObservationCardinalityNextEvmUnlockedTrueSlotWord σ ee))
      ByteArray.empty := by
  have hdecodeBody {pc : UInt256} (hlo : 5404 ≤ pc.toNat)
      (hhi : pc.toNat + 33 ≤ 6603) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 6603 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolIncreaseObservationCardinalityNextGrowBodyPatchDisjoint hlo hhi)]
  have hd5565 : decode code ⟨5565⟩ = some (.JUMPI, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5566 : decode code ⟨5566⟩ = some (.Push .PUSH1, some (⟨64⟩, 1)) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5568 : decode code ⟨5568⟩ = some (.DUP1, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5569 : decode code ⟨5569⟩ = some (.MLOAD, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5570 : decode code ⟨5570⟩ = some (.Push .PUSH2, some (⟨65535⟩, 2)) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5573 : decode code ⟨5573⟩ = some (.DUP1, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5574 : decode code ⟨5574⟩ = some (.DUP6, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5575 : decode code ⟨5575⟩ = some (.AND, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5576 : decode code ⟨5576⟩ = some (.DUP3, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5577 : decode code ⟨5577⟩ = some (.MSTORE, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5578 : decode code ⟨5578⟩ = some (.DUP4, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5579 : decode code ⟨5579⟩ = some (.AND, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5580 : decode code ⟨5580⟩ = some (.Push .PUSH1, some (⟨32⟩, 1)) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5582 : decode code ⟨5582⟩ = some (.DUP3, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5583 : decode code ⟨5583⟩ = some (.ADD, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5584 : decode code ⟨5584⟩ = some (.MSTORE, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5585 : decode code ⟨5585⟩ = some (.DUP2, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5586 : decode code ⟨5586⟩ = some (.MLOAD, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5587 :
      decode code ⟨5587⟩ =
        some (.Push .PUSH32, some (increaseObservationCardinalityNextEventTopic, 32)) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]
    native_decide
  have hd5620 : decode code ⟨5620⟩ = some (.SWAP3, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5621 : decode code ⟨5621⟩ = some (.SWAP2, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5622 : decode code ⟨5622⟩ = some (.DUP2, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5623 : decode code ⟨5623⟩ = some (.SWAP1, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5624 : decode code ⟨5624⟩ = some (.SUB, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5625 : decode code ⟨5625⟩ = some (.SWAP1, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5626 : decode code ⟨5626⟩ = some (.SWAP2, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5627 : decode code ⟨5627⟩ = some (.ADD, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5628 : decode code ⟨5628⟩ = some (.SWAP1, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have hd5629 : decode code ⟨5629⟩ = some (.LOG1, .none) := by
    rw [hdecodeBody (by native_decide) (by native_decide)]; native_decide
  have heqZero :
      UInt256.eq (UInt256.land old (⟨65535⟩ : UInt256))
        (UInt256.land obsNext (⟨65535⟩ : UInt256)) = ⟨0⟩ :=
    u256_eq_of_ne hchanged
  have rd5566 := h.jumpiNT hd5565 heqZero (by
    have h := hov
    simp only [List.length_cons] at h ⊢
    omega)
  have rd5569 := evm_run rd5566 with [
    raw push1 ⟨64⟩ hd5566 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw dup1 hd5568 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega)]
  have rd5570 := rd5569.mload 0 ⟨128⟩ (UInt256.ofNat 3) hd5569 mem_cost
    solcFreePtrMem_mload64 (by native_decide) (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega)
  have rd5577 := evm_run rd5570 with [
    raw push2 ⟨65535⟩ hd5570 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw dup1 hd5573 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw dup6 hd5574 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw and hd5575 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw dup3 hd5576 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega)]
  have rd5578 := rd5577.mstore 6 (increaseObservationCardinalityNextEventMem0 old)
    (UInt256.ofNat 5) hd5577 mem_cost rfl (by native_decide) (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega)
  have rd5584 := evm_run rd5578 with [
    raw dup4 hd5578 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw and hd5579 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw push1 ⟨32⟩ hd5580 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw dup3 hd5582 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw add hd5583 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega)]
  have rd5585 := rd5584.mstore 3
    (increaseObservationCardinalityNextEventMem old obsNext) (UInt256.ofNat 6)
    hd5584 mem_cost
    (by
      unfold increaseObservationCardinalityNextEventMem
      rw [show (((⟨128⟩ : UInt256) + ⟨32⟩).toNat) = 160 by native_decide])
    (by native_decide) (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega)
  have rd5586 := evm_run rd5585 with [
    raw dup2 hd5585 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega)]
  have rd5587 := rd5586.mload 0 ⟨128⟩ (UInt256.ofNat 6) hd5586 mem_cost
    (increaseObservationCardinalityNextEventMem_mload64 old obsNext)
    (by native_decide) (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega)
  have rd5629 := evm_run rd5587 with [
    raw pushConst increaseObservationCardinalityNextEventTopic
      (show Operation.POp.PUSH32 ≠ .PUSH0 by native_decide) hd5587 (by
        have h := hov
        simp only [List.length_cons] at h ⊢
        omega),
    raw swap3 hd5620 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw swap2 hd5621 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw dup2 hd5622 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw swap1 hd5623 (by evm_ov),
    raw sub hd5624 (by evm_ov),
    raw swap1 hd5625 (by evm_ov),
    raw swap2 hd5626 (by evm_ov),
    raw add hd5627 (by evm_ov),
    raw swap1 hd5628 (by evm_ov)]
  have rd5630 := rd5629.log1 0 (UInt256.ofNat 6) hd5629 hperm mem_cost
    (by native_decide) (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega)
  exact uniswapV3PoolIncreaseObservationCardinalityNextUnlockReturnFrom5630
    (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
    (R := R) (rdata := rdata) (obsNext := obsNext) (old := old) (arg := arg)
    (cA := cA) (σ := σ) hpatch rd5630 hperm (by
      have h := hov
      omega)

end Benchmarks.UniswapV3Pool
