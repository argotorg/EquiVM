import Benchmarks.UniswapV3Pool.BurnPositionUpdateMemory
import Benchmarks.UniswapV3Pool.BurnFullMathSlow

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.UniswapV3Pool

private theorem uniswapV3PoolBurnPositionUpdatePostReturnDecodeEqTemplate
    {v : PoolImmutables} {code : ByteArray} {pc : UInt256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hlo : 21769 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 21846) :
    decode code pc = decode uniswapV3PoolBytecode pc := by
  exact uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch
    (by
      have hsize : 21846 ≤ uniswapV3PoolBytecode.size := by native_decide
      omega)
    (by
      intro p hp
      simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord,
        List.lookup] at hp
      rcases hp with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals omega)

private theorem uniswapV3PoolPatchPreservesJumpDest21769 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨21769⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolPatchPreservesJumpDest21807 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨21807⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolPatchPreservesJumpDest21846 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨21846⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolPatchPreservesJumpDest21892 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨21892⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolPatchPreservesJumpDest21954 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨21954⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolPatchPreservesJumpDest19527 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨19527⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolPatchPreservesJumpDest19573 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨19573⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolPatchPreservesJumpDest16428 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨16428⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolPatchPreservesJumpDest16801 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨16801⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolPatchPreservesJumpDest9737 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨9737⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolJumpDestPatched21769 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨21769⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest21769

theorem uniswapV3PoolJumpDestPatched21807 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨21807⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest21807

theorem uniswapV3PoolJumpDestPatched21846 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨21846⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest21846

theorem uniswapV3PoolJumpDestPatched21892 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨21892⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest21892

theorem uniswapV3PoolJumpDestPatched21954 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨21954⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest21954

theorem uniswapV3PoolJumpDestPatched19527 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨19527⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest19527

theorem uniswapV3PoolJumpDestPatched19573 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨19573⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest19573

theorem uniswapV3PoolJumpDestPatched16428 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨16428⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest16428

theorem uniswapV3PoolJumpDestPatched16801 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨16801⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest16801

theorem uniswapV3PoolJumpDestPatched9737 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨9737⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest9737

private theorem uniswapV3PoolBurnPositionUpdateSkipLiquidityDecodeEqTemplate
    {v : PoolImmutables} {code : ByteArray} {pc : UInt256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hlo : 21807 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 21986) :
    decode code pc = decode uniswapV3PoolBytecode pc := by
  exact uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch
    (by
      have hsize : 21986 ≤ uniswapV3PoolBytecode.size := by native_decide
      omega)
    (by
      intro p hp
      simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord,
        List.lookup] at hp
      rcases hp with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals omega)

private theorem uniswapV3PoolBurnPositionUpdateReturnDecodeEqTemplate
    {v : PoolImmutables} {code : ByteArray} {pc : UInt256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hlo : 21954 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 21996) :
    decode code pc = decode uniswapV3PoolBytecode pc := by
  exact uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch
    (by
      have hsize : 21996 ≤ uniswapV3PoolBytecode.size := by native_decide
      omega)
    (by
      intro p hp
      simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord,
        List.lookup] at hp
      rcases hp with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals omega)

private theorem uniswapV3PoolBurnModifyPositionPostPositionUpdateDecodeEqTemplate
    {v : PoolImmutables} {code : ByteArray} {pc : UInt256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hlo : 19527 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 19620) :
    decode code pc = decode uniswapV3PoolBytecode pc := by
  exact uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch
    (by
      have hsize : 19620 ≤ uniswapV3PoolBytecode.size := by native_decide
      omega)
    (by
      intro p hp
      simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord,
        List.lookup] at hp
      rcases hp with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals omega)

private theorem uniswapV3PoolBurnModifyPositionReturnToCallerDecodeEqTemplate
    {v : PoolImmutables} {code : ByteArray} {pc : UInt256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hlo : 16428 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 16841) :
    decode code pc = decode uniswapV3PoolBytecode pc := by
  exact uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch
    (by
      have hsize : 16841 ≤ uniswapV3PoolBytecode.size := by native_decide
      omega)
    (by
      intro p hp
      simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord,
        List.lookup] at hp
      rcases hp with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals omega)

abbrev burnPositionUpdateTokensOwed0AddedSlot3
    (pos3 tokensOwed0 : UInt256) : UInt256 :=
  UInt256.lor
    (UInt256.land burnPositionUpdateSlot0Mask
      (tokensOwed0 + UInt256.land burnPositionUpdateSlot0Mask pos3))
    (UInt256.land pos3 (UInt256.lnot burnPositionUpdateSlot0Mask))

abbrev burnPositionUpdateTokensOwedAddedSlot3
    (pos3 tokensOwed0 tokensOwed1 : UInt256) : UInt256 :=
  UInt256.lor
    (UInt256.mul
      (UInt256.land burnPositionUpdateSlot0Mask
        (tokensOwed1 + UInt256.land burnPositionUpdateSlot0Mask
          (UInt256.div (burnPositionUpdateTokensOwed0AddedSlot3 pos3 tokensOwed0)
            (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩))))
      (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩))
    (UInt256.land burnPositionUpdateSlot0Mask
      (burnPositionUpdateTokensOwed0AddedSlot3 pos3 tokensOwed0))

theorem uniswapV3PoolBurnPositionUpdateStartMulDiv1 {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {tokensOwed0 z liquidity inside1 inside0 delta posBase retPos inside1' inside0'
      z2 z3 fee1 fee0 posBase' tick delta' upper lower owner ret free : UInt256}
    {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨21769⟩
      (tokensOwed0 :: z :: liquidity :: burnPositionKeyNewFreePtrWord :: inside1 ::
        inside0 :: delta :: posBase :: retPos :: inside1' :: inside0' :: z2 :: z3 ::
        fee1 :: fee0 :: posBase' :: tick :: delta' :: upper :: lower :: owner :: ret ::
        free :: R)
      (burnPositionUpdateMem5 σ ee (solcSlotWord σ ee posBase) posBase)
      (UInt256.ofNat 22) rdata (cA, σ) k C)
    (hov : R.length + 40 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨13017⟩
      (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩ ::
        burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase) ::
        UInt256.sub inside1 (solcSlotWord σ ee (posBase + (⟨2⟩ : UInt256))) ::
        ⟨21807⟩ :: ⟨0⟩ :: tokensOwed0 :: liquidity ::
        burnPositionKeyNewFreePtrWord :: inside1 :: inside0 :: delta :: posBase ::
        retPos :: inside1' :: inside0' :: z2 :: z3 :: fee1 :: fee0 :: posBase' ::
        tick :: delta' :: upper :: lower :: owner :: ret :: free :: R)
      (burnPositionUpdateMem5 σ ee (solcSlotWord σ ee posBase) posBase)
      (UInt256.ofNat 22) rdata (cA, σ) k' C' := by
  have hdec (pc : UInt256)
      (hlo : 21769 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 21846) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    exact uniswapV3PoolBurnPositionUpdatePostReturnDecodeEqTemplate hpatch hlo hhi
  have hd21769 : decode code ⟨21769⟩ = some (.JUMPDEST, .none) := by
    rw [hdec ⟨21769⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21770 : decode code ⟨21770⟩ = some (.SWAP1, .none) := by
    rw [hdec ⟨21770⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21771 : decode code ⟨21771⟩ = some (.POP, .none) := by
    rw [hdec ⟨21771⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21772 :
      decode code ⟨21772⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    rw [hdec ⟨21772⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21774 :
      decode code ⟨21774⟩ = some (.Push .PUSH2, some (⟨21807⟩, 2)) := by
    rw [hdec ⟨21774⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21777 : decode code ⟨21777⟩ = some (.DUP5, .none) := by
    rw [hdec ⟨21777⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21778 :
      decode code ⟨21778⟩ = some (.Push .PUSH1, some (⟨64⟩, 1)) := by
    rw [hdec ⟨21778⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21780 : decode code ⟨21780⟩ = some (.ADD, .none) := by
    rw [hdec ⟨21780⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21781 : decode code ⟨21781⟩ = some (.MLOAD, .none) := by
    rw [hdec ⟨21781⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21782 : decode code ⟨21782⟩ = some (.DUP7, .none) := by
    rw [hdec ⟨21782⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21783 : decode code ⟨21783⟩ = some (.SUB, .none) := by
    rw [hdec ⟨21783⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21784 : decode code ⟨21784⟩ = some (.DUP6, .none) := by
    rw [hdec ⟨21784⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21785 :
      decode code ⟨21785⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    rw [hdec ⟨21785⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21787 : decode code ⟨21787⟩ = some (.ADD, .none) := by
    rw [hdec ⟨21787⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21788 : decode code ⟨21788⟩ = some (.MLOAD, .none) := by
    rw [hdec ⟨21788⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21789 :
      decode code ⟨21789⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdec ⟨21789⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21791 :
      decode code ⟨21791⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdec ⟨21791⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21793 :
      decode code ⟨21793⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)) := by
    rw [hdec ⟨21793⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21795 : decode code ⟨21795⟩ = some (.SHL, .none) := by
    rw [hdec ⟨21795⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21796 : decode code ⟨21796⟩ = some (.SUB, .none) := by
    rw [hdec ⟨21796⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21797 : decode code ⟨21797⟩ = some (.AND, .none) := by
    rw [hdec ⟨21797⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21798 :
      decode code ⟨21798⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdec ⟨21798⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21800 :
      decode code ⟨21800⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)) := by
    rw [hdec ⟨21800⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21802 : decode code ⟨21802⟩ = some (.SHL, .none) := by
    rw [hdec ⟨21802⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21803 :
      decode code ⟨21803⟩ = some (.Push .PUSH2, some (⟨13017⟩, 2)) := by
    rw [hdec ⟨21803⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21806 : decode code ⟨21806⟩ = some (.JUMP, .none) := by
    rw [hdec ⟨21806⟩ (by native_decide) (by native_decide)]
    native_decide
  have rd21781 := evm_run h with [
    raw jumpdest hd21769 (by evm_ov),
    raw swap1 hd21770 (by simp only [List.length_cons] at hov ⊢; omega),
    raw pop hd21771 (by simp only [List.length_cons] at hov ⊢; omega),
    raw push1 ⟨0⟩ hd21772 (by evm_ov),
    raw push2 ⟨21807⟩ hd21774 (by evm_ov),
    raw dup5 hd21777 (by simp only [List.length_cons] at hov ⊢; omega),
    raw push1 ⟨64⟩ hd21778 (by evm_ov),
    raw add hd21780 (by evm_ov)]
  have rd21782 := by
    simpa using
      rd21781.mload 0 (solcSlotWord σ ee (posBase + (⟨2⟩ : UInt256)))
        (UInt256.ofNat 22) hd21781 mem_cost
        (burnPositionUpdateMem5_mloadFreePtrPlus64 σ ee (solcSlotWord σ ee posBase)
          posBase)
        (by native_decide)
        (by simp only [List.length_cons] at hov ⊢; omega)
  have rd21788 := evm_run rd21782 with [
    raw dup7 hd21782 (by simp only [List.length_cons] at hov ⊢; omega),
    raw sub hd21783 (by evm_ov),
    raw dup6 hd21784 (by simp only [List.length_cons] at hov ⊢; omega),
    raw push1 ⟨0⟩ hd21785 (by evm_ov),
    raw add hd21787 (by evm_ov)]
  have rd21789 := by
    simpa [show burnPositionKeyNewFreePtrWord + (⟨0⟩ : UInt256) =
        burnPositionKeyNewFreePtrWord from by native_decide] using
      rd21788.mload 0
        (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase))
        (UInt256.ofNat 22) hd21788 mem_cost
        (burnPositionUpdateMem5_mloadFreePtr σ ee (solcSlotWord σ ee posBase) posBase)
        (by native_decide)
        (by simp only [List.length_cons] at hov ⊢; omega)
  have rd21806 := evm_run rd21789 with [
    raw push1 ⟨1⟩ hd21789 (by evm_ov),
    raw push1 ⟨1⟩ hd21791 (by evm_ov),
    raw push1 ⟨128⟩ hd21793 (by evm_ov),
    raw shl hd21795 (by evm_ov),
    raw sub hd21796 (by evm_ov),
    raw and hd21797 (by evm_ov),
    raw push1 ⟨1⟩ hd21798 (by evm_ov),
    raw push1 ⟨128⟩ hd21800 (by evm_ov),
    raw shl hd21802 (by evm_ov),
    raw push2 ⟨13017⟩ hd21803 (by evm_ov)]
  have rd13017 := rd21806.jump hd21806 (uniswapV3PoolJumpDestPatched13017 hpatch)
    (by simp only [List.length_cons] at hov ⊢; omega)
  exact ⟨_, _, by
    simpa [burnPositionUpdateSlot0Mask, burnPositionUpdateSlot0Packed_mask] using rd13017⟩

theorem uniswapV3PoolBurnPositionUpdateMulDiv0Prod1ZeroStartMulDiv1
    {v : PoolImmutables} {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State}
    {inside1 inside0 delta posBase retPos inside1' inside0' z2 z3 fee1 fee0 posBase'
      tick delta' upper lower owner ret free : UInt256}
    {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨13017⟩
      (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩ ::
        burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase) ::
        UInt256.sub inside0 (solcSlotWord σ ee (posBase + (⟨1⟩ : UInt256))) ::
        ⟨21769⟩ :: ⟨0⟩ ::
        burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase) ::
        burnPositionKeyNewFreePtrWord :: inside1 :: inside0 :: delta :: posBase ::
        retPos :: inside1' :: inside0' :: z2 :: z3 :: fee1 :: fee0 :: posBase' ::
        tick :: delta' :: upper :: lower :: owner :: ret :: free :: R)
      (burnPositionUpdateMem5 σ ee (solcSlotWord σ ee posBase) posBase)
      (UInt256.ofNat 22) rdata (cA, σ) k C)
    (hprod1 :
      uniswapV3PoolFullMathMulDivProd1
          (UInt256.sub inside0 (solcSlotWord σ ee (posBase + (⟨1⟩ : UInt256))))
          (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase)) = ⟨0⟩)
    (hov : R.length + 45 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨13017⟩
      (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩ ::
        burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase) ::
        UInt256.sub inside1 (solcSlotWord σ ee (posBase + (⟨2⟩ : UInt256))) ::
        ⟨21807⟩ :: ⟨0⟩ ::
        UInt256.div
          (uniswapV3PoolFullMathMulDivProd0
            (UInt256.sub inside0 (solcSlotWord σ ee (posBase + (⟨1⟩ : UInt256))))
            (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase)))
          (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩) ::
        burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase) ::
        burnPositionKeyNewFreePtrWord :: inside1 :: inside0 :: delta :: posBase ::
        retPos :: inside1' :: inside0' :: z2 :: z3 :: fee1 :: fee0 :: posBase' ::
        tick :: delta' :: upper :: lower :: owner :: ret :: free :: R)
      (burnPositionUpdateMem5 σ ee (solcSlotWord σ ee posBase) posBase)
      (UInt256.ofNat 22) rdata (cA, σ) k' C' := by
  obtain ⟨_, _, hrd13044⟩ :=
    uniswapV3PoolFullMathMulDivStartProduct
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (mem := burnPositionUpdateMem5 σ ee (solcSlotWord σ ee posBase) posBase)
      (aw := UInt256.ofNat 22) (rdata := rdata) (acc := (cA, σ))
      (den := UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)
      (b := burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase))
      (a := UInt256.sub inside0 (solcSlotWord σ ee (posBase + (⟨1⟩ : UInt256))))
      (ret := ⟨21769⟩) (z := ⟨0⟩)
      (R := burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase) ::
        burnPositionKeyNewFreePtrWord :: inside1 :: inside0 :: delta :: posBase ::
        retPos :: inside1' :: inside0' :: z2 :: z3 :: fee1 :: fee0 :: posBase' ::
        tick :: delta' :: upper :: lower :: owner :: ret :: free :: R)
      hpatch h (by simp only [List.length_cons] at hov ⊢; omega)
  have hden :
      UInt256.gt (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩) ⟨0⟩ ≠ ⟨0⟩ := by
    native_decide
  obtain ⟨_, _, hrd21769⟩ :=
    uniswapV3PoolFullMathMulDivProd1ZeroReturn
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (mem := burnPositionUpdateMem5 σ ee (solcSlotWord σ ee posBase) posBase)
      (aw := UInt256.ofNat 22) (rdata := rdata) (acc := (cA, σ))
      (prod1 := uniswapV3PoolFullMathMulDivProd1
        (UInt256.sub inside0 (solcSlotWord σ ee (posBase + (⟨1⟩ : UInt256))))
        (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase)))
      (prod0 := uniswapV3PoolFullMathMulDivProd0
        (UInt256.sub inside0 (solcSlotWord σ ee (posBase + (⟨1⟩ : UInt256))))
        (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase)))
      (den := UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)
      (b := burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase))
      (a := UInt256.sub inside0 (solcSlotWord σ ee (posBase + (⟨1⟩ : UInt256))))
      (ret := ⟨21769⟩) (z := ⟨0⟩)
      (R := burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase) ::
        burnPositionKeyNewFreePtrWord :: inside1 :: inside0 :: delta :: posBase ::
        retPos :: inside1' :: inside0' :: z2 :: z3 :: fee1 :: fee0 :: posBase' ::
        tick :: delta' :: upper :: lower :: owner :: ret :: free :: R)
      hpatch hrd13044 hprod1 hden (uniswapV3PoolJumpDestPatched21769 hpatch)
      (by simp only [List.length_cons] at hov ⊢; omega)
  exact uniswapV3PoolBurnPositionUpdateStartMulDiv1
    (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
    (tokensOwed0 := UInt256.div
      (uniswapV3PoolFullMathMulDivProd0
        (UInt256.sub inside0 (solcSlotWord σ ee (posBase + (⟨1⟩ : UInt256))))
        (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase)))
      (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩))
    (z := ⟨0⟩)
    (liquidity := burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase))
    (inside1 := inside1) (inside0 := inside0) (delta := delta) (posBase := posBase)
    (retPos := retPos) (inside1' := inside1') (inside0' := inside0') (z2 := z2)
    (z3 := z3) (fee1 := fee1) (fee0 := fee0) (posBase' := posBase') (tick := tick)
    (delta' := delta') (upper := upper) (lower := lower) (owner := owner) (ret := ret)
    (free := free) (R := R) (rdata := rdata) (cA := cA) (σ := σ)
    hpatch hrd21769 (by omega)

theorem uniswapV3PoolBurnPositionUpdateDeltaZeroSkipLiquidityWrite {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {tokensOwed1 z tokensOwed0 liquidity inside1 inside0 delta posBase retPos inside1'
      inside0' z2 z3 fee1 fee0 posBase' tick delta' upper lower owner ret free : UInt256}
    {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hdelta : UInt256.signextend ⟨15⟩ delta = ⟨0⟩)
    (h : RD code ee g s0 ⟨21807⟩
      (tokensOwed1 :: z :: tokensOwed0 :: liquidity :: burnPositionKeyNewFreePtrWord ::
        inside1 :: inside0 :: delta :: posBase :: retPos :: inside1' :: inside0' ::
        z2 :: z3 :: fee1 :: fee0 :: posBase' :: tick :: delta' :: upper :: lower ::
        owner :: ret :: free :: R)
      (burnPositionUpdateMem5 σ ee (solcSlotWord σ ee posBase) posBase)
      (UInt256.ofNat 22) rdata (cA, σ) k C)
    (hov : R.length + 35 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨21846⟩
      (tokensOwed1 :: tokensOwed0 :: liquidity :: burnPositionKeyNewFreePtrWord ::
        inside1 :: inside0 :: delta :: posBase :: retPos :: inside1' :: inside0' ::
        z2 :: z3 :: fee1 :: fee0 :: posBase' :: tick :: delta' :: upper :: lower ::
        owner :: ret :: free :: R)
      (burnPositionUpdateMem5 σ ee (solcSlotWord σ ee posBase) posBase)
      (UInt256.ofNat 22) rdata (cA, σ) k' C' := by
  have hdec (pc : UInt256)
      (hlo : 21807 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 21900) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    exact uniswapV3PoolBurnPositionUpdateSkipLiquidityDecodeEqTemplate hpatch hlo (by omega)
  have hd21807 : decode code ⟨21807⟩ = some (.JUMPDEST, .none) := by
    rw [hdec ⟨21807⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21808 : decode code ⟨21808⟩ = some (.SWAP1, .none) := by
    rw [hdec ⟨21808⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21809 : decode code ⟨21809⟩ = some (.POP, .none) := by
    rw [hdec ⟨21809⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21810 : decode code ⟨21810⟩ = some (.DUP7, .none) := by
    rw [hdec ⟨21810⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21811 :
      decode code ⟨21811⟩ = some (.Push .PUSH1, some (⟨15⟩, 1)) := by
    rw [hdec ⟨21811⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21813 : decode code ⟨21813⟩ = some (.SIGNEXTEND, .none) := by
    rw [hdec ⟨21813⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21814 :
      decode code ⟨21814⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    rw [hdec ⟨21814⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21816 : decode code ⟨21816⟩ = some (.EQ, .none) := by
    rw [hdec ⟨21816⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21817 :
      decode code ⟨21817⟩ = some (.Push .PUSH2, some (⟨21846⟩, 2)) := by
    rw [hdec ⟨21817⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21820 : decode code ⟨21820⟩ = some (.JUMPI, .none) := by
    rw [hdec ⟨21820⟩ (by native_decide) (by native_decide)]
    native_decide
  have rd21813 := evm_run h with [
    raw jumpdest hd21807 (by evm_ov),
    raw swap1 hd21808 (by simp only [List.length_cons] at hov ⊢; omega),
    raw pop hd21809 (by simp only [List.length_cons] at hov ⊢; omega),
    raw dup7 hd21810 (by simp only [List.length_cons] at hov ⊢; omega),
    raw push1 ⟨15⟩ hd21811 (by evm_ov)]
  have rd21814 := by
    simpa using burnRDSignextend rd21813 hd21813
      (by simp only [List.length_cons] at hov ⊢; omega)
  have rd21820 := evm_run rd21814 with [
    raw push1 ⟨0⟩ hd21814 (by evm_ov),
    raw eq hd21816 (by evm_ov),
    raw push2 ⟨21846⟩ hd21817 (by evm_ov)]
  have rd21846 := rd21820.jumpiT hd21820
    (by rw [hdelta]; native_decide)
    (uniswapV3PoolJumpDestPatched21846 hpatch)
    (by simp only [List.length_cons] at hov ⊢; omega)
  exact ⟨_, _, rd21846⟩

theorem uniswapV3PoolBurnPositionUpdateMulDiv1Prod1ZeroSkipLiquidityWrite
    {v : PoolImmutables} {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State}
    {tokensOwed0 liquidity inside1 inside0 delta posBase retPos inside1' inside0'
      z2 z3 fee1 fee0 posBase' tick delta' upper lower owner ret free : UInt256}
    {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨13017⟩
      (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩ :: liquidity ::
        UInt256.sub inside1 (solcSlotWord σ ee (posBase + (⟨2⟩ : UInt256))) ::
        ⟨21807⟩ :: ⟨0⟩ :: tokensOwed0 :: liquidity ::
        burnPositionKeyNewFreePtrWord :: inside1 :: inside0 :: delta :: posBase ::
        retPos :: inside1' :: inside0' :: z2 :: z3 :: fee1 :: fee0 :: posBase' ::
        tick :: delta' :: upper :: lower :: owner :: ret :: free :: R)
      (burnPositionUpdateMem5 σ ee (solcSlotWord σ ee posBase) posBase)
      (UInt256.ofNat 22) rdata (cA, σ) k C)
    (hprod1 :
      uniswapV3PoolFullMathMulDivProd1
          (UInt256.sub inside1 (solcSlotWord σ ee (posBase + (⟨2⟩ : UInt256))))
          liquidity = ⟨0⟩)
    (hdelta : UInt256.signextend ⟨15⟩ delta = ⟨0⟩)
    (hov : R.length + 45 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨21846⟩
      (UInt256.div
          (uniswapV3PoolFullMathMulDivProd0
            (UInt256.sub inside1 (solcSlotWord σ ee (posBase + (⟨2⟩ : UInt256))))
            liquidity)
          (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩) ::
        tokensOwed0 :: liquidity :: burnPositionKeyNewFreePtrWord ::
        inside1 :: inside0 :: delta :: posBase :: retPos :: inside1' :: inside0' ::
        z2 :: z3 :: fee1 :: fee0 :: posBase' :: tick :: delta' :: upper :: lower ::
        owner :: ret :: free :: R)
      (burnPositionUpdateMem5 σ ee (solcSlotWord σ ee posBase) posBase)
      (UInt256.ofNat 22) rdata (cA, σ) k' C' := by
  obtain ⟨_, _, hrd13044⟩ :=
    uniswapV3PoolFullMathMulDivStartProduct
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (mem := burnPositionUpdateMem5 σ ee (solcSlotWord σ ee posBase) posBase)
      (aw := UInt256.ofNat 22) (rdata := rdata) (acc := (cA, σ))
      (den := UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)
      (b := liquidity)
      (a := UInt256.sub inside1 (solcSlotWord σ ee (posBase + (⟨2⟩ : UInt256))))
      (ret := ⟨21807⟩) (z := ⟨0⟩)
      (R := tokensOwed0 :: liquidity :: burnPositionKeyNewFreePtrWord ::
        inside1 :: inside0 :: delta :: posBase :: retPos :: inside1' :: inside0' ::
        z2 :: z3 :: fee1 :: fee0 :: posBase' :: tick :: delta' :: upper :: lower ::
        owner :: ret :: free :: R)
      hpatch h (by simp only [List.length_cons] at hov ⊢; omega)
  have hden :
      UInt256.gt (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩) ⟨0⟩ ≠ ⟨0⟩ := by
    native_decide
  obtain ⟨_, _, hrd21807⟩ :=
    uniswapV3PoolFullMathMulDivProd1ZeroReturn
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (mem := burnPositionUpdateMem5 σ ee (solcSlotWord σ ee posBase) posBase)
      (aw := UInt256.ofNat 22) (rdata := rdata) (acc := (cA, σ))
      (prod1 := uniswapV3PoolFullMathMulDivProd1
        (UInt256.sub inside1 (solcSlotWord σ ee (posBase + (⟨2⟩ : UInt256))))
        liquidity)
      (prod0 := uniswapV3PoolFullMathMulDivProd0
        (UInt256.sub inside1 (solcSlotWord σ ee (posBase + (⟨2⟩ : UInt256))))
        liquidity)
      (den := UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)
      (b := liquidity)
      (a := UInt256.sub inside1 (solcSlotWord σ ee (posBase + (⟨2⟩ : UInt256))))
      (ret := ⟨21807⟩) (z := ⟨0⟩)
      (R := tokensOwed0 :: liquidity :: burnPositionKeyNewFreePtrWord ::
        inside1 :: inside0 :: delta :: posBase :: retPos :: inside1' :: inside0' ::
        z2 :: z3 :: fee1 :: fee0 :: posBase' :: tick :: delta' :: upper :: lower ::
        owner :: ret :: free :: R)
      hpatch hrd13044 hprod1 hden (uniswapV3PoolJumpDestPatched21807 hpatch)
      (by simp only [List.length_cons] at hov ⊢; omega)
  exact uniswapV3PoolBurnPositionUpdateDeltaZeroSkipLiquidityWrite
    (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
    (tokensOwed1 := UInt256.div
      (uniswapV3PoolFullMathMulDivProd0
        (UInt256.sub inside1 (solcSlotWord σ ee (posBase + (⟨2⟩ : UInt256))))
        liquidity)
      (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩))
    (z := ⟨0⟩) (tokensOwed0 := tokensOwed0) (liquidity := liquidity)
    (inside1 := inside1) (inside0 := inside0) (delta := delta) (posBase := posBase)
    (retPos := retPos) (inside1' := inside1') (inside0' := inside0') (z2 := z2)
    (z3 := z3) (fee1 := fee1) (fee0 := fee0) (posBase' := posBase') (tick := tick)
    (delta' := delta') (upper := upper) (lower := lower) (owner := owner) (ret := ret)
    (free := free) (R := R) (rdata := rdata) (cA := cA) (σ := σ)
    hpatch hdelta hrd21807 (by omega)

theorem uniswapV3PoolBurnPositionUpdateMulDivsProd1ZeroSkipLiquidityWrite
    {v : PoolImmutables} {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State}
    {inside1 inside0 delta posBase retPos inside1' inside0' z2 z3 fee1 fee0 posBase'
      tick delta' upper lower owner ret free : UInt256}
    {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨13017⟩
      (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩ ::
        burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase) ::
        UInt256.sub inside0 (solcSlotWord σ ee (posBase + (⟨1⟩ : UInt256))) ::
        ⟨21769⟩ :: ⟨0⟩ ::
        burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase) ::
        burnPositionKeyNewFreePtrWord :: inside1 :: inside0 :: delta :: posBase ::
        retPos :: inside1' :: inside0' :: z2 :: z3 :: fee1 :: fee0 :: posBase' ::
        tick :: delta' :: upper :: lower :: owner :: ret :: free :: R)
      (burnPositionUpdateMem5 σ ee (solcSlotWord σ ee posBase) posBase)
      (UInt256.ofNat 22) rdata (cA, σ) k C)
    (hprod0 :
      uniswapV3PoolFullMathMulDivProd1
          (UInt256.sub inside0 (solcSlotWord σ ee (posBase + (⟨1⟩ : UInt256))))
          (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase)) = ⟨0⟩)
    (hprod1 :
      uniswapV3PoolFullMathMulDivProd1
          (UInt256.sub inside1 (solcSlotWord σ ee (posBase + (⟨2⟩ : UInt256))))
          (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase)) = ⟨0⟩)
    (hdelta : UInt256.signextend ⟨15⟩ delta = ⟨0⟩)
    (hov : R.length + 45 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨21846⟩
      (UInt256.div
          (uniswapV3PoolFullMathMulDivProd0
            (UInt256.sub inside1 (solcSlotWord σ ee (posBase + (⟨2⟩ : UInt256))))
            (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase)))
          (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩) ::
        UInt256.div
          (uniswapV3PoolFullMathMulDivProd0
            (UInt256.sub inside0 (solcSlotWord σ ee (posBase + (⟨1⟩ : UInt256))))
            (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase)))
          (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩) ::
        burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase) ::
        burnPositionKeyNewFreePtrWord :: inside1 :: inside0 :: delta :: posBase ::
        retPos :: inside1' :: inside0' :: z2 :: z3 :: fee1 :: fee0 :: posBase' ::
        tick :: delta' :: upper :: lower :: owner :: ret :: free :: R)
      (burnPositionUpdateMem5 σ ee (solcSlotWord σ ee posBase) posBase)
      (UInt256.ofNat 22) rdata (cA, σ) k' C' := by
  obtain ⟨_, _, hrdSecond13017⟩ :=
    uniswapV3PoolBurnPositionUpdateMulDiv0Prod1ZeroStartMulDiv1
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (inside1 := inside1) (inside0 := inside0) (delta := delta) (posBase := posBase)
      (retPos := retPos) (inside1' := inside1') (inside0' := inside0') (z2 := z2)
      (z3 := z3) (fee1 := fee1) (fee0 := fee0) (posBase' := posBase') (tick := tick)
      (delta' := delta') (upper := upper) (lower := lower) (owner := owner) (ret := ret)
      (free := free) (R := R) (rdata := rdata) (cA := cA) (σ := σ)
      hpatch h hprod0 (by omega)
  exact uniswapV3PoolBurnPositionUpdateMulDiv1Prod1ZeroSkipLiquidityWrite
    (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
    (tokensOwed0 := UInt256.div
      (uniswapV3PoolFullMathMulDivProd0
        (UInt256.sub inside0 (solcSlotWord σ ee (posBase + (⟨1⟩ : UInt256))))
        (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase)))
      (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩))
    (liquidity := burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase))
    (inside1 := inside1) (inside0 := inside0) (delta := delta) (posBase := posBase)
    (retPos := retPos) (inside1' := inside1') (inside0' := inside0') (z2 := z2)
    (z3 := z3) (fee1 := fee1) (fee0 := fee0) (posBase' := posBase') (tick := tick)
    (delta' := delta') (upper := upper) (lower := lower) (owner := owner) (ret := ret)
    (free := free) (R := R) (rdata := rdata) (cA := cA) (σ := σ)
    hpatch hrdSecond13017 hprod1 hdelta (by omega)

theorem uniswapV3PoolBurnPositionUpdateStoreFeeGrowthLastAfterSkip {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {tokensOwed1 tokensOwed0 liquidity inside1 inside0 delta posBase retPos inside1'
      inside0' z2 z3 fee1 fee0 posBase' tick delta' upper lower owner ret : UInt256}
    {free : UInt256} {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hperm : ee.perm = true)
    (h : RD code ee g s0 ⟨21846⟩
      (tokensOwed1 :: tokensOwed0 :: liquidity :: burnPositionKeyNewFreePtrWord ::
        inside1 :: inside0 :: delta :: posBase :: retPos :: inside1' :: inside0' ::
        z2 :: z3 :: fee1 :: fee0 :: posBase' :: tick :: delta' :: upper :: lower ::
        owner :: ret :: free :: R)
      (burnPositionUpdateMem5 σ ee (solcSlotWord σ ee posBase) posBase)
      (UInt256.ofNat 22) rdata (cA, σ) k C)
    (hov : R.length + 35 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨21861⟩
      (tokensOwed1 :: tokensOwed0 :: liquidity :: burnPositionKeyNewFreePtrWord ::
        inside1 :: inside0 :: delta :: posBase :: retPos :: inside1' :: inside0' ::
        z2 :: z3 :: fee1 :: fee0 :: posBase' :: tick :: delta' :: upper :: lower ::
        owner :: ret :: free :: R)
      (burnPositionUpdateMem5 σ ee (solcSlotWord σ ee posBase) posBase)
      (UInt256.ofNat 22) rdata
      (cA, sstoreAccountMap ee.codeOwner
        (sstoreAccountMap ee.codeOwner σ (posBase + (⟨1⟩ : UInt256)) inside0)
        (posBase + (⟨2⟩ : UInt256)) inside1) k' C' := by
  have hdec (pc : UInt256)
      (hlo : 21807 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 21900) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    exact uniswapV3PoolBurnPositionUpdateSkipLiquidityDecodeEqTemplate hpatch hlo (by omega)
  have hd21846 : decode code ⟨21846⟩ = some (.JUMPDEST, .none) := by
    rw [hdec ⟨21846⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21847 :
      decode code ⟨21847⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdec ⟨21847⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21849 : decode code ⟨21849⟩ = some (.DUP9, .none) := by
    rw [hdec ⟨21849⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21850 : decode code ⟨21850⟩ = some (.ADD, .none) := by
    rw [hdec ⟨21850⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21851 : decode code ⟨21851⟩ = some (.DUP7, .none) := by
    rw [hdec ⟨21851⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21852 : decode code ⟨21852⟩ = some (.SWAP1, .none) := by
    rw [hdec ⟨21852⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21853 : decode code ⟨21853⟩ = some (.SSTORE, .none) := by
    rw [hdec ⟨21853⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21854 :
      decode code ⟨21854⟩ = some (.Push .PUSH1, some (⟨2⟩, 1)) := by
    rw [hdec ⟨21854⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21856 : decode code ⟨21856⟩ = some (.DUP9, .none) := by
    rw [hdec ⟨21856⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21857 : decode code ⟨21857⟩ = some (.ADD, .none) := by
    rw [hdec ⟨21857⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21858 : decode code ⟨21858⟩ = some (.DUP6, .none) := by
    rw [hdec ⟨21858⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21859 : decode code ⟨21859⟩ = some (.SWAP1, .none) := by
    rw [hdec ⟨21859⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21860 : decode code ⟨21860⟩ = some (.SSTORE, .none) := by
    rw [hdec ⟨21860⟩ (by native_decide) (by native_decide)]
    native_decide
  have rd21853 := evm_run h with [
    raw jumpdest hd21846 (by evm_ov),
    raw push1 ⟨1⟩ hd21847 (by evm_ov),
    raw dup9 hd21849 (by simp only [List.length_cons] at hov ⊢; omega),
    raw add hd21850 (by evm_ov),
    raw dup7 hd21851 (by simp only [List.length_cons] at hov ⊢; omega),
    raw swap1 hd21852 (by simp only [List.length_cons] at hov ⊢; omega)]
  obtain ⟨_, _, rd21854⟩ := rd21853.sstore hperm hd21853
    (by simp only [List.length_cons] at hov ⊢; omega)
  have rd21860 := evm_run rd21854 with [
    raw push1 ⟨2⟩ hd21854 (by evm_ov),
    raw dup9 hd21856 (by simp only [List.length_cons] at hov ⊢; omega),
    raw add hd21857 (by evm_ov),
    raw dup6 hd21858 (by simp only [List.length_cons] at hov ⊢; omega),
    raw swap1 hd21859 (by simp only [List.length_cons] at hov ⊢; omega)]
  obtain ⟨_, _, rd21861⟩ := rd21860.sstore hperm hd21860
    (by simp only [List.length_cons] at hov ⊢; omega)
  exact ⟨_, _, rd21861⟩

theorem uniswapV3PoolBurnPositionUpdateMulDivsProd1ZeroStoreFeeGrowthLast
    {v : PoolImmutables} {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State}
    {inside1 inside0 delta posBase retPos inside1' inside0' z2 z3 fee1 fee0 posBase'
      tick delta' upper lower owner ret free : UInt256}
    {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hperm : ee.perm = true)
    (h : RD code ee g s0 ⟨13017⟩
      (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩ ::
        burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase) ::
        UInt256.sub inside0 (solcSlotWord σ ee (posBase + (⟨1⟩ : UInt256))) ::
        ⟨21769⟩ :: ⟨0⟩ ::
        burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase) ::
        burnPositionKeyNewFreePtrWord :: inside1 :: inside0 :: delta :: posBase ::
        retPos :: inside1' :: inside0' :: z2 :: z3 :: fee1 :: fee0 :: posBase' ::
        tick :: delta' :: upper :: lower :: owner :: ret :: free :: R)
      (burnPositionUpdateMem5 σ ee (solcSlotWord σ ee posBase) posBase)
      (UInt256.ofNat 22) rdata (cA, σ) k C)
    (hprod0 :
      uniswapV3PoolFullMathMulDivProd1
          (UInt256.sub inside0 (solcSlotWord σ ee (posBase + (⟨1⟩ : UInt256))))
          (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase)) = ⟨0⟩)
    (hprod1 :
      uniswapV3PoolFullMathMulDivProd1
          (UInt256.sub inside1 (solcSlotWord σ ee (posBase + (⟨2⟩ : UInt256))))
          (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase)) = ⟨0⟩)
    (hdelta : UInt256.signextend ⟨15⟩ delta = ⟨0⟩)
    (hov : R.length + 45 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨21861⟩
      (UInt256.div
          (uniswapV3PoolFullMathMulDivProd0
            (UInt256.sub inside1 (solcSlotWord σ ee (posBase + (⟨2⟩ : UInt256))))
            (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase)))
          (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩) ::
        UInt256.div
          (uniswapV3PoolFullMathMulDivProd0
            (UInt256.sub inside0 (solcSlotWord σ ee (posBase + (⟨1⟩ : UInt256))))
            (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase)))
          (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩) ::
        burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase) ::
        burnPositionKeyNewFreePtrWord :: inside1 :: inside0 :: delta :: posBase ::
        retPos :: inside1' :: inside0' :: z2 :: z3 :: fee1 :: fee0 :: posBase' ::
        tick :: delta' :: upper :: lower :: owner :: ret :: free :: R)
      (burnPositionUpdateMem5 σ ee (solcSlotWord σ ee posBase) posBase)
      (UInt256.ofNat 22) rdata
      (cA, sstoreAccountMap ee.codeOwner
        (sstoreAccountMap ee.codeOwner σ (posBase + (⟨1⟩ : UInt256)) inside0)
        (posBase + (⟨2⟩ : UInt256)) inside1) k' C' := by
  obtain ⟨_, _, hrd21846⟩ :=
    uniswapV3PoolBurnPositionUpdateMulDivsProd1ZeroSkipLiquidityWrite
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (inside1 := inside1) (inside0 := inside0) (delta := delta) (posBase := posBase)
      (retPos := retPos) (inside1' := inside1') (inside0' := inside0') (z2 := z2)
      (z3 := z3) (fee1 := fee1) (fee0 := fee0) (posBase' := posBase') (tick := tick)
      (delta' := delta') (upper := upper) (lower := lower) (owner := owner) (ret := ret)
      (free := free) (R := R) (rdata := rdata) (cA := cA) (σ := σ)
      hpatch h hprod0 hprod1 hdelta hov
  exact uniswapV3PoolBurnPositionUpdateStoreFeeGrowthLastAfterSkip
    (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
    (tokensOwed1 := UInt256.div
      (uniswapV3PoolFullMathMulDivProd0
        (UInt256.sub inside1 (solcSlotWord σ ee (posBase + (⟨2⟩ : UInt256))))
        (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase)))
      (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩))
    (tokensOwed0 := UInt256.div
      (uniswapV3PoolFullMathMulDivProd0
        (UInt256.sub inside0 (solcSlotWord σ ee (posBase + (⟨1⟩ : UInt256))))
        (burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase)))
      (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩))
    (liquidity := burnPositionUpdateSlot0Packed (solcSlotWord σ ee posBase))
    (inside1 := inside1) (inside0 := inside0) (delta := delta) (posBase := posBase)
    (retPos := retPos) (inside1' := inside1') (inside0' := inside0') (z2 := z2)
    (z3 := z3) (fee1 := fee1) (fee0 := fee0) (posBase' := posBase') (tick := tick)
    (delta' := delta') (upper := upper) (lower := lower) (owner := owner) (ret := ret)
    (free := free) (R := R) (rdata := rdata) (cA := cA) (σ := σ)
    hpatch hperm hrd21846 (by omega)

theorem uniswapV3PoolBurnPositionUpdateStoreTokensOwedSlot3 {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {tokensOwed1 tokensOwed0 liquidity freePtr inside1 inside0 delta posBase retPos
      inside1' inside0' z2 z3 fee1 fee0 posBase' tick delta' upper lower owner ret
      free : UInt256}
    {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hperm : ee.perm = true)
    (h : RD code ee g s0 ⟨21898⟩
      (tokensOwed1 :: tokensOwed0 :: liquidity :: freePtr :: inside1 :: inside0 ::
        delta :: posBase :: retPos :: inside1' :: inside0' :: z2 :: z3 :: fee1 ::
        fee0 :: posBase' :: tick :: delta' :: upper :: lower :: owner :: ret ::
        free :: R)
      mem aw rdata (cA, σ) k C)
    (hov : R.length + 35 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨21954⟩
      (tokensOwed1 :: tokensOwed0 :: liquidity :: freePtr :: inside1 :: inside0 ::
        delta :: posBase :: retPos :: inside1' :: inside0' :: z2 :: z3 :: fee1 ::
        fee0 :: posBase' :: tick :: delta' :: upper :: lower :: owner :: ret ::
        free :: R)
      mem aw rdata
      (cA, sstoreAccountMap ee.codeOwner σ (posBase + (⟨3⟩ : UInt256))
        (burnPositionUpdateTokensOwedAddedSlot3
          (solcSlotWord σ ee (posBase + (⟨3⟩ : UInt256))) tokensOwed0 tokensOwed1))
      k' C' := by
  have hdec (pc : UInt256)
      (hlo : 21807 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 21986) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    exact uniswapV3PoolBurnPositionUpdateSkipLiquidityDecodeEqTemplate hpatch hlo hhi
  have hd21898 :
      decode code ⟨21898⟩ = some (.Push .PUSH1, some (⟨3⟩, 1)) := by
    rw [hdec ⟨21898⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21900 : decode code ⟨21900⟩ = some (.DUP9, .none) := by
    rw [hdec ⟨21900⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21901 : decode code ⟨21901⟩ = some (.ADD, .none) := by
    rw [hdec ⟨21901⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21902 : decode code ⟨21902⟩ = some (.DUP1, .none) := by
    rw [hdec ⟨21902⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21903 : decode code ⟨21903⟩ = some (.SLOAD, .none) := by
    rw [hdec ⟨21903⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21904 :
      decode code ⟨21904⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdec ⟨21904⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21906 :
      decode code ⟨21906⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdec ⟨21906⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21908 :
      decode code ⟨21908⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)) := by
    rw [hdec ⟨21908⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21910 : decode code ⟨21910⟩ = some (.SHL, .none) := by
    rw [hdec ⟨21910⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21911 : decode code ⟨21911⟩ = some (.SUB, .none) := by
    rw [hdec ⟨21911⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21912 : decode code ⟨21912⟩ = some (.NOT, .none) := by
    rw [hdec ⟨21912⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21913 : decode code ⟨21913⟩ = some (.DUP2, .none) := by
    rw [hdec ⟨21913⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21914 : decode code ⟨21914⟩ = some (.AND, .none) := by
    rw [hdec ⟨21914⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21915 :
      decode code ⟨21915⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdec ⟨21915⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21917 :
      decode code ⟨21917⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdec ⟨21917⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21919 :
      decode code ⟨21919⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)) := by
    rw [hdec ⟨21919⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21921 : decode code ⟨21921⟩ = some (.SHL, .none) := by
    rw [hdec ⟨21921⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21922 : decode code ⟨21922⟩ = some (.SUB, .none) := by
    rw [hdec ⟨21922⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21923 : decode code ⟨21923⟩ = some (.SWAP2, .none) := by
    rw [hdec ⟨21923⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21924 : decode code ⟨21924⟩ = some (.DUP3, .none) := by
    rw [hdec ⟨21924⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21925 : decode code ⟨21925⟩ = some (.AND, .none) := by
    rw [hdec ⟨21925⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21926 : decode code ⟨21926⟩ = some (.DUP6, .none) := by
    rw [hdec ⟨21926⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21927 : decode code ⟨21927⟩ = some (.ADD, .none) := by
    rw [hdec ⟨21927⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21928 : decode code ⟨21928⟩ = some (.DUP3, .none) := by
    rw [hdec ⟨21928⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21929 : decode code ⟨21929⟩ = some (.AND, .none) := by
    rw [hdec ⟨21929⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21930 : decode code ⟨21930⟩ = some (.OR, .none) := by
    rw [hdec ⟨21930⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21931 : decode code ⟨21931⟩ = some (.DUP1, .none) := by
    rw [hdec ⟨21931⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21932 : decode code ⟨21932⟩ = some (.DUP3, .none) := by
    rw [hdec ⟨21932⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21933 : decode code ⟨21933⟩ = some (.AND, .none) := by
    rw [hdec ⟨21933⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21934 :
      decode code ⟨21934⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdec ⟨21934⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21936 :
      decode code ⟨21936⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)) := by
    rw [hdec ⟨21936⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21938 : decode code ⟨21938⟩ = some (.SHL, .none) := by
    rw [hdec ⟨21938⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21939 : decode code ⟨21939⟩ = some (.SWAP2, .none) := by
    rw [hdec ⟨21939⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21940 : decode code ⟨21940⟩ = some (.DUP3, .none) := by
    rw [hdec ⟨21940⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21941 : decode code ⟨21941⟩ = some (.SWAP1, .none) := by
    rw [hdec ⟨21941⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21942 : decode code ⟨21942⟩ = some (.DIV, .none) := by
    rw [hdec ⟨21942⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21943 : decode code ⟨21943⟩ = some (.DUP4, .none) := by
    rw [hdec ⟨21943⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21944 : decode code ⟨21944⟩ = some (.AND, .none) := by
    rw [hdec ⟨21944⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21945 : decode code ⟨21945⟩ = some (.DUP6, .none) := by
    rw [hdec ⟨21945⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21946 : decode code ⟨21946⟩ = some (.ADD, .none) := by
    rw [hdec ⟨21946⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21947 : decode code ⟨21947⟩ = some (.SWAP1, .none) := by
    rw [hdec ⟨21947⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21948 : decode code ⟨21948⟩ = some (.SWAP3, .none) := by
    rw [hdec ⟨21948⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21949 : decode code ⟨21949⟩ = some (.AND, .none) := by
    rw [hdec ⟨21949⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21950 : decode code ⟨21950⟩ = some (.MUL, .none) := by
    rw [hdec ⟨21950⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21951 : decode code ⟨21951⟩ = some (.OR, .none) := by
    rw [hdec ⟨21951⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21952 : decode code ⟨21952⟩ = some (.SWAP1, .none) := by
    rw [hdec ⟨21952⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21953 : decode code ⟨21953⟩ = some (.SSTORE, .none) := by
    rw [hdec ⟨21953⟩ (by native_decide) (by native_decide)]
    native_decide
  have rd21903 := evm_run h with [
    raw push1 ⟨3⟩ hd21898 (by evm_ov),
    raw dup9 hd21900 (by simp only [List.length_cons] at hov ⊢; omega),
    raw add hd21901 (by evm_ov),
    raw dup1 hd21902 (by simp only [List.length_cons] at hov ⊢; omega)]
  obtain ⟨_, _, rd21904⟩ := rd21903.sload hd21903
    (by simp only [List.length_cons] at hov ⊢; omega)
  have rd21953 := evm_run rd21904 with [
    raw push1 ⟨1⟩ hd21904 (by evm_ov),
    raw push1 ⟨1⟩ hd21906 (by evm_ov),
    raw push1 ⟨128⟩ hd21908 (by evm_ov),
    raw shl hd21910 (by evm_ov),
    raw sub hd21911 (by evm_ov),
    raw not hd21912 (by evm_ov),
    raw dup2 hd21913 (by simp only [List.length_cons] at hov ⊢; omega),
    raw and hd21914 (by evm_ov),
    raw push1 ⟨1⟩ hd21915 (by evm_ov),
    raw push1 ⟨1⟩ hd21917 (by evm_ov),
    raw push1 ⟨128⟩ hd21919 (by evm_ov),
    raw shl hd21921 (by evm_ov),
    raw sub hd21922 (by evm_ov),
    raw swap2 hd21923 (by simp only [List.length_cons] at hov ⊢; omega),
    raw dup3 hd21924 (by simp only [List.length_cons] at hov ⊢; omega),
    raw and hd21925 (by evm_ov),
    raw dup6 hd21926 (by simp only [List.length_cons] at hov ⊢; omega),
    raw add hd21927 (by evm_ov),
    raw dup3 hd21928 (by simp only [List.length_cons] at hov ⊢; omega),
    raw and hd21929 (by evm_ov),
    raw lor hd21930 (by evm_ov),
    raw dup1 hd21931 (by simp only [List.length_cons] at hov ⊢; omega),
    raw dup3 hd21932 (by simp only [List.length_cons] at hov ⊢; omega),
    raw and hd21933 (by evm_ov),
    raw push1 ⟨1⟩ hd21934 (by evm_ov),
    raw push1 ⟨128⟩ hd21936 (by evm_ov),
    raw shl hd21938 (by evm_ov),
    raw swap2 hd21939 (by simp only [List.length_cons] at hov ⊢; omega),
    raw dup3 hd21940 (by simp only [List.length_cons] at hov ⊢; omega),
    raw swap1 hd21941 (by simp only [List.length_cons] at hov ⊢; omega),
    raw div hd21942 (by evm_ov),
    raw dup4 hd21943 (by simp only [List.length_cons] at hov ⊢; omega),
    raw and hd21944 (by evm_ov),
    raw dup6 hd21945 (by simp only [List.length_cons] at hov ⊢; omega),
    raw add hd21946 (by evm_ov),
    raw swap1 hd21947 (by simp only [List.length_cons] at hov ⊢; omega),
    raw swap3 hd21948 (by simp only [List.length_cons] at hov ⊢; omega),
    raw and hd21949 (by evm_ov),
    raw mul hd21950 (by evm_ov),
    raw lor hd21951 (by evm_ov),
    raw swap1 hd21952 (by simp only [List.length_cons] at hov ⊢; omega)]
  obtain ⟨_, _, rd21954⟩ := rd21953.sstore hperm hd21953
    (by simp only [List.length_cons] at hov ⊢; omega)
  exact ⟨_, _, by
    simpa [burnPositionUpdateTokensOwedAddedSlot3,
      burnPositionUpdateTokensOwed0AddedSlot3, burnPositionUpdateSlot0Mask] using rd21954⟩

theorem uniswapV3PoolBurnPositionUpdateTokensOwed0NonzeroStore {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {tokensOwed1 tokensOwed0 liquidity freePtr inside1 inside0 delta posBase retPos
      inside1' inside0' z2 z3 fee1 fee0 posBase' tick delta' upper lower owner ret
      free : UInt256}
    {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hperm : ee.perm = true)
    (h : RD code ee g s0 ⟨21861⟩
      (tokensOwed1 :: tokensOwed0 :: liquidity :: freePtr :: inside1 :: inside0 ::
        delta :: posBase :: retPos :: inside1' :: inside0' :: z2 :: z3 :: fee1 ::
        fee0 :: posBase' :: tick :: delta' :: upper :: lower :: owner :: ret ::
        free :: R)
      mem aw rdata (cA, σ) k C)
    (htokens0 : UInt256.land burnPositionUpdateSlot0Mask tokensOwed0 ≠ ⟨0⟩)
    (hov : R.length + 35 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨21954⟩
      (tokensOwed1 :: tokensOwed0 :: liquidity :: freePtr :: inside1 :: inside0 ::
        delta :: posBase :: retPos :: inside1' :: inside0' :: z2 :: z3 :: fee1 ::
        fee0 :: posBase' :: tick :: delta' :: upper :: lower :: owner :: ret ::
        free :: R)
      mem aw rdata
      (cA, sstoreAccountMap ee.codeOwner σ (posBase + (⟨3⟩ : UInt256))
        (burnPositionUpdateTokensOwedAddedSlot3
          (solcSlotWord σ ee (posBase + (⟨3⟩ : UInt256))) tokensOwed0 tokensOwed1))
      k' C' := by
  have hdec (pc : UInt256)
      (hlo : 21807 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 21930) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    exact uniswapV3PoolBurnPositionUpdateSkipLiquidityDecodeEqTemplate hpatch hlo (by omega)
  have hd21861 :
      decode code ⟨21861⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdec ⟨21861⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21863 :
      decode code ⟨21863⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdec ⟨21863⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21865 :
      decode code ⟨21865⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)) := by
    rw [hdec ⟨21865⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21867 : decode code ⟨21867⟩ = some (.SHL, .none) := by
    rw [hdec ⟨21867⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21868 : decode code ⟨21868⟩ = some (.SUB, .none) := by
    rw [hdec ⟨21868⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21869 : decode code ⟨21869⟩ = some (.DUP3, .none) := by
    rw [hdec ⟨21869⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21870 : decode code ⟨21870⟩ = some (.AND, .none) := by
    rw [hdec ⟨21870⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21871 : decode code ⟨21871⟩ = some (.ISZERO, .none) := by
    rw [hdec ⟨21871⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21872 : decode code ⟨21872⟩ = some (.ISZERO, .none) := by
    rw [hdec ⟨21872⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21873 : decode code ⟨21873⟩ = some (.DUP1, .none) := by
    rw [hdec ⟨21873⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21874 :
      decode code ⟨21874⟩ = some (.Push .PUSH2, some (⟨21892⟩, 2)) := by
    rw [hdec ⟨21874⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21877 : decode code ⟨21877⟩ = some (.JUMPI, .none) := by
    rw [hdec ⟨21877⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21892 : decode code ⟨21892⟩ = some (.JUMPDEST, .none) := by
    rw [hdec ⟨21892⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21893 : decode code ⟨21893⟩ = some (.ISZERO, .none) := by
    rw [hdec ⟨21893⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21894 :
      decode code ⟨21894⟩ = some (.Push .PUSH2, some (⟨21954⟩, 2)) := by
    rw [hdec ⟨21894⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21897 : decode code ⟨21897⟩ = some (.JUMPI, .none) := by
    rw [hdec ⟨21897⟩ (by native_decide) (by native_decide)]
    native_decide
  have rd21877 := evm_run h with [
    raw push1 ⟨1⟩ hd21861 (by evm_ov),
    raw push1 ⟨1⟩ hd21863 (by evm_ov),
    raw push1 ⟨128⟩ hd21865 (by evm_ov),
    raw shl hd21867 (by evm_ov),
    raw sub hd21868 (by evm_ov),
    raw dup3 hd21869 (by simp only [List.length_cons] at hov ⊢; omega),
    raw and hd21870 (by evm_ov),
    raw iszero hd21871 (by evm_ov),
    raw iszero hd21872 (by evm_ov),
    raw dup1 hd21873 (by simp only [List.length_cons] at hov ⊢; omega),
    raw push2 ⟨21892⟩ hd21874 (by evm_ov)]
  have hcond0 :
      UInt256.isZero
          (UInt256.isZero (UInt256.land tokensOwed0 burnPositionUpdateSlot0Mask)) ≠
        ⟨0⟩ := by
    rw [u256_land_comm tokensOwed0 burnPositionUpdateSlot0Mask]
    rw [isZero_eq_zero_of_ne htokens0]
    native_decide
  have rd21892 := rd21877.jumpiT hd21877 hcond0
    (uniswapV3PoolJumpDestPatched21892 hpatch)
    (by simp only [List.length_cons] at hov ⊢; omega)
  have rd21897 := evm_run rd21892 with [
    raw jumpdest hd21892 (by evm_ov),
    raw iszero hd21893 (by evm_ov),
    raw push2 ⟨21954⟩ hd21894 (by evm_ov)]
  have hstore :
      UInt256.isZero
          (UInt256.isZero
            (UInt256.isZero (UInt256.land tokensOwed0 burnPositionUpdateSlot0Mask))) =
        ⟨0⟩ := by
    rw [u256_land_comm tokensOwed0 burnPositionUpdateSlot0Mask]
    rw [isZero_eq_zero_of_ne htokens0]
    native_decide
  have rd21898 := rd21897.jumpiNT hd21897 hstore
    (by simp only [List.length_cons] at hov ⊢; omega)
  exact uniswapV3PoolBurnPositionUpdateStoreTokensOwedSlot3
    (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
    (tokensOwed1 := tokensOwed1) (tokensOwed0 := tokensOwed0)
    (liquidity := liquidity) (freePtr := freePtr) (inside1 := inside1)
    (inside0 := inside0) (delta := delta) (posBase := posBase) (retPos := retPos)
    (inside1' := inside1') (inside0' := inside0') (z2 := z2) (z3 := z3)
    (fee1 := fee1) (fee0 := fee0) (posBase' := posBase') (tick := tick)
    (delta' := delta') (upper := upper) (lower := lower) (owner := owner)
    (ret := ret) (free := free) (R := R) (mem := mem) (aw := aw)
    (rdata := rdata) (cA := cA) (σ := σ) hpatch hperm rd21898 hov

theorem uniswapV3PoolBurnPositionUpdateTokensOwedZeroSkipStores {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {tokensOwed1 tokensOwed0 liquidity inside1 inside0 delta posBase retPos inside1'
      inside0' z2 z3 fee1 fee0 posBase' tick delta' upper lower owner ret free : UInt256}
    {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨21861⟩
      (tokensOwed1 :: tokensOwed0 :: liquidity :: burnPositionKeyNewFreePtrWord ::
        inside1 :: inside0 :: delta :: posBase :: retPos :: inside1' :: inside0' ::
        z2 :: z3 :: fee1 :: fee0 :: posBase' :: tick :: delta' :: upper :: lower ::
        owner :: ret :: free :: R)
      (burnPositionUpdateMem5 σ ee (solcSlotWord σ ee posBase) posBase)
      (UInt256.ofNat 22) rdata (cA, σ) k C)
    (htokens0 : UInt256.land burnPositionUpdateSlot0Mask tokensOwed0 = ⟨0⟩)
    (htokens1 : UInt256.land burnPositionUpdateSlot0Mask tokensOwed1 = ⟨0⟩)
    (hov : R.length + 35 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨21954⟩
      (tokensOwed1 :: tokensOwed0 :: liquidity :: burnPositionKeyNewFreePtrWord ::
        inside1 :: inside0 :: delta :: posBase :: retPos :: inside1' :: inside0' ::
        z2 :: z3 :: fee1 :: fee0 :: posBase' :: tick :: delta' :: upper :: lower ::
        owner :: ret :: free :: R)
      (burnPositionUpdateMem5 σ ee (solcSlotWord σ ee posBase) posBase)
      (UInt256.ofNat 22) rdata (cA, σ) k' C' := by
  have hdec (pc : UInt256)
      (hlo : 21807 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 21930) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    exact uniswapV3PoolBurnPositionUpdateSkipLiquidityDecodeEqTemplate hpatch hlo (by omega)
  have hd21861 :
      decode code ⟨21861⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdec ⟨21861⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21863 :
      decode code ⟨21863⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdec ⟨21863⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21865 :
      decode code ⟨21865⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)) := by
    rw [hdec ⟨21865⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21867 : decode code ⟨21867⟩ = some (.SHL, .none) := by
    rw [hdec ⟨21867⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21868 : decode code ⟨21868⟩ = some (.SUB, .none) := by
    rw [hdec ⟨21868⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21869 : decode code ⟨21869⟩ = some (.DUP3, .none) := by
    rw [hdec ⟨21869⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21870 : decode code ⟨21870⟩ = some (.AND, .none) := by
    rw [hdec ⟨21870⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21871 : decode code ⟨21871⟩ = some (.ISZERO, .none) := by
    rw [hdec ⟨21871⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21872 : decode code ⟨21872⟩ = some (.ISZERO, .none) := by
    rw [hdec ⟨21872⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21873 : decode code ⟨21873⟩ = some (.DUP1, .none) := by
    rw [hdec ⟨21873⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21874 :
      decode code ⟨21874⟩ = some (.Push .PUSH2, some (⟨21892⟩, 2)) := by
    rw [hdec ⟨21874⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21877 : decode code ⟨21877⟩ = some (.JUMPI, .none) := by
    rw [hdec ⟨21877⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21878 : decode code ⟨21878⟩ = some (.POP, .none) := by
    rw [hdec ⟨21878⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21879 :
      decode code ⟨21879⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    rw [hdec ⟨21879⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21881 : decode code ⟨21881⟩ = some (.DUP2, .none) := by
    rw [hdec ⟨21881⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21882 :
      decode code ⟨21882⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdec ⟨21882⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21884 :
      decode code ⟨21884⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdec ⟨21884⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21886 :
      decode code ⟨21886⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)) := by
    rw [hdec ⟨21886⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21888 : decode code ⟨21888⟩ = some (.SHL, .none) := by
    rw [hdec ⟨21888⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21889 : decode code ⟨21889⟩ = some (.SUB, .none) := by
    rw [hdec ⟨21889⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21890 : decode code ⟨21890⟩ = some (.AND, .none) := by
    rw [hdec ⟨21890⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21891 : decode code ⟨21891⟩ = some (.GT, .none) := by
    rw [hdec ⟨21891⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21892 : decode code ⟨21892⟩ = some (.JUMPDEST, .none) := by
    rw [hdec ⟨21892⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21893 : decode code ⟨21893⟩ = some (.ISZERO, .none) := by
    rw [hdec ⟨21893⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21894 :
      decode code ⟨21894⟩ = some (.Push .PUSH2, some (⟨21954⟩, 2)) := by
    rw [hdec ⟨21894⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21897 : decode code ⟨21897⟩ = some (.JUMPI, .none) := by
    rw [hdec ⟨21897⟩ (by native_decide) (by native_decide)]
    native_decide
  have rd21877 := evm_run h with [
    raw push1 ⟨1⟩ hd21861 (by evm_ov),
    raw push1 ⟨1⟩ hd21863 (by evm_ov),
    raw push1 ⟨128⟩ hd21865 (by evm_ov),
    raw shl hd21867 (by evm_ov),
    raw sub hd21868 (by evm_ov),
    raw dup3 hd21869 (by simp only [List.length_cons] at hov ⊢; omega),
    raw and hd21870 (by evm_ov),
    raw iszero hd21871 (by evm_ov),
    raw iszero hd21872 (by evm_ov),
    raw dup1 hd21873 (by simp only [List.length_cons] at hov ⊢; omega),
    raw push2 ⟨21892⟩ hd21874 (by evm_ov)]
  have hcond0 :
      UInt256.isZero
          (UInt256.isZero (UInt256.land tokensOwed0 burnPositionUpdateSlot0Mask)) =
        ⟨0⟩ := by
    rw [u256_land_comm tokensOwed0 burnPositionUpdateSlot0Mask]
    rw [htokens0]
    native_decide
  have rd21878 := by
    simpa [burnPositionUpdateSlot0Mask] using
      rd21877.jumpiNT hd21877 hcond0
        (by simp only [List.length_cons] at hov ⊢; omega)
  have rd21892 := evm_run rd21878 with [
    raw pop hd21878 (by simp only [List.length_cons] at hov ⊢; omega),
    raw push1 ⟨0⟩ hd21879 (by evm_ov),
    raw dup2 hd21881 (by simp only [List.length_cons] at hov ⊢; omega),
    raw push1 ⟨1⟩ hd21882 (by evm_ov),
    raw push1 ⟨1⟩ hd21884 (by evm_ov),
    raw push1 ⟨128⟩ hd21886 (by evm_ov),
    raw shl hd21888 (by evm_ov),
    raw sub hd21889 (by evm_ov),
    raw and hd21890 (by evm_ov),
    raw gt hd21891 (by evm_ov),
    raw jumpdest hd21892 (by evm_ov),
    raw iszero hd21893 (by evm_ov),
    raw push2 ⟨21954⟩ hd21894 (by evm_ov)]
  have hcond1 :
      UInt256.isZero
          (UInt256.gt (UInt256.land burnPositionUpdateSlot0Mask tokensOwed1) ⟨0⟩) ≠
        ⟨0⟩ := by
    rw [htokens1]
    native_decide
  exact ⟨_, _, by
    simpa [burnPositionUpdateSlot0Mask] using
      rd21892.jumpiT hd21897 hcond1 (uniswapV3PoolJumpDestPatched21954 hpatch)
        (by simp only [List.length_cons] at hov ⊢; omega)⟩

theorem uniswapV3PoolBurnPositionUpdatePostReturnJump {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {tokensOwed1 tokensOwed0 liquidity freePtr inside1 inside0 delta posBase retPos
      inside1' inside0' z2 z3 fee1 fee0 posBase' tick delta' upper lower owner ret
      free : UInt256}
    {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hdest : (D_J code 0).contains retPos = true)
    (h : RD code ee g s0 ⟨21954⟩
      (tokensOwed1 :: tokensOwed0 :: liquidity :: freePtr :: inside1 :: inside0 ::
        delta :: posBase :: retPos :: inside1' :: inside0' :: z2 :: z3 :: fee1 ::
        fee0 :: posBase' :: tick :: delta' :: upper :: lower :: owner :: ret ::
        free :: R)
      mem aw rdata acc k C)
    (hov : R.length + 35 ≤ 1024) :
    ∃ k' C', RD code ee g s0 retPos
      (inside1' :: inside0' :: z2 :: z3 :: fee1 :: fee0 :: posBase' :: tick ::
        delta' :: upper :: lower :: owner :: ret :: free :: R)
      mem aw rdata acc k' C' := by
  have hdec (pc : UInt256)
      (hlo : 21954 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 21996) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    exact uniswapV3PoolBurnPositionUpdateReturnDecodeEqTemplate hpatch hlo hhi
  have hd21954 : decode code ⟨21954⟩ = some (.JUMPDEST, .none) := by
    rw [hdec ⟨21954⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21955 : decode code ⟨21955⟩ = some (.POP, .none) := by
    rw [hdec ⟨21955⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21956 : decode code ⟨21956⟩ = some (.POP, .none) := by
    rw [hdec ⟨21956⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21957 : decode code ⟨21957⟩ = some (.POP, .none) := by
    rw [hdec ⟨21957⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21958 : decode code ⟨21958⟩ = some (.POP, .none) := by
    rw [hdec ⟨21958⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21959 : decode code ⟨21959⟩ = some (.POP, .none) := by
    rw [hdec ⟨21959⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21960 : decode code ⟨21960⟩ = some (.POP, .none) := by
    rw [hdec ⟨21960⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21961 : decode code ⟨21961⟩ = some (.POP, .none) := by
    rw [hdec ⟨21961⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21962 : decode code ⟨21962⟩ = some (.POP, .none) := by
    rw [hdec ⟨21962⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd21963 : decode code ⟨21963⟩ = some (.JUMP, .none) := by
    rw [hdec ⟨21963⟩ (by native_decide) (by native_decide)]
    native_decide
  have rd21963 := evm_run h with [
    raw jumpdest hd21954 (by evm_ov),
    raw pop hd21955 (by simp only [List.length_cons] at hov ⊢; omega),
    raw pop hd21956 (by simp only [List.length_cons] at hov ⊢; omega),
    raw pop hd21957 (by simp only [List.length_cons] at hov ⊢; omega),
    raw pop hd21958 (by simp only [List.length_cons] at hov ⊢; omega),
    raw pop hd21959 (by simp only [List.length_cons] at hov ⊢; omega),
    raw pop hd21960 (by simp only [List.length_cons] at hov ⊢; omega),
    raw pop hd21961 (by simp only [List.length_cons] at hov ⊢; omega),
    raw pop hd21962 (by simp only [List.length_cons] at hov ⊢; omega)]
  exact ⟨_, _, rd21963.jump hd21963 hdest
    (by simp only [List.length_cons] at hov ⊢; omega)⟩

theorem uniswapV3PoolBurnPositionUpdateTokensOwedZeroReturn {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {tokensOwed1 tokensOwed0 liquidity inside1 inside0 delta posBase retPos inside1'
      inside0' z2 z3 fee1 fee0 posBase' tick delta' upper lower owner ret free : UInt256}
    {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hdest : (D_J code 0).contains retPos = true)
    (h : RD code ee g s0 ⟨21861⟩
      (tokensOwed1 :: tokensOwed0 :: liquidity :: burnPositionKeyNewFreePtrWord ::
        inside1 :: inside0 :: delta :: posBase :: retPos :: inside1' :: inside0' ::
        z2 :: z3 :: fee1 :: fee0 :: posBase' :: tick :: delta' :: upper :: lower ::
        owner :: ret :: free :: R)
      (burnPositionUpdateMem5 σ ee (solcSlotWord σ ee posBase) posBase)
      (UInt256.ofNat 22) rdata (cA, σ) k C)
    (htokens0 : UInt256.land burnPositionUpdateSlot0Mask tokensOwed0 = ⟨0⟩)
    (htokens1 : UInt256.land burnPositionUpdateSlot0Mask tokensOwed1 = ⟨0⟩)
    (hov : R.length + 35 ≤ 1024) :
    ∃ k' C', RD code ee g s0 retPos
      (inside1' :: inside0' :: z2 :: z3 :: fee1 :: fee0 :: posBase' :: tick ::
        delta' :: upper :: lower :: owner :: ret :: free :: R)
      (burnPositionUpdateMem5 σ ee (solcSlotWord σ ee posBase) posBase)
      (UInt256.ofNat 22) rdata (cA, σ) k' C' := by
  obtain ⟨_, _, hrd21954⟩ :=
    uniswapV3PoolBurnPositionUpdateTokensOwedZeroSkipStores
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (tokensOwed1 := tokensOwed1) (tokensOwed0 := tokensOwed0)
      (liquidity := liquidity) (inside1 := inside1) (inside0 := inside0)
      (delta := delta) (posBase := posBase) (retPos := retPos)
      (inside1' := inside1') (inside0' := inside0') (z2 := z2) (z3 := z3)
      (fee1 := fee1) (fee0 := fee0) (posBase' := posBase') (tick := tick)
      (delta' := delta') (upper := upper) (lower := lower) (owner := owner)
      (ret := ret) (free := free) (R := R) (rdata := rdata) (cA := cA)
      (σ := σ) hpatch h htokens0 htokens1 hov
  exact uniswapV3PoolBurnPositionUpdatePostReturnJump
    (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
    (tokensOwed1 := tokensOwed1) (tokensOwed0 := tokensOwed0)
    (liquidity := liquidity) (freePtr := burnPositionKeyNewFreePtrWord)
    (inside1 := inside1) (inside0 := inside0) (delta := delta) (posBase := posBase)
    (retPos := retPos) (inside1' := inside1') (inside0' := inside0') (z2 := z2)
    (z3 := z3) (fee1 := fee1) (fee0 := fee0) (posBase' := posBase') (tick := tick)
    (delta' := delta') (upper := upper) (lower := lower) (owner := owner) (ret := ret)
    (free := free) (R := R)
    (mem := burnPositionUpdateMem5 σ ee (solcSlotWord σ ee posBase) posBase)
    (aw := UInt256.ofNat 22) (rdata := rdata) (acc := (cA, σ))
    hpatch hdest hrd21954 hov

theorem uniswapV3PoolBurnModifyPositionAfterPositionUpdateZeroDeltaReturn
    {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {inside1 inside0 z2 z3 fee1 fee0 posBase tick delta upper lower owner ret free :
      UInt256}
    {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hdest : (D_J code 0).contains ret = true)
    (h : RD code ee g s0 ⟨19527⟩
      (inside1 :: inside0 :: z2 :: z3 :: fee1 :: fee0 :: posBase :: tick :: delta ::
        upper :: lower :: owner :: ret :: free :: R)
      mem aw rdata acc k C)
    (hdelta : UInt256.slt (UInt256.signextend ⟨15⟩ delta) ⟨0⟩ = ⟨0⟩)
    (hov : R.length + 17 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret (posBase :: free :: R) mem aw rdata acc k' C' := by
  have hdec (pc : UInt256)
      (hlo : 19527 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 19620) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    exact uniswapV3PoolBurnModifyPositionPostPositionUpdateDecodeEqTemplate hpatch hlo hhi
  have hd19527 : decode code ⟨19527⟩ = some (.JUMPDEST, .none) := by
    rw [hdec ⟨19527⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd19528 : decode code ⟨19528⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    rw [hdec ⟨19528⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd19530 : decode code ⟨19530⟩ = some (.DUP10, .none) := by
    rw [hdec ⟨19530⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd19531 : decode code ⟨19531⟩ = some (.Push .PUSH1, some (⟨15⟩, 1)) := by
    rw [hdec ⟨19531⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd19533 : decode code ⟨19533⟩ = some (.SIGNEXTEND, .none) := by
    rw [hdec ⟨19533⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd19534 : decode code ⟨19534⟩ = some (.SLT, .none) := by
    rw [hdec ⟨19534⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd19535 : decode code ⟨19535⟩ = some (.ISZERO, .none) := by
    rw [hdec ⟨19535⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd19536 : decode code ⟨19536⟩ = some (.Push .PUSH2, some (⟨19573⟩, 2)) := by
    rw [hdec ⟨19536⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd19539 : decode code ⟨19539⟩ = some (.JUMPI, .none) := by
    rw [hdec ⟨19539⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd19573 : decode code ⟨19573⟩ = some (.JUMPDEST, .none) := by
    rw [hdec ⟨19573⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd19574 : decode code ⟨19574⟩ = some (.POP, .none) := by
    rw [hdec ⟨19574⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd19575 : decode code ⟨19575⟩ = some (.POP, .none) := by
    rw [hdec ⟨19575⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd19576 : decode code ⟨19576⟩ = some (.POP, .none) := by
    rw [hdec ⟨19576⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd19577 : decode code ⟨19577⟩ = some (.POP, .none) := by
    rw [hdec ⟨19577⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd19578 : decode code ⟨19578⟩ = some (.POP, .none) := by
    rw [hdec ⟨19578⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd19579 : decode code ⟨19579⟩ = some (.POP, .none) := by
    rw [hdec ⟨19579⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd19580 : decode code ⟨19580⟩ = some (.SWAP6, .none) := by
    rw [hdec ⟨19580⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd19581 : decode code ⟨19581⟩ = some (.SWAP5, .none) := by
    rw [hdec ⟨19581⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd19582 : decode code ⟨19582⟩ = some (.POP, .none) := by
    rw [hdec ⟨19582⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd19583 : decode code ⟨19583⟩ = some (.POP, .none) := by
    rw [hdec ⟨19583⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd19584 : decode code ⟨19584⟩ = some (.POP, .none) := by
    rw [hdec ⟨19584⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd19585 : decode code ⟨19585⟩ = some (.POP, .none) := by
    rw [hdec ⟨19585⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd19586 : decode code ⟨19586⟩ = some (.POP, .none) := by
    rw [hdec ⟨19586⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd19587 : decode code ⟨19587⟩ = some (.JUMP, .none) := by
    rw [hdec ⟨19587⟩ (by native_decide) (by native_decide)]
    native_decide
  have rd19533 := evm_run h with [
    raw jumpdest hd19527 (by evm_ov),
    raw push1 ⟨0⟩ hd19528 (by evm_ov),
    raw dup10 hd19530 (by simp only [List.length_cons] at hov ⊢; omega),
    raw push1 ⟨15⟩ hd19531 (by evm_ov)]
  have rd19534 := by
    simpa using burnRDSignextend rd19533 hd19533
      (by simp only [List.length_cons] at hov ⊢; omega)
  have rd19539 := evm_run rd19534 with [
    raw slt hd19534 (by evm_ov),
    raw iszero hd19535 (by evm_ov),
    raw push2 ⟨19573⟩ hd19536 (by evm_ov)]
  have hcond :
      UInt256.isZero (UInt256.slt (UInt256.signextend ⟨15⟩ delta) ⟨0⟩) ≠ ⟨0⟩ := by
    rw [hdelta]
    native_decide
  have rd19573 := rd19539.jumpiT hd19539 hcond
    (uniswapV3PoolJumpDestPatched19573 hpatch)
    (by simp only [List.length_cons] at hov ⊢; omega)
  have rd19587 := evm_run rd19573 with [
    raw jumpdest hd19573 (by evm_ov),
    raw pop hd19574 (by simp only [List.length_cons] at hov ⊢; omega),
    raw pop hd19575 (by simp only [List.length_cons] at hov ⊢; omega),
    raw pop hd19576 (by simp only [List.length_cons] at hov ⊢; omega),
    raw pop hd19577 (by simp only [List.length_cons] at hov ⊢; omega),
    raw pop hd19578 (by simp only [List.length_cons] at hov ⊢; omega),
    raw pop hd19579 (by simp only [List.length_cons] at hov ⊢; omega),
    raw swap6 hd19580 (by simp only [List.length_cons] at hov ⊢; omega),
    raw swap5 hd19581 (by simp only [List.length_cons] at hov ⊢; omega),
    raw pop hd19582 (by simp only [List.length_cons] at hov ⊢; omega),
    raw pop hd19583 (by simp only [List.length_cons] at hov ⊢; omega),
    raw pop hd19584 (by simp only [List.length_cons] at hov ⊢; omega),
    raw pop hd19585 (by simp only [List.length_cons] at hov ⊢; omega),
    raw pop hd19586 (by simp only [List.length_cons] at hov ⊢; omega)]
  exact ⟨_, _, rd19587.jump hd19587 hdest
    (by simp only [List.length_cons] at hov ⊢; omega)⟩

theorem uniswapV3PoolBurnPositionUpdateTokensOwedZeroZeroDeltaModifyPositionReturn
    {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {tokensOwed1 tokensOwed0 liquidity inside1 inside0 delta posBase inside1' inside0'
      z2 z3 fee1 fee0 posBase' tick delta' upper lower owner ret free : UInt256}
    {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hdest : (D_J code 0).contains ret = true)
    (h : RD code ee g s0 ⟨21861⟩
      (tokensOwed1 :: tokensOwed0 :: liquidity :: burnPositionKeyNewFreePtrWord ::
        inside1 :: inside0 :: delta :: posBase :: ⟨19527⟩ :: inside1' :: inside0' ::
        z2 :: z3 :: fee1 :: fee0 :: posBase' :: tick :: delta' :: upper :: lower ::
        owner :: ret :: free :: R)
      (burnPositionUpdateMem5 σ ee (solcSlotWord σ ee posBase) posBase)
      (UInt256.ofNat 22) rdata (cA, σ) k C)
    (htokens0 : UInt256.land burnPositionUpdateSlot0Mask tokensOwed0 = ⟨0⟩)
    (htokens1 : UInt256.land burnPositionUpdateSlot0Mask tokensOwed1 = ⟨0⟩)
    (hdelta : UInt256.slt (UInt256.signextend ⟨15⟩ delta') ⟨0⟩ = ⟨0⟩)
    (hov : R.length + 35 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret (posBase' :: free :: R)
      (burnPositionUpdateMem5 σ ee (solcSlotWord σ ee posBase) posBase)
      (UInt256.ofNat 22) rdata (cA, σ) k' C' := by
  obtain ⟨_, _, hrd19527⟩ :=
    uniswapV3PoolBurnPositionUpdateTokensOwedZeroReturn
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (tokensOwed1 := tokensOwed1) (tokensOwed0 := tokensOwed0)
      (liquidity := liquidity) (inside1 := inside1) (inside0 := inside0)
      (delta := delta) (posBase := posBase) (retPos := ⟨19527⟩)
      (inside1' := inside1') (inside0' := inside0') (z2 := z2) (z3 := z3)
      (fee1 := fee1) (fee0 := fee0) (posBase' := posBase') (tick := tick)
      (delta' := delta') (upper := upper) (lower := lower) (owner := owner)
      (ret := ret) (free := free) (R := R) (rdata := rdata) (cA := cA)
      (σ := σ) hpatch (uniswapV3PoolJumpDestPatched19527 hpatch) h htokens0 htokens1
      hov
  exact uniswapV3PoolBurnModifyPositionAfterPositionUpdateZeroDeltaReturn
    (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
    (inside1 := inside1') (inside0 := inside0') (z2 := z2) (z3 := z3)
    (fee1 := fee1) (fee0 := fee0) (posBase := posBase') (tick := tick)
    (delta := delta') (upper := upper) (lower := lower) (owner := owner)
    (ret := ret) (free := free) (R := R)
    (mem := burnPositionUpdateMem5 σ ee (solcSlotWord σ ee posBase) posBase)
    (aw := UInt256.ofNat 22) (rdata := rdata) (acc := (cA, σ))
    hpatch hdest hrd19527 hdelta
    (by omega)

theorem uniswapV3PoolBurnModifyPositionReturnZeroAmountToCaller {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pos0 memPosBase posBase free r1 r2 r3 ret : UInt256}
    {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hdest : (D_J code 0).contains ret = true)
    (hzero : burnAmountCleanWord ee = ⟨0⟩)
    (h : RD code ee g s0 ⟨16428⟩
      (posBase :: free :: r1 :: r2 :: r3 :: ⟨128⟩ :: ret :: R)
      (burnPositionUpdateMem5 σ ee pos0 memPosBase) (UInt256.ofNat 22) rdata
      (cA, σ) k C)
    (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret (r1 :: r2 :: posBase :: R)
      (burnPositionUpdateMem5 σ ee pos0 memPosBase) (UInt256.ofNat 22) rdata
      (cA, σ) k' C' := by
  have hdec (pc : UInt256)
      (hlo : 16428 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 16841) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    exact uniswapV3PoolBurnModifyPositionReturnToCallerDecodeEqTemplate hpatch hlo hhi
  have hd16428 : decode code ⟨16428⟩ = some (.JUMPDEST, .none) := by
    rw [hdec ⟨16428⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd16429 : decode code ⟨16429⟩ = some (.SWAP4, .none) := by
    rw [hdec ⟨16429⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd16430 : decode code ⟨16430⟩ = some (.POP, .none) := by
    rw [hdec ⟨16430⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd16431 : decode code ⟨16431⟩ = some (.DUP5, .none) := by
    rw [hdec ⟨16431⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd16432 :
      decode code ⟨16432⟩ = some (.Push .PUSH1, some (⟨96⟩, 1)) := by
    rw [hdec ⟨16432⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd16434 : decode code ⟨16434⟩ = some (.ADD, .none) := by
    rw [hdec ⟨16434⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd16435 : decode code ⟨16435⟩ = some (.MLOAD, .none) := by
    rw [hdec ⟨16435⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd16436 :
      decode code ⟨16436⟩ = some (.Push .PUSH1, some (⟨15⟩, 1)) := by
    rw [hdec ⟨16436⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd16438 : decode code ⟨16438⟩ = some (.SIGNEXTEND, .none) := by
    rw [hdec ⟨16438⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd16439 :
      decode code ⟨16439⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    rw [hdec ⟨16439⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd16441 : decode code ⟨16441⟩ = some (.EQ, .none) := by
    rw [hdec ⟨16441⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd16442 :
      decode code ⟨16442⟩ = some (.Push .PUSH2, some (⟨16801⟩, 2)) := by
    rw [hdec ⟨16442⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd16445 : decode code ⟨16445⟩ = some (.JUMPI, .none) := by
    rw [hdec ⟨16445⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd16801 : decode code ⟨16801⟩ = some (.JUMPDEST, .none) := by
    rw [hdec ⟨16801⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd16802 : decode code ⟨16802⟩ = some (.POP, .none) := by
    rw [hdec ⟨16802⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd16803 : decode code ⟨16803⟩ = some (.SWAP2, .none) := by
    rw [hdec ⟨16803⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd16804 : decode code ⟨16804⟩ = some (.SWAP4, .none) := by
    rw [hdec ⟨16804⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd16805 : decode code ⟨16805⟩ = some (.SWAP1, .none) := by
    rw [hdec ⟨16805⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd16806 : decode code ⟨16806⟩ = some (.SWAP3, .none) := by
    rw [hdec ⟨16806⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd16807 : decode code ⟨16807⟩ = some (.POP, .none) := by
    rw [hdec ⟨16807⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd16808 : decode code ⟨16808⟩ = some (.JUMP, .none) := by
    rw [hdec ⟨16808⟩ (by native_decide) (by native_decide)]
    native_decide
  have rd16435 := evm_run h with [
    raw jumpdest hd16428 (by evm_ov),
    raw swap4 hd16429 (by simp only [List.length_cons] at hov ⊢; omega),
    raw pop hd16430 (by simp only [List.length_cons] at hov ⊢; omega),
    raw dup5 hd16431 (by simp only [List.length_cons] at hov ⊢; omega),
    raw push1 ⟨96⟩ hd16432 (by evm_ov),
    raw add hd16434 (by evm_ov)]
  have rd16436 := by
    simpa [show ((⟨128⟩ : UInt256) + ⟨96⟩) = (⟨224⟩ : UInt256) from by decide,
      show ((⟨96⟩ : UInt256) + ⟨128⟩) = (⟨224⟩ : UInt256) from by decide] using
      rd16435.mload 0
        (UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord ee)))
        (UInt256.ofNat 22) hd16435 mem_cost
        (burnPositionUpdateMem5_mload224 σ ee pos0 memPosBase)
        (by native_decide)
        (by simp only [List.length_cons] at hov ⊢; omega)
  have rd16438 := evm_run rd16436 with [
    raw push1 ⟨15⟩ hd16436 (by evm_ov)]
  have rd16439 := by
    simpa using burnRDSignextend rd16438 hd16438
      (by simp only [List.length_cons] at hov ⊢; omega)
  have rd16445 := evm_run rd16439 with [
    raw push1 ⟨0⟩ hd16439 (by evm_ov),
    raw eq hd16441 (by evm_ov),
    raw push2 ⟨16801⟩ hd16442 (by evm_ov)]
  have hcond :
      UInt256.eq ⟨0⟩
          (UInt256.signextend ⟨15⟩
            (UInt256.signextend ⟨15⟩
              (UInt256.sub ⟨0⟩ (burnAmountCleanWord ee)))) ≠
        ⟨0⟩ := by
    rw [hzero]
    native_decide
  have rd16801 := rd16445.jumpiT hd16445 hcond
    (uniswapV3PoolJumpDestPatched16801 hpatch)
    (by simp only [List.length_cons] at hov ⊢; omega)
  have rd16808 := evm_run rd16801 with [
    raw jumpdest hd16801 (by evm_ov),
    raw pop hd16802 (by simp only [List.length_cons] at hov ⊢; omega),
    raw swap2 hd16803 (by simp only [List.length_cons] at hov ⊢; omega),
    raw swap4 hd16804 (by omega),
    raw swap1 hd16805 (by simp only [List.length_cons]; omega),
    raw swap3 hd16806 (by simp only [List.length_cons]; omega),
    raw pop hd16807 (by simp only [List.length_cons]; omega)]
  exact ⟨_, _, rd16808.jump hd16808 hdest
    (by simp only [List.length_cons]; omega)⟩

theorem uniswapV3PoolBurnPositionUpdateTokensOwedZeroZeroDeltaReturnToCaller
    {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {tokensOwed1 tokensOwed0 liquidity inside1 inside0 delta posBase inside1' inside0'
      z2 z3 fee1 fee0 posBase' tick delta' upper lower owner free r1 r2 r3 callerRet :
      UInt256}
    {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hdest : (D_J code 0).contains callerRet = true)
    (hzero : burnAmountCleanWord ee = ⟨0⟩)
    (h : RD code ee g s0 ⟨21861⟩
      (tokensOwed1 :: tokensOwed0 :: liquidity :: burnPositionKeyNewFreePtrWord ::
        inside1 :: inside0 :: delta :: posBase :: ⟨19527⟩ :: inside1' :: inside0' ::
        z2 :: z3 :: fee1 :: fee0 :: posBase' :: tick :: delta' :: upper :: lower ::
        owner :: ⟨16428⟩ :: free :: r1 :: r2 :: r3 :: ⟨128⟩ :: callerRet :: R)
      (burnPositionUpdateMem5 σ ee (solcSlotWord σ ee posBase) posBase)
      (UInt256.ofNat 22) rdata (cA, σ) k C)
    (htokens0 : UInt256.land burnPositionUpdateSlot0Mask tokensOwed0 = ⟨0⟩)
    (htokens1 : UInt256.land burnPositionUpdateSlot0Mask tokensOwed1 = ⟨0⟩)
    (hdelta : UInt256.slt (UInt256.signextend ⟨15⟩ delta') ⟨0⟩ = ⟨0⟩)
    (hov : R.length + 40 ≤ 1024) :
    ∃ k' C', RD code ee g s0 callerRet (r1 :: r2 :: posBase' :: R)
      (burnPositionUpdateMem5 σ ee (solcSlotWord σ ee posBase) posBase)
      (UInt256.ofNat 22) rdata (cA, σ) k' C' := by
  obtain ⟨_, _, hrd16428⟩ :=
    uniswapV3PoolBurnPositionUpdateTokensOwedZeroZeroDeltaModifyPositionReturn
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (tokensOwed1 := tokensOwed1) (tokensOwed0 := tokensOwed0)
      (liquidity := liquidity) (inside1 := inside1) (inside0 := inside0)
      (delta := delta) (posBase := posBase) (inside1' := inside1')
      (inside0' := inside0') (z2 := z2) (z3 := z3) (fee1 := fee1) (fee0 := fee0)
      (posBase' := posBase') (tick := tick) (delta' := delta') (upper := upper)
      (lower := lower) (owner := owner) (ret := ⟨16428⟩) (free := free)
      (R := r1 :: r2 :: r3 :: ⟨128⟩ :: callerRet :: R) (rdata := rdata)
      (cA := cA) (σ := σ) hpatch (uniswapV3PoolJumpDestPatched16428 hpatch)
      h htokens0 htokens1 hdelta
      (by simp only [List.length_cons] at hov ⊢; omega)
  exact uniswapV3PoolBurnModifyPositionReturnZeroAmountToCaller
    (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
    (pos0 := solcSlotWord σ ee posBase) (memPosBase := posBase) (posBase := posBase')
    (free := free) (r1 := r1) (r2 := r2) (r3 := r3) (ret := callerRet) (R := R)
    (rdata := rdata) (cA := cA) (σ := σ) hpatch hdest hzero hrd16428
    (by omega)

end Benchmarks.UniswapV3Pool
