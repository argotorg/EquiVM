import Benchmarks.UniswapV3Pool.BurnPositionUpdateTokensOwedBridge

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.UniswapV3Pool

private theorem uniswapV3PoolBurnPostPositionUpdateDecodeEqTemplate
    {v : PoolImmutables} {code : ByteArray} {pc : UInt256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hlo : 9737 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 9808) :
    decode code pc = decode uniswapV3PoolBytecode pc := by
  exact uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch
    (by
      have hsize : 9808 ≤ uniswapV3PoolBytecode.size := by native_decide
      omega)
    (by
      intro p hp
      simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord,
        List.lookup] at hp
      rcases hp with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals omega)

private theorem uniswapV3PoolPatchPreservesJumpDest9833 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨9833⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolJumpDestPatched9833 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨9833⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest9833

private theorem uniswapV3PoolBurnEventDecodeEqTemplate
    {v : PoolImmutables} {code : ByteArray} {pc : UInt256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hlo : 9833 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 9984) :
    decode code pc = decode uniswapV3PoolBytecode pc := by
  exact uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch
    (by
      have hsize : 9984 ≤ uniswapV3PoolBytecode.size := by native_decide
      omega)
    (by
      intro p hp
      simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord,
        List.lookup] at hp
      rcases hp with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals omega)

abbrev burnPostPositionUpdateEventTopic : UInt256 :=
  ⟨5529215719100538921338848767238990743315658914736670698561097943341164173356⟩

noncomputable def burnPostPositionUpdateEventMem0
    (σ : AccountMap) (I : ExecutionEnv) (pos0 posBase amount : UInt256) :
    ByteArray :=
  writeWord (burnPositionUpdateMem5 σ I pos0 posBase)
    (burnPositionKeyNewFreePtrWord + (⟨160⟩ : UInt256)).toNat
    (UInt256.land amount burnPositionUpdateSlot0Mask)

noncomputable def burnPostPositionUpdateEventMem1
    (σ : AccountMap) (I : ExecutionEnv) (pos0 posBase amount : UInt256) :
    ByteArray :=
  writeWord (burnPostPositionUpdateEventMem0 σ I pos0 posBase amount)
    (burnPositionKeyNewFreePtrWord + (⟨160⟩ : UInt256) + (⟨32⟩ : UInt256)).toNat
    ⟨0⟩

noncomputable def burnPostPositionUpdateEventMem
    (σ : AccountMap) (I : ExecutionEnv) (pos0 posBase amount : UInt256) :
    ByteArray :=
  writeWord (burnPostPositionUpdateEventMem1 σ I pos0 posBase amount)
    (burnPositionKeyNewFreePtrWord + (⟨160⟩ : UInt256) + (⟨64⟩ : UInt256)).toNat
    ⟨0⟩

theorem burnPostPositionUpdateEventMem0_size
    (σ : AccountMap) (I : ExecutionEnv) (pos0 posBase amount : UInt256) :
    (burnPostPositionUpdateEventMem0 σ I pos0 posBase amount).size = 730 := by
  unfold burnPostPositionUpdateEventMem0
  rw [writeWord_size _ _ _ (by
    rw [burnPositionUpdateMem5_size σ I pos0 posBase]
    native_decide)]
  rw [burnPositionUpdateMem5_size σ I pos0 posBase]
  native_decide

theorem burnPostPositionUpdateEventMem1_size
    (σ : AccountMap) (I : ExecutionEnv) (pos0 posBase amount : UInt256) :
    (burnPostPositionUpdateEventMem1 σ I pos0 posBase amount).size = 762 := by
  unfold burnPostPositionUpdateEventMem1
  rw [writeWord_size _ _ _ (by
    rw [burnPostPositionUpdateEventMem0_size σ I pos0 posBase amount]
    native_decide)]
  rw [burnPostPositionUpdateEventMem0_size σ I pos0 posBase amount]
  native_decide

theorem burnPostPositionUpdateEventMem_size
    (σ : AccountMap) (I : ExecutionEnv) (pos0 posBase amount : UInt256) :
    (burnPostPositionUpdateEventMem σ I pos0 posBase amount).size = 794 := by
  unfold burnPostPositionUpdateEventMem
  rw [writeWord_size _ _ _ (by
    rw [burnPostPositionUpdateEventMem1_size σ I pos0 posBase amount]
    native_decide)]
  rw [burnPostPositionUpdateEventMem1_size σ I pos0 posBase amount]
  native_decide

theorem burnPostPositionUpdateEventMem_read64
    (σ : AccountMap) (I : ExecutionEnv) (pos0 posBase amount : UInt256) :
    (burnPostPositionUpdateEventMem σ I pos0 posBase amount).readWithPadding 64 32 =
      UInt256.toByteArray (burnPositionKeyNewFreePtrWord + (⟨160⟩ : UInt256)) := by
  unfold burnPostPositionUpdateEventMem
  rw [writeWord_read_preserved
    (burnPostPositionUpdateEventMem1 σ I pos0 posBase amount)
    (burnPositionKeyNewFreePtrWord + (⟨160⟩ : UInt256) + (⟨64⟩ : UInt256)).toNat
    64 (⟨0⟩ : UInt256)
    (by
      rw [burnPostPositionUpdateEventMem1_size σ I pos0 posBase amount]
      native_decide)
    (by
      rw [burnPostPositionUpdateEventMem1_size σ I pos0 posBase amount]
      native_decide)]
  unfold burnPostPositionUpdateEventMem1
  rw [writeWord_read_preserved
    (burnPostPositionUpdateEventMem0 σ I pos0 posBase amount)
    (burnPositionKeyNewFreePtrWord + (⟨160⟩ : UInt256) + (⟨32⟩ : UInt256)).toNat
    64 (⟨0⟩ : UInt256)
    (by
      rw [burnPostPositionUpdateEventMem0_size σ I pos0 posBase amount]
      native_decide)
    (by
      rw [burnPostPositionUpdateEventMem0_size σ I pos0 posBase amount]
      native_decide)]
  unfold burnPostPositionUpdateEventMem0
  rw [writeWord_read_preserved
    (burnPositionUpdateMem5 σ I pos0 posBase)
    (burnPositionKeyNewFreePtrWord + (⟨160⟩ : UInt256)).toNat
    64 (UInt256.land amount burnPositionUpdateSlot0Mask)
    (by
      rw [burnPositionUpdateMem5_size σ I pos0 posBase]
      native_decide)
    (by
      rw [burnPositionUpdateMem5_size σ I pos0 posBase]
      native_decide)]
  exact burnPositionUpdateMem5_read64 σ I pos0 posBase

theorem burnPostPositionUpdateEventMem_mload64
    (σ : AccountMap) (I : ExecutionEnv) (pos0 posBase amount : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥
        (burnPostPositionUpdateEventMem σ I pos0 posBase amount).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 25 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((burnPostPositionUpdateEventMem σ I pos0 posBase amount).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
      burnPositionKeyNewFreePtrWord + (⟨160⟩ : UInt256) := by
  exact mloadWordValue_of_readWithPadding
    (by rw [burnPostPositionUpdateEventMem_size σ I pos0 posBase amount]; native_decide)
    (by native_decide)
      (by
        simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
          using burnPostPositionUpdateEventMem_read64 σ I pos0 posBase amount)

abbrev burnPostPositionUpdateUnlockedClearMask : UInt256 :=
  UInt256.lnot (UInt256.shiftLeft ⟨255⟩ ⟨240⟩)

abbrev burnPostPositionUpdateUnlockedSlotWord (σ : AccountMap) (I : ExecutionEnv) :
    UInt256 :=
  UInt256.lor
    (UInt256.shiftLeft ⟨1⟩ ⟨240⟩)
    (UInt256.land burnPostPositionUpdateUnlockedClearMask (codeOwnerStorageWord I σ ⟨0⟩))

noncomputable def burnPostPositionUpdateReturnMem0
    (σ : AccountMap) (I : ExecutionEnv) (pos0 posBase amount : UInt256) :
    ByteArray :=
  writeWord (burnPostPositionUpdateEventMem σ I pos0 posBase amount)
    (burnPositionKeyNewFreePtrWord + (⟨160⟩ : UInt256)).toNat ⟨0⟩

noncomputable def burnPostPositionUpdateReturnMem
    (σ : AccountMap) (I : ExecutionEnv) (pos0 posBase amount : UInt256) :
    ByteArray :=
  writeWord (burnPostPositionUpdateReturnMem0 σ I pos0 posBase amount)
    (burnPositionKeyNewFreePtrWord + (⟨160⟩ : UInt256) + (⟨32⟩ : UInt256)).toNat ⟨0⟩

theorem burnPostPositionUpdateReturnMem0_size
    (σ : AccountMap) (I : ExecutionEnv) (pos0 posBase amount : UInt256) :
    (burnPostPositionUpdateReturnMem0 σ I pos0 posBase amount).size = 794 := by
  unfold burnPostPositionUpdateReturnMem0
  rw [writeWord_size _ _ _ (by
    rw [burnPostPositionUpdateEventMem_size σ I pos0 posBase amount]
    native_decide)]
  rw [burnPostPositionUpdateEventMem_size σ I pos0 posBase amount]
  native_decide

theorem burnPostPositionUpdateReturnMem_size
    (σ : AccountMap) (I : ExecutionEnv) (pos0 posBase amount : UInt256) :
    (burnPostPositionUpdateReturnMem σ I pos0 posBase amount).size = 794 := by
  unfold burnPostPositionUpdateReturnMem
  rw [writeWord_size _ _ _ (by
    rw [burnPostPositionUpdateReturnMem0_size σ I pos0 posBase amount]
    native_decide)]
  rw [burnPostPositionUpdateReturnMem0_size σ I pos0 posBase amount]
  native_decide

theorem burnPostPositionUpdateReturnMem_read64
    (σ : AccountMap) (I : ExecutionEnv) (pos0 posBase amount : UInt256) :
    (burnPostPositionUpdateReturnMem σ I pos0 posBase amount).readWithPadding 64 32 =
      UInt256.toByteArray (burnPositionKeyNewFreePtrWord + (⟨160⟩ : UInt256)) := by
  unfold burnPostPositionUpdateReturnMem
  rw [writeWord_read_preserved
    (burnPostPositionUpdateReturnMem0 σ I pos0 posBase amount)
    (burnPositionKeyNewFreePtrWord + (⟨160⟩ : UInt256) + (⟨32⟩ : UInt256)).toNat
    64 (⟨0⟩ : UInt256)
    (by rw [burnPostPositionUpdateReturnMem0_size σ I pos0 posBase amount]; native_decide)
    (by rw [burnPostPositionUpdateReturnMem0_size σ I pos0 posBase amount]; native_decide)]
  unfold burnPostPositionUpdateReturnMem0
  rw [writeWord_read_preserved
    (burnPostPositionUpdateEventMem σ I pos0 posBase amount)
    (burnPositionKeyNewFreePtrWord + (⟨160⟩ : UInt256)).toNat
    64 (⟨0⟩ : UInt256)
    (by rw [burnPostPositionUpdateEventMem_size σ I pos0 posBase amount]; native_decide)
    (by rw [burnPostPositionUpdateEventMem_size σ I pos0 posBase amount]; native_decide)]
  exact burnPostPositionUpdateEventMem_read64 σ I pos0 posBase amount

theorem burnPostPositionUpdateReturnMem_mload64
    (σ : AccountMap) (I : ExecutionEnv) (pos0 posBase amount : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥
        (burnPostPositionUpdateReturnMem σ I pos0 posBase amount).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 25 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((burnPostPositionUpdateReturnMem σ I pos0 posBase amount).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
      burnPositionKeyNewFreePtrWord + (⟨160⟩ : UInt256) := by
  exact mloadWordValue_of_readWithPadding
    (mem := burnPostPositionUpdateReturnMem σ I pos0 posBase amount)
    (aw := UInt256.ofNat 25) (off := ⟨64⟩)
    (v := burnPositionKeyNewFreePtrWord + (⟨160⟩ : UInt256))
    (by rw [burnPostPositionUpdateReturnMem_size σ I pos0 posBase amount]; native_decide)
    (by native_decide)
    (by
      simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        using burnPostPositionUpdateReturnMem_read64 σ I pos0 posBase amount)

theorem burnPostPositionUpdateReturnMem_readFree
    (σ : AccountMap) (I : ExecutionEnv) (pos0 posBase amount : UInt256) :
    (burnPostPositionUpdateReturnMem σ I pos0 posBase amount).readWithPadding
        (burnPositionKeyNewFreePtrWord + (⟨160⟩ : UInt256)).toNat 64 =
      UInt256.toByteArray (⟨0⟩ : UInt256) ++ UInt256.toByteArray (⟨0⟩ : UInt256) := by
  have hsize := burnPostPositionUpdateReturnMem_size σ I pos0 posBase amount
  have hleft :
      (burnPostPositionUpdateReturnMem σ I pos0 posBase amount).readWithPadding
          (burnPositionKeyNewFreePtrWord + (⟨160⟩ : UInt256)).toNat 32 =
        UInt256.toByteArray (⟨0⟩ : UInt256) := by
    unfold burnPostPositionUpdateReturnMem
    rw [writeWord_read_preserved
      (burnPostPositionUpdateReturnMem0 σ I pos0 posBase amount)
      (burnPositionKeyNewFreePtrWord + (⟨160⟩ : UInt256) + (⟨32⟩ : UInt256)).toNat
      (burnPositionKeyNewFreePtrWord + (⟨160⟩ : UInt256)).toNat
      (⟨0⟩ : UInt256)
      (by rw [burnPostPositionUpdateReturnMem0_size σ I pos0 posBase amount]; native_decide)
      (by rw [burnPostPositionUpdateReturnMem0_size σ I pos0 posBase amount]; native_decide)]
    unfold burnPostPositionUpdateReturnMem0
    exact writeWord_read_back
      (burnPostPositionUpdateEventMem σ I pos0 posBase amount)
      (burnPositionKeyNewFreePtrWord + (⟨160⟩ : UInt256)).toNat
      (⟨0⟩ : UInt256)
      (by rw [burnPostPositionUpdateEventMem_size σ I pos0 posBase amount]; native_decide)
  have hright :
      (burnPostPositionUpdateReturnMem σ I pos0 posBase amount).readWithPadding
          ((burnPositionKeyNewFreePtrWord + (⟨160⟩ : UInt256)).toNat + 32) 32 =
        UInt256.toByteArray (⟨0⟩ : UInt256) := by
    unfold burnPostPositionUpdateReturnMem
    simpa [show (burnPositionKeyNewFreePtrWord + (⟨160⟩ : UInt256) +
        (⟨32⟩ : UInt256)).toNat =
          (burnPositionKeyNewFreePtrWord + (⟨160⟩ : UInt256)).toNat + 32 by
        native_decide] using
      writeWord_read_back
        (burnPostPositionUpdateReturnMem0 σ I pos0 posBase amount)
        (burnPositionKeyNewFreePtrWord + (⟨160⟩ : UInt256) + (⟨32⟩ : UInt256)).toNat
        (⟨0⟩ : UInt256)
        (by rw [burnPostPositionUpdateReturnMem0_size σ I pos0 posBase amount]; native_decide)
  rw [byteArray_readWithPadding_split
    (burnPostPositionUpdateReturnMem σ I pos0 posBase amount)
    (burnPositionKeyNewFreePtrWord + (⟨160⟩ : UInt256)).toNat 32 32
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [hsize]; native_decide)]
  rw [hleft, hright]

theorem uniswapV3PoolBurnPostPositionUpdateZeroAmountsToEvent {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {posBase amount upper lower ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨9737⟩
      (⟨0⟩ :: ⟨0⟩ :: posBase :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        amount :: upper :: lower :: ret :: R)
      mem aw rdata acc k C)
    (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨9833⟩
      (⟨0⟩ :: ⟨0⟩ :: posBase :: ⟨0⟩ :: ⟨0⟩ :: amount :: upper :: lower :: ret :: R)
      mem aw rdata acc k' C' := by
  have hdec (pc : UInt256)
      (hlo : 9737 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 9808) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    exact uniswapV3PoolBurnPostPositionUpdateDecodeEqTemplate hpatch hlo hhi
  have hd9737 : decode code ⟨9737⟩ = some (.JUMPDEST, .none) := by
    rw [hdec ⟨9737⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9738 : decode code ⟨9738⟩ = some (.SWAP3, .none) := by
    rw [hdec ⟨9738⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9739 : decode code ⟨9739⟩ = some (.POP, .none) := by
    rw [hdec ⟨9739⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9740 : decode code ⟨9740⟩ = some (.SWAP3, .none) := by
    rw [hdec ⟨9740⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9741 : decode code ⟨9741⟩ = some (.POP, .none) := by
    rw [hdec ⟨9741⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9742 : decode code ⟨9742⟩ = some (.SWAP3, .none) := by
    rw [hdec ⟨9742⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9743 : decode code ⟨9743⟩ = some (.POP, .none) := by
    rw [hdec ⟨9743⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9744 : decode code ⟨9744⟩ = some (.DUP2, .none) := by
    rw [hdec ⟨9744⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9745 : decode code ⟨9745⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    rw [hdec ⟨9745⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9747 : decode code ⟨9747⟩ = some (.SUB, .none) := by
    rw [hdec ⟨9747⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9748 : decode code ⟨9748⟩ = some (.SWAP5, .none) := by
    rw [hdec ⟨9748⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9749 : decode code ⟨9749⟩ = some (.POP, .none) := by
    rw [hdec ⟨9749⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9750 : decode code ⟨9750⟩ = some (.DUP1, .none) := by
    rw [hdec ⟨9750⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9751 : decode code ⟨9751⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    rw [hdec ⟨9751⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9753 : decode code ⟨9753⟩ = some (.SUB, .none) := by
    rw [hdec ⟨9753⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9754 : decode code ⟨9754⟩ = some (.SWAP4, .none) := by
    rw [hdec ⟨9754⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9755 : decode code ⟨9755⟩ = some (.POP, .none) := by
    rw [hdec ⟨9755⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9756 : decode code ⟨9756⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    rw [hdec ⟨9756⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9758 : decode code ⟨9758⟩ = some (.DUP6, .none) := by
    rw [hdec ⟨9758⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9759 : decode code ⟨9759⟩ = some (.GT, .none) := by
    rw [hdec ⟨9759⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9760 : decode code ⟨9760⟩ = some (.DUP1, .none) := by
    rw [hdec ⟨9760⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9761 : decode code ⟨9761⟩ = some (.Push .PUSH2, some (⟨9770⟩, 2)) := by
    rw [hdec ⟨9761⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9764 : decode code ⟨9764⟩ = some (.JUMPI, .none) := by
    rw [hdec ⟨9764⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9765 : decode code ⟨9765⟩ = some (.POP, .none) := by
    rw [hdec ⟨9765⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9766 : decode code ⟨9766⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    rw [hdec ⟨9766⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9768 : decode code ⟨9768⟩ = some (.DUP5, .none) := by
    rw [hdec ⟨9768⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9769 : decode code ⟨9769⟩ = some (.GT, .none) := by
    rw [hdec ⟨9769⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9770 : decode code ⟨9770⟩ = some (.JUMPDEST, .none) := by
    rw [hdec ⟨9770⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9771 : decode code ⟨9771⟩ = some (.ISZERO, .none) := by
    rw [hdec ⟨9771⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9772 : decode code ⟨9772⟩ = some (.Push .PUSH2, some (⟨9833⟩, 2)) := by
    rw [hdec ⟨9772⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9775 : decode code ⟨9775⟩ = some (.JUMPI, .none) := by
    rw [hdec ⟨9775⟩ (by native_decide) (by native_decide)]
    native_decide
  have rd9764 := evm_run h with [
    raw jumpdest hd9737 (by evm_ov),
    raw swap3 hd9738 (by simp only [List.length_cons] at hov ⊢; omega),
    raw pop hd9739 (by simp only [List.length_cons] at hov ⊢; omega),
    raw swap3 hd9740 (by simp only [List.length_cons] at hov ⊢; omega),
    raw pop hd9741 (by simp only [List.length_cons] at hov ⊢; omega),
    raw swap3 hd9742 (by simp only [List.length_cons] at hov ⊢; omega),
    raw pop hd9743 (by simp only [List.length_cons] at hov ⊢; omega),
    raw dup2 hd9744 (by simp only [List.length_cons] at hov ⊢; omega),
    raw push1 ⟨0⟩ hd9745 (by evm_ov),
    raw sub hd9747 (by evm_ov),
    raw swap5 hd9748 (by simp only [List.length_cons] at hov ⊢; omega),
    raw pop hd9749 (by simp only [List.length_cons] at hov ⊢; omega),
    raw dup1 hd9750 (by simp only [List.length_cons] at hov ⊢; omega),
    raw push1 ⟨0⟩ hd9751 (by evm_ov),
    raw sub hd9753 (by evm_ov),
    raw swap4 hd9754 (by simp only [List.length_cons] at hov ⊢; omega),
    raw pop hd9755 (by simp only [List.length_cons] at hov ⊢; omega),
    raw push1 ⟨0⟩ hd9756 (by evm_ov),
    raw dup6 hd9758 (by simp only [List.length_cons] at hov ⊢; omega),
    raw gt hd9759 (by evm_ov),
    raw dup1 hd9760 (by simp only [List.length_cons] at hov ⊢; omega),
    raw push2 ⟨9770⟩ hd9761 (by evm_ov)]
  have hcond0 :
      UInt256.gt (UInt256.sub ⟨0⟩ ⟨0⟩) ⟨0⟩ = ⟨0⟩ := by
    native_decide
  have rd9765 := rd9764.jumpiNT hd9764 hcond0
    (by simp only [List.length_cons] at hov ⊢; omega)
  have rd9775 := evm_run rd9765 with [
    raw pop hd9765 (by simp only [List.length_cons] at hov ⊢; omega),
    raw push1 ⟨0⟩ hd9766 (by evm_ov),
    raw dup5 hd9768 (by simp only [List.length_cons] at hov ⊢; omega),
    raw gt hd9769 (by evm_ov),
    raw jumpdest hd9770 (by evm_ov),
    raw iszero hd9771 (by evm_ov),
    raw push2 ⟨9833⟩ hd9772 (by evm_ov)]
  have hcond1 :
      UInt256.isZero (UInt256.gt (UInt256.sub ⟨0⟩ ⟨0⟩) ⟨0⟩) ≠ ⟨0⟩ := by
    native_decide
  exact ⟨_, _, rd9775.jumpiT hd9775 hcond1 (uniswapV3PoolJumpDestPatched9833 hpatch)
    (by simp only [List.length_cons] at hov ⊢; omega)⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolBurnPostPositionUpdateEventLog {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {σ : AccountMap} {pos0 posBase amount upper lower ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨9833⟩
      (⟨0⟩ :: ⟨0⟩ :: posBase :: ⟨0⟩ :: ⟨0⟩ :: amount :: upper :: lower ::
        ret :: R)
      (burnPositionUpdateMem5 σ ee pos0 posBase) (UInt256.ofNat 22) rdata acc k C)
    (hperm : ee.perm = true)
    (hov : R.length + 24 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨9921⟩
      (⟨0⟩ :: ⟨0⟩ :: posBase :: ⟨0⟩ :: ⟨0⟩ :: amount :: upper :: lower ::
        ret :: R)
      (burnPostPositionUpdateEventMem σ ee pos0 posBase amount) (UInt256.ofNat 25)
      rdata acc k' C' := by
  have hdec (pc : UInt256)
      (hlo : 9833 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 9984) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    exact uniswapV3PoolBurnEventDecodeEqTemplate hpatch hlo hhi
  have hd9833 : decode code ⟨9833⟩ = some (.JUMPDEST, .none) := by
    rw [hdec ⟨9833⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9834 : decode code ⟨9834⟩ = some (.Push .PUSH1, some (⟨64⟩, 1)) := by
    rw [hdec ⟨9834⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9836 : decode code ⟨9836⟩ = some (.DUP1, .none) := by
    rw [hdec ⟨9836⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9837 : decode code ⟨9837⟩ = some (.MLOAD, .none) := by
    rw [hdec ⟨9837⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9838 : decode code ⟨9838⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdec ⟨9838⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9840 : decode code ⟨9840⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdec ⟨9840⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9842 : decode code ⟨9842⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)) := by
    rw [hdec ⟨9842⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9844 : decode code ⟨9844⟩ = some (.SHL, .none) := by
    rw [hdec ⟨9844⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9845 : decode code ⟨9845⟩ = some (.SUB, .none) := by
    rw [hdec ⟨9845⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9846 : decode code ⟨9846⟩ = some (.DUP9, .none) := by
    rw [hdec ⟨9846⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9847 : decode code ⟨9847⟩ = some (.AND, .none) := by
    rw [hdec ⟨9847⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9848 : decode code ⟨9848⟩ = some (.DUP2, .none) := by
    rw [hdec ⟨9848⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9849 : decode code ⟨9849⟩ = some (.MSTORE, .none) := by
    rw [hdec ⟨9849⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9850 : decode code ⟨9850⟩ = some (.Push .PUSH1, some (⟨32⟩, 1)) := by
    rw [hdec ⟨9850⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9852 : decode code ⟨9852⟩ = some (.DUP2, .none) := by
    rw [hdec ⟨9852⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9853 : decode code ⟨9853⟩ = some (.ADD, .none) := by
    rw [hdec ⟨9853⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9854 : decode code ⟨9854⟩ = some (.DUP8, .none) := by
    rw [hdec ⟨9854⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9855 : decode code ⟨9855⟩ = some (.SWAP1, .none) := by
    rw [hdec ⟨9855⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9856 : decode code ⟨9856⟩ = some (.MSTORE, .none) := by
    rw [hdec ⟨9856⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9857 : decode code ⟨9857⟩ = some (.DUP1, .none) := by
    rw [hdec ⟨9857⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9858 : decode code ⟨9858⟩ = some (.DUP3, .none) := by
    rw [hdec ⟨9858⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9859 : decode code ⟨9859⟩ = some (.ADD, .none) := by
    rw [hdec ⟨9859⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9860 : decode code ⟨9860⟩ = some (.DUP7, .none) := by
    rw [hdec ⟨9860⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9861 : decode code ⟨9861⟩ = some (.SWAP1, .none) := by
    rw [hdec ⟨9861⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9862 : decode code ⟨9862⟩ = some (.MSTORE, .none) := by
    rw [hdec ⟨9862⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9863 : decode code ⟨9863⟩ = some (.SWAP1, .none) := by
    rw [hdec ⟨9863⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9864 : decode code ⟨9864⟩ = some (.MLOAD, .none) := by
    rw [hdec ⟨9864⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9865 : decode code ⟨9865⟩ = some (.Push .PUSH1, some (⟨2⟩, 1)) := by
    rw [hdec ⟨9865⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9867 : decode code ⟨9867⟩ = some (.DUP10, .none) := by
    rw [hdec ⟨9867⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9868 : decode code ⟨9868⟩ = some (.DUP2, .none) := by
    rw [hdec ⟨9868⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9869 : decode code ⟨9869⟩ = some (.SIGNEXTEND, .none) := by
    rw [hdec ⟨9869⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9870 : decode code ⟨9870⟩ = some (.SWAP3, .none) := by
    rw [hdec ⟨9870⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9871 : decode code ⟨9871⟩ = some (.SWAP1, .none) := by
    rw [hdec ⟨9871⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9872 : decode code ⟨9872⟩ = some (.DUP12, .none) := by
    rw [hdec ⟨9872⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9873 : decode code ⟨9873⟩ = some (.SWAP1, .none) := by
    rw [hdec ⟨9873⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9874 : decode code ⟨9874⟩ = some (.SIGNEXTEND, .none) := by
    rw [hdec ⟨9874⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9875 : decode code ⟨9875⟩ = some (.SWAP2, .none) := by
    rw [hdec ⟨9875⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9876 : decode code ⟨9876⟩ = some (.CALLER, .none) := by
    rw [hdec ⟨9876⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9877 : decode code ⟨9877⟩ = some (.SWAP2, .none) := by
    rw [hdec ⟨9877⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9878 :
      decode code ⟨9878⟩ =
        some (.Push .PUSH32, some (burnPostPositionUpdateEventTopic, 32)) := by
    rw [hdec ⟨9878⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9911 : decode code ⟨9911⟩ = some (.SWAP2, .none) := by
    rw [hdec ⟨9911⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9912 : decode code ⟨9912⟩ = some (.SWAP1, .none) := by
    rw [hdec ⟨9912⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9913 : decode code ⟨9913⟩ = some (.DUP2, .none) := by
    rw [hdec ⟨9913⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9914 : decode code ⟨9914⟩ = some (.SWAP1, .none) := by
    rw [hdec ⟨9914⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9915 : decode code ⟨9915⟩ = some (.SUB, .none) := by
    rw [hdec ⟨9915⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9916 : decode code ⟨9916⟩ = some (.Push .PUSH1, some (⟨96⟩, 1)) := by
    rw [hdec ⟨9916⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9918 : decode code ⟨9918⟩ = some (.ADD, .none) := by
    rw [hdec ⟨9918⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9919 : decode code ⟨9919⟩ = some (.SWAP1, .none) := by
    rw [hdec ⟨9919⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9920 : decode code ⟨9920⟩ = some (.LOG4, .none) := by
    rw [hdec ⟨9920⟩ (by native_decide) (by native_decide)]
    native_decide
  have rd9837 := evm_run h with [
    raw jumpdest hd9833 (by evm_ov),
    raw push1 ⟨64⟩ hd9834 (by evm_ov),
    raw dup1 hd9836 (by evm_ov)]
  have rd9838 := evm_run rd9837 with [
    raw mload 0 (burnPositionKeyNewFreePtrWord + (⟨160⟩ : UInt256))
      (UInt256.ofNat 22) hd9837 mem_cost
      (burnPositionUpdateMem5_mload64 σ ee pos0 posBase)
      (by native_decide) (by evm_ov)]
  have rd9849 := evm_run rd9838 with [
    raw push1 ⟨1⟩ hd9838 (by evm_ov),
    raw push1 ⟨1⟩ hd9840 (by evm_ov),
    raw push1 ⟨128⟩ hd9842 (by evm_ov),
    raw shl hd9844 (by evm_ov),
    raw sub hd9845 (by evm_ov),
    raw dup9 hd9846 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw and hd9847 (by evm_ov),
    raw dup2 hd9848 (by evm_ov),
    raw mstore 4 (burnPostPositionUpdateEventMem0 σ ee pos0 posBase amount)
      (UInt256.ofNat 23) hd9849 mem_cost rfl (by native_decide) (by
        have h := hov
        simp only [List.length_cons] at h ⊢
        omega)]
  have rd9856 := evm_run rd9849 with [
    raw push1 ⟨32⟩ hd9850 (by evm_ov),
    raw dup2 hd9852 (by evm_ov),
    raw add hd9853 (by evm_ov),
    raw dup8 hd9854 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw swap1 hd9855 (by evm_ov),
    raw mstore 3 (burnPostPositionUpdateEventMem1 σ ee pos0 posBase amount)
      (UInt256.ofNat 24) hd9856 mem_cost rfl (by native_decide) (by
        have h := hov
        simp only [List.length_cons] at h ⊢
        omega)]
  have rd9862 := evm_run rd9856 with [
    raw dup1 hd9857 (by evm_ov),
    raw dup3 hd9858 (by evm_ov),
    raw add hd9859 (by evm_ov),
    raw dup7 hd9860 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw swap1 hd9861 (by evm_ov),
    raw mstore 3 (burnPostPositionUpdateEventMem σ ee pos0 posBase amount)
      (UInt256.ofNat 25) hd9862 mem_cost rfl (by native_decide) (by
        have h := hov
        simp only [List.length_cons] at h ⊢
        omega)]
  have rd9864 := evm_run rd9862 with [
    raw swap1 hd9863 (by evm_ov)]
  have rd9865 := evm_run rd9864 with [
    raw mload 0 (burnPositionKeyNewFreePtrWord + (⟨160⟩ : UInt256))
      (UInt256.ofNat 25) hd9864 mem_cost
      (burnPostPositionUpdateEventMem_mload64 σ ee pos0 posBase amount)
      (by native_decide) (by evm_ov)]
  have rd9869 := evm_run rd9865 with [
    raw push1 ⟨2⟩ hd9865 (by evm_ov),
    raw dup10 hd9867 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw dup2 hd9868 (by evm_ov)]
  have rd9870 := RD.signextend rd9869 hd9869 (by
    have h := hov
    simp only [List.length_cons] at h ⊢
    omega)
  have rd9872 := evm_run rd9870 with [
    raw swap3 hd9870 (by evm_ov),
    raw swap1 hd9871 (by evm_ov)]
  have rd9873 := RD.dup12 rd9872 hd9872 (by
    have h := hov
    simp only [List.length_cons] at h ⊢
    omega)
  have rd9874 := evm_run rd9873 with [
    raw swap1 hd9873 (by evm_ov)]
  have rd9875 := RD.signextend rd9874 hd9874 (by
    have h := hov
    simp only [List.length_cons] at h ⊢
    omega)
  have rd9919 := evm_run rd9875 with [
    raw swap2 hd9875 (by evm_ov),
    raw caller hd9876 (by evm_ov),
    raw swap2 hd9877 (by evm_ov),
    raw pushConst burnPostPositionUpdateEventTopic
      (show Operation.POp.PUSH32 ≠ Operation.POp.PUSH0 by native_decide)
      hd9878 (by evm_ov),
    raw swap2 hd9911 (by evm_ov),
    raw swap1 hd9912 (by evm_ov),
    raw dup2 hd9913 (by evm_ov),
    raw swap1 hd9914 (by evm_ov),
    raw sub hd9915 (by evm_ov),
    raw push1 ⟨96⟩ hd9916 (by evm_ov),
    raw add hd9918 (by evm_ov)]
  have rd9921 := evm_run rd9919 with [
    raw swap1 hd9919 (by evm_ov),
    raw log4 0 (UInt256.ofNat 25) hd9920 hperm mem_cost
      (by native_decide) (by
        have h := hov
        simp only [List.length_cons] at h ⊢
        omega)]
  exact ⟨_, _, by simpa [burnPositionUpdateSlot0Mask] using rd9921⟩

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolBurnPostPositionUpdateUnlockReturn {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {σmem σacc : AccountMap} {pos0 posBase amount upper lower : UInt256}
    {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨9921⟩
      (⟨0⟩ :: ⟨0⟩ :: posBase :: ⟨0⟩ :: ⟨0⟩ :: amount :: upper :: lower ::
        ⟨621⟩ :: R)
      (burnPostPositionUpdateEventMem σmem ee pos0 posBase amount) (UInt256.ofNat 25)
      rdata (cA, σacc) k C)
    (hperm : ee.perm = true)
    (hov : R.length + 12 ≤ 1024) :
    RDret code g s0
      (cA, sstoreAccountMap ee.codeOwner σacc ⟨0⟩
        (burnPostPositionUpdateUnlockedSlotWord σacc ee))
      (UInt256.toByteArray (⟨0⟩ : UInt256) ++ UInt256.toByteArray (⟨0⟩ : UInt256)) := by
  have hdecEvent (pc : UInt256)
      (hlo : 9833 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 9984) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    exact uniswapV3PoolBurnEventDecodeEqTemplate hpatch hlo hhi
  have hd9921 : decode code ⟨9921⟩ = some (.POP, .none) := by
    rw [hdecEvent ⟨9921⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9922 : decode code ⟨9922⟩ = some (.POP, .none) := by
    rw [hdecEvent ⟨9922⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9923 : decode code ⟨9923⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    rw [hdecEvent ⟨9923⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9925 : decode code ⟨9925⟩ = some (.DUP1, .none) := by
    rw [hdecEvent ⟨9925⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9926 : decode code ⟨9926⟩ = some (.SLOAD, .none) := by
    rw [hdecEvent ⟨9926⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9927 : decode code ⟨9927⟩ = some (.Push .PUSH1, some (⟨255⟩, 1)) := by
    rw [hdecEvent ⟨9927⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9929 : decode code ⟨9929⟩ = some (.Push .PUSH1, some (⟨240⟩, 1)) := by
    rw [hdecEvent ⟨9929⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9931 : decode code ⟨9931⟩ = some (.SHL, .none) := by
    rw [hdecEvent ⟨9931⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9932 : decode code ⟨9932⟩ = some (.NOT, .none) := by
    rw [hdecEvent ⟨9932⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9933 : decode code ⟨9933⟩ = some (.AND, .none) := by
    rw [hdecEvent ⟨9933⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9934 : decode code ⟨9934⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdecEvent ⟨9934⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9936 : decode code ⟨9936⟩ = some (.Push .PUSH1, some (⟨240⟩, 1)) := by
    rw [hdecEvent ⟨9936⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9938 : decode code ⟨9938⟩ = some (.SHL, .none) := by
    rw [hdecEvent ⟨9938⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9939 : decode code ⟨9939⟩ = some (.OR, .none) := by
    rw [hdecEvent ⟨9939⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9940 : decode code ⟨9940⟩ = some (.SWAP1, .none) := by
    rw [hdecEvent ⟨9940⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9941 : decode code ⟨9941⟩ = some (.SSTORE, .none) := by
    rw [hdecEvent ⟨9941⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9942 : decode code ⟨9942⟩ = some (.POP, .none) := by
    rw [hdecEvent ⟨9942⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9943 : decode code ⟨9943⟩ = some (.SWAP1, .none) := by
    rw [hdecEvent ⟨9943⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9944 : decode code ⟨9944⟩ = some (.SWAP5, .none) := by
    rw [hdecEvent ⟨9944⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9945 : decode code ⟨9945⟩ = some (.SWAP1, .none) := by
    rw [hdecEvent ⟨9945⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9946 : decode code ⟨9946⟩ = some (.SWAP4, .none) := by
    rw [hdecEvent ⟨9946⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9947 : decode code ⟨9947⟩ = some (.POP, .none) := by
    rw [hdecEvent ⟨9947⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9948 : decode code ⟨9948⟩ = some (.SWAP2, .none) := by
    rw [hdecEvent ⟨9948⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9949 : decode code ⟨9949⟩ = some (.POP, .none) := by
    rw [hdecEvent ⟨9949⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9950 : decode code ⟨9950⟩ = some (.POP, .none) := by
    rw [hdecEvent ⟨9950⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd9951 : decode code ⟨9951⟩ = some (.JUMP, .none) := by
    rw [hdecEvent ⟨9951⟩ (by native_decide) (by native_decide)]
    native_decide
  have hd621 : decode code ⟨621⟩ = some (.JUMPDEST, .none) := by
    rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
    native_decide
  have hd622 : decode code ⟨622⟩ = some (.Push .PUSH1, some (⟨64⟩, 1)) := by
    rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
    native_decide
  have hd624 : decode code ⟨624⟩ = some (.DUP1, .none) := by
    rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
    native_decide
  have hd625 : decode code ⟨625⟩ = some (.MLOAD, .none) := by
    rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
    native_decide
  have hd626 : decode code ⟨626⟩ = some (.SWAP3, .none) := by
    rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
    native_decide
  have hd627 : decode code ⟨627⟩ = some (.DUP4, .none) := by
    rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
    native_decide
  have hd628 : decode code ⟨628⟩ = some (.MSTORE, .none) := by
    rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
    native_decide
  have hd629 : decode code ⟨629⟩ = some (.Push .PUSH1, some (⟨32⟩, 1)) := by
    rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
    native_decide
  have hd631 : decode code ⟨631⟩ = some (.DUP4, .none) := by
    rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
    native_decide
  have hd632 : decode code ⟨632⟩ = some (.ADD, .none) := by
    rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
    native_decide
  have hd633 : decode code ⟨633⟩ = some (.SWAP2, .none) := by
    rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
    native_decide
  have hd634 : decode code ⟨634⟩ = some (.SWAP1, .none) := by
    rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
    native_decide
  have hd635 : decode code ⟨635⟩ = some (.SWAP2, .none) := by
    rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
    native_decide
  have hd636 : decode code ⟨636⟩ = some (.MSTORE, .none) := by
    rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
    native_decide
  have hd637 : decode code ⟨637⟩ = some (.DUP1, .none) := by
    rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
    native_decide
  have hd638 : decode code ⟨638⟩ = some (.MLOAD, .none) := by
    rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
    native_decide
  have hd639 : decode code ⟨639⟩ = some (.SWAP2, .none) := by
    rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
    native_decide
  have hd640 : decode code ⟨640⟩ = some (.DUP3, .none) := by
    rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
    native_decide
  have hd641 : decode code ⟨641⟩ = some (.SWAP1, .none) := by
    rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
    native_decide
  have hd642 : decode code ⟨642⟩ = some (.SUB, .none) := by
    rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
    native_decide
  have hd643 : decode code ⟨643⟩ = some (.ADD, .none) := by
    rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
    native_decide
  have hd644 : decode code ⟨644⟩ = some (.SWAP1, .none) := by
    rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
    native_decide
  have hd645 : decode code ⟨645⟩ = some (.RETURN, .none) := by
    rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
    native_decide
  have rd9926 := evm_run h with [
    raw pop hd9921 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw pop hd9922 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw push1 ⟨0⟩ hd9923 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw dup1 hd9925 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega)]
  obtain ⟨_, _, rd9927₀⟩ := rd9926.sload hd9926 (by evm_ov)
  have rd9941 := evm_run rd9927₀ with [
    raw push1 ⟨255⟩ hd9927 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw push1 ⟨240⟩ hd9929 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw shl hd9931 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw not hd9932 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw and hd9933 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw push1 ⟨1⟩ hd9934 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw push1 ⟨240⟩ hd9936 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw shl hd9938 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw lor hd9939 (by evm_ov),
    raw swap1 hd9940 (by evm_ov)]
  obtain ⟨_, _, rd9942⟩ := rd9941.sstore hperm hd9941 (by evm_ov)
  have rd9951 := evm_run rd9942 with [
    raw pop hd9942 (by evm_ov),
    raw swap1 hd9943 (by evm_ov),
    raw swap5 hd9944 (by
      have h := hov
      omega),
    raw swap1 hd9945 (by evm_ov),
    raw swap4 hd9946 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw pop hd9947 (by evm_ov),
    raw swap2 hd9948 (by evm_ov),
    raw pop hd9949 (by evm_ov),
    raw pop hd9950 (by evm_ov)]
  have rd621 := rd9951.jump hd9951
    (uniswapV3PoolJumpDestPatched2258 hpatch (by native_decide)) (by evm_ov)
  have rd628 := evm_run rd621 with [
    raw jumpdest hd621 (by evm_ov),
    raw push1 ⟨64⟩ hd622 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw dup1 hd624 (by evm_ov),
    raw mload 0 (burnPositionKeyNewFreePtrWord + (⟨160⟩ : UInt256))
      (UInt256.ofNat 25) hd625 mem_cost
      (burnPostPositionUpdateEventMem_mload64 σmem ee pos0 posBase amount)
      (by native_decide) (by evm_ov),
    raw swap3 hd626 (by evm_ov),
    raw dup4 hd627 (by evm_ov)]
  have rd637 := evm_run rd628 with [
    raw mstore 0 (burnPostPositionUpdateReturnMem0 σmem ee pos0 posBase amount)
      (UInt256.ofNat 25) hd628 mem_cost (by rfl) (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ hd629 (by evm_ov),
    raw dup4 hd631 (by evm_ov),
    raw add hd632 (by evm_ov),
    raw swap2 hd633 (by evm_ov),
    raw swap1 hd634 (by evm_ov),
    raw swap2 hd635 (by evm_ov),
    raw mstore 0 (burnPostPositionUpdateReturnMem σmem ee pos0 posBase amount)
      (UInt256.ofNat 25) hd636 mem_cost
      (by
        rw [show ((burnPositionKeyNewFreePtrWord + (⟨160⟩ : UInt256)) +
              (⟨32⟩ : UInt256)).toNat =
            (burnPositionKeyNewFreePtrWord + (⟨160⟩ : UInt256) +
              (⟨32⟩ : UInt256)).toNat from by native_decide]
        rfl)
      (by native_decide) (by evm_ov)]
  exact evm_run rd637 with [
    raw dup1 hd637 (by evm_ov),
    raw mload 0 (burnPositionKeyNewFreePtrWord + (⟨160⟩ : UInt256))
      (UInt256.ofNat 25) hd638 mem_cost
      (burnPostPositionUpdateReturnMem_mload64 σmem ee pos0 posBase amount)
      (by native_decide) (by evm_ov),
    raw swap2 hd639 (by evm_ov),
    raw dup3 hd640 (by evm_ov),
    raw swap1 hd641 (by evm_ov),
    raw sub hd642 (by evm_ov),
    raw add hd643 (by evm_ov),
    raw swap1 hd644 (by evm_ov),
    raw ret 0
      (UInt256.toByteArray (⟨0⟩ : UInt256) ++ UInt256.toByteArray (⟨0⟩ : UInt256))
      hd645 mem_cost
      (by
        rw [show (burnPositionKeyNewFreePtrWord + (⟨160⟩ : UInt256)).toNat =
            (burnPositionKeyNewFreePtrWord + (⟨160⟩ : UInt256)).toNat from rfl,
          show (UInt256.sub
                (burnPositionKeyNewFreePtrWord + (⟨160⟩ : UInt256))
                (burnPositionKeyNewFreePtrWord + (⟨160⟩ : UInt256)) +
              (⟨64⟩ : UInt256)).toNat = 64
            from by native_decide]
        exact burnPostPositionUpdateReturnMem_readFree σmem ee pos0 posBase amount)
      (by evm_ov)]

abbrev burnPostPositionUpdateTokensOwedAccountMap
    (ee : ExecutionEnv) (σ : AccountMap)
    (posBase tokensOwed0 tokensOwed1 : UInt256) : AccountMap :=
  sstoreAccountMap ee.codeOwner σ (posBase + (⟨3⟩ : UInt256))
    (burnPositionUpdateTokensOwedAddedSlot3
      (solcSlotWord σ ee (posBase + (⟨3⟩ : UInt256))) tokensOwed0 tokensOwed1)

theorem burnPostPositionUpdateUnlockedSlotWord_eq_slot0UnlockedTrueSlotWord
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ evm.accountMap) (hEnv : evm.executionEnv = I) :
    burnPostPositionUpdateUnlockedSlotWord σ I = slot0UnlockedTrueSlotWord evm := by
  simpa [burnPostPositionUpdateUnlockedSlotWord, burnPostPositionUpdateUnlockedClearMask,
    slot0UnlockedClearMask] using
    slot0UnlockedTrueSlotWord_eq_of_accountMapEquiv
      (evm := evm) (σ := σ) (I := I) hAccounts hEnv

theorem burnPostPositionUpdateFinalAccountMapEquiv
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ evm.accountMap) (hEnv : evm.executionEnv = I) :
    accountMapEquiv
      (sstoreAccountMap I.codeOwner σ ⟨0⟩
        (burnPostPositionUpdateUnlockedSlotWord σ I))
      (slot0AfterUnlockState evm).accountMap := by
  have hword := burnPostPositionUpdateUnlockedSlotWord_eq_slot0UnlockedTrueSlotWord
    (evm := evm) (σ := σ) (I := I) hAccounts hEnv
  rw [hword]
  simpa [slot0AfterUnlockState, storageStore_accountMap, hEnv] using
    accountMapEquiv_sstoreAccountMap I.codeOwner ⟨0⟩
      (slot0UnlockedTrueSlotWord evm) hAccounts

theorem uniswapV3PoolBurnZeroDeltaPositionUpdateToFinalReturnCases
    {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {tokensOwed1 tokensOwed0 liquidity inside1 inside0 delta posBase inside1' inside0'
      z2 z3 fee1 fee0 tick delta' lower upper owner free r3 amount eventUpper eventLower :
      UInt256}
    {R : List UInt256} {σmem : AccountMap} {pos0 : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hdest : (D_J code 0).contains ⟨9737⟩ = true)
    (hperm : ee.perm = true)
    (hzero : burnAmountCleanWord ee = ⟨0⟩)
    (hmload224 :
      (if (⟨224⟩ : UInt256).toNat ≥
          (burnPositionUpdateMem5 σmem ee pos0 posBase).size
          ∨ (⟨224⟩ : UInt256) ≥ UInt256.ofNat 22 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((burnPositionUpdateMem5 σmem ee pos0 posBase).readWithPadding
              (⟨224⟩ : UInt256).toNat 32))) =
        UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord ee)))
    (h : RD code ee g s0 ⟨21861⟩
      (tokensOwed1 :: tokensOwed0 :: liquidity :: burnPositionKeyNewFreePtrWord ::
        inside1 :: inside0 :: delta :: posBase :: ⟨19527⟩ :: inside1' :: inside0' ::
        z2 :: z3 :: fee1 :: fee0 :: posBase :: tick :: delta' :: upper :: lower ::
        owner :: ⟨16428⟩ :: free :: ⟨0⟩ :: ⟨0⟩ :: r3 :: ⟨128⟩ :: ⟨9737⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: amount :: eventUpper ::
        eventLower :: ⟨621⟩ :: R)
      (burnPositionUpdateMem5 σmem ee pos0 posBase) (UInt256.ofNat 22) rdata
      (cA, σ) k C)
    (hdelta : UInt256.slt (UInt256.signextend ⟨15⟩ delta') ⟨0⟩ = ⟨0⟩)
    (hov : R.length + 49 ≤ 1024) :
    (RDret code g s0
        (cA, sstoreAccountMap ee.codeOwner σ ⟨0⟩
          (burnPostPositionUpdateUnlockedSlotWord σ ee))
        (UInt256.toByteArray (⟨0⟩ : UInt256) ++ UInt256.toByteArray (⟨0⟩ : UInt256)) ∧
      UInt256.land burnPositionUpdateSlot0Mask tokensOwed0 = ⟨0⟩ ∧
      UInt256.land burnPositionUpdateSlot0Mask tokensOwed1 = ⟨0⟩) ∨
    (RDret code g s0
        (cA, sstoreAccountMap ee.codeOwner
          (burnPostPositionUpdateTokensOwedAccountMap ee σ posBase tokensOwed0 tokensOwed1)
          ⟨0⟩
          (burnPostPositionUpdateUnlockedSlotWord
            (burnPostPositionUpdateTokensOwedAccountMap ee σ posBase tokensOwed0 tokensOwed1)
            ee))
        (UInt256.toByteArray (⟨0⟩ : UInt256) ++ UInt256.toByteArray (⟨0⟩ : UInt256)) ∧
      (UInt256.land burnPositionUpdateSlot0Mask tokensOwed0 ≠ ⟨0⟩ ∨
        UInt256.land burnPositionUpdateSlot0Mask tokensOwed1 ≠ ⟨0⟩)) := by
  obtain hcases :=
    uniswapV3PoolBurnPositionUpdateZeroDeltaReturnToCallerByTokensCases
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (tokensOwed1 := tokensOwed1) (tokensOwed0 := tokensOwed0)
      (liquidity := liquidity) (inside1 := inside1) (inside0 := inside0)
      (delta := delta) (posBase := posBase) (inside1' := inside1')
      (inside0' := inside0') (z2 := z2) (z3 := z3) (fee1 := fee1)
      (fee0 := fee0) (posBase' := posBase) (tick := tick) (delta' := delta')
      (upper := upper) (lower := lower) (owner := owner) (free := free)
      (r1 := ⟨0⟩) (r2 := ⟨0⟩) (r3 := r3) (callerRet := ⟨9737⟩)
      (R := ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: amount :: eventUpper ::
        eventLower :: ⟨621⟩ :: R)
      (mem := burnPositionUpdateMem5 σmem ee pos0 posBase) (rdata := rdata)
      (cA := cA) (σ := σ)
      hpatch hdest hperm hzero hmload224 h hdelta
      (by simp only [List.length_cons]; omega)
  rcases hcases with hzeroTokens | hsomeTokens
  · rcases hzeroTokens with ⟨_, _, hrdRet, htokens0, htokens1⟩
    obtain ⟨_, _, hrdEvent⟩ :=
      uniswapV3PoolBurnPostPositionUpdateZeroAmountsToEvent
        (v := v) hpatch hrdRet
        (by omega)
    obtain ⟨_, _, hrdLog⟩ :=
      uniswapV3PoolBurnPostPositionUpdateEventLog
        (v := v) (σ := σmem) (pos0 := pos0) hpatch hrdEvent hperm
        (by omega)
    have hrdSuccess :=
      uniswapV3PoolBurnPostPositionUpdateUnlockReturn
        (v := v) hpatch hrdLog hperm
        (by omega)
    exact Or.inl ⟨hrdSuccess, htokens0, htokens1⟩
  · rcases hsomeTokens with ⟨_, _, hrdRet, htokens⟩
    obtain ⟨_, _, hrdEvent⟩ :=
      uniswapV3PoolBurnPostPositionUpdateZeroAmountsToEvent
        (v := v) hpatch hrdRet
        (by omega)
    obtain ⟨_, _, hrdLog⟩ :=
      uniswapV3PoolBurnPostPositionUpdateEventLog
        (v := v) (σ := σmem) (pos0 := pos0) hpatch hrdEvent hperm
        (by omega)
    have hrdSuccess :=
      uniswapV3PoolBurnPostPositionUpdateUnlockReturn
        (v := v) hpatch hrdLog hperm
        (by omega)
    exact Or.inr ⟨by
      simpa [burnPostPositionUpdateTokensOwedAccountMap] using hrdSuccess, htokens⟩

end Benchmarks.UniswapV3Pool
