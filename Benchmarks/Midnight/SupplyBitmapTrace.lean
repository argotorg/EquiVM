import Benchmarks.Midnight.PositionBitmapStorage
import Benchmarks.Midnight.BitmapCountTrace
import Benchmarks.Midnight.CollateralBlocksStatic

variable {fork : Ethereum.Fork}

/-! The supply-collateral bitmap write, including the static-call exit. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem supplyBitmapWrite {I : ExecutionEnv} {g : Sat256} {s0 : State}
    (evm : EVM.State) (henv : evm.executionEnv = I)
    {mem rdata : ByteArray} {aw ignored id user index : UInt256} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 15 ≤ 1024) (hi : index.toNat < 128)
    (rd : RD fork midnightBytecode I g s0 ⟨17274⟩
      (ignored :: positionSlot id user :: index :: R) mem aw rdata evm.accountMap k C) :
    (I.perm = false ∧ RDstatic fork midnightBytecode g s0) ∨
    (I.perm = true ∧ ∃ k' C', C ≤ C' ∧
      let bitmap := bitmapSet (positionBitmapWord evm id user) index
      RD fork midnightBytecode I g s0 ⟨17385⟩
        ([bitmap, countMask1, bitmap, countMask4, countMultiplier, UInt256.ofNat 255,
          UInt256.ofNat 16, index] ++ R) mem aw rdata
        (storeHigh128 evm (positionSlot id user + ⟨2⟩) bitmap).accountMap k' C') := by
  cases hp : I.perm with
  | false => exact Or.inl ⟨rfl, collateral_block_17274_static hstack hp rd⟩
  | true =>
    obtain ⟨k', C', hc, rd1⟩ := collateral_block_17274_mono hstack hp (by jump_dest) rd
    have hr : (evm.accountMap.get? I.codeOwner |>.option (⟨0⟩ : UInt256)
        (fun ac ↦ ac.storage.getD (positionSlot id user + UInt256.ofNat 2) ⟨0⟩)) =
        healthPositionWord evm id user := by
      rw [healthPositionWord, storageLoad_codeOwner_eq_solcSlotWordAt evm I _
        (congrArg ExecutionEnv.codeOwner henv)]
      rfl
    have hn := bitmapSet_clean (positionBitmapWord_lt evm id user) hi
    change bitmapSet (positionBitmapWord evm id user) index =
      UInt256.lor (UInt256.shiftLeft (UInt256.ofNat 1) index)
        (UInt256.shiftRight (healthPositionWord evm id user) (UInt256.ofNat 128)) at hn
    have hclean : UInt256.land (bitmapSet (positionBitmapWord evm id user) index)
        (UInt256.ofNat (2^128 - 1)) = bitmapSet (positionBitmapWord evm id user) index :=
      uint128Mask_clean (low128_lt _)
    simp only [midnightBlocks.midnight_block_17274_stack, uint128Mask_computed,
      hr, ← hn, hclean, shiftLeft128_highMask] at rd1
    have hac : (storeHigh128 evm (positionSlot id user + ⟨2⟩)
        (bitmapSet (positionBitmapWord evm id user) index)).accountMap =
        sstoreAccountMap I.codeOwner evm.accountMap (positionSlot id user + UInt256.ofNat 2)
          (setUint128HighWord (healthPositionWord evm id user)
            (bitmapSet (positionBitmapWord evm id user) index)) := by
      simp only [storeHigh128, storageStore_accountMap, healthPositionWord, henv]
      rfl
    refine Or.inr ⟨rfl, k', C', hc, ?_⟩
    dsimp only
    rw [hac]
    exact rd1

end Benchmarks.Midnight
