import Benchmarks.Midnight.WithdrawCollateralBlocksGas
import Benchmarks.Midnight.PositionBitmapStorage
import Benchmarks.Midnight.BitmapArithmetic

/-! Clearing a collateral bitmap bit after its balance has been withdrawn. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000 in
theorem withdrawBitmapWrite {I : ExecutionEnv} {g : Sat256} {s0 : State}
    (evm : EVM.State) (henv : evm.executionEnv = I)
    {mem rdata : ByteArray} {aw id user index : UInt256} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 7 ≤ 1024) (hperm : I.perm = true)
    (rd : RD midnightBytecode I g s0 ⟨4742⟩
      (index :: positionSlot id user :: R) mem aw rdata evm.accountMap k C) :
    ∃ k' C', C ≤ C' ∧
      RD midnightBytecode I g s0 ⟨4795⟩ R mem aw rdata
        (storeHigh128 evm (positionSlot id user + ⟨2⟩)
          (bitmapClear (positionBitmapWord evm id user) index)).accountMap k' C' := by
  obtain ⟨k', C', hc, rd1⟩ := withdrawal_block_4742_mono hstack hperm (by jump_dest) rd
  have hr : (evm.accountMap.get? I.codeOwner |>.option (⟨0⟩ : UInt256)
      (fun ac ↦ ac.storage.getD (positionSlot id user + UInt256.ofNat 2) ⟨0⟩)) =
      healthPositionWord evm id user := by
    rw [healthPositionWord, storageLoad_codeOwner_eq_solcSlotWordAt evm I _
      (congrArg ExecutionEnv.codeOwner henv)]
    rfl
  have hb : UInt256.land
      (UInt256.land (UInt256.lnot (UInt256.shiftLeft (UInt256.ofNat 1) index))
        (UInt256.shiftRight (healthPositionWord evm id user) (UInt256.ofNat 128)))
      (UInt256.ofNat (2^128-1)) = bitmapClear (positionBitmapWord evm id user) index := by
    rw [u256_land_comm (UInt256.lnot _)]
    rfl
  simp only [midnightBlocks.midnight_block_4742_stack, uint128Mask_computed,
    hr, hb, shiftLeft128_highMask] at rd1
  have hac : (storeHigh128 evm (positionSlot id user + ⟨2⟩)
      (bitmapClear (positionBitmapWord evm id user) index)).accountMap =
      sstoreAccountMap I.codeOwner evm.accountMap (positionSlot id user + UInt256.ofNat 2)
        (setUint128HighWord (healthPositionWord evm id user)
          (bitmapClear (positionBitmapWord evm id user) index)) := by
    simp only [storeHigh128, storageStore_accountMap, healthPositionWord, henv]
    rfl
  refine ⟨k', C', hc, ?_⟩
  rw [hac]
  exact rd1

end Benchmarks.Midnight
