import Benchmarks.Midnight.LiquidateBitmapGas
import Benchmarks.Midnight.PositionBitmapStorage
import Benchmarks.Midnight.BitmapArithmetic
import Benchmarks.Midnight.PackedStorageSourceState

/-! Clearing the liquidated collateral's bit preserves the other packed position field. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightLiquidateBitmapWrite {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id borrower index : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 7 ≤ 1024) (hp : I.perm = true)
    (hi : calldataWord I.calldata 36 = index) (hs : SourceState s0 I σ evm)
    (rd : RD midnightBytecode I g s0 ⟨6952⟩
      (positionSlot id borrower :: R) mem aw rdata σ k C) :
    ∃ k' C', C ≤ C' ∧
      RD midnightBytecode I g s0 ⟨6833⟩ (positionSlot id borrower :: R) mem aw rdata
        (storeHigh128Accounts σ I (positionSlot id borrower + ⟨2⟩)
          (bitmapClear (positionBitmapWord evm id borrower) index)) k' C' := by
  obtain ⟨k', C', hc, rd'⟩ := liquidate_block_6952_mono hstack hp (by jump_dest) rd
  have hi' : uInt256OfByteArray (I.calldata.readBytes 36 32) = index := hi
  have hr : (σ.get? I.codeOwner |>.option (⟨0⟩ : UInt256)
      (fun ac ↦ ac.storage.getD (positionSlot id borrower + UInt256.ofNat 2) ⟨0⟩)) =
      healthPositionWord evm id borrower := (hs.storageRead _).symm
  have hb : UInt256.land
      (UInt256.shiftRight (healthPositionWord evm id borrower) (UInt256.ofNat 128))
      (UInt256.lnot (UInt256.shiftLeft (UInt256.ofNat 1) index)) =
      bitmapClear (positionBitmapWord evm id borrower) index := by
    symm
    apply uint128Mask_clean
    rw [uland_toNat]
    exact Nat.and_le_left.trans_lt (positionBitmapWord_lt evm id borrower)
  simp only [uint128Mask_computed, show (UInt256.ofNat 36).toNat = 36 from rfl, hi', hr] at rd'
  rw [u256_land_comm (UInt256.lnot uint128Mask), shiftLeft128_highMask, hb,
    u256_lor_comm] at rd'
  have hw : healthPositionWord evm id borrower =
      solcSlotWordAt (positionSlot id borrower + ⟨2⟩) σ I := hs.storageRead _
  refine ⟨k', C', hc, ?_⟩
  simpa only [storeHigh128Accounts, setUint128HighWord, ← hw] using rd'

end Benchmarks.Midnight
