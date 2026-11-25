import Benchmarks.Midnight.TakeAmountsMemory
import Benchmarks.Midnight.RuntimeBlocks_045

variable {fork : Ethereum.Fork}

/-! Initialize the new consumed amount and select the asset-cap or unit-cap path. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

def takeConsumptionReadPC (offer : OfferData) : UInt256 :=
  if offer.maxAssets = ⟨0⟩ then ⟨14604⟩ else ⟨11710⟩

theorem midnightTakeConsumptionMode {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw marketPtr arrayPtr callbackPtr root : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} {offer : OfferData}
    (hstack : R.length + 4 ≤ 1024)
    (ho : OfferStored mem ⟨832⟩ marketPtr arrayPtr callbackPtr root offer)
    (hc : OfferCanonical offer) (hroot : memLoad (UInt256.ofNat 384) mem = ⟨832⟩)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨11681⟩ R mem aw rdata σ k C) :
    ∃ aw' k' C', MemoryFunding credit (writeWord mem 480 ⟨0⟩) aw' C' ∧
      RD fork midnightBytecode I g s0 (takeConsumptionReadPC offer) R
        (writeWord mem 480 ⟨0⟩) aw' rdata σ k' C' := by
  have hm : 416 ≤ mem.size := by
    have hh := ho.words.size
    change 832 + 32 * 15 ≤ mem.size at hh
    omega
  have ho1 := ho.writeWord_below (off := 480) ⟨0⟩ (by decide)
  have hroot1 : memLoad (UInt256.ofNat 384) (writeWord mem 480 ⟨0⟩) = ⟨832⟩ := by
    rw [memLoad_writeWord_preserved mem 480 (UInt256.ofNat 384) _ hm (Or.inl (by decide)), hroot]
  have hassets : memLoad (UInt256.ofNat 416 + (⟨832⟩ : UInt256)) (writeWord mem 480 ⟨0⟩) =
      offer.maxAssets := by
    rw [u256_add_comm]
    exact ho1.words.load_offset ⟨13, by change 13 < 15; decide⟩ rfl
  have hload : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))
      (memLoad (UInt256.ofNat 416 + memLoad (UInt256.ofNat 384)
        (writeWord mem 480 ⟨0⟩)) (writeWord mem 480 ⟨0⟩)) = offer.maxAssets := by
    rw [hroot1, hassets, uint128Mask_computed, u256_land_comm, uint128Mask_clean hc.maxAssets]
  have hfold : (⟨0⟩ : UInt256).toByteArray.write 0 mem (UInt256.ofNat 480).toNat 32 =
      writeWord mem 480 ⟨0⟩ := rfl
  by_cases hz : offer.maxAssets = ⟨0⟩
  · have rd1 := midnightBlocks.midnight_block_11681_taken hstack (by
      simp only [hfold, hload, hz]
      decide) (by jump_dest) rd
    simp only [midnightBlocks.midnight_block_11681_taken_memory] at rd1
    have ha1 := memoryFundingAt (credit := credit) rd1 (by memory_fund ha)
    simp only [takeConsumptionReadPC, if_pos hz]
    exact ⟨_, _, _, ha1, rd1⟩
  · have rd1 := midnightBlocks.midnight_block_11681_fallthrough hstack (by
      simp only [hfold, hload]
      exact isZero_eq_zero_of_ne hz) rd
    simp only [midnightBlocks.midnight_block_11681_fallthrough_memory] at rd1
    have ha1 := memoryFundingAt (credit := credit) rd1 (by memory_fund ha)
    simp only [takeConsumptionReadPC, if_neg hz]
    exact ⟨_, _, _, ha1, rd1⟩

end Benchmarks.Midnight
