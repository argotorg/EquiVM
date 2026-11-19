import Benchmarks.Midnight.TakePriceGuard
import Benchmarks.Midnight.ZeroFloorSub

/-! Complete price rounding and prepare the time-dependent settlement-fee call. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

def takeTimeToMaturity (I : ExecutionEnv) (offer : OfferData) : UInt256 :=
  zeroFloorSubWord offer.market.maturity (UInt256.ofNat I.header.timestamp)

theorem midnightTakePricePrepare {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw marketPtr arrayPtr callbackPtr root id slot ratifierPtr : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} {offer : OfferData}
    (hstack : R.length + 9 ≤ 1024)
    (ho : OfferStored mem ⟨832⟩ marketPtr arrayPtr callbackPtr root offer)
    (hroot : memLoad (UInt256.ofNat 384) mem = ⟨832⟩)
    (hid : memLoad (UInt256.ofNat 512) mem = id)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨11514⟩
      (UInt256.div (tickPriceNumerator offer.tick.toNat)
          (tickPriceDenominator offer.tick.toNat) ::
        UInt256.ofNat 49999999999 :: UInt256.ofNat 100000000000 ::
        UInt256.ofNat 100000000000 :: ratifierPtr :: slot :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', MemoryFunding credit (writeWord mem 800 ⟨0⟩) aw' C' ∧
      RD midnightBytecode I g s0 ⟨21835⟩
        (id :: takeTimeToMaturity I offer :: UInt256.ofNat 11556 :: UInt256.ofNat 11591 ::
          tickPriceWord offer.tick.toNat :: slot :: ratifierPtr :: takeTimeToMaturity I offer :: R)
        (writeWord mem 800 ⟨0⟩) aw' rdata σ k' C' := by
  have hm : 832 ≤ mem.size := by
    have hh := ho.words.size
    change 832 + 32 * 15 ≤ mem.size at hh
    omega
  have ho1 := ho.writeWord_below (off := 800) ⟨0⟩ (by decide)
  have hroot1 : memLoad (UInt256.ofNat 384) (writeWord mem 800 ⟨0⟩) = ⟨832⟩ := by
    rw [memLoad_writeWord_preserved _ _ _ _ (by change 384 + 32 ≤ mem.size; omega)
      (Or.inl (by decide)), hroot]
  have hid1 : memLoad (UInt256.ofNat 512) (writeWord mem 800 ⟨0⟩) = id := by
    rw [memLoad_writeWord_preserved _ _ _ _ (by change 512 + 32 ≤ mem.size; omega)
      (Or.inl (by decide)), hid]
  have hmarket : memLoad (⟨832⟩ : UInt256) (writeWord mem 800 ⟨0⟩) = marketPtr := by
    simpa only [u256_add_zero] using ho1.words.load_offset ⟨0, by change 0 < 15; decide⟩ rfl
  have htime : memLoad (marketPtr + UInt256.ofNat 128) (writeWord mem 800 ⟨0⟩) =
      offer.market.maturity := ho1.market.words.load_offset ⟨4, by change 4 < 8; decide⟩ rfl
  have rd1 := midnightBlocks.midnight_block_11514 hstack (by jump_dest) rd
  simp only [midnightBlocks.midnight_block_11514_memory] at rd1
  have ha1 := memoryFundingAt (credit := credit) rd1 (by memory_fund ha)
  change MemoryFunding credit (writeWord mem 800 ⟨0⟩) _ _ at ha1
  simp only [midnightBlocks.midnight_block_11514_stack,
    midnightBlocks.midnight_block_11514_memory] at rd1
  have hfold : (⟨0⟩ : UInt256).toByteArray.write 0 mem (UInt256.ofNat 800).toNat 32 =
      writeWord mem 800 ⟨0⟩ := rfl
  simp only [hfold] at rd1 ha1
  rw [hid1, hroot1, hmarket, htime] at rd1
  rw [hroot1, hmarket] at ha1
  have hz : UInt256.mul
      (UInt256.lt (UInt256.ofNat I.header.timestamp) offer.market.maturity)
      (UInt256.sub offer.market.maturity (UInt256.ofNat I.header.timestamp)) =
      takeTimeToMaturity I offer := zeroFloorSubWord_eq _ _
  simp only [hz] at rd1
  exact ⟨_, _, _, ha1, rd1⟩

end Benchmarks.Midnight
