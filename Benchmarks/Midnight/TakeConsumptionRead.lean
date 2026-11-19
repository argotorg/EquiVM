import Benchmarks.Midnight.TakeConsumptionUnitsRead
import Benchmarks.Midnight.TakeConsumptionAssetsRead
import Benchmarks.Midnight.TakeConsumptionCap

/-! Both consumed-counter paths reach the same checked-addition routine. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightTakeConsumptionRead {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw marketPtr arrayPtr callbackPtr root units bought sold : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} {offer : OfferData}
    (hstack : R.length + 5 ≤ 1024)
    (ho : OfferStored mem ⟨832⟩ marketPtr arrayPtr callbackPtr root offer)
    (hc : OfferCanonical offer) (hroot : memLoad (UInt256.ofNat 384) mem = ⟨832⟩)
    (hu : calldataWord I.calldata 68 = units)
    (hb : memLoad (UInt256.ofNat 256) mem = bought)
    (hs : memLoad (UInt256.ofNat 416) mem = sold)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨11681⟩ R mem aw rdata σ k C) :
    ∃ aw' k' C', MemoryFunding credit (takeConsumptionReadMemory mem offer) aw' C' ∧
      RD midnightBytecode I g s0 ⟨19536⟩
        (takeConsumedWord σ I offer :: takeConsumedDelta offer units bought sold ::
          takeConsumptionCheckPC offer :: R)
        (takeConsumptionReadMemory mem offer) aw' rdata σ k' C' := by
  have hm : 448 ≤ mem.size := by
    have hh := ho.words.size
    change 832 + 32 * 15 ≤ mem.size at hh
    omega
  obtain ⟨aw1, k1, C1, ha1, rd1⟩ := midnightTakeConsumptionMode (by omega) ho hc hroot ha rd
  have ho1 := ho.writeWord_below (off := 480) ⟨0⟩ (by decide)
  have hroot1 : memLoad (UInt256.ofNat 384) (writeWord mem 480 ⟨0⟩) = ⟨832⟩ := by
    rw [memLoad_writeWord_preserved mem 480 (UInt256.ofNat 384) _ (by change 416 ≤ mem.size; omega)
      (Or.inl (by decide)), hroot]
  by_cases hz : offer.maxAssets = ⟨0⟩
  · simp only [takeConsumptionReadPC, if_pos hz] at rd1
    obtain ⟨aw2, k2, C2, ha2, rd2⟩ := midnightTakeConsumedUnitsRead hstack ho1 hroot1 ha1 rd1
    rw [hu] at rd2
    simp only [takeConsumedDelta, takeConsumptionCheckPC, if_pos hz]
    exact ⟨aw2, k2, C2, ha2, rd2⟩
  · simp only [takeConsumptionReadPC, if_neg hz] at rd1
    obtain ⟨aw2, k2, C2, ha2, rd2⟩ := midnightTakeConsumedAssetsRead hstack ho1 hroot1 ha1 rd1
    change MemoryFunding credit (takeConsumptionReadMemory mem offer) aw2 C2 at ha2
    change RD midnightBytecode I g s0 (takeConsumedAssetPC offer.buy)
      (takeConsumedWord σ I offer :: UInt256.ofNat 11794 :: R)
      (takeConsumptionReadMemory mem offer) aw2 rdata σ k2 C2 at rd2
    by_cases hbuy : offer.buy = ⟨0⟩
    · simp only [takeConsumedAssetPC, if_pos hbuy] at rd2
      have rd3 := midnightBlocks.midnight_block_14594
        (by simp only [List.length_cons]; omega) (by jump_dest) rd2
      have ha3 := memoryFundingAt (credit := credit) rd3 (by memory_fund ha2)
      simp only [midnightBlocks.midnight_block_14594_stack,
        takeConsumptionReadMemory_load offer (UInt256.ofNat 416) (by decide) hm
          (Or.inl (by decide)), hs] at rd3
      simp only [takeConsumedDelta, takeConsumptionCheckPC, if_neg hz, if_pos hbuy]
      exact ⟨_, _, _, ha3, rd3⟩
    · simp only [takeConsumedAssetPC, if_neg hbuy] at rd2
      have rd3 := midnightBlocks.midnight_block_11785
        (by simp only [List.length_cons]; omega) (by jump_dest) rd2
      have ha3 := memoryFundingAt (credit := credit) rd3 (by memory_fund ha2)
      simp only [midnightBlocks.midnight_block_11785_stack,
        takeConsumptionReadMemory_load (mem := mem) offer (UInt256.ofNat 256) (by decide)
          (by change 288 ≤ mem.size; omega)
          (Or.inl (by decide)), hb] at rd3
      simp only [takeConsumedDelta, takeConsumptionCheckPC, if_neg hz, if_neg hbuy]
      exact ⟨_, _, _, ha3, rd3⟩

end Benchmarks.Midnight
