import Benchmarks.Midnight.TakeLock
import Benchmarks.Midnight.OfferSourceValues
import Benchmarks.Midnight.OfferHeapMemory
import Benchmarks.Midnight.RuntimeBlocks_051
import Benchmarks.Midnight.RuntimeBlocks_050

/-! Selecting the maker or taker byte buffer for the seller callback. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def takeSellerData (offer : OfferData) (data : ByteArray) : ByteArray :=
  if offer.buy = ⟨0⟩ then offer.callbackData else data

def takeSellerDataPtr (offer : OfferData) (callbackPtr takerPtr : UInt256) : UInt256 :=
  if offer.buy = ⟨0⟩ then callbackPtr else takerPtr

def takeSellerDataExpr : Expr :=
  .ite (.field (.var "offer") "buy") (.var "takerCallbackData")
    (.field (.var "offer") "callbackData")

theorem evalTakeSellerData {frame : Frame} {evm : State} {offer : OfferData} {data : ByteArray}
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value))
    (hd : frame.locals.get? "takerCallbackData" = some (.bytes data)) :
    evalExpr? config frame evm takeSellerDataExpr = .ok (.bytes (takeSellerData offer data)) := by
  rw [takeSellerDataExpr, evalExpr?, evalOfferBuy ho]
  simp only [wordToElemBool, bind, EvalResult.bind]
  by_cases hz : offer.buy = ⟨0⟩
  · simp only [takeSellerData, hz, if_true, decide_true, Bool.not_true,
      evalOfferCallbackData ho]
  · simp only [takeSellerData, hz, if_false, decide_false, Bool.not_false,
      evalExpr?, hd, EvalResult.ofOption]

theorem takeSellerData_stored {mem data : ByteArray} {offer : OfferData}
    {callbackPtr takerPtr : UInt256}
    (hc : MemoryByteString mem callbackPtr offer.callbackData)
    (ht : MemoryByteString mem takerPtr data) :
    MemoryByteString mem (takeSellerDataPtr offer callbackPtr takerPtr) (takeSellerData offer data) :=
  by
    by_cases hz : offer.buy = ⟨0⟩
    · simpa only [takeSellerDataPtr, takeSellerData, if_pos hz] using hc
    · simpa only [takeSellerDataPtr, takeSellerData, if_neg hz] using ht

set_option maxRecDepth 10000

theorem midnightTakeSellerData {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw marketPtr arrayPtr callbackPtr limit takerPtr callback : UInt256}
    {offer : OfferData} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (ho : OfferStored mem ⟨832⟩ marketPtr arrayPtr callbackPtr limit offer)
    (hoffer : memLoad (UInt256.ofNat 384) mem = ⟨832⟩)
    (htaker : memLoad (UInt256.ofNat 320) mem = takerPtr)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨13456⟩ (callback :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', MemoryFunding credit mem aw' C' ∧
      RD midnightBytecode I g s0 ⟨13482⟩
        ([callback, takeSellerDataPtr offer callbackPtr takerPtr, ⟨32⟩, ⟨13626⟩] ++ R)
        mem aw' rdata σ k' C' := by
  have hbuy : memLoad (UInt256.ofNat 32 + memLoad (UInt256.ofNat 384) mem) mem = offer.buy := by
    rw [hoffer, u256_add_comm]
    exact ho.words.load_offset ⟨1, by change 1 < 15; decide⟩ rfl
  have hcb : memLoad (memLoad (UInt256.ofNat 384) mem + UInt256.ofNat 256) mem = callbackPtr := by
    rw [hoffer]
    exact ho.words.load_offset ⟨8, by change 8 < 15; decide⟩ rfl
  by_cases hz : offer.buy = ⟨0⟩
  · have rd1 := midnightBlocks.midnight_block_13456_taken hstack
      (by rw [hbuy, hz]; decide) (by jump_dest) rd
    have ha1 := memoryFundingAt (credit := credit) rd1 (by memory_fund ha)
    simp only [midnightBlocks.midnight_block_13456_taken_stack] at rd1
    have rd2 := midnightBlocks.midnight_block_13759
      (by simp only [List.length_cons]; omega) (by jump_dest) rd1
    have ha2 := memoryFundingAt (credit := credit) rd2 (by memory_fund ha1)
    simp only [midnightBlocks.midnight_block_13759_stack, hcb] at rd2
    simp only [takeSellerDataPtr, if_pos hz]
    exact ⟨_, _, _, ha2, rd2⟩
  · have rd1 := midnightBlocks.midnight_block_13456_fallthrough hstack
      (by rw [hbuy, isZero_eq_zero_of_ne hz]; rfl) rd
    have ha1 := memoryFundingAt (credit := credit) rd1 (by memory_fund ha)
    simp only [midnightBlocks.midnight_block_13456_fallthrough_stack] at rd1
    have rd2 := midnightBlocks.midnight_block_13477
      (by simp only [List.length_cons]; omega) rd1
    have ha2 := memoryFundingAt (credit := credit) rd2 (by memory_fund ha1)
    simp only [midnightBlocks.midnight_block_13477_stack, htaker] at rd2
    simp only [takeSellerDataPtr, if_neg hz]
    exact ⟨_, _, _, ha2, rd2⟩

end Benchmarks.Midnight
