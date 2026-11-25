import Benchmarks.Midnight.TakeAmountsSource
import Benchmarks.Midnight.TakeAmountsMemory

variable {fork : Ethereum.Fork}

/-! Source/runtime correspondence for both take asset amounts. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightTakeAmounts {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {mem rdata : ByteArray}
    {aw marketPtr arrayPtr callbackPtr root id units taker buyerPrice sellerPrice : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} {offer : OfferData}
    {receiver callback : AccountAddress} {ratifierData data : ByteArray}
    (hstack : R.length + 8 ≤ 1024)
    (hf : TakeSourceFrame frame offer id units taker receiver callback ratifierData data)
    (hb : frame.locals.get? "buyerPrice" = some (.int buyerPrice.toNat))
    (hs : frame.locals.get? "sellerPrice" = some (.int sellerPrice.toNat))
    (ho : OfferStored mem ⟨832⟩ marketPtr arrayPtr callbackPtr root offer)
    (hroot : memLoad (UInt256.ofNat 384) mem = ⟨832⟩)
    (hunits : calldataWord I.calldata 68 = units) (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨11591⟩ (buyerPrice :: sellerPrice :: R)
      mem aw rdata σ k C) :
    (ExecBlock fork config frame evm (takeTransition.body.drop 22) .reverted ∧
      RDrev fork midnightBytecode g s0) ∨
    (ABlock fork config evm frame (takeTransition.body.drop 22)
        (takeAmountsFrame frame offer.buy units buyerPrice sellerPrice)
        (takeTransition.body.drop 25) ∧
      TakeSourceFrame (takeAmountsFrame frame offer.buy units buyerPrice sellerPrice)
        offer id units taker receiver callback ratifierData data ∧
      ∃ aw' k' C',
        MemoryFunding credit (takeAmountsMemory mem (takeAmount offer.buy units buyerPrice)
          (takeAmount offer.buy units sellerPrice)) aw' C' ∧
        RD fork midnightBytecode I g s0 ⟨11681⟩ R
          (takeAmountsMemory mem (takeAmount offer.buy units buyerPrice)
            (takeAmount offer.buy units sellerPrice)) aw' rdata σ k' C') := by
  have hbuy : memLoad (UInt256.ofNat 32 + memLoad (UInt256.ofNat 384) mem) mem = offer.buy := by
    rw [hroot, u256_add_comm]
    exact ho.words.load_offset ⟨1, by change 1 < 15; decide⟩ rfl
  rcases midnightTakeBuyerAmount (by simp only [List.length_cons]; omega) hbuy hunits ha rd with
    ⟨hbad, hr⟩ | ⟨hsafe, aw1, k1, C1, ha1, rd1⟩
  · exact Or.inl ⟨takeAmountsSourceRevert hf.contract hf.units hf.offerValue hb hs
      (fun h ↦ hbad h.1), hr⟩
  · have ho1 := takeAmountMemory_offer (off := 256) ho (by decide)
      (takeAmount offer.buy units buyerPrice)
    have hroot1 : memLoad (UInt256.ofNat 384)
        (takeAmountMemory mem 256 (takeAmount offer.buy units buyerPrice)) = ⟨832⟩ := by
      rw [takeAmountMemory_load _ _ _ (by
        have hm := ho.words.size
        change 832 + 32 * 15 ≤ mem.size at hm
        change 384 + 32 ≤ mem.size
        omega) (Or.inr (by decide)), hroot]
    have hbuy1 : memLoad (UInt256.ofNat 32 + memLoad (UInt256.ofNat 384)
        (takeAmountMemory mem 256 (takeAmount offer.buy units buyerPrice)))
        (takeAmountMemory mem 256 (takeAmount offer.buy units buyerPrice)) = offer.buy := by
      rw [hroot1, u256_add_comm]
      exact ho1.words.load_offset ⟨1, by change 1 < 15; decide⟩ rfl
    rcases midnightTakeSellerAmount (by omega) hbuy1 hunits ha1 rd1 with
      ⟨hbad, hr⟩ | ⟨hsafe2, aw2, k2, C2, ha2, rd2⟩
    · exact Or.inl ⟨takeAmountsSourceRevert hf.contract hf.units hf.offerValue hb hs
        (fun h ↦ hbad h.2), hr⟩
    · exact Or.inr ⟨takeAmountsSource hf.contract hf.units hf.offerValue hb hs ⟨hsafe, hsafe2⟩,
        hf.amounts, aw2, k2, C2, ha2, rd2⟩

end Benchmarks.Midnight
