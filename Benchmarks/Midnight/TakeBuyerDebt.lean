import Benchmarks.Midnight.TakeBuyerDebtCalculate
import Benchmarks.Midnight.TakeBuyerDebtWrite

variable {fork : Ethereum.Fork}

/-! The buyer debt assignment agrees with the runtime, including static-mode rejection. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightTakeBuyerDebt {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {offer : OfferData} {mem rdata : ByteArray}
    {aw id units taker buyer debt sellerSlot marketSlot decrease ratifierPtr : UInt256}
    {receiver callback : AccountAddress} {ratifierData data : ByteArray}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 19 ≤ 1024)
    (hf : TakeSourceFrame frame offer id units taker receiver callback ratifierData data)
    (hp : frame.locals.get? "buyerPos" = some (.storageRef (positionRef id buyer) positionType))
    (hi : frame.locals.get? "buyerCreditIncrease" =
      some (.int (takeBuyerCreditIncrease evm id buyer units).toNat))
    (hcanon : buyer.toNat < EVM.addressModulus)
    (hunits : calldataWord I.calldata 68 = units)
    (hs : SourceState s0 I σ evm) (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨12316⟩
      ([positionSlot id buyer, debt, low128 (healthPositionWord evm id buyer), sellerSlot,
        marketSlot, decrease, ratifierPtr, takeBuyerCreditIncrease evm id buyer units] ++ R)
      mem aw rdata σ k C) :
    (ExecBlock fork config frame evm (takeTransition.body.drop 46) .staticViolation ∧
      RDstatic fork midnightBytecode g s0) ∨
    (I.perm = true ∧ ∃ σ' k' C',
      (∀ result, ExecBlock fork config
          (takeBuyerDebtFrame frame units (low128 (healthPositionWord evm id buyer)))
          (takeBuyerDebtState evm id buyer units) (takeTransition.body.drop 48) result →
        ExecBlock fork config frame evm (takeTransition.body.drop 46) result) ∧
      TakeSourceFrame (takeBuyerDebtFrame frame units (low128 (healthPositionWord evm id buyer)))
        offer id units taker receiver callback ratifierData data ∧
      SourceState s0 I σ' (takeBuyerDebtState evm id buyer units) ∧
      MemoryFunding credit mem (M aw (UInt256.ofNat 224) ⟨32⟩) C' ∧
      RD fork midnightBytecode I g s0 ⟨20456⟩
        ([positionFieldWord (takeBuyerDebtState evm id buyer units) id buyer 1,
          memLoad (UInt256.ofNat 224) mem, ⟨4216⟩, ⟨12386⟩, positionSlot id buyer, debt,
          ⟨12505⟩, ⟨2⟩, ⟨12517⟩, uint128Mask, sellerSlot, marketSlot, decrease,
          ratifierPtr, takeBuyerCreditIncrease evm id buyer units] ++ R)
        mem (M aw (UInt256.ofNat 224) ⟨32⟩) rdata σ' k' C') := by
  have hx0 := takeBuyerRepayCall (fork := fork) (evm := evm) hf.contract hf.units hi (low128_lt _)
  have hp1 : (takeBuyerDebtFrame frame units (low128 (healthPositionWord evm id buyer))).locals.get?
      "buyerPos" = some (.storageRef (positionRef id buyer) positionType) :=
    (store_get_ne _ _ (by decide)).trans hp
  obtain ⟨k1, C1, hc1, rd1⟩ := midnightTakeBuyerDebtCalculate hstack (low128_lt _) hunits rd
  simp only [List.cons_append, List.nil_append] at rd1
  rcases midnightTakeBuyerDebtWrite
      (by simp only [List.length_cons]; omega)
      (ha.mono hc1) rd1 with
    ⟨hfalse, hr⟩ | ⟨htrue, k2, C2, ha2, rd2⟩
  · refine Or.inl ⟨?_, hr⟩
    rw [takeBuyerDebt_shape]
    exact ExecBlock.consNormal hx0 (ExecBlock.consStatic
      (takeBuyerDebtWriteStatic hp1 hcanon (wordLocal_get ..) (by rw [hs.env]; exact hfalse)))
  · let value := UInt256.sub (low128 (healthPositionWord evm id buyer))
      (takeBuyerRepayment units (low128 (healthPositionWord evm id buyer)))
    let σ' := storeLow128Accounts σ I (positionSlot id buyer + ⟨2⟩) value
    have hs' : SourceState s0 I σ' (takeBuyerDebtState evm id buyer units) :=
      SourceState.storeLow128 hs _ value
    have hread : UInt256.shiftRight (solcSlotWordAt (positionSlot id buyer) σ' I)
        (UInt256.ofNat 128) =
        positionFieldWord (takeBuyerDebtState evm id buyer units) id buyer 1 := by
      change UInt256.shiftRight (solcSlotWordAt (positionSlot id buyer) σ' I)
        (UInt256.ofNat 128) = UInt256.shiftRight
        (Stele.EVM.storageLoad (takeBuyerDebtState evm id buyer units)
          (takeBuyerDebtState evm id buyer units).executionEnv.codeOwner (positionSlot id buyer))
        (UInt256.ofNat 128)
      rw [hs'.storageRead]
      rfl
    change RD fork midnightBytecode I g s0 ⟨20456⟩
      ([UInt256.shiftRight (solcSlotWordAt (positionSlot id buyer) σ' I) (UInt256.ofNat 128),
        memLoad (UInt256.ofNat 224) mem, ⟨4216⟩, ⟨12386⟩, positionSlot id buyer, debt,
        ⟨12505⟩, ⟨2⟩, ⟨12517⟩, uint128Mask, sellerSlot, marketSlot, decrease,
        ratifierPtr, takeBuyerCreditIncrease evm id buyer units] ++ R)
      mem (M aw (UInt256.ofNat 224) ⟨32⟩) rdata σ' k2 C2 at rd2
    rw [hread] at rd2
    refine Or.inr ⟨htrue, σ', k2, C2, ?_, hf.insert "__c21" _ (by decide), hs', ha2, rd2⟩
    intro result hx
    rw [takeBuyerDebt_shape]
    exact ExecBlock.consNormal hx0 (ExecBlock.consNormal
      (takeBuyerDebtWrite hp1 hcanon (wordLocal_get ..) (by rw [hs.env]; exact htrue)) hx)

end Benchmarks.Midnight
