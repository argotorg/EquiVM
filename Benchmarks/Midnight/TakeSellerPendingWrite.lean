import Benchmarks.Midnight.TakeSellerPendingStore
import Benchmarks.Midnight.TakeBuyerCredit

variable {fork : Ethereum.Fork}

/-! The seller pending-fee subtraction uses storage after the buyer writes. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def takeSellerPendingWriteState (evm : State) (id seller fee : UInt256) : State :=
  storeHigh128 evm (positionSlot id seller) (UInt256.sub (positionFieldWord evm id seller 1) fee)

theorem takeSellerPendingWrite_shape : takeTransition.body.drop 51 =
    takeTransition.body[51]! :: takeTransition.body.drop 52 := rfl

set_option maxRecDepth 10000

theorem midnightTakeSellerPendingWrite {credit : Nat} {I : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {frame : Frame} {mem rdata : ByteArray} {aw id seller fee debt : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024)
    (hp : frame.locals.get? "sellerPos" = some (.storageRef (positionRef id seller) positionType))
    (hf : frame.locals.get? "sellerPendingFeeDecrease" = some (.int fee.toNat))
    (hcanon : seller.toNat < EVM.addressModulus) (hfee : fee.toNat < 2^128)
    (hperm : I.perm = true) (hs : SourceState s0 I σ evm)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨19743⟩
      ([positionFieldWord evm id seller 1, fee, ⟨12437⟩, ⟨12469⟩, debt, ⟨12505⟩, ⟨2⟩,
        ⟨12517⟩, uint128Mask, positionSlot id seller] ++ R) mem aw rdata σ k C) :
    (ExecBlock fork config frame evm (takeTransition.body.drop 51) .reverted ∧
      RDrev fork midnightBytecode g s0) ∨
    ∃ σ' k' C',
      (∀ result, ExecBlock fork config frame (takeSellerPendingWriteState evm id seller fee)
          (takeTransition.body.drop 52) result →
        ExecBlock fork config frame evm (takeTransition.body.drop 51) result) ∧
      SourceState s0 I σ' (takeSellerPendingWriteState evm id seller fee) ∧
      MemoryFunding credit mem aw C' ∧
      RD fork midnightBytecode I g s0 ⟨12469⟩
        ([debt, ⟨12505⟩, ⟨2⟩, ⟨12517⟩, uint128Mask, positionSlot id seller] ++ R)
        mem aw rdata σ' k' C' := by
  have he := evalNamedPositionField (evm := evm) 1 hcanon hp
  simp only [List.cons_append, List.nil_append] at rd
  by_cases hle : fee.toNat ≤ (positionFieldWord evm id seller 1).toNat
  · obtain ⟨k1, C1, hc1, rd1⟩ := midnightCheckedSub128_mono
      (by simp only [List.length_cons]; omega) (positionFieldWord_lt evm id seller 1)
      hfee hle (by jump_dest) rd
    obtain ⟨k2, C2, hc2, rd2⟩ := midnightTakeSellerPendingStore
      (by omega) hperm (by jump_dest) rd1
    let σ' := storeHigh128Accounts σ I (positionSlot id seller)
      (UInt256.sub (positionFieldWord evm id seller 1) fee)
    have hs' : SourceState s0 I σ' (takeSellerPendingWriteState evm id seller fee) :=
      SourceState.storeHigh128 hs _ _
    refine Or.inr ⟨σ', k2, C2, ?_, hs', ha.mono (by omega), rd2⟩
    intro result hx
    rw [takeSellerPendingWrite_shape]
    exact ExecBlock.consNormal (ExecStmt.assign (Or.inr (by rw [hs.env]; exact hperm))
      (evalCheckedSub128 he (evalWordLocal hf) (positionFieldWord_lt evm id seller 1) hle)
      (assignNamedPositionField 1 _ hcanon hp)) hx
  · refine Or.inl ⟨?_, midnightCheckedSub128Revert
      (by simp only [List.length_cons]; omega) (positionFieldWord_lt evm id seller 1)
      hfee (Nat.lt_of_not_ge hle) rd⟩
    rw [takeSellerPendingWrite_shape]
    exact ExecBlock.consRevert (ExecStmt.assignExprRevert
      (evalCheckedSubUnderflow ⟨128, by decide⟩ he (evalWordLocal hf) (Nat.lt_of_not_ge hle)))

end Benchmarks.Midnight
