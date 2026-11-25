import Benchmarks.Midnight.TakeSellerCreditBlocks
import Benchmarks.Midnight.TakeBuyerCredit

variable {fork : Ethereum.Fork}

/-! Checked narrowing and subtraction of the seller's credit. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def takeSellerCreditWriteFrame (frame : Frame) (decrease : UInt256) : Frame :=
  wordLocal frame "__c23" decrease

def takeSellerCreditWriteState (evm : State) (id seller decrease : UInt256) : State :=
  storeLow128 evm (positionSlot id seller) (UInt256.sub (positionFieldWord evm id seller 0) decrease)

theorem takeSellerCreditWrite_shape : takeTransition.body.drop 52 =
    takeTransition.body[52]! :: takeTransition.body[53]! :: takeTransition.body.drop 54 := rfl

set_option maxRecDepth 10000

theorem midnightTakeSellerCredit {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {mem rdata : ByteArray} {aw id seller debt marketSlot decrease : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 15 ≤ 1024) (hc : frame.contract = contract)
    (hp : frame.locals.get? "sellerPos" = some (.storageRef (positionRef id seller) positionType))
    (hd : frame.locals.get? "sellerCreditDecrease" = some (.int decrease.toNat))
    (hcanon : seller.toNat < EVM.addressModulus) (hperm : I.perm = true)
    (hs : SourceState s0 I σ evm) (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨12469⟩
      ([debt, ⟨12505⟩, ⟨2⟩, ⟨12517⟩, uint128Mask, positionSlot id seller, marketSlot,
        decrease] ++ R) mem aw rdata σ k C) :
    (ExecBlock fork config frame evm (takeTransition.body.drop 52) .reverted ∧
      RDrev fork midnightBytecode g s0) ∨
    ∃ σ' k' C', decrease.toNat < 2^128 ∧
      (∀ result, ExecBlock fork config (takeSellerCreditWriteFrame frame decrease)
          (takeSellerCreditWriteState evm id seller decrease) (takeTransition.body.drop 54) result →
        ExecBlock fork config frame evm (takeTransition.body.drop 52) result) ∧
      SourceState s0 I σ' (takeSellerCreditWriteState evm id seller decrease) ∧
      MemoryFunding credit mem aw C' ∧
      RD fork midnightBytecode I g s0 ⟨23403⟩
        ([debt, ⟨12505⟩, ⟨2⟩, ⟨12517⟩, uint128Mask, positionSlot id seller, marketSlot,
          decrease] ++ R) mem aw rdata σ' k' C' := by
  have hargs : evalExprs? config frame evm [.var "sellerCreditDecrease"] =
      .ok [.int decrease.toNat] := by
    simp only [evalExprs?, evalWordLocal hd, bind, pure, EvalResult.bind]
  simp only [List.cons_append, List.nil_append] at rd
  have rd1 := midnightBlocks.midnight_block_12469 (by omega) (by jump_dest) rd
  simp only [midnightBlocks.midnight_block_12469_stack] at rd1
  by_cases hd128 : decrease.toNat < 2^128
  · have hx0 := callToUint128 (fork := fork) (name := "__c23") hc hargs hd128
    have hp1 : (takeSellerCreditWriteFrame frame decrease).locals.get? "sellerPos" =
        some (.storageRef (positionRef id seller) positionType) :=
      (store_get_ne _ _ (by decide)).trans hp
    have he := evalNamedPositionField (evm := evm) 0 hcanon hp1
    obtain ⟨k2, C2, hc2, rd2⟩ := midnightToUint128_mono
      (by simp only [List.length_cons]; omega) hd128 (by jump_dest) rd1
    obtain ⟨k3, C3, hc3, rd3⟩ := midnightTakeSellerCreditBalanceRead
      (by simp only [List.length_cons]; omega) rd2
    simp only [List.cons_append, List.nil_append] at rd3
    rw [← positionCreditSourceWord hs] at rd3
    by_cases hle : decrease.toNat ≤ (positionFieldWord evm id seller 0).toNat
    · obtain ⟨k4, C4, hc4, rd4⟩ := midnightCheckedSub128_mono
        (by simp only [List.length_cons]; omega) (positionFieldWord_lt evm id seller 0)
        hd128 hle (by jump_dest) rd3
      obtain ⟨k5, C5, hc5, rd5⟩ := midnightTakeSellerCreditStore
        (by simp only [List.length_cons]; omega) hperm rd4
      let σ' := storeLow128Accounts σ I (positionSlot id seller)
        (UInt256.sub (positionFieldWord evm id seller 0) decrease)
      have hs' : SourceState s0 I σ' (takeSellerCreditWriteState evm id seller decrease) :=
        SourceState.storeLow128 hs _ _
      refine Or.inr ⟨σ', k5, C5, hd128, ?_, hs', ha.mono (by omega), rd5⟩
      intro result hx
      rw [takeSellerCreditWrite_shape]
      exact ExecBlock.consNormal hx0 (ExecBlock.consNormal
        (ExecStmt.assign (Or.inr (by rw [hs.env]; exact hperm))
          (evalCheckedSub128 he (evalWordLocal (wordLocal_get ..))
            (positionFieldWord_lt evm id seller 0) hle)
          (assignNamedPositionField 0 _ hcanon hp1)) hx)
    · refine Or.inl ⟨?_, midnightCheckedSub128Revert
        (by simp only [List.length_cons]; omega) (positionFieldWord_lt evm id seller 0)
        hd128 (Nat.lt_of_not_ge hle) rd3⟩
      rw [takeSellerCreditWrite_shape]
      exact ExecBlock.consNormal hx0 (ExecBlock.consRevert (ExecStmt.assignExprRevert
        (evalCheckedSubUnderflow ⟨128, by decide⟩ he (evalWordLocal (wordLocal_get ..))
          (Nat.lt_of_not_ge hle))))
  · refine Or.inl ⟨?_, midnightToUint128Revert
      (by simp only [List.length_cons]; omega) (Nat.le_of_not_lt hd128) rd1⟩
    rw [takeSellerCreditWrite_shape]
    exact ExecBlock.consRevert (callToUint128Revert hc hargs (Nat.le_of_not_lt hd128))

end Benchmarks.Midnight
