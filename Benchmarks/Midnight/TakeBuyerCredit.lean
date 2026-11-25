import Benchmarks.Midnight.TakeBuyerCreditBlocks
import Benchmarks.Midnight.TakeBuyerPendingWrite
import Benchmarks.Midnight.TakeCreditSource
import Benchmarks.Midnight.CheckedUint128Gas

variable {fork : Ethereum.Fork}

/-! The checked buyer credit increase and the subsequent seller pending-fee read. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def takeBuyerCreditWriteFrame (frame : Frame) (increase : UInt256) : Frame :=
  wordLocal frame "__c22" increase

def takeBuyerCreditWriteState (evm : State) (id buyer increase : UInt256) : State :=
  storeLow128 evm (positionSlot id buyer) (positionFieldWord evm id buyer 0 + increase)

theorem takeBuyerCreditWrite_shape : takeTransition.body.drop 49 =
    takeTransition.body[49]! :: takeTransition.body[50]! :: takeTransition.body.drop 51 := rfl

theorem positionPendingSourceWord {s0 evm : State} {I : ExecutionEnv} {σ : AccountMap}
    (hs : SourceState s0 I σ evm) (id user : UInt256) :
    positionFieldWord evm id user 1 =
      UInt256.shiftRight (solcSlotWordAt (positionSlot id user) σ I) (UInt256.ofNat 128) := by
  change UInt256.shiftRight (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner
    (positionSlot id user)) (UInt256.ofNat 128) = _
  rw [hs.storageRead]
  rfl

set_option maxRecDepth 10000

theorem midnightTakeBuyerCredit {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {mem rdata : ByteArray}
    {aw id buyer seller debt marketSlot decrease ratifierPtr increase : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 18 ≤ 1024) (hc : frame.contract = contract)
    (hp : frame.locals.get? "buyerPos" = some (.storageRef (positionRef id buyer) positionType))
    (hi : frame.locals.get? "buyerCreditIncrease" = some (.int increase.toNat))
    (hcanon : buyer.toNat < EVM.addressModulus) (hperm : I.perm = true)
    (hs : SourceState s0 I σ evm) (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨12386⟩
      ([positionSlot id buyer, debt, ⟨12505⟩, ⟨2⟩, ⟨12517⟩, uint128Mask,
        positionSlot id seller, marketSlot, decrease, ratifierPtr, increase] ++ R)
      mem aw rdata σ k C) :
    (ExecBlock fork config frame evm (takeTransition.body.drop 49) .reverted ∧
      RDrev fork midnightBytecode g s0) ∨
    ∃ σ' k' C', increase.toNat < 2^128 ∧
      (∀ result, ExecBlock fork config (takeBuyerCreditWriteFrame frame increase)
          (takeBuyerCreditWriteState evm id buyer increase) (takeTransition.body.drop 51) result →
        ExecBlock fork config frame evm (takeTransition.body.drop 49) result) ∧
      SourceState s0 I σ' (takeBuyerCreditWriteState evm id buyer increase) ∧
      MemoryFunding credit mem (M aw (UInt256.ofNat 160) ⟨32⟩) C' ∧
      RD fork midnightBytecode I g s0 ⟨19743⟩
        ([positionFieldWord (takeBuyerCreditWriteState evm id buyer increase) id seller 1,
          memLoad (UInt256.ofNat 160) mem, ⟨12437⟩, ⟨12469⟩, debt, ⟨12505⟩, ⟨2⟩,
          ⟨12517⟩, uint128Mask, positionSlot id seller, marketSlot, decrease, ratifierPtr,
          increase] ++ R) mem (M aw (UInt256.ofNat 160) ⟨32⟩) rdata σ' k' C' := by
  have hargs : evalExprs? config frame evm [.var "buyerCreditIncrease"] =
      .ok [.int increase.toNat] := by
    simp only [evalExprs?, evalWordLocal hi, bind, pure, EvalResult.bind]
  simp only [List.cons_append, List.nil_append] at rd
  have rd1 := midnightBlocks.midnight_block_12386 (by omega) (by jump_dest) rd
  simp only [midnightBlocks.midnight_block_12386_stack] at rd1
  by_cases hi128 : increase.toNat < 2^128
  · have hx0 := callToUint128 (fork := fork) (name := "__c22") hc hargs hi128
    have hp1 : (takeBuyerCreditWriteFrame frame increase).locals.get? "buyerPos" =
        some (.storageRef (positionRef id buyer) positionType) :=
      (store_get_ne _ _ (by decide)).trans hp
    have he := evalNamedPositionField (evm := evm) 0 hcanon hp1
    obtain ⟨k2, C2, hc2, rd2⟩ := midnightToUint128_mono
      (by simp only [List.length_cons]; omega) hi128 (by jump_dest) rd1
    obtain ⟨k3, C3, hc3, rd3⟩ := midnightTakeBuyerCreditRead
      (by simp only [List.length_cons]; omega) rd2
    rw [← positionCreditSourceWord hs] at rd3
    by_cases hsum : (positionFieldWord evm id buyer 0).toNat + increase.toNat < 2^128
    · obtain ⟨k4, C4, hc4, rd4⟩ := midnightCheckedAdd128_mono
        (by simp only [List.length_cons]; omega) (positionFieldWord_lt evm id buyer 0)
        hi128 hsum (by jump_dest) rd3
      obtain ⟨k5, C5, ha5, rd5⟩ := midnightTakeBuyerCreditStore
        (by simp only [List.length_cons]; omega) hperm (ha.mono (by omega)) rd4
      let σ' := storeLow128Accounts σ I (positionSlot id buyer)
        (positionFieldWord evm id buyer 0 + increase)
      have hs' : SourceState s0 I σ' (takeBuyerCreditWriteState evm id buyer increase) :=
        SourceState.storeLow128 hs _ _
      have hr := positionPendingSourceWord hs' id seller
      change positionFieldWord (takeBuyerCreditWriteState evm id buyer increase) id seller 1 =
        UInt256.shiftRight (solcSlotWordAt (positionSlot id seller)
          (storeLow128Accounts σ I (positionSlot id buyer)
            (positionFieldWord evm id buyer 0 + increase)) I) (UInt256.ofNat 128) at hr
      rw [← hr] at rd5
      refine Or.inr ⟨σ', k5, C5, hi128, ?_, hs', ha5, rd5⟩
      intro result hx
      rw [takeBuyerCreditWrite_shape]
      exact ExecBlock.consNormal hx0 (ExecBlock.consNormal
        (ExecStmt.assign (Or.inr (by rw [hs.env]; exact hperm))
          (evalCheckedAdd128 he (evalWordLocal (wordLocal_get ..)) hsum)
          (assignNamedPositionField 0 _ hcanon hp1)) hx)
    · refine Or.inl ⟨?_, midnightCheckedAdd128Revert
        (by simp only [List.length_cons]; omega) (positionFieldWord_lt evm id buyer 0)
        hi128 (Nat.le_of_not_lt hsum) rd3⟩
      rw [takeBuyerCreditWrite_shape]
      exact ExecBlock.consNormal hx0 (ExecBlock.consRevert (ExecStmt.assignExprRevert
        (evalCheckedAdd128Overflow he (evalWordLocal (wordLocal_get ..))
          (Nat.le_of_not_lt hsum))))
  · refine Or.inl ⟨?_, midnightToUint128Revert
      (by simp only [List.length_cons]; omega) (Nat.le_of_not_lt hi128) rd1⟩
    rw [takeBuyerCreditWrite_shape]
    exact ExecBlock.consRevert (callToUint128Revert hc hargs (Nat.le_of_not_lt hi128))

end Benchmarks.Midnight
