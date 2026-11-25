import Benchmarks.Midnight.TakeSellerDebtBlocks
import Benchmarks.Midnight.TakeBuyerCredit
import Benchmarks.Midnight.MarketBalanceFields

variable {fork : Ethereum.Fork}

/-! The seller debt increase completes the ordered position writes. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def takeSellerDebtWriteFrame (frame : Frame) (debt : UInt256) : Frame :=
  wordLocal frame "__c24" debt

def takeSellerDebtWriteState (evm : State) (id seller debt : UInt256) : State :=
  storeLow128 evm (positionSlot id seller + ⟨2⟩) (low128 (healthPositionWord evm id seller) + debt)

theorem takeSellerDebtWrite_shape : takeTransition.body.drop 54 =
    takeTransition.body[54]! :: takeTransition.body[55]! :: takeTransition.body.drop 56 := rfl

theorem marketTotalSourceWord {s0 evm : State} {I : ExecutionEnv} {σ : AccountMap}
    (hs : SourceState s0 I σ evm) (id : UInt256) :
    marketBalanceWord evm id 0 = low128 (solcSlotWordAt (solcMappingSlot ⟨1⟩ id) σ I) := by
  change low128 (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner (solcMappingSlot ⟨1⟩ id)) = _
  rw [hs.storageRead]
  rfl

set_option maxRecDepth 10000

theorem midnightTakeSellerDebt {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {mem rdata : ByteArray} {aw id seller debt decrease ratifierPtr increase : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024) (hc : frame.contract = contract)
    (hp : frame.locals.get? "sellerPos" = some (.storageRef (positionRef id seller) positionType))
    (hd : frame.locals.get? "sellerDebtIncrease" = some (.int debt.toNat))
    (hcanon : seller.toNat < EVM.addressModulus) (hperm : I.perm = true)
    (hs : SourceState s0 I σ evm) (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨23403⟩
      ([debt, ⟨12505⟩, ⟨2⟩, ⟨12517⟩, uint128Mask, positionSlot id seller,
        solcMappingSlot ⟨1⟩ id, decrease, ratifierPtr, increase] ++ R) mem aw rdata σ k C) :
    (ExecBlock fork config frame evm (takeTransition.body.drop 54) .reverted ∧
      RDrev fork midnightBytecode g s0) ∨
    ∃ σ' k' C',
      (∀ result, ExecBlock fork config (takeSellerDebtWriteFrame frame debt)
          (takeSellerDebtWriteState evm id seller debt) (takeTransition.body.drop 56) result →
        ExecBlock fork config frame evm (takeTransition.body.drop 54) result) ∧
      SourceState s0 I σ' (takeSellerDebtWriteState evm id seller debt) ∧
      MemoryFunding credit mem aw C' ∧
      RD fork midnightBytecode I g s0 ⟨19536⟩
        ([marketBalanceWord (takeSellerDebtWriteState evm id seller debt) id 0,
          increase, ⟨12561⟩, decrease, ⟨4204⟩, ⟨12566⟩, uint128Mask, solcMappingSlot ⟨1⟩ id,
          decrease, ratifierPtr, increase] ++ R) mem aw rdata σ' k' C' := by
  have hargs : evalExprs? config frame evm [.var "sellerDebtIncrease"] = .ok [.int debt.toNat] := by
    simp only [evalExprs?, evalWordLocal hd, bind, pure, EvalResult.bind]
  simp only [List.cons_append, List.nil_append] at rd
  by_cases hd128 : debt.toNat < 2^128
  · have hx0 := callToUint128 (fork := fork) (name := "__c24") hc hargs hd128
    have hp1 : (takeSellerDebtWriteFrame frame debt).locals.get? "sellerPos" =
        some (.storageRef (positionRef id seller) positionType) :=
      (store_get_ne _ _ (by decide)).trans hp
    have he := evalNamedPositionDebt (evm := evm) hcanon hp1
    obtain ⟨k1, C1, hc1, rd1⟩ := midnightToUint128_mono
      (by simp only [List.length_cons]; omega) hd128 (by jump_dest) rd
    obtain ⟨k2, C2, hc2, rd2⟩ := midnightTakeSellerDebtRead
      (by simp only [List.length_cons]; omega) rd1
    rw [← positionDebtSourceWord hs] at rd2
    by_cases hsum : (low128 (healthPositionWord evm id seller)).toNat + debt.toNat < 2^128
    · obtain ⟨k3, C3, hc3, rd3⟩ := midnightCheckedAdd128_mono
        (by simp only [List.length_cons]; omega) (low128_lt _) hd128 hsum (by jump_dest) rd2
      obtain ⟨k4, C4, hc4, rd4⟩ := midnightTakeSellerDebtStore (by omega) hperm rd3
      let σ' := storeLow128Accounts σ I (positionSlot id seller + ⟨2⟩)
        (low128 (healthPositionWord evm id seller) + debt)
      have hs' : SourceState s0 I σ' (takeSellerDebtWriteState evm id seller debt) :=
        SourceState.storeLow128 hs _ _
      have hr := marketTotalSourceWord hs' id
      change marketBalanceWord (takeSellerDebtWriteState evm id seller debt) id 0 =
        low128 (solcSlotWordAt (solcMappingSlot ⟨1⟩ id)
          (storeLow128Accounts σ I (positionSlot id seller + ⟨2⟩)
            (low128 (healthPositionWord evm id seller) + debt)) I) at hr
      rw [← hr] at rd4
      refine Or.inr ⟨σ', k4, C4, ?_, hs', ha.mono (by omega), rd4⟩
      intro result hx
      rw [takeSellerDebtWrite_shape]
      exact ExecBlock.consNormal hx0 (ExecBlock.consNormal
        (ExecStmt.assign (Or.inr (by rw [hs.env]; exact hperm))
          (evalCheckedAdd128 he (evalWordLocal (wordLocal_get ..)) hsum)
          (assignNamedPositionDebt _ hcanon hp1)) hx)
    · refine Or.inl ⟨?_, midnightCheckedAdd128Revert
        (by simp only [List.length_cons]; omega) (low128_lt _) hd128 (Nat.le_of_not_lt hsum) rd2⟩
      rw [takeSellerDebtWrite_shape]
      exact ExecBlock.consNormal hx0 (ExecBlock.consRevert (ExecStmt.assignExprRevert
        (evalCheckedAdd128Overflow he (evalWordLocal (wordLocal_get ..))
          (Nat.le_of_not_lt hsum))))
  · refine Or.inl ⟨?_, midnightToUint128Revert
      (by simp only [List.length_cons]; omega) (Nat.le_of_not_lt hd128) rd⟩
    rw [takeSellerDebtWrite_shape]
    exact ExecBlock.consRevert (callToUint128Revert hc hargs (Nat.le_of_not_lt hd128))

end Benchmarks.Midnight
