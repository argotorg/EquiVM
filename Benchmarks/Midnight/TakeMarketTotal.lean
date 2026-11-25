import Benchmarks.Midnight.TakeMarketStore
import Benchmarks.Midnight.TakeSellerDebt
import Benchmarks.Midnight.CheckedAddGas

variable {fork : Ethereum.Fork}

/-! Checked market total-units arithmetic, followed by its packed write. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def takeMarketTotalValue (evm : State) (id increase decrease : UInt256) : UInt256 :=
  UInt256.sub (marketBalanceWord evm id 0 + increase) decrease

def takeMarketTotalFrame (frame : Frame) (value : UInt256) : Frame :=
  wordLocal frame "__c25" value

def takeMarketTotalState (evm : State) (id increase decrease : UInt256) : State :=
  marketBalanceStore evm id 0 (takeMarketTotalValue evm id increase decrease)

def takeMarketTotalAddExpr : Expr :=
  .inRange (.uint ⟨256, by decide⟩) (.binary .add
    (.storage { base := "_marketState", steps := [.field "totalUnits"] })
    (.var "buyerCreditIncrease"))

def takeMarketTotalExpr : Expr :=
  .inRange (.uint ⟨256, by decide⟩)
    (.binary .sub takeMarketTotalAddExpr (.var "sellerCreditDecrease"))

theorem takeMarketTotal_shape : takeTransition.body.drop 56 =
    .internalCall "UtilsLib_toUint128" [takeMarketTotalExpr] "__c25" ::
    takeTransition.body[57]! :: takeTransition.body.drop 58 := rfl

set_option maxRecDepth 10000

theorem midnightTakeMarketTotal {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {mem rdata : ByteArray} {aw id decrease increase : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024) (hc : frame.contract = contract)
    (hm : frame.locals.get? "_marketState" = some (.storageRef (marketStateRef id) marketStateType))
    (hi : frame.locals.get? "buyerCreditIncrease" = some (.int increase.toNat))
    (hd : frame.locals.get? "sellerCreditDecrease" = some (.int decrease.toNat))
    (hperm : I.perm = true) (hs : SourceState s0 I σ evm) (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨19536⟩
      ([marketBalanceWord evm id 0, increase, ⟨12561⟩, decrease, ⟨4204⟩, ⟨12566⟩,
        uint128Mask, solcMappingSlot ⟨1⟩ id] ++ R) mem aw rdata σ k C) :
    (ExecBlock fork config frame evm (takeTransition.body.drop 56) .reverted ∧
      RDrev fork midnightBytecode g s0) ∨
    ∃ σ' k' C',
      (∀ result, ExecBlock fork config
          (takeMarketTotalFrame frame (takeMarketTotalValue evm id increase decrease))
          (takeMarketTotalState evm id increase decrease) (takeTransition.body.drop 58) result →
        ExecBlock fork config frame evm (takeTransition.body.drop 56) result) ∧
      SourceState s0 I σ' (takeMarketTotalState evm id increase decrease) ∧
      MemoryFunding credit mem
        (M (M aw (UInt256.ofNat 416) ⟨32⟩) (UInt256.ofNat 256) ⟨32⟩) C' ∧
      RD fork midnightBytecode I g s0 ⟨19447⟩
        (memLoad (UInt256.ofNat 256) mem :: memLoad (UInt256.ofNat 416) mem :: ⟨12598⟩ :: R)
        mem (M (M aw (UInt256.ofNat 416) ⟨32⟩) (UInt256.ofNat 256) ⟨32⟩) rdata σ' k' C' := by
  simp only [List.cons_append, List.nil_append] at rd
  have he0 := evalMarketBalance (evm := evm) 0 hm
  have hei := evalWordLocal (cfg := config) (evm := evm) hi
  have hed := evalWordLocal (cfg := config) (evm := evm) hd
  by_cases hadd : (marketBalanceWord evm id 0).toNat + increase.toNat < UInt256.size
  · have headd : evalExpr? config frame evm takeMarketTotalAddExpr =
        .ok (.int (marketBalanceWord evm id 0 + increase).toNat) :=
      checkedAddSourceOk he0 hei hadd
    obtain ⟨k1, C1, hc1, rd1⟩ := midnightCheckedAdd_mono
      (by simp only [List.length_cons]; omega) hadd (by jump_dest) rd
    have rd2 := midnightBlocks.midnight_block_12561
      (by simp only [List.length_cons]; omega) (by jump_dest) rd1
    by_cases hsub : decrease.toNat ≤ (marketBalanceWord evm id 0 + increase).toNat
    · have he : evalExpr? config frame evm takeMarketTotalExpr =
          .ok (.int (takeMarketTotalValue evm id increase decrease).toNat) :=
        uint256RangeSourceOk (subSourceOk headd hed hsub) (takeMarketTotalValue evm id increase decrease).val.isLt
      have hargs : evalExprs? config frame evm [takeMarketTotalExpr] =
          .ok [.int (takeMarketTotalValue evm id increase decrease).toNat] := by
        simp only [evalExprs?, he, bind, pure, EvalResult.bind]
      obtain ⟨k3, C3, hc3, rd3⟩ := midnightCheckedSub_mono
        (by simp only [List.length_cons]; omega) hsub (by jump_dest) rd2
      have rd4 := midnightBlocks.midnight_block_4204
        (by simp only [List.length_cons]; omega) (by jump_dest) rd3
      by_cases h128 : (takeMarketTotalValue evm id increase decrease).toNat < 2^128
      · obtain ⟨k5, C5, hc5, rd5⟩ := midnightToUint128_mono
          (by simp only [List.length_cons]; omega) h128 (by jump_dest) rd4
        obtain ⟨k6, C6, ha6, rd6⟩ := midnightTakeMarketStore (by omega)
          hperm (ha.mono (by omega)) rd5
        have hm1 : (takeMarketTotalFrame frame
            (takeMarketTotalValue evm id increase decrease)).locals.get? "_marketState" =
            some (.storageRef (marketStateRef id) marketStateType) :=
          (store_get_ne _ _ (by decide)).trans hm
        refine Or.inr ⟨_, k6, C6, ?_, SourceState.storeLow128 hs _ _, ha6, rd6⟩
        intro result hx
        rw [takeMarketTotal_shape]
        exact ExecBlock.consNormal (callToUint128 hc hargs h128) (ExecBlock.consNormal
          (ExecStmt.assign (Or.inr (by rw [hs.env]; exact hperm))
            (evalWordLocal (wordLocal_get ..)) (assignMarketBalance 0 _ hm1)) hx)
      · refine Or.inl ⟨?_, midnightToUint128Revert
          (by simp only [List.length_cons]; omega) (Nat.le_of_not_lt h128) rd4⟩
        rw [takeMarketTotal_shape]
        exact ExecBlock.consRevert (callToUint128Revert hc hargs (Nat.le_of_not_lt h128))
    · refine Or.inl ⟨?_, midnightCheckedSubRevert
        (by simp only [List.length_cons]; omega) (Nat.lt_of_not_ge hsub) rd2⟩
      have he : evalExpr? config frame evm takeMarketTotalExpr = .revert :=
        evalCheckedSubUnderflow ⟨256, by decide⟩ headd hed (Nat.lt_of_not_ge hsub)
      rw [takeMarketTotal_shape]
      apply ExecBlock.consRevert (ExecStmt.internalCallArgsRevert _)
      simp only [evalExprs?, he, bind, EvalResult.bind]
  · refine Or.inl ⟨?_, midnightCheckedAddRevert
      (by simp only [List.length_cons]; omega) (Nat.le_of_not_lt hadd) rd⟩
    have he : evalExpr? config frame evm takeMarketTotalAddExpr = .revert :=
      checkedAddSourceOverflow he0 hei (Nat.le_of_not_lt hadd)
    rw [takeMarketTotal_shape]
    apply ExecBlock.consRevert (ExecStmt.internalCallArgsRevert _)
    simp only [evalExprs?, takeMarketTotalExpr, evalExpr?, he, bind, EvalResult.bind]

end Benchmarks.Midnight
