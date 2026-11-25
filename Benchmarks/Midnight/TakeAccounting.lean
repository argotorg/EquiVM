import Benchmarks.Midnight.TakeAccountingStore
import Benchmarks.Midnight.TakeAccountingSource
import Benchmarks.Midnight.TakeMarketTotal

variable {fork : Ethereum.Fork}

/-! The final accounting updates before callbacks are selected and the trade is logged. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def takeAccountingState (evm : State) (offer : OfferData) (bought sold value : UInt256) : State :=
  storeLow128 (takeSettlementState evm offer (UInt256.sub bought sold))
    (consumedSlot offer.group (UInt256.ofNat offer.maker.val)) value

def takeAccountingMemory (mem : ByteArray) (offer : OfferData) : ByteArray :=
  consumedHashMemory (takeSettlementMemory mem offer) offer.group (UInt256.ofNat offer.maker.val)

def takeAssetDifferenceExpr : Expr :=
  .inRange (.uint ⟨256, by decide⟩) (.binary .sub (.var "buyerAssets") (.var "sellerAssets"))

def takeSettlementExpr : Expr :=
  .inRange (.uint ⟨256, by decide⟩) (.binary .add (.storage takeSettlementRef) takeAssetDifferenceExpr)

theorem takeAccounting_shape : takeTransition.body.drop 58 =
    .assign .storage takeSettlementRef takeSettlementExpr ::
    .assign .storage takeConsumedRef (.cast (.var "newConsumed")
      (.elem (.int packedUInt128Int))) :: takeTransition.body.drop 60 := rfl

set_option maxRecDepth 10000

theorem midnightTakeAccounting {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {mem rdata : ByteArray}
    {aw bought sold value marketPtr arrayPtr callbackPtr root : UInt256}
    {offer : OfferData} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024) (hc : frame.contract = contract)
    (hn : frame.locals.get? "claimableSettlementFee" = none)
    (hcn : frame.locals.get? "consumed" = none)
    (hof : frame.locals.get? "offer" = some (Model.offerValue offer.value))
    (hb : frame.locals.get? "buyerAssets" = some (.int bought.toNat))
    (hsold : frame.locals.get? "sellerAssets" = some (.int sold.toNat))
    (hv : frame.locals.get? "newConsumed" = some (.int value.toNat))
    (hv128 : value.toNat < 2^128) (hperm : I.perm = true)
    (ho : OfferStored mem ⟨832⟩ marketPtr arrayPtr callbackPtr root offer)
    (hoffer : memLoad (UInt256.ofNat 384) mem = ⟨832⟩)
    (hvalue : memLoad (UInt256.ofNat 480) mem = value)
    (hs : SourceState s0 I σ evm) (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨19447⟩
      (bought :: sold :: ⟨12598⟩ :: R) mem aw rdata σ k C) :
    (ExecBlock fork config frame evm (takeTransition.body.drop 58) .reverted ∧
      RDrev fork midnightBytecode g s0) ∨
    ∃ σ' aw' k' C', sold.toNat ≤ bought.toNat ∧
      (∀ result, ExecBlock fork config frame (takeAccountingState evm offer bought sold value)
          (takeTransition.body.drop 60) result →
        ExecBlock fork config frame evm (takeTransition.body.drop 58) result) ∧
      SourceState s0 I σ' (takeAccountingState evm offer bought sold value) ∧
      MemoryFunding credit (takeAccountingMemory mem offer) aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨12719⟩ (offer.buy :: R)
        (takeAccountingMemory mem offer) aw' rdata σ' k' C' := by
  have hefee := evalTakeSettlement (evm := evm) hc hn hof
  have heb := evalWordLocal (cfg := config) (evm := evm) hb
  have hes := evalWordLocal (cfg := config) (evm := evm) hsold
  by_cases hsub : sold.toNat ≤ bought.toNat
  · have hesub : evalExpr? config frame evm takeAssetDifferenceExpr =
        .ok (.int (UInt256.sub bought sold).toNat) :=
      uint256RangeSourceOk (subSourceOk heb hes hsub) (UInt256.sub bought sold).val.isLt
    obtain ⟨k1, C1, hc1, rd1⟩ := midnightCheckedSub_mono (by omega) hsub (by jump_dest) rd
    obtain ⟨aw2, k2, C2, ha2, rd2⟩ := midnightTakeSettlementRead (by omega)
      ho hoffer (ha.mono hc1) rd1
    have hfee : claimSettlementBalance evm offer.market.loanToken =
        solcSlotWordAt (claimSettlementSlot offer.market.loanToken) σ I := hs.storageRead _
    rw [← hfee] at rd2
    by_cases hadd : (claimSettlementBalance evm offer.market.loanToken).toNat +
        (UInt256.sub bought sold).toNat < UInt256.size
    · obtain ⟨k3, C3, hc3, rd3⟩ := midnightCheckedAdd_mono
        (by simp only [List.length_cons]; omega) hadd (by jump_dest) rd2
      have hmem : 512 ≤ mem.size := by
        have h := ho.words.size
        change 832 + 32 * 15 ≤ mem.size at h
        omega
      have hp := twoWordHashMem_prefix mem (UInt256.ofNat offer.market.loanToken.val)
        (UInt256.ofNat 6) root.toNat
      have hoffer2 : memLoad (UInt256.ofNat 384) (takeSettlementMemory mem offer) = ⟨832⟩ := by
        rw [takeSettlementMemory, memLoad_twoWordHashMem _ _ (UInt256.ofNat 384)
          (by decide) (by change 416 ≤ mem.size; omega), hoffer]
      have hv2 : memLoad (UInt256.ofNat 480) (takeSettlementMemory mem offer) = value := by
        rw [takeSettlementMemory, memLoad_twoWordHashMem _ _ (UInt256.ofNat 480)
          (by decide) hmem, hvalue]
      obtain ⟨aw4, k4, C4, ha4, rd4⟩ := midnightTakeAccountingStore (by omega) hperm
        (ho.preserve hp) hoffer2 hv2 (ha2.mono hc3) rd3
      have hsf : SourceState s0 I
          (sstoreAccountMap I.codeOwner σ (claimSettlementSlot offer.market.loanToken)
            (claimSettlementBalance evm offer.market.loanToken + UInt256.sub bought sold))
          (takeSettlementState evm offer (UInt256.sub bought sold)) := by
        simpa only [hfee] using hs.readModifyWrite
          (claimSettlementSlot offer.market.loanToken) (fun old ↦ old + UInt256.sub bought sold)
      refine Or.inr ⟨_, aw4, k4, C4, hsub, ?_, SourceState.storeLow128 hsf _ _, ha4, rd4⟩
      intro result hx
      rw [takeAccounting_shape]
      apply ExecBlock.consNormal (ExecStmt.assign (Or.inr (by rw [hs.env]; exact hperm))
        (checkedAddSourceOk hefee hesub hadd) (assignTakeSettlement _ hc hn hof))
      apply ExecBlock.consNormal (ExecStmt.assign (Or.inr (by rw [hsf.env]; exact hperm))
        _ (assignTakeConsumed value hc hcn hof)) hx
      simpa only [low128, uint128Mask_clean hv128] using
        evalCast128 (evalWordLocal (evm := takeSettlementState evm offer
          (UInt256.sub bought sold)) hv)
    · refine Or.inl ⟨?_, midnightCheckedAddRevert
        (by simp only [List.length_cons]; omega) (Nat.le_of_not_lt hadd) rd2⟩
      rw [takeAccounting_shape]
      exact ExecBlock.consRevert (ExecStmt.assignExprRevert
        (checkedAddSourceOverflow hefee hesub (Nat.le_of_not_lt hadd)))
  · refine Or.inl ⟨?_, midnightCheckedSubRevert (by omega) (Nat.lt_of_not_ge hsub) rd⟩
    have hesub : evalExpr? config frame evm takeAssetDifferenceExpr = .revert :=
      evalCheckedSubUnderflow ⟨256, by decide⟩ heb hes (Nat.lt_of_not_ge hsub)
    rw [takeAccounting_shape]
    apply ExecBlock.consRevert (ExecStmt.assignExprRevert _)
    rw [takeSettlementExpr, evalExpr?, evalExpr_binary_nonshort (by decide) (by decide),
      hefee, hesub]
    rfl

end Benchmarks.Midnight
