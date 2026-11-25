import Benchmarks.Midnight.LiquidateBalanceGas
import Benchmarks.Midnight.LiquidateAmountsGuard
import Benchmarks.Midnight.MarketBalanceFields
import Benchmarks.Midnight.ToUint128Source
import Benchmarks.Midnight.CheckedExtraGas
import Benchmarks.Midnight.CheckedUint128Gas
import Benchmarks.Midnight.PackedStorageSourceState
import Benchmarks.Midnight.TransferBudget

variable {fork : Ethereum.Fork}

/-! Checked conversion and increase of the market's withdrawable balance. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem liquidateWithdrawable {I : ExecutionEnv} {g : Sat256} {s0 evm : State} {frame : Frame}
    {mem rdata : ByteArray} {aw id index seized repaid borrower mode root : UInt256} {credit : Nat}
    {receiver callback : AccountAddress} {data : ByteArray} {m : MarketData}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (hstack : R.length + 9 ≤ 1024)
    (hf : LiquidateSourceFrame frame m id index seized repaid borrower mode receiver callback data)
    (hp : I.perm = true) (hpaid : memLoad ⟨608⟩ mem = repaid)
    (hslot : memLoad ⟨672⟩ mem = solcMappingSlot ⟨1⟩ id)
    (hs : SourceState s0 I σ evm) (hb : TransferBudget root credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨6833⟩ R mem aw rdata σ k C) :
    (ExecBlock fork config frame evm ((liquidateAmountsBody.drop 10).take 2) .reverted ∧
      RDrev fork midnightBytecode g s0) ∨
    (repaid.toNat < 2^128 ∧ ∃ evm' σ' aw' k' C',
      ExecBlock fork config frame evm ((liquidateAmountsBody.drop 10).take 2)
        (.ok (wordLocal frame "__c29" repaid) evm') ∧
      SourceState s0 I σ' evm' ∧ TransferBudget root credit mem aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨23403⟩
        (repaid :: ⟨6914⟩ :: ⟨6925⟩ :: uint128Mask :: ⟨2⟩ :: R) mem aw' rdata σ' k' C') := by
  have ha : evalExprs? config frame evm [.var "repaidUnits"] = .ok [.int repaid.toNat] := by
    simp only [evalExprs?, evalWordLocal hf.repaid, bind, pure, EvalResult.bind]
  have rd1 := midnightBlocks.midnight_block_6833 (R := R) (by omega) (by jump_dest) rd
  have hb1 := transferBudgetAt (root := root) (credit := credit) rd1 (by transfer_budget hb)
  simp only [midnightBlocks.midnight_block_6833_stack,
    show UInt256.ofNat 608 = (⟨608⟩ : UInt256) from rfl, hpaid] at rd1 hb1
  by_cases h128 : repaid.toNat < 2^128
  · have hx0 := callToUint128 (fork := fork) (name := "__c29") hf.contract ha h128
    have hf1 := hf.insert "__c29" (.int repaid.toNat) (by decide)
    obtain ⟨k2, C2, hc2, rd2⟩ := midnightToUint128_mono
      (by omega) h128 (by jump_dest) rd1
    have hb2 := hb1.mono hc2
    obtain ⟨k3, C3, hc3, rd3⟩ := liquidate_block_6845_paid (R := R)
      (by omega) (by jump_dest) rd2
    have hb3 := transferBudgetAt (root := root) (credit := credit) rd3 (by
      simp only [memExpansionCost] at hc3
      transfer_budget hb2)
    let old := marketBalanceWord evm id 1
    have hw : low128 (solcSlotWordAt (solcMappingSlot ⟨1⟩ id + UInt256.ofNat 1) σ I) = old :=
      congrArg low128 (hs.storageRead _).symm
    simp only [midnightBlocks.midnight_block_6845_stack, uint128Mask_computed,
      show UInt256.ofNat 672 = (⟨672⟩ : UInt256) from rfl, hslot] at rd3 hb3
    dsimp only [low128, solcSlotWordAt] at hw
    rw [hw] at rd3
    by_cases hsum : old.toNat + repaid.toNat < 2^128
    · obtain ⟨k4, C4, hc4, rd4⟩ := midnightCheckedAdd128_mono
        (by simp only [List.length_cons]; omega) (marketBalanceWord_lt evm id 1) h128 hsum
        (by jump_dest) rd3
      have hb4 := hb3.mono hc4
      obtain ⟨k5, C5, hc5, rd5⟩ := liquidate_block_6873_paid (R := R)
        (by omega) hp (by jump_dest) rd4
      have hb5 := transferBudgetAt (root := root) (credit := credit) rd5 (by
        simp only [memExpansionCost] at hc5
        transfer_budget hb4)
      simp only [midnightBlocks.midnight_block_6873_stack, uint128Mask_computed,
        show UInt256.ofNat 608 = (⟨608⟩ : UInt256) from rfl, hpaid] at rd5 hb5
      let evm1 := marketBalanceStore evm id 1 (old + repaid)
      let σ1 := storeLow128Accounts σ I (solcMappingSlot ⟨1⟩ id + ⟨1⟩) (old + repaid)
      have hs1 : SourceState s0 I σ1 evm1 :=
        SourceState.storeLow128 hs _ (old + repaid)
      have hx1 : ExecStmt fork config (wordLocal frame "__c29" repaid) evm
          (liquidateAmountsBody[11]!) (.ok (wordLocal frame "__c29" repaid) evm1) :=
        ExecStmt.assign (Or.inr (by rw [hs.env]; exact hp))
          (evalCheckedAdd128 (evalMarketBalance 1 hf1.marketState)
            (evalWordLocal (wordLocal_get ..)) hsum) (assignMarketBalance 1 _ hf1.marketState)
      exact Or.inr ⟨h128, evm1, σ1, _, k5, C5,
        ExecBlock.consNormal hx0 (ExecBlock.consNormal hx1 ExecBlock.nil), hs1, hb5, rd5⟩
    · refine Or.inl ⟨ExecBlock.consNormal hx0 (ExecBlock.consRevert
        (ExecStmt.assignExprRevert (evalCheckedAdd128Overflow (evalMarketBalance 1 hf1.marketState)
          (evalWordLocal (wordLocal_get ..)) (Nat.le_of_not_gt hsum)))),
        midnightCheckedAdd128Revert (by simp only [List.length_cons]; omega)
          (marketBalanceWord_lt evm id 1) h128 (Nat.le_of_not_gt hsum) rd3⟩
  · exact Or.inl ⟨ExecBlock.consRevert (callToUint128Revert hf.contract ha (Nat.le_of_not_gt h128)),
      midnightToUint128Revert (by omega) (Nat.le_of_not_gt h128) rd1⟩

end Benchmarks.Midnight
