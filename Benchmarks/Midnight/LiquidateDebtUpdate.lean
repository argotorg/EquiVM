import Benchmarks.Midnight.LiquidateBalanceGas
import Benchmarks.Midnight.LiquidateAmountsGuard
import Benchmarks.Midnight.ToUint128Source
import Benchmarks.Midnight.CheckedUint128Gas
import Benchmarks.Midnight.PackedStorageSourceState
import Benchmarks.Midnight.TransferBudget

variable {fork : Ethereum.Fork}

/-! The final checked debt subtraction and packed position write in liquidation. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem liquidateDebtUpdate {I : ExecutionEnv} {g : Sat256} {s0 evm : State} {frame : Frame}
    {mem rdata : ByteArray} {aw id index seized repaid borrower mode badDebt dp dl receiverWord
      selector root : UInt256} {credit : Nat} {receiver callback : AccountAddress}
    {data : ByteArray} {m : MarketData} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 17 ≤ 1024)
    (hf : LiquidateSourceFrame frame m id index seized repaid borrower mode receiver callback data)
    (hp : I.perm = true) (h128 : repaid.toNat < 2^128) (hcanon : borrower.toNat < EVM.addressModulus)
    (hs : SourceState s0 I σ evm) (hb : TransferBudget root credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨23403⟩
      ([repaid, ⟨6914⟩, ⟨6925⟩, uint128Mask, ⟨2⟩, positionSlot id borrower, dp, dl,
        borrower, badDebt, receiverWord, mode, selector] ++ R) mem aw rdata σ k C) :
    (ExecBlock fork config frame evm (liquidateAmountsBody.drop 12) .reverted ∧
      RDrev fork midnightBytecode g s0) ∨
    (∃ evm' σ' k' C',
      ExecBlock fork config frame evm (liquidateAmountsBody.drop 12)
        (.ok (wordLocal frame "__c30" repaid) evm') ∧
      SourceState s0 I σ' evm' ∧ TransferBudget root credit mem aw C' ∧
      RD fork midnightBytecode I g s0 ⟨5480⟩
        ([selector, selector, selector, dp, dl, borrower, badDebt, receiverWord, mode, selector] ++ R)
        mem aw rdata σ' k' C') := by
  have ha : evalExprs? config frame evm [.var "repaidUnits"] = .ok [.int repaid.toNat] := by
    simp only [evalExprs?, evalWordLocal hf.repaid, bind, pure, EvalResult.bind]
  have hx0 := callToUint128 (fork := fork) (name := "__c30") hf.contract ha h128
  have hf1 := hf.insert "__c30" (.int repaid.toNat) (by decide)
  obtain ⟨k1, C1, hc1, rd1⟩ := midnightToUint128_mono
    (R := [⟨6925⟩, uint128Mask, ⟨2⟩, positionSlot id borrower, dp, dl,
      borrower, badDebt, receiverWord, mode, selector] ++ R)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    h128 (by jump_dest) rd
  obtain ⟨k2, C2, hc2, rd2⟩ := liquidate_block_6914_paid
    (R := [dp, dl, borrower, badDebt, receiverWord, mode, selector] ++ R)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    (by jump_dest) rd1
  let debt := low128 (healthPositionWord evm id borrower)
  have hw : (σ.get? I.codeOwner |>.option (⟨0⟩ : UInt256)
      (fun ac ↦ ac.storage.getD (positionSlot id borrower + ⟨2⟩) ⟨0⟩)) =
      healthPositionWord evm id borrower := (hs.storageRead _).symm
  simp only [midnightBlocks.midnight_block_6914_stack, hw] at rd2
  have hr : evalExpr? config (wordLocal frame "__c30" repaid) evm
      (.storage { base := "_position", steps := [.field "debt"] }) = .ok (.int debt.toNat) :=
    evalHealthDebt hcanon hf1.position
  by_cases hle : repaid.toNat ≤ debt.toNat
  · obtain ⟨k3, C3, hc3, rd3⟩ := midnightCheckedSub128_mono
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      (low128_lt _) h128 hle (by jump_dest) rd2
    obtain ⟨k4, C4, hc4, rd4⟩ := liquidate_block_6925_paid (R := R)
      (by omega) hp (by jump_dest) rd3
    simp only [midnightBlocks.midnight_block_6925_stack, uint128Mask_computed] at rd4
    let value := UInt256.sub debt repaid
    let evm1 := storeLow128 evm (positionSlot id borrower + ⟨2⟩) value
    let σ1 := storeLow128Accounts σ I (positionSlot id borrower + ⟨2⟩) value
    have hs1 : SourceState s0 I σ1 evm1 := SourceState.storeLow128 hs _ value
    have hx1 : ExecStmt fork config (wordLocal frame "__c30" repaid) evm
        (liquidateAmountsBody[13]!) (.ok (wordLocal frame "__c30" repaid) evm1) :=
      ExecStmt.assign (Or.inr (by rw [hs.env]; exact hp))
        (evalCheckedSub128 hr (evalWordLocal (wordLocal_get ..)) (low128_lt _) hle)
        (assignHealthDebt value hcanon hf1.position)
    exact Or.inr ⟨evm1, σ1, k4, C4, ExecBlock.consNormal hx0
      (ExecBlock.consNormal hx1 ExecBlock.nil), hs1, hb.mono (by omega), rd4⟩
  · exact Or.inl ⟨ExecBlock.consNormal hx0 (ExecBlock.consRevert (ExecStmt.assignExprRevert
      (evalCheckedSubUnderflow ⟨128, by decide⟩ hr (evalWordLocal (wordLocal_get ..))
        (Nat.lt_of_not_ge hle)))), midnightCheckedSub128Revert
          (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
          (low128_lt _) h128 (Nat.lt_of_not_ge hle) rd2⟩

end Benchmarks.Midnight
