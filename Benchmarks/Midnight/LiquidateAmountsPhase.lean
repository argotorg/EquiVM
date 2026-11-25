import Benchmarks.Midnight.LiquidateAmounts

variable {fork : Ethereum.Fork}

/-! The conditional amount calculation and storage-update phase of liquidation. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem liquidateAmountsPhase {I : ExecutionEnv} {g : Sat256} {s0 evm : State} {frame : Frame}
    {mem rdata : ByteArray} {aw id index seized repaid borrower mode bitmap maxDebt price
      originalDebt badDebt head dp dl receiverWord selector root : UInt256} {credit : Nat}
    {receiver callback : AccountAddress} {data : ByteArray} {m : MarketData}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (hstack : R.length + 23 ≤ 1024)
    (hf : LiquidateSourceFrame frame m id index seized repaid borrower mode receiver callback data)
    (ha : LiquidateAccumulators frame bitmap maxDebt price originalDebt badDebt)
    (hcanon : borrower.toNat < EVM.addressModulus)
    (hd : decodeCalldataMarket I.calldata 4 = some m) (hi : calldataWord I.calldata 36 = index)
    (hcs : calldataWord I.calldata 68 = seized) (hcr : calldataWord I.calldata 100 = repaid)
    (hms : memLoad ⟨640⟩ mem = seized) (hmr : memLoad ⟨608⟩ mem = repaid)
    (hslot : memLoad ⟨672⟩ mem = solcMappingSlot ⟨1⟩ id)
    (hsize : 704 ≤ mem.size) (hs : SourceState s0 I σ evm)
    (hb : TransferBudget root credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨5468⟩
      ([head, UInt256.isZero (UInt256.isZero repaid), UInt256.isZero repaid, maxDebt, price,
        positionSlot id borrower, dp, dl, borrower, badDebt, receiverWord, mode, selector] ++ R)
      mem aw rdata σ k C) :
    (ExecStmt fork config frame evm (liquidateTransition.body[18]!) .reverted ∧
      RDrev fork midnightBytecode g s0) ∨
    (ExecStmt fork config frame evm (liquidateTransition.body[18]!) .staticViolation ∧
      RDstatic fork midnightBytecode g s0) ∨
    ∃ frame' evm' σ' seized' repaid' mem' d0 d1 d2 aw' k' C',
      ExecStmt fork config frame evm (liquidateTransition.body[18]!) (.ok frame' evm') ∧
      LiquidateSourceFrame frame' m id index seized' repaid' borrower mode receiver callback data ∧
      LiquidateAccumulators frame' bitmap maxDebt price originalDebt badDebt ∧
      SourceState s0 I σ' evm' ∧ memLoad ⟨640⟩ mem' = seized' ∧ memLoad ⟨608⟩ mem' = repaid' ∧
      mem.size ≤ mem'.size ∧
      (∀ read : UInt256, read.toNat + 32 ≤ mem.size →
        (read.toNat + 32 ≤ 608 ∨ 672 ≤ read.toNat) → memLoad read mem' = memLoad read mem) ∧
      TransferBudget root credit mem' aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨5480⟩
        ([d0, d1, d2, dp, dl, borrower, badDebt, receiverWord, mode, selector] ++ R)
        mem' aw' rdata σ' k' C' := by
  have hg := evalLiquidateAmountsGuard (evm := evm) hf.seized hf.repaid
  rcases midnightLiquidateAmountsGuard
    (R := [maxDebt, price, positionSlot id borrower, dp, dl, borrower, badDebt,
      receiverWord, mode, selector] ++ R)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hcs rd with
    ⟨hzs, hzr, k1, C1, hc1, rd1⟩ | ⟨hn, k1, C1, hc1, rd1⟩
  · have hg0 := hg.trans (by simp only [hzs, hzr]; rfl)
    exact Or.inr (Or.inr ⟨frame, evm, σ, seized, repaid, mem,
      maxDebt, price, positionSlot id borrower, aw, k1, C1,
      ExecStmt.iteFalse hg0 ExecBlock.nil, hf, ha, hs, hms, hmr, le_refl _,
      fun _ _ _ ↦ rfl, hb.mono hc1, rd1⟩)
  · have hnpos : 0 < repaid.toNat ∨ 0 < seized.toNat := by
      have positive (w : UInt256) (hw : w ≠ ⟨0⟩) : 0 < w.toNat := by
        by_contra h
        apply hw
        apply u256_inj
        change w.toNat = 0
        omega
      exact hn.elim (fun h ↦ Or.inl (positive _ h)) (fun h ↦ Or.inr (positive _ h))
    have hg1 := hg.trans (by rw [decide_eq_true hnpos])
    rcases liquidateAmounts (R := R) hstack hf ha hcanon hd hi hcs hcr hms hmr hslot hsize
      hs (hb.mono hc1) rd1 with ⟨hx, hr⟩ | ⟨hx, hr⟩ |
        ⟨f2, evm2, σ2, seized2, repaid2, mem2, aw2, k2, C2,
          hx2, hf2, ha2, hs2, hms2, hmr2, hsize2, hmem2, hb2, rd2⟩
    · exact Or.inl ⟨ExecStmt.iteTrue hg1 hx, hr⟩
    · exact Or.inr (Or.inl ⟨ExecStmt.iteTrue hg1 hx, hr⟩)
    · exact Or.inr (Or.inr ⟨f2, evm2, σ2, seized2, repaid2, mem2,
        selector, selector, selector, aw2, k2, C2, ExecStmt.iteTrue hg1 hx2,
        hf2, ha2, hs2, hms2, hmr2, hsize2, hmem2, hb2, rd2⟩)

end Benchmarks.Midnight
