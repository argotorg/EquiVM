import Benchmarks.Midnight.SupplyNewCollateral
import Benchmarks.Midnight.SupplyCollateralTail

variable {fork : Ethereum.Fork}

/-! Joining the optional first-collateral branch to the final supply path. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem supplyCollateralIf {I : ExecutionEnv} {g : UInt256} {s0 evm : State}
    {frame : Frame} {m : MarketData} {mem rdata : ByteArray}
    {aw market array limit root check old index id user assets extra : UInt256}
    {token : AccountAddress} {credit k C : Nat} {R : List UInt256}
    (hs : SourceState s0 I evm.accountMap evm)
    (hf : SupplySourceFrame frame m id user index assets old token)
    (hcanon : user.toNat < EVM.addressModulus) (hi : index.toNat < 128)
    (hindex : index.toNat < m.collaterals.length)
    (hcheck : check ≠ ⟨0⟩ ↔ old = ⟨0⟩ ∧ assets ≠ ⟨0⟩)
    (hstack : R.length + 26 ≤ 1024) (hmem : 128 ≤ mem.size)
    (hm : MarketStored mem market array limit m)
    (hroot : root.toNat + 32 < 2^64) (hlower : 128 ≤ root.toNat)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (hb : TransferBudget root credit mem aw C)
    (hb32 : TransferBudget (root + UInt256.ofNat 32) credit mem aw C)
    (hcredit : 4 * ((root.toNat + safeTransferCallAllocation true + 31) / 32) ≤ credit + 999921)
    (hcredit32 : 4 * (((root + UInt256.ofNat 32).toNat + safeTransferCallAllocation true + 31) / 32)
      ≤ credit + 999921)
    (hgas : midnightGasBound g) (hfork : fork ≥ .osaka)
    (rd : RD fork midnightBytecode I (Sat256.ofUInt256 g) s0 ⟨17119⟩
      ([check, market + UInt256.ofNat 96, positionSlot id user, old, index, id, user,
        UInt256.ofNat token.val, assets, positionSlot id user + UInt256.ofNat 3, extra] ++ R)
      mem aw rdata evm.accountMap k C) :
    X fork (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (RDrev fork midnightBytecode (Sat256.ofUInt256 g) s0 ∧
      ExecBlock fork config frame evm (supplyCollateralTransition.body.drop 8) .reverted) ∨
    (RDstatic fork midnightBytecode (Sat256.ofUInt256 g) s0 ∧
      ExecBlock fork config frame evm (supplyCollateralTransition.body.drop 8) .staticViolation) ∨
    ∃ frame' evm',
      ExecBlock fork config frame evm (supplyCollateralTransition.body.drop 8) (.ok frame' evm') ∧
      RDret fork midnightBytecode (Sat256.ofUInt256 g) s0 evm'.accountMap ByteArray.empty := by
  have hguard := evalSupplyNewCollateralGuard evm hf
  simp only [List.cons_append, List.nil_append] at rd
  by_cases hcond : check = ⟨0⟩
  · have hno : ¬ (old = ⟨0⟩ ∧ assets ≠ ⟨0⟩) := by
      intro h; exact (hcheck.mpr h) hcond
    have hif : ExecStmt fork config frame evm (supplyCollateralTransition.body[8]!) (.ok frame evm) :=
      ExecStmt.iteFalse (by simpa only [decide_eq_false hno] using hguard) ExecBlock.nil
    have rd1 := midnightBlocks.midnight_block_17119_fallthrough
      (by simp only [List.length_cons]; omega) hcond rd
    have hb1 := transferBudgetAt (root := root) (credit := credit) rd1 (by transfer_budget hb)
    rcases supplyCollateralTail hs hf hcanon hi (by simp only [List.length_cons]; omega) hmem
        (by omega) hlower hfree hzero hb1 hcredit hgas hfork rd1 with
      hoog | ⟨hr, hbody⟩ | ⟨hr, hbody⟩ | ⟨frame', evm', hbody, hr⟩
    · exact Or.inl hoog
    · exact Or.inr (Or.inl ⟨hr, ExecBlock.consNormal hif hbody⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hr, ExecBlock.consNormal hif hbody⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨frame', evm', ExecBlock.consNormal hif hbody, hr⟩))
  · have hyes := hcheck.mp hcond
    have hguardTrue : evalExpr? config frame evm supplyNewCollateralGuard = .ok (.bool true) := by
      simpa only [decide_eq_true hyes] using hguard
    have rd1 := midnightBlocks.midnight_block_17119_taken
      (by simp only [List.length_cons]; omega) hcond (by jump_dest) rd
    have hb1 := transferBudgetAt (root := root + UInt256.ofNat 32) (credit := credit) rd1
      (by transfer_budget hb32)
    rcases supplyNewCollateral hs hf hcanon hi hindex (by simp only [List.length_cons]; omega)
        hm hroot hlower hfree hb1 rd1 with
      ⟨hr, hbody⟩ | ⟨hr, hbody⟩ |
        ⟨frame', evm', out, aw2, k2, C2, hs', hf', hbody, hp, hsize, hfree2, hb2, rd2⟩
    · exact Or.inr (Or.inl ⟨hr, ExecBlock.consRevert (ExecStmt.iteTrue hguardTrue hbody)⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hr, ExecBlock.consStatic (ExecStmt.iteTrue hguardTrue hbody)⟩))
    · have hif : ExecStmt fork config frame evm (supplyCollateralTransition.body[8]!)
          (.ok frame' evm') := ExecStmt.iteTrue hguardTrue hbody
      have rd3 := midnightBlocks.midnight_block_17462 (R := R) (by omega) (by jump_dest) rd2
      have hb3 := transferBudgetAt (root := root + UInt256.ofNat 32) (credit := credit) rd3
        (by transfer_budget hb2)
      have hn : (root + UInt256.ofNat 32).toNat = root.toNat + 32 :=
        addWord_toNat root (UInt256.ofNat 32) (by change root.toNat + 32 < 2^256; omega)
      have hm' : 128 ≤ (oraclePriceMemory mem root out).size := by rw [hsize]; omega
      have hz : memLoad (UInt256.ofNat 96) (oraclePriceMemory mem root out) = ⟨0⟩ := by
        rw [hp.load (UInt256.ofNat 96) (by decide) hlower hmem, hzero]
      rcases supplyCollateralTail hs' hf' hcanon hi (by simp only [List.length_cons]; omega) hm'
          (by rw [hn]; exact hroot) (by rw [hn]; omega) hfree2 hz hb3 hcredit32 hgas hfork rd3 with
        hoog | ⟨hr, htail⟩ | ⟨hr, htail⟩ | ⟨frame'', evm'', htail, hr⟩
      · exact Or.inl hoog
      · exact Or.inr (Or.inl ⟨hr, ExecBlock.consNormal hif htail⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨hr, ExecBlock.consNormal hif htail⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨frame'', evm'', ExecBlock.consNormal hif htail, hr⟩))

end Benchmarks.Midnight
