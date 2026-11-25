import Benchmarks.Midnight.LiquidateCallback
import Benchmarks.Midnight.LiquidateLoanTransfer

variable {fork : Ethereum.Fork}

/-! The optional callback, final loan-token pull, and liquidation return. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightLiquidateAfterTransfer {I : ExecutionEnv} {g : UInt256} {s0 evm : State}
    {frame : Frame} {mem rdata : ByteArray}
    {aw root id index seized repaid borrower mode dp dl badDebt saved : UInt256}
    {receiver callback payer : AccountAddress} {m : MarketData} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 26 ≤ 1024)
    (hf : LiquidateSourceFrame frame m id index seized repaid borrower mode receiver callback
      (I.calldata.extract dp.toNat (dp.toNat + dl.toNat)))
    (hbad : frame.locals.get? "badDebt" = some (.int badDebt.toNat))
    (hpay : frame.locals.get? "payer" = some (.address payer))
    (hd : decodeCalldataMarket I.calldata 4 = some m)
    (hi : calldataWord I.calldata 36 = index)
    (hlo : 832 ≤ root.toNat) (hsize : 832 ≤ mem.size)
    (hid : memLoad (UInt256.ofNat 768) mem = id)
    (hz : memLoad (UInt256.ofNat 800) mem = ⟨0⟩)
    (hcallback : memLoad (UInt256.ofNat 736) mem = UInt256.ofNat callback.val)
    (hcanon : borrower.toNat < EVM.addressModulus)
    (hseized : memLoad (UInt256.ofNat 640) mem = seized)
    (hpaid : memLoad (UInt256.ofNat 608) mem = repaid)
    (hdl : dl.toNat < 2^64) (hdata : dp.toNat + dl.toNat ≤ I.calldata.size)
    (hh : TransferHeap mem aw root C) (hgas : midnightGasBound g) (hfork : fork ≥ .osaka)
    (hs : SourceState s0 I σ evm)
    (rd : RD fork midnightBytecode I (Sat256.ofUInt256 g) s0 ⟨5755⟩
      ([dp, dl, borrower, badDebt, UInt256.ofNat receiver.val, UInt256.ofNat payer.val, saved] ++ R)
      mem aw rdata σ k C) :
    X fork (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (ExecBlock fork config frame evm (liquidateTransition.body.drop 22) .reverted ∧
      RDrev fork midnightBytecode (Sat256.ofUInt256 g) s0) ∨
    ∃ frame' evm',
      ExecBlock fork config frame evm (liquidateTransition.body.drop 22)
        (.returned frame' evm' (some [.int seized.toNat, .int repaid.toNat])) ∧
      RDret fork midnightBytecode (Sat256.ofUInt256 g) s0 evm'.accountMap
        (wordArrayBytes [seized, repaid]) := by
  have hclean : UInt256.land (memLoad (UInt256.ofNat 736) mem)
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) =
      UInt256.ofNat callback.val := by
    rw [hcallback, addressMask_computed]
    exact addressWord_val_clean callback
  by_cases hcb : callback = 0
  · have sourcePrefix {result : ExecResult}
        (ht : ExecBlock fork config frame evm (liquidateTransition.body.drop 23) result) :
        ExecBlock fork config frame evm (liquidateTransition.body.drop 22) result := by
      change ExecBlock fork config frame evm
        (liquidateTransition.body[22]! :: liquidateTransition.body.drop 23) result
      rw [liquidateCallback_shape]
      exact .consNormal (.iteFalse (by rw [repayCallbackCondition_eval hf.callback]; simp [hcb])
        .nil) ht
    have rd1 := midnightBlocks.midnight_block_5755_fallthrough
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      (by rw [hclean, hcb]; rfl) rd
    have ha1 := memoryFundingAt (credit := transferHeapCredit root) rd1 (by memory_fund hh.funding)
    have hh1 : TransferHeap mem (M aw ⟨736⟩ ⟨32⟩) root _ :=
      { hh with
        covered := hh.covered.trans (Nat.mul_le_mul_left 32 (memoryWords_ge aw _ _))
        funding := ha1 }
    rcases midnightLiquidateLoanTransfer (R := saved :: R)
        (by simp only [List.length_cons]; omega) hf hpay hd hlo hsize hseized hpaid hh1
        hgas hfork hs rd1 with hoog | ⟨ht, hr⟩ | ⟨frame', evm', ht, hr⟩
    · exact Or.inl hoog
    · exact Or.inr (Or.inl ⟨sourcePrefix ht, hr⟩)
    · exact Or.inr (Or.inr ⟨frame', evm', sourcePrefix ht, hr⟩)
  · have hword : UInt256.ofNat callback.val ≠ (⟨0⟩ : UInt256) := by
      intro h
      apply hcb
      apply Fin.ext
      have hn := congrArg UInt256.toNat h
      change callback.val = 0
      simpa only [show (UInt256.ofNat callback.val).toNat = callback.val from
        addressWord_toNat_val callback] using hn
    have hcond : evalExpr? config frame evm repayCallbackCondition = .ok (.bool true) := by
      rw [repayCallbackCondition_eval hf.callback, decide_eq_true hcb]
    have rd1 := midnightBlocks.midnight_block_5755_taken
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      (by rw [hclean]; exact hword) (by jump_dest) rd
    have ha1 := memoryFundingAt (credit := transferHeapCredit root) rd1 (by memory_fund hh.funding)
    have hh1 : TransferHeap mem (M aw ⟨736⟩ ⟨32⟩) root _ :=
      { hh with
        covered := hh.covered.trans (Nat.mul_le_mul_left 32 (memoryWords_ge aw _ _))
        funding := ha1 }
    rcases midnightLiquidateCallback (R := UInt256.ofNat payer.val :: saved :: R)
        (by simp only [List.length_cons]; omega) hf hbad hd hi hlo hsize hid hz hcallback
        hcanon hseized hpaid hdl hdata hh1 hgas hs rd1 with
      hoog | ⟨ht, hr⟩ | ⟨evm2, σ2, out, mem2, aw2, k2, C2, ht, hs2, hp2, hlo2, hh2, rd2⟩
    · exact Or.inl hoog
    · refine Or.inr (Or.inl ⟨?_, hr⟩)
      change ExecBlock fork config frame evm
        (liquidateTransition.body[22]! :: liquidateTransition.body.drop 23) .reverted
      rw [liquidateCallback_shape]
      exact .consRevert (.iteTrue hcond ht)
    · have sourcePrefix {result : ExecResult}
          (htail : ExecBlock fork config (liquidateCallbackFrame frame (calldataWord out 0)) evm2
            (liquidateTransition.body.drop 23) result) :
          ExecBlock fork config frame evm (liquidateTransition.body.drop 22) result := by
        change ExecBlock fork config frame evm
          (liquidateTransition.body[22]! :: liquidateTransition.body.drop 23) result
        rw [liquidateCallback_shape]
        exact .consNormal (.iteTrue hcond ht) htail
      have rd3 := midnightBlocks.midnight_block_6265 (R := R) (by omega) (by jump_dest) rd2
      have hh3 := hh2.mono (show C2 ≤ C2 + 26 by omega)
      simp only [midnightBlocks.midnight_block_6265_stack] at rd3
      have hpay2 : (liquidateCallbackFrame frame (calldataWord out 0)).locals.get? "payer" =
          some (.address payer) := by rw [liquidateCallbackFrame_get _ _ _ (by decide), hpay]
      rcases midnightLiquidateLoanTransfer (R := saved :: R)
          (by simp only [List.length_cons]; omega) (liquidateCallbackFrame_arguments hf _) hpay2 hd
          (hlo.trans hlo2) (hsize.trans hp2.size)
          ((hp2.load ⟨640⟩ (by decide) (by change 672 ≤ root.toNat; omega)
            (by change 672 ≤ mem.size; omega)).trans hseized)
          ((hp2.load ⟨608⟩ (by decide) (by change 640 ≤ root.toNat; omega)
            (by change 640 ≤ mem.size; omega)).trans hpaid)
          hh3 hgas hfork hs2 rd3 with hoog | ⟨htail, hr⟩ | ⟨frame', evm', htail, hr⟩
      · exact Or.inl hoog
      · exact Or.inr (Or.inl ⟨sourcePrefix htail, hr⟩)
      · exact Or.inr (Or.inr ⟨frame', evm', sourcePrefix htail, hr⟩)

end Benchmarks.Midnight
