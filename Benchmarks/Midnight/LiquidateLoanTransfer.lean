import Benchmarks.Midnight.LiquidateReturn
import Benchmarks.Midnight.MarketLoanToken
import Benchmarks.Midnight.CalldataAddressRead
import Benchmarks.Midnight.InitMarketDefaultsSource
import Benchmarks.Midnight.TransferHeap

variable {fork : Ethereum.Fork}

/-! The final loan-token pull and return after liquidation's optional callback. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem liquidateLoanTransferArgs {frame : Frame} {evm : State} {m : MarketData}
    {id index seized repaid borrower mode : UInt256} {receiver callback payer : AccountAddress}
    {data : ByteArray}
    (hf : LiquidateSourceFrame frame m id index seized repaid borrower mode receiver callback data)
    (hp : frame.locals.get? "payer" = some (.address payer)) :
    evalExprs? config frame evm
      [.field (.var "market") "loanToken", .var "payer", .env .this, .var "repaidUnits"] =
      .ok [.address m.loanToken, .address payer, .address evm.executionEnv.codeOwner,
        .int repaid.toNat] := by
  simp only [evalExprs?, evalMarketLoanToken hf.market, evalExpr?, hp, hf.repaid,
    envValue, EvalResult.ofOption, EvalResult.bind, bind, pure]

theorem midnightLiquidateLoanTransfer {I : ExecutionEnv} {g : UInt256} {s0 evm : State}
    {frame : Frame} {mem rdata : ByteArray} {aw root id index seized repaid borrower mode
      x0 x1 x2 x3 x4 : UInt256} {receiver callback payer : AccountAddress} {data : ByteArray}
    {m : MarketData} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 20 ≤ 1024)
    (hf : LiquidateSourceFrame frame m id index seized repaid borrower mode receiver callback data)
    (hp : frame.locals.get? "payer" = some (.address payer))
    (hd : decodeCalldataMarket I.calldata 4 = some m)
    (hlo : 832 ≤ root.toNat) (hsize : 832 ≤ mem.size)
    (hseized : memLoad (UInt256.ofNat 640) mem = seized)
    (hpaid : memLoad (UInt256.ofNat 608) mem = repaid) (hh : TransferHeap mem aw root C)
    (hgas : midnightGasBound g) (hfork : fork ≥ .osaka) (hs : SourceState s0 I σ evm)
    (rd : RD fork midnightBytecode I (Sat256.ofUInt256 g) s0 ⟨5773⟩
      ([x0, x1, x2, x3, x4, UInt256.ofNat payer.val] ++ R) mem aw rdata σ k C) :
    X fork (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (ExecBlock fork config frame evm (liquidateTransition.body.drop 23) .reverted ∧
      RDrev fork midnightBytecode (Sat256.ofUInt256 g) s0) ∨
    ∃ frame' evm',
      ExecBlock fork config frame evm (liquidateTransition.body.drop 23)
        (.returned frame' evm' (some [.int seized.toNat, .int repaid.toNat])) ∧
      RDret fork midnightBytecode (Sat256.ofUInt256 g) s0 evm'.accountMap
        (wordArrayBytes [seized, repaid]) := by
  simp only [List.cons_append, List.nil_append] at rd
  have rd1 := midnightBlocks.midnight_block_5773 (by omega) (by jump_dest) rd
  simp only [midnightBlocks.midnight_block_5773_stack] at rd1
  obtain ⟨k2, C2, hc2, rd2⟩ := midnightCalldataAddressDirectRead
    (R := [UInt256.ofNat payer.val, ⟨5803⟩, x0, x1, x2, x3, x4,
      UInt256.ofNat payer.val] ++ R)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    (decodeCalldataMarket_loanToken hd) (by jump_dest) rd1
  have hf2 := hh.funding.mono (show C ≤ C2 by omega)
  have rd3 := midnightBlocks.midnight_block_5791
    (R := [⟨5803⟩, x0, x1, x2, x3, x4, UInt256.ofNat payer.val] ++ R)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    (by jump_dest) rd2
  have hf3 := memoryFundingAt (credit := transferHeapCredit root) rd3 (by memory_fund hf2)
  have hh3 : TransferHeap mem (M aw ⟨608⟩ ⟨32⟩) root _ :=
    { hh with
      covered := hh.covered.trans (Nat.mul_le_mul_left 32 (memoryWords_ge aw _ _))
      funding := hf3 }
  simp only [midnightBlocks.midnight_block_5791_stack, hpaid] at rd3
  have he := liquidateLoanTransferArgs (evm := evm) hf hp
  rw [hs.env] at he
  have hl : lookupCallable? frame.contract "SafeTransferLib_safeTransferFrom" =
      some (safeTransferFunctionFor true).toCallable := by
    rw [hf.contract]; exact safeTransferLookup true
  rcases safeTransferHeap true frame.immutables
    (R := [x0, x1, x2, x3, x4, UInt256.ofNat payer.val] ++ R)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    hh3 hgas hfork hs (by jump_dest) rd3 with
      hoog | ⟨hb, hr⟩ | ⟨evm', σ', out, mem', root', aw', k', C', hb, hs', hprefix, hroot, hh', rd'⟩
  · exact Or.inl hoog
  · exact Or.inr (Or.inl ⟨ExecBlock.consRevert (internalCallFunctionRevert he hl
      (safeTransferBind true m.loanToken payer I.codeOwner repaid)
      (by simpa only [safeTransferFrame, hf.contract] using hb)), hr⟩)
  · rcases midnightMemoryPaid_headroom rd' hh'.funding.accounting.paid hgas hh'.covered with
      hoog | hroom
    · exact Or.inl hoog
    have hf' : LiquidateSourceFrame (resumeAfterInternalCall frame "__c33" none)
        m id index seized repaid borrower mode receiver callback data :=
      hf.insert "__c33" .unit (by decide)
    refine Or.inr (Or.inr ⟨_, evm', ExecBlock.consNormal
      (internalCallFunctionReturn he hl (safeTransferBind true m.loanToken payer I.codeOwner repaid)
        (by simpa only [safeTransferFrame, hf.contract] using hb))
      (ExecBlock.consReturn (liquidateReturnSource hf')), ?_⟩)
    rw [← hs'.accounts]
    exact midnightLiquidateReturn
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      (by omega) (by omega) (hsize.trans hprefix.size) hh'.free
      ((hprefix.load ⟨640⟩ (by decide) (by change 672 ≤ root.toNat; omega)
        (by change 672 ≤ mem.size; omega)).trans hseized)
      ((hprefix.load ⟨608⟩ (by decide) (by change 640 ≤ root.toNat; omega)
        (by change 640 ≤ mem.size; omega)).trans hpaid) rd'

end Benchmarks.Midnight
