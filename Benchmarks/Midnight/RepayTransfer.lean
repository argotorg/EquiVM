import Benchmarks.Midnight.RepaySourceEntry
import Benchmarks.Midnight.SafeTransferBudget
import Benchmarks.Midnight.InitMarketDefaultsSource
import Benchmarks.Midnight.RuntimeBlocks_039
import Benchmarks.Midnight.RuntimeBlocks_017

variable {fork : Ethereum.Fork}

/-! Repayment's final loan-token transfer and empty ABI return. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem repayTransferArgs {frame : Frame} {evm : State} {m : MarketData}
    {id user units : UInt256} {callback payer : AccountAddress} {data : ByteArray}
    (hf : RepaySourceFrame frame m id user units callback data)
    (hp : frame.locals.get? "payer" = some (.address payer)) :
    evalExprs? config frame evm
      [.field (.var "market") "loanToken", .var "payer", .env .this, .var "units"] =
      .ok [.address m.loanToken, .address payer, .address evm.executionEnv.codeOwner,
        .int units.toNat] := by
  simp only [evalExprs?, evalMarketLoanToken hf.market, evalExpr?, hp, hf.units,
    envValue, EvalResult.ofOption, EvalResult.bind, bind, pure]

theorem midnightRepayTransfer {I : ExecutionEnv} {g : UInt256} {s0 evm : State}
    {frame : Frame} {m : MarketData} {mem rdata : ByteArray} {σ : AccountMap}
    {aw root market id user units x0 x1 x2 x3 x4 : UInt256}
    {callback payer : AccountAddress} {data : ByteArray} {credit k C : Nat} {R : List UInt256}
    (hs : SourceState s0 I σ evm) (hf : RepaySourceFrame frame m id user units callback data)
    (hp : frame.locals.get? "payer" = some (.address payer))
    (hstack : R.length + 22 ≤ 1024) (hmem : 832 ≤ mem.size) (hlower : 832 ≤ root.toNat)
    (hloan : memLoad (market + UInt256.ofNat 64) mem = UInt256.ofNat m.loanToken.val)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (hzero800 : memLoad (UInt256.ofNat 800) mem = ⟨0⟩)
    (hb : TransferBudget root credit mem aw C) (hused : root.toNat ≤ mem.size)
    (hcredit : 4 * ((root.toNat + safeTransferCallAllocation true + 31) / 32) ≤ credit + 999921)
    (hgas : midnightGasBound g) (hfork : fork ≥ .osaka)
    (rd : RD fork midnightBytecode I (Sat256.ofUInt256 g) s0 ⟨10100⟩
      ([x0, x1, x2, x3, x4, UInt256.ofNat payer.val, units, market] ++ R)
      mem aw rdata σ k C) :
    X fork (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (RDrev fork midnightBytecode (Sat256.ofUInt256 g) s0 ∧
      ExecBlock fork config frame evm (repayTransition.body.drop 12) .reverted) ∨
    ∃ frame' evm',
      ExecBlock fork config frame evm (repayTransition.body.drop 12) (.ok frame' evm') ∧
      RDret fork midnightBytecode (Sat256.ofUInt256 g) s0 evm'.accountMap ByteArray.empty := by
  simp only [List.cons_append, List.nil_append] at rd
  have rd1 := midnightBlocks.midnight_block_10100 (by omega) (by jump_dest) rd
  have hb1 := transferBudgetAt (root := root) (credit := credit) rd1 (by transfer_budget hb)
  have hclean : UInt256.land (UInt256.ofNat m.loanToken.val) solcAddrMask =
      UInt256.ofNat m.loanToken.val := addressWord_val_clean m.loanToken
  simp only [midnightBlocks.midnight_block_10100_stack, addressMask_computed,
    hloan, hclean] at rd1
  have he := repayTransferArgs (evm := evm) hf hp
  rw [hs.env] at he
  have hl : lookupCallable? frame.contract "SafeTransferLib_safeTransferFrom" =
      some (safeTransferFunctionFor true).toCallable := by
    rw [hf.contract]; exact safeTransferLookup true
  rcases safeTransferBudgeted true frame.immutables (token := m.loanToken) (sender := payer)
      (recipient := I.codeOwner) (value := units)
      (by change R.length + 8 + 14 ≤ 1024; omega) (by omega) (by omega) hfree hzero
      hb1 hused hcredit hgas hfork hs (by jump_dest) rd1 with
    hoog | ⟨hbody, hr⟩ |
      ⟨evm', σ', out, mem', ptr', aw2, k2, C2, hbody, hs', hp2, _, _, _, _, rd2⟩
  · exact Or.inl hoog
  · exact Or.inr (Or.inl ⟨hr, ExecBlock.consRevert
      (internalCallFunctionRevert he hl (safeTransferBind true m.loanToken payer I.codeOwner units)
        (by simpa only [safeTransferFrame, hf.contract] using hbody))⟩)
  · refine Or.inr (Or.inr ⟨_, evm', ExecBlock.consNormal
      (internalCallFunctionReturn he hl (safeTransferBind true m.loanToken payer I.codeOwner units)
        (by simpa only [safeTransferFrame, hf.contract] using hbody)) ExecBlock.nil, ?_⟩)
    rw [hs'.accounts] at rd2
    have hzret : memLoad (UInt256.ofNat 800) mem' = ⟨0⟩ := by
      rw [hp2.load (UInt256.ofNat 800) (by decide) hlower hmem, hzero800]
    have hr := midnightBlocks.midnight_block_3723
      (by change R.length + 8 + 2 ≤ 1024; omega) rd2
    simpa only [hzret, show (⟨0⟩ : UInt256).toNat = 0 from rfl,
      byteArray_readWithPadding_zero] using hr

end Benchmarks.Midnight
