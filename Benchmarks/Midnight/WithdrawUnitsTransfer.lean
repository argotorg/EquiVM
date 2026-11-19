import Benchmarks.Midnight.WithdrawUnitsSourceFrame
import Benchmarks.Midnight.SafeTransferBudget
import Benchmarks.Midnight.InitMarketDefaultsSource
import Benchmarks.Midnight.RuntimeBlocks_017

/-! The withdrawal event, token transfer, and empty ABI return. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem withdrawUnitsEmit {frame : Frame} {m : MarketData} {evm : EVM.State}
    {id user units decrease : UInt256} {receiver : AccountAddress}
    (hf : WithdrawUnitsSourceFrame frame m id user units receiver)
    (hd : frame.locals.get? "pendingFeeDecrease" = some (.int decrease.toNat))
    (hp : evm.executionEnv.perm = true) :
    ABlock config evm frame (withdrawTransition.body.drop 16)
      frame (withdrawTransition.body.drop 17) := by
  refine ⟨fun h ↦ ExecBlock.consNormal (ExecStmt.emit (vals :=
    [.address evm.executionEnv.source, wordBytes32Value id, .int units.toNat,
      .address (AccountAddress.ofNat user.toNat), .address receiver, .int decrease.toNat]) hp ?_) h⟩
  simp only [evalExprs?, evalExpr?, hf.idValue, hf.units, hf.userValue, hf.receiver, hd,
    envValue, EvalResult.ofOption, EvalResult.bind, bind, pure]

theorem withdrawUnitsTransferArgs {frame : Frame} {m : MarketData} {evm : EVM.State}
    {id user units : UInt256} {receiver : AccountAddress}
    (hf : WithdrawUnitsSourceFrame frame m id user units receiver) :
    evalExprs? config frame evm [.field (.var "market") "loanToken", .var "receiver", .var "units"] =
      .ok [.address m.loanToken, .address receiver, .int units.toNat] := by
  simp only [evalExprs?, evalMarketLoanToken hf.market, evalExpr?, hf.receiver, hf.units,
    EvalResult.ofOption, EvalResult.bind, bind, pure]

theorem withdrawUnitsTransfer {I : ExecutionEnv} {g : UInt256} {s0 evm : State}
    {frame : Frame} {m : MarketData} {mem rdata : ByteArray}
    {aw root id user units decrease : UInt256} {receiver : AccountAddress}
    {credit k C : Nat} {R : List UInt256}
    (hs : SourceState s0 I evm.accountMap evm)
    (hf : WithdrawUnitsSourceFrame frame m id user units receiver)
    (hd : frame.locals.get? "pendingFeeDecrease" = some (.int decrease.toNat))
    (hperm : I.perm = true) (hstack : R.length + 16 ≤ 1024) (hmem : 832 ≤ mem.size)
    (hroot : root.toNat < 2^64) (hlower : 832 ≤ root.toNat)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (hzero800 : memLoad (UInt256.ofNat 800) mem = ⟨0⟩)
    (hb : TransferBudget root credit mem aw C) (hused : root.toNat ≤ mem.size)
    (hcredit : 4 * ((root.toNat + safeTransferCallAllocation false + 31) / 32) ≤ credit + 999921)
    (hgas : midnightGasBound g) (hfork : I.fork ≥ .osaka)
    (rd : RD midnightBytecode I (Sat256.ofUInt256 g) s0 ⟨23236⟩
      ([UInt256.ofNat m.loanToken.val, UInt256.ofNat receiver.val, units, UInt256.ofNat 3723] ++ R)
      mem aw rdata evm.accountMap k C) :
    X (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (RDrev midnightBytecode (Sat256.ofUInt256 g) s0 ∧
      ExecBlock config frame evm (withdrawTransition.body.drop 16) .reverted) ∨
    ∃ frame' evm',
      ExecBlock config frame evm (withdrawTransition.body.drop 16) (.ok frame' evm') ∧
      RDret midnightBytecode (Sat256.ofUInt256 g) s0 evm'.accountMap ByteArray.empty := by
  simp only [List.cons_append, List.nil_append] at rd
  have hl : lookupCallable? frame.contract "SafeTransferLib_safeTransfer" =
      some (safeTransferFunctionFor false).toCallable := by
    rw [hf.contract]; exact safeTransferLookup false
  have sourcePrefix {result : ExecResult}
      (ht : ExecBlock config frame evm (withdrawTransition.body.drop 17) result) :
      ExecBlock config frame evm (withdrawTransition.body.drop 16) result :=
    (withdrawUnitsEmit hf hd (by rw [hs.env]; exact hperm)).run ht
  rcases safeTransferBudgeted false frame.immutables (token := m.loanToken) (sender := I.source)
      (recipient := receiver) (value := units) (by omega) (by omega) (by omega)
      hfree hzero hb hused hcredit hgas hfork hs (by jump_dest) rd with
    hoog | ⟨hbody, hr⟩ |
      ⟨evm', σ', out, mem', ptr', aw2, k2, C2, hbody, hs', hp2, _, _, _, _, rd2⟩
  · exact Or.inl hoog
  · exact Or.inr (Or.inl ⟨hr, sourcePrefix (ExecBlock.consRevert
      (internalCallFunctionRevert (withdrawUnitsTransferArgs hf) hl
        (safeTransferBind false m.loanToken I.source receiver units)
        (by simpa only [safeTransferFrame, hf.contract] using hbody)))⟩)
  · refine Or.inr (Or.inr ⟨_, evm', sourcePrefix (ExecBlock.consNormal
      (internalCallFunctionReturn (withdrawUnitsTransferArgs hf) hl
        (safeTransferBind false m.loanToken I.source receiver units)
        (by simpa only [safeTransferFrame, hf.contract] using hbody)) ExecBlock.nil), ?_⟩)
    rw [hs'.accounts] at rd2
    have hzret : memLoad (UInt256.ofNat 800) mem' = ⟨0⟩ := by
      rw [hp2.load (UInt256.ofNat 800) (by decide) hlower hmem, hzero800]
    have hr := midnightBlocks.midnight_block_3723 (by omega) rd2
    simpa only [hzret, show (⟨0⟩ : UInt256).toNat = 0 from rfl,
      byteArray_readWithPadding_zero] using hr

end Benchmarks.Midnight
