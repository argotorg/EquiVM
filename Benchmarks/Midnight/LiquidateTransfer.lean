import Benchmarks.Midnight.LiquidateTransferPrepare
import Benchmarks.Midnight.LiquidateEventSource

variable {fork : Ethereum.Fork}

/-! The outgoing collateral transfer, including source reverts and the post-call heap. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

def liquidateTransferFrame (frame : Frame) : Frame :=
  resumeAfterInternalCall frame "__c31" none

theorem liquidateTransferFrame_arguments {frame : Frame} {m : MarketData}
    {id index seized repaid borrower mode : UInt256} {receiver callback : AccountAddress}
    {data : ByteArray}
    (hf : LiquidateSourceFrame frame m id index seized repaid borrower mode receiver callback data) :
    LiquidateSourceFrame (liquidateTransferFrame frame) m id index seized repaid borrower mode
      receiver callback data := hf.insert "__c31" .unit (by decide)

theorem liquidateTransferFrame_get (frame : Frame) (name : Ident) (hn : name ≠ "__c31") :
    (liquidateTransferFrame frame).locals.get? name = frame.locals.get? name := by
  unfold liquidateTransferFrame resumeAfterInternalCall
  exact store_get_ne _ _ (by simp [Ne.symm hn])

theorem liquidateTransferArgs_eval {frame : Frame} {evm : State} {m : MarketData}
    {id index seized repaid borrower mode : UInt256} {receiver callback : AccountAddress}
    {data : ByteArray}
    (hf : LiquidateSourceFrame frame m id index seized repaid borrower mode receiver callback data)
    (hidx : index.toNat < m.collaterals.length) :
    evalExprs? config frame evm [liquidateTokenExpr, .var "receiver", .var "seizedAssets"] =
      .ok [.address m.collaterals[index.toNat].token, .address receiver, .int seized.toNat] := by
  simp only [evalExprs?, evalLiquidateToken hf.market hf.index hidx, evalExpr?, hf.receiver,
    hf.seized, EvalResult.ofOption, EvalResult.bind, bind, pure]

theorem midnightLiquidateTransfer {I : ExecutionEnv} {g : UInt256} {s0 evm : State}
    {frame : Frame} {mem rdata : ByteArray} {aw root id index seized repaid borrower mode
      dp dl badDebt : UInt256} {receiver callback payer : AccountAddress} {data : ByteArray}
    {m : MarketData} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 20 ≤ 1024)
    (hf : LiquidateSourceFrame frame m id index seized repaid borrower mode receiver callback data)
    (hd : decodeCalldataMarket I.calldata 4 = some m)
    (hi : calldataWord I.calldata 36 = index) (hidx : index.toNat < m.collaterals.length)
    (hseized : memLoad (UInt256.ofNat 640) mem = seized) (hh : TransferHeap mem aw root C)
    (hgas : midnightGasBound g) (hfork : fork ≥ .osaka) (hs : SourceState s0 I σ evm)
    (rd : RD fork midnightBytecode I (Sat256.ofUInt256 g) s0 ⟨20488⟩
      ([⟨4⟩ + calldataWord I.calldata 4, calldataWord I.calldata 4 + ⟨100⟩,
        ⟨5734⟩, ⟨5750⟩, UInt256.ofNat receiver.val, ⟨5543⟩, ⟨5755⟩,
        dp, dl, borrower, badDebt, UInt256.ofNat receiver.val, UInt256.ofNat payer.val] ++ R)
      mem aw rdata σ k C) :
    X fork (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (ExecStmt fork config frame evm (liquidateTransition.body[21]!) .reverted ∧
      RDrev fork midnightBytecode (Sat256.ofUInt256 g) s0) ∨
    ∃ (evm' : State) (σ' : AccountMap) (out mem' : ByteArray) (root' aw' : UInt256) (k' C' : Nat),
      ExecStmt fork config frame evm (liquidateTransition.body[21]!)
        (.ok (liquidateTransferFrame frame) evm') ∧
      SourceState s0 I σ' evm' ∧ MemoryPrefix mem mem' root.toNat ∧
      root.toNat ≤ root'.toNat ∧ TransferHeap mem' aw' root' C' ∧
      RD fork midnightBytecode I (Sat256.ofUInt256 g) s0 ⟨5755⟩
        ([dp, dl, borrower, badDebt, UInt256.ofNat receiver.val, UInt256.ofNat payer.val] ++ R)
        mem' aw' out σ' k' C' := by
  obtain ⟨aw1, k1, C1, hh1, rd1⟩ := midnightLiquidateTransferPrepare
    (R := [dp, dl, borrower, badDebt, UInt256.ofNat receiver.val, UInt256.ofNat payer.val] ++ R)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    hd hi hidx hseized hh rd
  have he := liquidateTransferArgs_eval (evm := evm) hf hidx
  have hl : lookupCallable? frame.contract "SafeTransferLib_safeTransfer" =
      some (safeTransferFunctionFor false).toCallable := by
    rw [hf.contract]; exact safeTransferLookup false
  rcases safeTransferHeap false frame.immutables
    (R := [dp, dl, borrower, badDebt, UInt256.ofNat receiver.val, UInt256.ofNat payer.val] ++ R)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    hh1 hgas hfork hs (by jump_dest) rd1 with
      hoog | ⟨hb, hr⟩ | ⟨evm', σ', out, mem', root', aw', k', C', hb, hs', hp, hlo, hh', rd'⟩
  · exact Or.inl hoog
  · exact Or.inr (Or.inl ⟨internalCallFunctionRevert he hl
      (safeTransferBind false m.collaterals[index.toNat].token I.source receiver seized)
      (by simpa only [safeTransferFrame, hf.contract] using hb), hr⟩)
  · exact Or.inr (Or.inr ⟨evm', σ', out, mem', root', aw', k', C',
      internalCallFunctionReturn he hl
        (safeTransferBind false m.collaterals[index.toNat].token I.source receiver seized)
        (by simpa only [safeTransferFrame, hf.contract] using hb), hs', hp, hlo, hh', rd'⟩)

end Benchmarks.Midnight
