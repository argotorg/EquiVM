import Benchmarks.Midnight.FlashLoanArguments
import Benchmarks.Midnight.AdminSource

variable {fork : Ethereum.Fork}

/-! Source locals, the equal-length guard, and the flash-loan event. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

structure FlashLoanSourceFrame (frame : Frame) (tokens assets : List UInt256)
    (callback : AccountAddress) (data : ByteArray) : Prop where
  contract : frame.contract = Benchmarks.Midnight.contract
  tokens : frame.locals.get? "tokens" = some (.array (addressWordArrayValues tokens))
  assets : frame.locals.get? "assets" = some (.array (wordArrayValues assets))
  callback : frame.locals.get? "callback" = some (.address callback)
  data : frame.locals.get? "data" = some (.bytes data)

theorem FlashLoanSourceFrame.insert {frame : Frame} {tokens assets : List UInt256}
    {callback : AccountAddress} {data : ByteArray}
    (h : FlashLoanSourceFrame frame tokens assets callback data) (name : Ident) (value : Value)
    (hn : name ∉ ["tokens", "assets", "callback", "data"]) :
    FlashLoanSourceFrame { frame with locals := frame.locals.insert name value }
      tokens assets callback data := by
  rcases h with ⟨hc, ht, ha, hcb, hd⟩
  simp only [List.mem_cons, not_or] at hn
  constructor <;> simp_all [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]

def flashLoanExternalFrame (origin : EVM.State) (tokens assets : List UInt256)
    (callback : AccountAddress) (data : ByteArray) : Frame :=
  calldataFrame contract (flashLoanArguments tokens assets callback data) ∅ origin

theorem flashLoanExternalFrame_spec (origin : EVM.State) (tokens assets : List UInt256)
    (callback : AccountAddress) (data : ByteArray) :
    FlashLoanSourceFrame (flashLoanExternalFrame origin tokens assets callback data)
      tokens assets callback data := by
  constructor
  · rfl
  all_goals simp [flashLoanExternalFrame, calldataFrame, flashLoanArguments,
    Std.HashMap.getElem_insert]

def flashLoanLengthGuard : Expr :=
  .binary .eq (.arrayLength .localVar { base := "tokens" })
    (.arrayLength .localVar { base := "assets" })

theorem flashLoanLengthEval {frame : Frame} {evm : EVM.State} {tokens assets : List UInt256}
    {callback : AccountAddress} {data : ByteArray}
    (hf : FlashLoanSourceFrame frame tokens assets callback data) :
    evalExpr? config frame evm flashLoanLengthGuard =
      .ok (.bool (decide (tokens.length = assets.length))) := by
  simp only [flashLoanLengthGuard, evalExpr?, readLocalPath?, hf.tokens, hf.assets,
    addressWordArrayValues, wordArrayValues, List.length_map, evalBinaryOp?, bind, pure,
    EvalResult.bind, Reasoning.VyperDispatch.value_int_beq, Int.ofNat_inj]

theorem flashLoanEntrySource {origin : EVM.State} {tokens assets : List UInt256}
    {callback : AccountAddress} {data : ByteArray} {result : ExecResult}
    (hwv : origin.executionEnv.weiValue = ⟨0⟩)
    (hlimit : origin.executionEnv.calldata.size < calldataLimit)
    (hlen : tokens.length = assets.length)
    (htail : ExecBlock fork config (flashLoanExternalFrame origin tokens assets callback data) origin
      (flashLoanTransition.body.drop 4) result) :
    ExecBlock fork config
      { contract := contract
        locals := flashLoanArguments tokens assets callback data
        immutables := ∅ }
      origin flashLoanTransition.body result := by
  apply guardedBodyBlock hwv hlimit
  apply ExecBlock.consNormal (ExecStmt.requireTrue ?_) htail
  exact (flashLoanLengthEval (flashLoanExternalFrame_spec origin tokens assets callback data)).trans
    (by rw [decide_eq_true hlen])

theorem flashLoanLengthRevertSource {origin : EVM.State} {tokens assets : List UInt256}
    {callback : AccountAddress} {data : ByteArray}
    (hwv : origin.executionEnv.weiValue = ⟨0⟩)
    (hlimit : origin.executionEnv.calldata.size < calldataLimit)
    (hlen : tokens.length ≠ assets.length) :
    ExecBlock fork config
      { contract := contract
        locals := flashLoanArguments tokens assets callback data
        immutables := ∅ }
      origin flashLoanTransition.body .reverted := by
  apply guardedBodyBlock hwv hlimit
  apply ExecBlock.consRevert (ExecStmt.requireFalse ?_)
  exact (flashLoanLengthEval (flashLoanExternalFrame_spec origin tokens assets callback data)).trans
    (by rw [decide_eq_false hlen])

theorem flashLoanEventArgs {frame : Frame} {evm : EVM.State} {tokens assets : List UInt256}
    {callback : AccountAddress} {data : ByteArray}
    (hf : FlashLoanSourceFrame frame tokens assets callback data) :
    evalExprs? config frame evm [.env .caller, .var "tokens", .var "assets", .var "callback"] =
      .ok [.address evm.executionEnv.source, .array (addressWordArrayValues tokens),
        .array (wordArrayValues assets), .address callback] := by
  simp only [evalExprs?, evalExpr?, hf.tokens, hf.assets, hf.callback,
    envValue, EvalResult.ofOption, EvalResult.bind, bind, pure]

theorem flashLoanEmit {frame : Frame} {evm : EVM.State} {tokens assets : List UInt256}
    {callback : AccountAddress} {data : ByteArray}
    (hf : FlashLoanSourceFrame frame tokens assets callback data)
    (hp : evm.executionEnv.perm = true) :
    ABlock fork config evm frame (flashLoanTransition.body.drop 4)
      frame (flashLoanTransition.body.drop 5) :=
  ⟨fun h ↦ ExecBlock.consNormal (ExecStmt.emit hp (flashLoanEventArgs hf)) h⟩

theorem flashLoanEmitStatic {frame : Frame} {evm : EVM.State} {tokens assets : List UInt256}
    {callback : AccountAddress} {data : ByteArray}
    (hf : FlashLoanSourceFrame frame tokens assets callback data)
    (hp : evm.executionEnv.perm = false) :
    ExecBlock fork config frame evm (flashLoanTransition.body.drop 4) .staticViolation :=
  ExecBlock.consStatic (ExecStmt.emitStatic (flashLoanEventArgs hf) hp)

end Benchmarks.Midnight
