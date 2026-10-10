import Benchmarks.UniswapV3.Pool.TickFeeModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

def tickFeeLocals (a : TickFeeArgs) : Store :=
  (((((∅ : Store).insert "feeGrowthGlobal1X128" (.int (Int.ofNat a.global1.toNat))).insert
    "feeGrowthGlobal0X128" (.int (Int.ofNat a.global0.toNat))).insert
    "tickCurrent" (.int a.current)).insert "tickUpper" (.int a.upper)).insert
    "tickLower" (.int a.lower)

def tickFeeFrame (imms : Store) (a : TickFeeArgs) : Frame :=
  {contract := contract, locals := tickFeeLocals a, immutables := imms}

def tickFeeZerosFrame (imms : Store) (a : TickFeeArgs) : Frame :=
  let locals := ((tickFeeLocals a).insert "feeGrowthInside0X128" (.int 0)).insert
    "feeGrowthInside1X128" (.int 0)
  {tickFeeFrame imms a with locals := locals}

def tickFeeLowerAliasFrame (imms : Store) (a : TickFeeArgs) : Frame :=
  let locals := (tickFeeZerosFrame imms a).locals.insert "lower" (tickAlias a.lower)
  {tickFeeZerosFrame imms a with locals := locals}

def tickFeeAliasesFrame (imms : Store) (a : TickFeeArgs) : Frame :=
  let locals := (tickFeeLowerAliasFrame imms a).locals.insert "upper" (tickAlias a.upper)
  {tickFeeLowerAliasFrame imms a with locals := locals}

def tickFeeBelowZeroFrame (imms : Store) (a : TickFeeArgs) : Frame :=
  let locals := ((tickFeeAliasesFrame imms a).locals.insert "feeGrowthBelow0X128" (.int 0)).insert
    "feeGrowthBelow1X128" (.int 0)
  {tickFeeAliasesFrame imms a with locals := locals}

theorem tickFeeBind (a : TickFeeArgs) :
    bindParams? tickFeeFunction.params [.int a.lower, .int a.upper, .int a.current,
      .int (Int.ofNat a.global0.toNat), .int (Int.ofNat a.global1.toNat)] =
      some (tickFeeLocals a) := rfl

theorem tickFeePrefix (imms : Store) (evm : EVM.State) (a : TickFeeArgs) :
    ExecBlock config (tickFeeFrame imms a) evm (tickFeeFunction.body.take 6)
      (.ok (tickFeeBelowZeroFrame imms a) evm) := by
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (value := .int 0) (by simp only [evalExpr?, pure])) ?_
  refine ExecBlock.consNormal (solm' := tickFeeZerosFrame imms a)
    (ExecStmt.letDecl (value := .int 0) (by simp only [evalExpr?, pure])) ?_
  refine ExecBlock.consNormal (solm' := tickFeeLowerAliasFrame imms a) (evm' := evm)
    (ExecStmt.letStorage ?_) ?_
  · apply resolveTickReference _ imms evm "tickLower" a.lower
    · simp [tickFeeZerosFrame, tickFeeFrame, tickFeeLocals, Std.HashMap.getElem_insert]
    · simp [tickFeeZerosFrame, tickFeeFrame, tickFeeLocals, Std.HashMap.getElem_insert]
  · refine ExecBlock.consNormal (solm' := tickFeeAliasesFrame imms a) (evm' := evm)
      (ExecStmt.letStorage ?_) ?_
    · apply resolveTickReference _ imms evm "tickUpper" a.upper
      · simp [tickFeeLowerAliasFrame, tickFeeZerosFrame, tickFeeFrame, tickFeeLocals,
          Std.HashMap.getElem_insert]
      · simp [tickFeeLowerAliasFrame, tickFeeZerosFrame, tickFeeFrame, tickFeeLocals, Std.HashMap.getElem_insert]
    · refine ExecBlock.consNormal
        (ExecStmt.letDecl (value := .int 0) (by simp only [evalExpr?, pure])) ?_
      exact ExecBlock.consNormal
        (ExecStmt.letDecl (value := .int 0) (by simp only [evalExpr?, pure])) ExecBlock.nil

end Benchmarks.UniswapV3.Pool
