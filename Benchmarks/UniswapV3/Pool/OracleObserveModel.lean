import Benchmarks.UniswapV3.Pool.OracleObserveSingleSource
import Benchmarks.UniswapV3.Pool.SourceArrays

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def oracleObserveFunction : FunctionDecl := contract.functions[5]!
theorem oracleObserveLookup : lookupCallable? contract "Oracle_observe" =
    some oracleObserveFunction.toCallable := rfl

def oracleSecondsAgoValues (secondsAgos : List UInt256) : List Value :=
  secondsAgos.map (fun secondsAgo ↦ .int (Int.ofNat secondsAgo.toNat))

def oracleObserveLocals (time : UInt256) (secondsAgos : List UInt256) (tick : Int)
    (index liquidity card : UInt256) : Store :=
  ((((((∅ : Store).insert "cardinality" (.int (Int.ofNat card.toNat))).insert
    "liquidity" (.int (Int.ofNat liquidity.toNat))).insert "index"
    (.int (Int.ofNat index.toNat))).insert "tick" (.int tick)).insert
    "secondsAgos" (.array (oracleSecondsAgoValues secondsAgos))).insert "time" (.int (Int.ofNat time.toNat))

def oracleObserveFrame (imms : Store) (time : UInt256) (secondsAgos : List UInt256) (tick : Int)
    (index liquidity card : UInt256) : Frame :=
  {contract := contract, immutables := imms,
   locals := oracleObserveLocals time secondsAgos tick index liquidity card}

theorem oracleObserveBind (time : UInt256) (secondsAgos : List UInt256) (tick : Int)
    (index liquidity card : UInt256) :
    bindParams? oracleObserveFunction.params [.int (Int.ofNat time.toNat),
      .array (oracleSecondsAgoValues secondsAgos), .int tick, .int (Int.ofNat index.toNat),
      .int (Int.ofNat liquidity.toNat), .int (Int.ofNat card.toNat)] =
      some (oracleObserveLocals time secondsAgos tick index liquidity card) := rfl

def oracleObserveZeroFrame (imms : Store) (time : UInt256) (secondsAgos : List UInt256) (tick : Int)
    (index liquidity card : UInt256) : Frame :=
  { (oracleObserveFrame imms time secondsAgos tick index liquidity card) with
    locals := ((oracleObserveLocals time secondsAgos tick index liquidity card).insert
      "tickCumulatives" (.array [])).insert "secondsPerLiquidityCumulativeX128s" (.array []) }

def oracleObserveTicksFrame (imms : Store) (time : UInt256) (secondsAgos : List UInt256) (tick : Int)
    (index liquidity card : UInt256) : Frame :=
  { (oracleObserveZeroFrame imms time secondsAgos tick index liquidity card) with
    locals := (oracleObserveZeroFrame imms time secondsAgos tick index liquidity card).locals.insert
      "tickCumulatives" (.array (List.replicate secondsAgos.length (.int 0))) }

def oracleObserveAllocatedFrame (imms : Store) (time : UInt256) (secondsAgos : List UInt256) (tick : Int)
    (index liquidity card : UInt256) : Frame :=
  { (oracleObserveTicksFrame imms time secondsAgos tick index liquidity card) with
    locals := (oracleObserveTicksFrame imms time secondsAgos tick index liquidity card).locals.insert
      "secondsPerLiquidityCumulativeX128s" (.array (List.replicate secondsAgos.length (.int 0))) }

def oracleObserveCondition : Expr :=
  .binary .lt (.var "i") (.arrayLength .localVar ⟨"secondsAgos", []⟩)
def oracleObservePost : List Stmt :=
  [.assign .localVar ⟨"i", []⟩
    (.cast (.binary .add (.var "i") (.intLit 1)) (.elem (.int (.uint ⟨256, by decide⟩))))]
def oracleObserveLoopBody : List Stmt :=
  [.internalCall "Oracle_observeSingle" [.var "time", .index (.var "secondsAgos") (.var "i"),
      .var "tick", .var "index", .var "liquidity", .var "cardinality"] "__c0",
   .assign .localVar ⟨"tickCumulatives", [.aindex (.var "i")]⟩ (.tupleGet (.var "__c0") 0),
   .assign .localVar ⟨"secondsPerLiquidityCumulativeX128s", [.aindex (.var "i")]⟩
     (.tupleGet (.var "__c0") 1)]

theorem oracleObserveFor : oracleObserveFunction.body[7]! =
    .for [.letDecl "i" (some (.elem (.int (.uint ⟨256, by decide⟩)))) (.intLit 0)]
      oracleObserveCondition oracleObservePost oracleObserveLoopBody := rfl

theorem oracleObserveZeroPrefix (imms : Store) (evm : EVM.State) (time : UInt256)
    (secondsAgos : List UInt256) (tick : Int) (index liquidity card : UInt256) :
    ExecBlock config (oracleObserveFrame imms time secondsAgos tick index liquidity card) evm
      (oracleObserveFunction.body.take 2)
      (.ok (oracleObserveZeroFrame imms time secondsAgos tick index liquidity card) evm) := by
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := .array []) ?_)
    (ExecBlock.consNormal (ExecStmt.letDecl (value := .array []) ?_) ExecBlock.nil)
  · exact evalExpr_newIntArray (.sint ⟨56, by decide⟩) 0 (by simp only [evalExpr?, pure]; rfl)
  · exact evalExpr_newIntArray (.uint ⟨160, by decide⟩) 0 (by simp only [evalExpr?, pure]; rfl)

end Benchmarks.UniswapV3.Pool
