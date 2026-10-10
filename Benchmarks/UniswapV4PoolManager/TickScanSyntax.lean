import Benchmarks.UniswapV4PoolManager.TickScanNextSource
import Benchmarks.UniswapV4PoolManager.TickScanMask

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

abbrev tickScanFunction : FunctionDecl := contract.functions[103]!
theorem tickScan_lookup : lookupCallable? contract "TickBitmap_nextInitializedTickWithinOneWord" =
    some tickScanFunction.toCallable := rfl

def tickScanPreludeStmts (lte : Bool) : List Stmt :=
  [.internalCall "TickBitmap_position" [.var "compressed"] "position",
   .letDecl "wordPos" (some (.elem (.int (.sint ⟨16, by decide⟩)))) (.tupleGet (.var "position") 0),
   .letDecl "bitPos" (some (.elem (.int (.uint ⟨8, by decide⟩)))) (.tupleGet (.var "position") 1),
   .letDecl "mask" (some abiUInt256) (tickScanMaskExpr lte),
   .letDecl "masked" (some abiUInt256) (.binary (.bitAnd (.uint ⟨256, by decide⟩))
     (.storage {base := "self", steps := [.mindex (.var "wordPos")]}) (.var "mask")),
   .letDecl "initialized" (some (.elem .bool)) (.binary .ne (.var "masked") (.intLit 0))]

def tickScanDefaultExpr (lte : Bool) : Expr :=
  if lte then .var "bitPos"
  else .cast (.binary .sub (.intLit 255) (.var "bitPos")) (.elem (.int (.uint ⟨8, by decide⟩)))

def tickScanIndexName (lte : Bool) : Ident := if lte then "msb" else "lsb"
def tickScanIndexFunctionName (lte : Bool) : Ident :=
  if lte then "BitMath_mostSignificantBit" else "BitMath_leastSignificantBit"

def tickScanDistanceExpr (lte : Bool) : Expr :=
  .cast (if lte then .binary .sub (.var "bitPos") (.var "msb")
    else .binary .sub (.var "lsb") (.var "bitPos")) (.elem (.int (.uint ⟨8, by decide⟩)))

def tickScanInitializedStmts (lte : Bool) : List Stmt :=
  [.internalCall (tickScanIndexFunctionName lte) [.var "masked"] (tickScanIndexName lte),
   .assign .localVar {base := "next"} (tickScanNextExpr (tickScanDistanceExpr lte) lte)]

def tickScanTailStmts (lte : Bool) : List Stmt :=
  [.letDecl "next" (some (.elem (.int (.sint ⟨24, by decide⟩))))
      (tickScanNextExpr (tickScanDefaultExpr lte) lte),
     .ite (.var "initialized") (tickScanInitializedStmts lte) [],
     .return [.var "next", .var "initialized"]]

def tickScanBranchStmts (lte : Bool) : List Stmt := tickScanPreludeStmts lte ++ tickScanTailStmts lte

def tickScanIncrementExpr : Expr :=
  .cast (.binary .add (.var "compressed") (.intLit 1)) (.elem (.int (.sint ⟨24, by decide⟩)))

theorem tickScan_body_eq : tickScanFunction.body =
    [.internalCall "TickBitmap_compress" [.var "tick", .var "tickSpacing"] "compressed",
     .ite (.var "lte") (tickScanBranchStmts true)
       (.assign .localVar {base := "compressed"} tickScanIncrementExpr :: tickScanBranchStmts false)] := rfl

end Benchmarks.UniswapV4PoolManager
