import Benchmarks.Morpho.MetaMorphoV1_1.MaxDepositReadersSource
import Benchmarks.Morpho.MetaMorphoV1_1.MaxDepositArithmeticSource

/-! Named loop fragments of the allocated max-deposit source function. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

def maxDepositCondition : Expr :=
  .binary .lt (.var "i") (.arrayLength .storage { base := "supplyQueue", steps := [] })

def maxDepositPost : List Stmt :=
  [.assign .localVar { base := "i", steps := [] }
    (.inRange (.uint ⟨256, by decide⟩) (.binary .add (.var "i") (.intLit 1)))]

def maxDepositCapCondition : Expr := .binary .eq (.var "supplyCap") (.intLit 0)

def maxDepositIteration : List Stmt :=
  [.letDecl "id" (some (.elem (.bytes ⟨31, by decide⟩)))
     (.storage { base := "supplyQueue", steps := [.aindex (.var "i")] }),
   .letDecl "supplyCap" (some abiUInt256)
     (.storage { base := "config", steps := [.mindex (.var "id"), .field "cap"] }),
   .ite maxDepositCapCondition [.continue] []] ++ maxDepositReaders ++ maxDepositArithmetic

set_option maxRecDepth 2000 in
theorem allocatedMaxDepositFunction_body :
    allocatedMaxDepositFunction.body =
      [.letDecl "totalSuppliable" (some abiUInt256) (.intLit 0),
       .for [.letDecl "i" (some abiUInt256) (.intLit 0)] maxDepositCondition maxDepositPost
         maxDepositIteration,
       .return [.var "totalSuppliable", .var cursorName]] := by
  decide +kernel

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
