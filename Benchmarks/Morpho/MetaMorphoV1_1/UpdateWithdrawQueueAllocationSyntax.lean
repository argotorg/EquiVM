import Benchmarks.Morpho.MetaMorphoV1_1.MaxDepositAllocationSyntax

/-! Memory accounting for the two withdrawal-queue arrays and the supply-share reader. -/

open Solm ABI

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

def reserveWordArray (length : Ident) : Stmt :=
  .internalCall allocateFunction.name
    [.var cursorName, .binary .add (.intLit 32) (.binary .mul (.intLit 32) (.var length))]
    cursorName

def allocatedUpdateWithdrawQueueTransition : TransitionDecl :=
  let source := Syntax.contractSyntax.transitions[20]!
  { source with
    body := source.body.take 7 ++
      [.letDecl cursorName none (.intLit 128), reserveWordArray "currLength"] ++
      (source.body.drop 7).take 2 ++ [reserveWordArray "newLength"] ++
      allocationBody (fun name ↦
        if name == "MorphoLib_supplyShares" then some allocatedSupplySharesFunction.name
        else none) (fun _ ↦ 0) (source.body.drop 9) }

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
