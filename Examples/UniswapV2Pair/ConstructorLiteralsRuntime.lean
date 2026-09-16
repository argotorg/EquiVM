import Examples.UniswapV2Pair.ConstructorHashEntry

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace UniswapV2Pair

set_option maxRecDepth 2000

set_option maxHeartbeats 1000000 in
theorem RD.uniswapConstructorLiterals {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {typeHash : UInt256} {R : List UInt256} {k C : Nat}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (rd49 : RD uniswapV2PairInitcode I g s0 ⟨49⟩
      (typeHash :: ⟨64⟩ :: ⟨128⟩ :: ⟨128⟩ :: ⟨1⟩ :: R)
      constructorTypeInputMem ⟨7⟩ ByteArray.empty acc k C)
    (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairInitcode I g s0 ⟨100⟩
      (⟨256⟩ :: typeHash :: ⟨64⟩ :: ⟨32⟩ :: ⟨128⟩ :: ⟨1⟩ :: R)
      constructorLiteralMem ⟨8⟩ ByteArray.empty acc k' C' := by
  have rd53 := evm_run rd49 with [dup3, dup3, add, dup3]
  have rd54 := RD.mstoreWord rd53 (by native_decide) (by evm_ov)
  have rd57 := evm_run rd54 with [push1 ⟨10⟩, dup4]
  have rd58 := RD.mstoreWord rd57 (by native_decide) (by evm_ov)
  have rd69 := RD.pushConst rd58 ⟨201718945720142287350553⟩ (width := 10) (op := .PUSH10)
    (by native_decide) (by native_decide) (by evm_ov)
  have rd77 := evm_run rd69 with [push1 ⟨177⟩, shl, push1 ⟨32⟩, swap4, dup5, add]
  have rd78 := RD.mstoreWord rd77 (by native_decide) (by evm_ov)
  have rd79 := evm_run rd78 with [dup2]
  have rd80 := RD.mloadWord (value := ⟨192⟩) rd79 (by native_decide)
    (by unfold memoryWordLoad; native_decide) (by evm_ov)
  have rd84 := evm_run rd80 with [dup1, dup4, add, dup4]
  have rd85 := RD.mstoreWord rd84 (by native_decide) (by evm_ov)
  have rd88 := evm_run rd85 with [push1 ⟨1⟩, dup2]
  have rd89 := RD.mstoreWord rd88 (by native_decide) (by evm_ov)
  have rd97 := evm_run rd89 with [push1 ⟨49⟩, push1 ⟨248⟩, shl, swap1, dup5, add]
  have rd98 := RD.mstoreWord rd97 (by native_decide) (by evm_ov)
  have rd99 := evm_run rd98 with [dup2]
  exact ⟨_, _, RD.mloadWord (value := ⟨256⟩) rd99 (by native_decide)
    (by unfold memoryWordLoad; native_decide) (by evm_ov)⟩

end UniswapV2Pair
