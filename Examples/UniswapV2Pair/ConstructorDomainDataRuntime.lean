import Examples.UniswapV2Pair.ConstructorDomainMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace UniswapV2Pair

set_option maxRecDepth 2000

set_option maxHeartbeats 1000000 in
theorem RD.uniswapConstructorDomainData {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {typeHash : UInt256} {R : List UInt256} {k C : Nat}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (rd100 : RD uniswapV2PairInitcode I g s0 ⟨100⟩
      (⟨256⟩ :: typeHash :: ⟨64⟩ :: ⟨32⟩ :: ⟨128⟩ :: ⟨1⟩ :: R)
      constructorLiteralMem ⟨8⟩ ByteArray.empty acc k C)
    (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairInitcode I g s0 ⟨200⟩
      (⟨160⟩ :: ⟨64⟩ :: ⟨32⟩ :: ⟨128⟩ :: ⟨256⟩ :: R)
      (constructorDomainDataMem typeHash (UInt256.ofNat I.codeOwner.val))
      ⟨14⟩ ByteArray.empty acc k' C' := by
  have rd106 := evm_run rd100 with [dup1, dup5, add, swap2, swap1, swap2]
  have rd107 := RD.mstoreWord rd106 (by native_decide) (by evm_ov)
  have rd140 := RD.pushConst rd107 constructorNameHashWord (width := 32) (op := .PUSH32)
    (by native_decide) (by native_decide) (by evm_ov)
  have rd143 := evm_run rd140 with [dup2, dup4, add]
  have rd144 := RD.mstoreWord rd143 (by native_decide) (by evm_ov)
  have rd177 := RD.pushConst rd144 constructorVersionHashWord (width := 32) (op := .PUSH32)
    (by native_decide) (by native_decide) (by evm_ov)
  have rd181 := evm_run rd177 with [push1 ⟨96⟩, dup3, add]
  have rd182 := RD.mstoreWord rd181 (by native_decide) (by evm_ov)
  have rd189 := evm_run rd182 with [push1 ⟨128⟩, dup2, add, swap5, swap1, swap5]
  have rd190 := RD.mstoreWord rd189 (by native_decide) (by evm_ov)
  have rd199 := evm_run rd190 with [address, push1 ⟨160⟩, dup1, dup7, add, swap2, swap1, swap2]
  exact ⟨_, _, RD.mstoreWord rd199 (by native_decide) (by evm_ov)⟩

end UniswapV2Pair
