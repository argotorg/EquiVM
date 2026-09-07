import Examples.UniswapV2Pair.ConstructorMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace UniswapV2Pair

set_option maxRecDepth 2000

set_option maxHeartbeats 1000000 in
theorem RD.uniswapConstructorTypeHash {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {R : List UInt256} {k C : Nat}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (rd23 : RD uniswapV2PairInitcode I g s0 ⟨23⟩ R solcFreePtrMem ⟨3⟩ ByteArray.empty acc k C)
    (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairInitcode I g s0 ⟨49⟩
      (constructorTypeHashWord :: ⟨64⟩ :: ⟨128⟩ :: ⟨128⟩ :: ⟨1⟩ :: R)
      constructorTypeInputMem ⟨7⟩ ByteArray.empty acc k' C' := by
  have rd25 := evm_run rd23 with [push1 ⟨64⟩]
  have rd26 := RD.mloadWord rd25 (by native_decide)
    solcFreePtrMem_mload64 (by evm_ov)
  have rd27 := RD.chainid rd26 (by native_decide) (by evm_ov)
  have rd35 := evm_run rd27 with [swap1, dup1, push1 ⟨82⟩, push2 ⟨9094⟩, dup3]
  have rd36 := RD.codecopyAny rd35 (by native_decide) (by evm_ov)
  have rd39 := evm_run rd36 with [push1 ⟨64⟩, dup1]
  have rd40 := RD.mloadWord rd39 (by native_decide) constructorTypeInputMem_mload64 (by evm_ov)
  have rd48 := evm_run rd40 with [swap2, dup3, swap1, sub, push1 ⟨82⟩, add, dup3]
  refine ⟨_, _, RD.keccak256 0 constructorTypeHashWord ⟨7⟩ rd48
    (by native_decide) ?_ ?_ ?_ (by evm_ov)⟩
  · intro s haw hstk
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
      List.getElem!_cons_zero, List.getElem!_cons_succ]
    native_decide
  · change UInt256.ofNat (fromByteArrayBigEndian (ffi.KEC
      (constructorTypeInputMem.readWithPadding 128 82))) = _
    rw [constructorTypeInputMem_read]
  · native_decide

end UniswapV2Pair
