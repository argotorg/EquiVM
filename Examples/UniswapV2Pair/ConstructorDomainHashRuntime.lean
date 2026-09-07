import Examples.UniswapV2Pair.ConstructorDomainDataRuntime

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace UniswapV2Pair

set_option maxRecDepth 2000

noncomputable abbrev constructorDomainHashWord (thisWord : UInt256) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (ffi.KEC
    (constructorDomainBytes constructorTypeHashWord thisWord)))

set_option maxHeartbeats 1000000 in
theorem RD.uniswapConstructorDomainHash {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {R : List UInt256} {k C : Nat}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (rd200 : RD uniswapV2PairInitcode I g s0 ⟨200⟩
      (⟨160⟩ :: ⟨64⟩ :: ⟨32⟩ :: ⟨128⟩ :: ⟨256⟩ :: R)
      (constructorDomainDataMem constructorTypeHashWord (UInt256.ofNat I.codeOwner.val))
      ⟨14⟩ ByteArray.empty acc k C)
    (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairInitcode I g s0 ⟨225⟩
      (constructorDomainHashWord (UInt256.ofNat I.codeOwner.val) :: ⟨128⟩ :: R)
      (constructorDomainMem constructorTypeHashWord (UInt256.ofNat I.codeOwner.val))
      ⟨14⟩ ByteArray.empty acc k' C' := by
  have rd201 := evm_run rd200 with [dup2]
  have hm64 : memoryWordLoad
      (constructorDomainDataMem constructorTypeHashWord (UInt256.ofNat I.codeOwner.val))
      ⟨14⟩ ⟨64⟩ = ⟨256⟩ := by
    apply mloadWordValue_of_readWithPadding
    · rw [constructorDomainDataMem_size]; decide
    · native_decide
    · exact constructorDomainDataMem_read64 _ _
  have rd202 := RD.mloadWord rd201 (by native_decide) hm64 (by evm_ov)
  have rd209 := evm_run rd202 with [dup1, dup7, sub, swap1, swap2, add, dup2]
  have rd210 := RD.mstoreWord rd209 (by native_decide) (by evm_ov)
  have rd216 := evm_run rd210 with [push1 ⟨192⟩, swap1, swap5, add, swap1]
  have rd217 := RD.mstoreWord rd216 (by native_decide) (by evm_ov)
  have rd218 := evm_run rd217 with [dup3]
  have hm256 : memoryWordLoad
      (constructorDomainMem constructorTypeHashWord (UInt256.ofNat I.codeOwner.val))
      ⟨14⟩ ⟨256⟩ = ⟨160⟩ := by
    apply mloadWordValue_of_readWithPadding
    · rw [constructorDomainMem_size]; decide
    · native_decide
    · exact constructorDomainMem_read256 _ _
  have rd219 := RD.mloadWord rd218 (by native_decide) hm256 (by evm_ov)
  have rd224 := evm_run rd219 with [swap3, add, swap2, swap1, swap2]
  refine ⟨_, _, RD.keccak256 0 _ ⟨14⟩ rd224 (by native_decide) ?_ ?_ ?_ (by evm_ov)⟩
  · intro s haw hstk
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
      List.getElem!_cons_zero, List.getElem!_cons_succ]
    native_decide
  · change UInt256.ofNat (fromByteArrayBigEndian (ffi.KEC
      ((constructorDomainMem _ _).readWithPadding 288 160))) = _
    rw [constructorDomainMem_read288]
  · native_decide

end UniswapV2Pair
