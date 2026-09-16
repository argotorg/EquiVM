import Examples.UniswapV2Pair.MintRuntimeBalance

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1000000 in
theorem uniswapBurnRuntimeReservesLoaded
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {toWord ret sel : UInt256} {k C : ℕ}
    (rd4179 : RD uniswapV2PairBytecode I g s0 ⟨4179⟩
      [⟨0⟩, ⟨0⟩, ⟨0⟩, toWord, ret, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD uniswapV2PairBytecode I g s0 ⟨4189⟩
      [reserve1Word σ I, reserve0Word σ I, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, toWord, ret, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd2852 := evm_run rd4179 with [dup1, push2 ⟨4187⟩, push2 ⟨2852⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd4187⟩ := RD.uniswapGetReservesRoutine rd2852 (by jump_dest) (by evm_ov)
  have rd4189 := evm_run rd4187 with [jumpdest, pop]
  exact ⟨_, _, rd4189⟩

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1000000 in
theorem uniswapBurnRuntimeFirstBalanceOfExtcodesize
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {toWord ret sel : UInt256} {k C : ℕ}
    (rd4179 : RD uniswapV2PairBytecode I g s0 ⟨4179⟩
      [⟨0⟩, ⟨0⟩, ⟨0⟩, toWord, ret, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD uniswapV2PairBytecode I g s0 ⟨4267⟩
      [UInt256.land solcAddrMask (uniswapSlotWord ⟨6⟩ σ I),
        UInt256.land solcAddrMask (uniswapSlotWord ⟨6⟩ σ I),
        ⟨128⟩, ⟨36⟩, ⟨128⟩, ⟨32⟩, ⟨164⟩, balanceOfSelectorWord,
        UInt256.land solcAddrMask (uniswapSlotWord ⟨6⟩ σ I), ⟨0⟩,
        UInt256.land solcAddrMask (uniswapSlotWord ⟨7⟩ σ I),
        UInt256.land solcAddrMask (uniswapSlotWord ⟨6⟩ σ I),
        reserve1Word σ I, reserve0Word σ I, ⟨0⟩, ⟨0⟩, toWord, ret, sel]
      (balanceOfThisCalldataMem (UInt256.ofNat I.codeOwner.val)) (UInt256.ofNat 6)
      ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, rd4189⟩ := uniswapBurnRuntimeReservesLoaded rd4179
  have rd4191 := evm_run rd4189 with [push1 ⟨6⟩]
  obtain ⟨_, _, rd4192⟩ := rd4191.sload (by native_decide) (by evm_ov)
  have rd4194 := evm_run rd4192 with [push1 ⟨7⟩]
  obtain ⟨_, _, rd4195⟩ := rd4194.sload (by native_decide) (by evm_ov)
  have rd4208 := evm_run rd4195 with [push1 ⟨64⟩, dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    push4 balanceOfSelectorWord, push1 ⟨224⟩, shl, dup2]
  have rd4209 := rd4208.mstore 6 balanceOfThisSelectorMem (UInt256.ofNat 5)
    (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)
  have rd4214 := evm_run rd4209 with [address, push1 ⟨4⟩, dup3, add]
  have rd4215 := rd4214.mstore 3
    (balanceOfThisCalldataMem (UInt256.ofNat I.codeOwner.val)) (UInt256.ofNat 6)
    (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)
  have rd4238 := evm_run rd4215 with [swap1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide)
      mem_cost (balanceOfThisCalldataMem_mload64 (UInt256.ofNat I.codeOwner.val))
      (by decide) (by evm_ov),
    swap5, swap7, pop, swap3, swap5, pop,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, swap2, dup3, and, swap4, swap2, and, swap2]
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
    solcAddrMask from by decide] at rd4238
  have rd4267 := evm_run rd4238 with [push1 ⟨0⟩, swap2, dup5, swap2,
    push4 balanceOfSelectorWord, swap2, push1 ⟨36⟩, dup1, dup4, add,
    swap3, push1 ⟨32⟩, swap3, swap2, swap1, dup3, swap1, sub, add, dup2, dup7, dup1]
  rw [show (⟨128⟩ : UInt256) + ⟨36⟩ = ⟨164⟩ from by decide,
    show UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ = ⟨0⟩ from by decide,
    show (⟨0⟩ : UInt256) + ⟨36⟩ = ⟨36⟩ from by decide] at rd4267
  exact ⟨_, _, by simpa [uniswapSlotWord] using rd4267⟩

set_option maxHeartbeats 1000000 in
theorem uniswapBurnRuntimeFirstBalanceOfMissingCodeReverts
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {mem rdata : ByteArray} {aw target : UInt256} {R : List UInt256} {k C : ℕ}
    (rd4267 : RD uniswapV2PairBytecode I g s0 ⟨4267⟩
      (target :: target :: R) mem aw rdata (cA, σ) k C)
    (hnoCode : extCodeSizeWord σ target = ⟨0⟩) (hov : R.length + 4 ≤ 1024) :
    RDrev uniswapV2PairBytecode g s0 := by
  exact RD.solcExtcodesizeGuardMissing (okPc := ⟨4279⟩) rd4267 hnoCode
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) hov

end UniswapV2Pair
