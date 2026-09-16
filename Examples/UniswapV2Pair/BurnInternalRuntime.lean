import Examples.UniswapV2Pair.MintInternalMintRuntime

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
set_option maxRecDepth 2000000
namespace UniswapV2Pair

set_option maxHeartbeats 1000000 in
theorem uniswapInternalBurnRuntimeBalanceSubEntry
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ} {value holder ret : UInt256} {R : List UInt256}
    (rd8302 : RD uniswapV2PairBytecode I g s0 ⟨8302⟩ (value :: holder :: ret :: R)
      mem feeToStaticcallActiveWords rdata (cA, σ) k C)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g s0 ⟨6879⟩
      (value :: uniswapCodeOwnerStorageWord I σ
        (uniswapInternalMintBalanceHashSlot holder mem) ::
        ⟨8343⟩ :: value :: holder :: ret :: R)
      (uniswapInternalMintBalanceHashMem holder mem) feeToStaticcallActiveWords rdata
      (cA, σ) k' C' := by
  have rd8313 := evm_run rd8302 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup3, and]
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide] at rd8313
  have rd8317 := evm_run rd8313 with [push1 ⟨0⟩, swap1, dup2]
  have rd8318 := rd8317.mstore 0 (wordAt0Mem (UInt256.land holder solcAddrMask) mem)
    feeToStaticcallActiveWords (by native_decide) mem_cost (by rfl) (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd8323pre := evm_run rd8318 with [push1 ⟨1⟩, push1 ⟨32⟩]
  have rd8323 := rd8323pre.mstore 0 (uniswapInternalMintBalanceHashMem holder mem)
    feeToStaticcallActiveWords (by native_decide) mem_cost (by rfl) (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd8326 := evm_run rd8323 with [push1 ⟨64⟩, swap1]
  have rd8327 := rd8326.keccak256 0 (uniswapInternalMintBalanceHashSlot holder mem)
    feeToStaticcallActiveWords (by native_decide) mem_cost (by rfl) (by native_decide)
    (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rd8328⟩ := rd8327.sload (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd8342 := evm_run rd8328 with [
    push2 ⟨8343⟩, swap1, dup3, push4 ⟨0xffffffff⟩, push2 ⟨6879⟩, and]
  rw [show UInt256.land (⟨6879⟩ : UInt256) ⟨0xffffffff⟩ = ⟨6879⟩ from by decide] at rd8342
  exact ⟨_, _, rd8342.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem uniswapInternalBurnRuntimeStoreBalanceSupplySubEntry
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ}
    {newBalance value holder ret : UInt256} {R : List UInt256}
    (rd8343 : RD uniswapV2PairBytecode I g s0 ⟨8343⟩
      (newBalance :: value :: holder :: ret :: R)
      mem feeToStaticcallActiveWords rdata (cA, σ) k C)
    (hperm : I.perm = true) (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g s0 ⟨6879⟩
      (value :: uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σ
          (uniswapInternalMintBalanceHashSlot holder mem) newBalance) ⟨0⟩ ::
        ⟨8388⟩ :: value :: holder :: ret :: R)
      (uniswapInternalMintBalanceHashMem holder mem) feeToStaticcallActiveWords rdata
      (cA, sstoreAccountMap I.codeOwner σ
        (uniswapInternalMintBalanceHashSlot holder mem) newBalance) k' C' := by
  have rd8354 := evm_run rd8343 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup4, and]
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide] at rd8354
  have rd8358 := evm_run rd8354 with [push1 ⟨0⟩, swap1, dup2]
  have rd8359 := rd8358.mstore 0 (wordAt0Mem (UInt256.land holder solcAddrMask) mem)
    feeToStaticcallActiveWords (by native_decide) mem_cost (by rfl) (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd8364pre := evm_run rd8359 with [push1 ⟨1⟩, push1 ⟨32⟩]
  have rd8364 := rd8364pre.mstore 0 (uniswapInternalMintBalanceHashMem holder mem)
    feeToStaticcallActiveWords (by native_decide) mem_cost (by rfl) (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd8367 := evm_run rd8364 with [push1 ⟨64⟩, dup2]
  have rd8368 := rd8367.keccak256 0 (uniswapInternalMintBalanceHashSlot holder mem)
    feeToStaticcallActiveWords (by native_decide) mem_cost (by rfl) (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd8371 := evm_run rd8368 with [swap2, swap1, swap2]
  obtain ⟨_, _, rd8372⟩ := rd8371.sstore hperm (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd8373⟩ := rd8372.sload (by native_decide) (by evm_ov)
  have rd8387 := evm_run rd8373 with [
    push2 ⟨8388⟩, swap1, dup3, push4 ⟨0xffffffff⟩, push2 ⟨6879⟩, and]
  rw [show UInt256.land (⟨6879⟩ : UInt256) ⟨0xffffffff⟩ = ⟨6879⟩ from by decide] at rd8387
  exact ⟨_, _, rd8387.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem uniswapInternalBurnRuntimeStoreSupplyEmitAndJump
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ}
    {newSupply value holder ret : UInt256} {R : List UInt256}
    (rd8388 : RD uniswapV2PairBytecode I g s0 ⟨8388⟩
      (newSupply :: value :: holder :: ret :: R)
      mem feeToStaticcallActiveWords rdata (cA, σ) k C)
    (hperm : I.perm = true) (hmem : 160 ≤ mem.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hret : (D_J uniswapV2PairBytecode 0).contains ret = true)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g s0 ret R
      (uniswapInternalMintLogMem value mem) feeToStaticcallActiveWords rdata
      (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩ newSupply) k' C' := by
  have rd8393 := evm_run rd8388 with [jumpdest, push1 ⟨0⟩, swap1, dup2]
  obtain ⟨_, _, rd8394⟩ := rd8393.sstore hperm (by native_decide) (by evm_ov)
  have rd8397 := evm_run rd8394 with [push1 ⟨64⟩, dup1]
  have rd8398 := rd8397.mload 0 ⟨128⟩ feeToStaticcallActiveWords
    (by native_decide) mem_cost
    (mloadFreePtrValue (by omega) (by native_decide) hread64)
    (by native_decide) (by evm_ov)
  have rd8400 := evm_run rd8398 with [dup4, dup2]
  have rd8401 := rd8400.mstore 0 (uniswapInternalMintLogMem value mem)
    feeToStaticcallActiveWords (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd8402 := evm_run rd8401 with [swap1]
  have rd8403 := rd8402.mload 0 ⟨128⟩ feeToStaticcallActiveWords
    (by native_decide) mem_cost
    (mloadFreePtrValue
      (by rw [uniswapInternalMintLogMem_size_of_ge160 value hmem]; omega)
      (by native_decide) (uniswapInternalMintLogMem_read64_of_ge160 value hmem hread64))
    (by native_decide) (by evm_ov)
  have rd8414 := evm_run rd8403 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup6, and, swap2]
  have rd8447 := rd8414.pushConst
    (⟨100389287136786176327247604509743168900146139575972864366142685224231313322991⟩ : UInt256)
    (width := 32) (op := .PUSH32) (by native_decide) (by decide) (by evm_ov)
  have rd8456 := evm_run rd8447 with [
    swap2, swap1, dup2, swap1, sub, push1 ⟨32⟩, add, swap1]
  have rd8457 := rd8456.log3 0 feeToStaticcallActiveWords (by native_decide) hperm
    mem_cost (by native_decide) (by evm_ov)
  have rd8459 := evm_run rd8457 with [pop, pop]
  exact ⟨_, _, rd8459.jump (by native_decide) hret (by evm_ov)⟩

end UniswapV2Pair
