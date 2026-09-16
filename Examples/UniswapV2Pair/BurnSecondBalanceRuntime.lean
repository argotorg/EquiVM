import Examples.UniswapV2Pair.BurnFirstBalanceRuntime

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

set_option maxHeartbeats 1000000 in
theorem uniswapBurnRuntimeSecondBalanceOfExtcodesize
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {out : ByteArray} {balance0 token1 : UInt256} {R : List UInt256} {k C : ℕ}
    (rd4324 : RD uniswapV2PairBytecode I g s0 ⟨4324⟩
      (balance0 :: ⟨0⟩ :: token1 :: R)
      (balanceOfThisStaticcallMem (UInt256.ofNat I.codeOwner.val) out)
      balanceOfThisStaticcallActiveWords out (cA, σ) k C)
    (hout32 : 32 ≤ out.size) (houtSize : out.size < UInt256.size)
    (hov : R.length + 24 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g s0 ⟨4387⟩
      (UInt256.land token1 solcAddrMask :: UInt256.land token1 solcAddrMask ::
        ⟨128⟩ :: ⟨36⟩ :: ⟨128⟩ :: ⟨32⟩ :: ⟨164⟩ :: balanceOfSelectorWord ::
        UInt256.land token1 solcAddrMask :: ⟨0⟩ :: balance0 :: token1 :: R)
      (balanceOfThisRebuiltCalldataMem (UInt256.ofNat I.codeOwner.val) out)
      balanceOfThisStaticcallActiveWords out (cA, σ) k' C' := by
  have rd4337 := evm_run rd4324 with [push1 ⟨64⟩, dup1,
    raw mload 0 ⟨128⟩ balanceOfThisStaticcallActiveWords (by decide)
      mem_cost (balanceOfThisStaticcallMem_mload64_of_size_ge
        (UInt256.ofNat I.codeOwner.val) out hout32 houtSize)
      (by decide) (by simp only [List.length_cons]; omega),
    push4 balanceOfSelectorWord, push1 ⟨224⟩, shl, dup2]
  have rd4338 := rd4337.mstore 0
    ((UInt256.toByteArray balanceOfSelectorShifted).write 0
      (balanceOfThisStaticcallMem (UInt256.ofNat I.codeOwner.val) out) 128 32)
    balanceOfThisStaticcallActiveWords
    (by native_decide) mem_cost rfl (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd4343 := evm_run rd4338 with [address, push1 ⟨4⟩, dup3, add]
  have rd4344 := rd4343.mstore 0
    (balanceOfThisRebuiltCalldataMem (UInt256.ofNat I.codeOwner.val) out)
    balanceOfThisStaticcallActiveWords
    (by native_decide) mem_cost rfl (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd4363 := evm_run rd4344 with [swap1,
    raw mload 0 ⟨128⟩ balanceOfThisStaticcallActiveWords (by decide)
      mem_cost (balanceOfThisRebuiltCalldataMem_mload64_of_size_ge
        (UInt256.ofNat I.codeOwner.val) out hout32 houtSize)
      (by decide) (by simp only [List.length_cons]; omega),
    swap2, swap3, pop, push1 ⟨0⟩, swap2,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup6, and, swap2]
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
    solcAddrMask from by decide] at rd4363
  have rd4387 := evm_run rd4363 with [push4 balanceOfSelectorWord, swap2,
    push1 ⟨36⟩, dup1, dup4, add, swap3, push1 ⟨32⟩, swap3, swap2, swap1,
    dup3, swap1, sub, add, dup2, dup7, dup1]
  rw [show (⟨128⟩ : UInt256) + ⟨36⟩ = ⟨164⟩ from by decide,
    show UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ = ⟨0⟩ from by decide,
    show (⟨0⟩ : UInt256) + ⟨36⟩ = ⟨36⟩ from by decide] at rd4387
  exact ⟨_, _, rd4387⟩

set_option maxHeartbeats 1000000 in
theorem uniswapBurnRuntimeSecondBalanceOfResultBranchesOfTail
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {o : ByteArray} {target : UInt256} {R : List UInt256} {k C : ℕ}
    (rd4387 : RD uniswapV2PairBytecode I g s0 ⟨4387⟩
      (target :: target :: ⟨128⟩ :: ⟨36⟩ :: ⟨128⟩ :: ⟨32⟩ :: ⟨164⟩ ::
        balanceOfSelectorWord :: target :: R)
      (balanceOfThisRebuiltCalldataMem (UInt256.ofNat I.codeOwner.val) o) balanceOfThisStaticcallActiveWords
      o (cA, σ) k C)
    (hdepth : I.depth.val < 1024) (hcode : extCodeSizeWord σ target ≠ ⟨0⟩)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hov : R.length + 20 ≤ 1024) :
    ∃ (cA'' : Batteries.RBSet AccountAddress compare) (σ'' : AccountMap)
      (z1 : Bool) (o1 : ByteArray) (A_in1 : Substate) (callGas1 : UInt256),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA'', σ'', g'', A', z1, o1) = Ethereum.EVM.Θ I.blobVersionedHashes
          cA s0.genesisBlockHeader s0.blocks σ s0.σ₀ A_in1
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner.val)) I.sender
          (AccountAddress.ofUInt256 target) (toExecute σ (AccountAddress.ofUInt256 target))
          callGas1 (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((balanceOfThisRebuiltCalldataMem (UInt256.ofNat I.codeOwner.val) o).readWithPadding 128 36)
          (I.depth + 1) I.header false)
      ∧ (z1 = false → RDrev uniswapV2PairBytecode g s0)
      ∧ (z1 = true → o1.size < 32 → RDrev uniswapV2PairBytecode g s0)
      ∧ (z1 = true → 32 ≤ o1.size → ∃ k' C',
        RD uniswapV2PairBytecode I g s0 ⟨4444⟩
          (UInt256.ofNat (fromByteArrayBigEndian (o1.extract 0 32)) :: R)
          (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
          balanceOfThisStaticcallActiveWords o1 (cA'', σ'') k' C')
      ∧ o1.size < UInt256.size := by
  obtain ⟨gasWord, _, _, rd4402⟩ :=
    RD.solcExtcodesizeGuardOkGas (okPc := ⟨4399⟩) rd4387 hcode
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest)
      (by native_decide) (by native_decide) (by native_decide)
      (by simp only [List.length_cons]; omega)
  obtain ⟨cA'', σ'', z1, o1, A_in1, callGas1, k', C', hΘ1, rd4403, ho1Size⟩ :=
    RD.solcStaticcall rd4402 (by native_decide) hdepth
      (by simp only [List.length_cons]; omega)
  refine ⟨cA'', σ'', z1, o1, A_in1, callGas1, ?_, ?_, ?_, ?_, ho1Size⟩
  · simpa [balanceOfThisRebuiltStaticcallMem, initState] using hΘ1
  · intro hz1
    have hstatus : (if z1 then (⟨1⟩ : UInt256) else ⟨0⟩) = ⟨0⟩ := by
      simp [hz1]
    exact RD.solcCallSuccessGuardMissing (okPc := ⟨4419⟩) rd4403 hstatus
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) ho1Size
      (by simp only [List.length_cons]; omega)
  · intro hz1 hshort
    have hstatus : (if z1 then (⟨1⟩ : UInt256) else ⟨0⟩) ≠ ⟨0⟩ := by
      rw [hz1]
      decide
    obtain ⟨_, _, rd4421⟩ :=
      RD.solcCallSuccessGuardOk (okPc := ⟨4419⟩) rd4403 hstatus
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
        (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
        (by simp only [List.length_cons]; omega)
    exact RD.uniswapRebuiltBalanceOfReturnWordDecodeShortReverts
      (pc := ⟨4421⟩) (okPc := ⟨4441⟩) (self := UInt256.ofNat I.codeOwner.val)
      rd4421 ho32 hoSize hshort ho1Size
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by omega)
  · intro hz1 ho132
    have hstatus : (if z1 then (⟨1⟩ : UInt256) else ⟨0⟩) ≠ ⟨0⟩ := by
      rw [hz1]
      decide
    obtain ⟨_, _, rd4421⟩ :=
      RD.solcCallSuccessGuardOk (okPc := ⟨4419⟩) rd4403 hstatus
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
        (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
        (by simp only [List.length_cons]; omega)
    obtain ⟨k'', C'', rd4444⟩ :=
      RD.uniswapRebuiltBalanceOfReturnWordDecodeOk
        (pc := ⟨4421⟩) (okPc := ⟨4441⟩) (self := UInt256.ofNat I.codeOwner.val)
        rd4421 ho32 hoSize ho132 ho1Size
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
        (by jump_dest) (by native_decide) (by native_decide) (by native_decide)
        (by omega)
    exact ⟨k'', C'', rd4444⟩

set_option maxHeartbeats 1000000 in
theorem uniswapBurnRuntimeSecondBalanceOfMissingCodeReverts
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {mem rdata : ByteArray} {aw target : UInt256} {R : List UInt256} {k C : ℕ}
    (rd4387 : RD uniswapV2PairBytecode I g s0 ⟨4387⟩
      (target :: target :: R) mem aw rdata (cA, σ) k C)
    (hnoCode : extCodeSizeWord σ target = ⟨0⟩) (hov : R.length + 4 ≤ 1024) :
    RDrev uniswapV2PairBytecode g s0 := by
  exact RD.solcExtcodesizeGuardMissing (okPc := ⟨4399⟩) rd4387 hnoCode
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) hov

end UniswapV2Pair
