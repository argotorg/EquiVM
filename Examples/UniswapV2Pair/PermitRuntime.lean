import Examples.UniswapV2Pair.PermitHashMemory
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000



namespace UniswapV2Pair

set_option maxHeartbeats 2000000 in
theorem RD.uniswapPermitStructHash {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {nonce owner spender value deadline domain s r v ret : UInt256}
    {R : List UInt256} {baseMem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5589⟩
      (nonce :: ⟨1⟩ :: ⟨64⟩ :: ⟨32⟩ :: ⟨0⟩ :: owner :: solcAddrMask ::
        domain :: s :: r :: v :: deadline :: value :: spender :: owner :: ret :: R)
      baseMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hbaseSize : baseMem.size = 96)
    (hbaseRead64 :
      baseMem.readWithPadding 64 32 = UInt256.toByteArray (⟨128⟩ : UInt256))
    (hspenderMask : UInt256.land spender solcAddrMask = spender)
    (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5688⟩
      (permitRuntimeStructHashWord baseMem owner spender value nonce deadline ::
        ⟨64⟩ :: ⟨32⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨1⟩ ::
        domain :: s :: r :: v :: deadline :: value :: spender :: owner :: ret :: R)
      (permitRuntimeStructHashMem baseMem owner spender value nonce deadline)
      (UInt256.ofNat 11) rdata (cA, σ) k' C' := by
  have hbaseMload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ baseMem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          (baseMem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩ :=
    mloadWordValue_of_readWithPadding
      (by rw [hbaseSize]; decide)
      (by native_decide)
      hbaseRead64
  have rd5591 := evm_run h with [
    dup3,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost hbaseMload64 (by native_decide) (by evm_ov)]
  have rd5624 := rd5591.pushConst permitRuntimeTypehashWord (width := 32) (op := .PUSH32)
    (by native_decide) (by native_decide) (by evm_ov)
  have rd5627 := evm_run rd5624 with [dup2, dup7, add]
  have rd5628 := evm_run rd5627 with [
    raw mstore 9 (permitRuntimeStructHashDataMem0 baseMem)
      (UInt256.ofNat 6) (by native_decide) mem_cost (by rfl)
      (by native_decide) (by evm_ov)]
  have rd5634 := evm_run rd5628 with [
    dup1, dup5, add, swap7, swap1, swap7,
    raw mstore 3 (permitRuntimeStructHashDataMem1 baseMem owner)
      (UInt256.ofNat 7) (by native_decide) mem_cost (by rfl)
      (by native_decide) (by evm_ov)]
  have rd5638₀ := evm_run rd5634 with [swap6, dup14, and]
  have rd5638 := rd5638₀
  rw [hspenderMask] at rd5638
  have rd5643 := evm_run rd5638 with [
    push1 ⟨96⟩, dup7, add,
    raw mstore 3 (permitRuntimeStructHashDataMem2 baseMem owner spender)
      (UInt256.ofNat 8) (by native_decide) mem_cost (by rfl)
      (by native_decide) (by evm_ov)]
  have rd5650 := evm_run rd5643 with [
    push1 ⟨128⟩, dup6, add, dup13, swap1,
    raw mstore 3 (permitRuntimeStructHashDataMem3 baseMem owner spender value)
      (UInt256.ofNat 9) (by native_decide) mem_cost (by rfl)
      (by native_decide) (by evm_ov)]
  have rd5658 := evm_run rd5650 with [
    push1 ⟨160⟩, dup6, add, swap6, swap1, swap6,
    raw mstore 3 (permitRuntimeStructHashDataMem4 baseMem owner spender value nonce)
      (UInt256.ofNat 10) (by native_decide) mem_cost (by rfl)
      (by native_decide) (by evm_ov)]
  have rd5666 := evm_run rd5658 with [
    push1 ⟨192⟩, dup1, dup6, add, raw dup12 (by native_decide) (by evm_ov), swap1,
    raw mstore 3 (permitRuntimeStructHashDataMem baseMem owner spender value nonce deadline)
      (UInt256.ofNat 11) (by native_decide) mem_cost (by rfl)
      (by native_decide) (by evm_ov)]
  have rd5676 := evm_run rd5666 with [
    dup2,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 11) (by native_decide)
      mem_cost
      (permitRuntimeStructHashDataMem_mload64 owner spender value nonce deadline hbaseSize
        hbaseRead64)
      (by native_decide) (by evm_ov),
    dup1, dup7, sub, swap1, swap2, add, dup2,
    raw mstore 0 (permitRuntimeStructHashLenMem baseMem owner spender value nonce deadline)
      (UInt256.ofNat 11) (by native_decide) mem_cost (by rfl)
      (by native_decide) (by evm_ov)]
  have rd5682 := evm_run rd5676 with [
    push1 ⟨224⟩, dup6, add, dup3,
    raw mstore 0 (permitRuntimeStructHashMem baseMem owner spender value nonce deadline)
      (UInt256.ofNat 11) (by native_decide) mem_cost (by rfl)
      (by native_decide) (by evm_ov)]
  have rd5688 := evm_run rd5682 with [
    dup1,
    raw mload 0 ⟨192⟩ (UInt256.ofNat 11) (by native_decide)
      mem_cost
      (permitRuntimeStructHashMem_mload128 owner spender value nonce deadline hbaseSize)
      (by native_decide) (by evm_ov),
    swap1, dup4, add,
    raw keccak256 0
      (permitRuntimeStructHashWord baseMem owner spender value nonce deadline)
      (UInt256.ofNat 11) (by native_decide) mem_cost (by rfl)
      (by native_decide) (by evm_ov)]
  exact ⟨_, _, rd5688⟩

set_option maxHeartbeats 2000000 in
theorem RD.uniswapPermitDigestHash {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {structHash domain s r v deadline value spender owner ret : UInt256}
    {R : List UInt256} {baseMem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5688⟩
      (structHash :: ⟨64⟩ :: ⟨32⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨1⟩ ::
        domain :: s :: r :: v :: deadline :: value :: spender :: owner :: ret :: R)
      baseMem (UInt256.ofNat 11) rdata (cA, σ) k C)
    (hbaseSize : baseMem.size = 352)
    (hbaseRead64 :
      baseMem.readWithPadding 64 32 = UInt256.toByteArray (⟨352⟩ : UInt256))
    (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5746⟩
      (permitRuntimeDigestWord baseMem domain structHash ::
        ⟨64⟩ :: ⟨32⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨1⟩ :: ⟨450⟩ ::
        s :: r :: v :: deadline :: value :: spender :: owner :: ret :: R)
      (permitRuntimeDigestMem baseMem domain structHash)
      (UInt256.ofNat 15) rdata (cA, σ) k' C' := by
  have rd5699 := evm_run h with [
    push2 ⟨6401⟩, push1 ⟨240⟩, shl, push2 ⟨256⟩, dup7, add,
    raw mstore 6 (permitRuntimeDigestDataMem0 baseMem)
      (UInt256.ofNat 13) (by native_decide) mem_cost (by rfl)
      (by native_decide) (by evm_ov)]
  have rd5708 := evm_run rd5699 with [
    push2 ⟨258⟩, dup6, add, swap7, swap1, swap7,
    raw mstore 3 (permitRuntimeDigestDataMem1 baseMem domain)
      (UInt256.ofNat 14) (by native_decide) mem_cost (by rfl)
      (by native_decide) (by evm_ov)]
  have rd5718 := evm_run rd5708 with [
    push2 ⟨290⟩, dup1, dup6, add, swap7, swap1, swap7,
    raw mstore 3 (permitRuntimeDigestDataMem baseMem domain structHash)
      (UInt256.ofNat 15) (by native_decide) mem_cost (by rfl)
      (by native_decide) (by evm_ov)]
  have rd5729 := evm_run rd5718 with [
    dup1,
    raw mload 0 ⟨352⟩ (UInt256.ofNat 15) (by native_decide)
      mem_cost
      (permitRuntimeDigestDataMem_mload64 domain structHash hbaseSize hbaseRead64)
      (by native_decide) (by evm_ov),
    dup1, dup6, sub, swap1, swap7, add, dup7,
    raw mstore 0 (permitRuntimeDigestLenMem baseMem domain structHash)
      (UInt256.ofNat 15) (by native_decide) mem_cost (by rfl)
      (by native_decide) (by evm_ov)]
  have rd5737 := evm_run rd5729 with [
    push2 ⟨322⟩, dup5, add, dup1, dup3,
    raw mstore 0 (permitRuntimeDigestMem baseMem domain structHash)
      (UInt256.ofNat 15) (by native_decide) mem_cost (by rfl)
      (by native_decide) (by evm_ov)]
  have rd5746 := evm_run rd5737 with [
    dup7,
    raw mload 0 ⟨66⟩ (UInt256.ofNat 15) (by native_decide)
      mem_cost
      (permitRuntimeDigestMem_mload352 domain structHash hbaseSize)
      (by native_decide) (by evm_ov),
    swap7, dup4, add, swap7, swap1, swap7,
    raw keccak256 0
      (permitRuntimeDigestWord baseMem domain structHash)
      (UInt256.ofNat 15) (by native_decide) mem_cost (by rfl)
      (by native_decide) (by evm_ov)]
  exact ⟨_, _, rd5746⟩

set_option maxHeartbeats 2000000 in
theorem RD.uniswapPermitEcrecoverStaticcallMade {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {digest s r v deadline value spender owner ret : UInt256}
    {R : List UInt256} {baseMem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5746⟩
      (digest :: ⟨64⟩ :: ⟨32⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨1⟩ :: ⟨450⟩ ::
        s :: r :: v :: deadline :: value :: spender :: owner :: ret :: R)
      baseMem (UInt256.ofNat 15) rdata (cA, σ) k C)
    (hbaseSize : baseMem.size = 450)
    (hvMask : UInt256.land (⟨255⟩ : UInt256) v = v)
    (hdepth : ee.depth.val < 1024)
    (hov : R.length + 24 ≤ 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (o : ByteArray) (A_in : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ ee.blobVersionedHashes cA
          s0.genesisBlockHeader s0.blocks σ s0.σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat ee.codeOwner)) ee.sender
          (AccountAddress.ofUInt256 (⟨1⟩ : UInt256))
          (toExecute σ (AccountAddress.ofUInt256 (⟨1⟩ : UInt256)))
          callGas (UInt256.ofNat ee.gasPrice) ⟨0⟩ ⟨0⟩
          ((permitRuntimeEcrecoverInputMem baseMem digest v r s).readWithPadding 482 128)
          (ee.depth + 1) ee.header false)
      ∧ RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5814⟩
          ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨610⟩ :: ⟨1⟩ :: ⟨0⟩ ::
            digest :: s :: r :: v :: deadline :: value :: spender :: owner :: ret :: R)
          (o.write 0 (permitRuntimeEcrecoverInputMem baseMem digest v r s) 450
            (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat)
          (UInt256.ofNat 20) o (cA', σ') k' C'
      ∧ o.size < UInt256.size := by
  have rd5749 := evm_run h with [
    swap6, dup4, swap1,
    raw mstore 3 (permitRuntimeEcrecoverMem0 baseMem)
      (UInt256.ofNat 16) (by native_decide) mem_cost (by rfl)
      (by native_decide) (by evm_ov)]
  have rd5757 := evm_run rd5749 with [
    push2 ⟨354⟩, dup5, add, dup1, dup3,
    raw mstore 0 (permitRuntimeEcrecoverMem1 baseMem)
      (UInt256.ofNat 16) (by native_decide) mem_cost (by rfl)
      (by native_decide) (by evm_ov)]
  have rd5760 := evm_run rd5757 with [
    dup7, swap1,
    raw mstore 3 (permitRuntimeEcrecoverMem2 baseMem digest)
      (UInt256.ofNat 17) (by native_decide) mem_cost (by rfl)
      (by native_decide) (by evm_ov)]
  have rd5764₀ := evm_run rd5760 with [push1 ⟨255⟩, dup10, and]
  have rd5764 := rd5764₀
  rw [u256_land_comm v (⟨255⟩ : UInt256)] at rd5764
  rw [hvMask] at rd5764
  have rd5770 := evm_run rd5764 with [
    push2 ⟨386⟩, dup6, add,
    raw mstore 3 (permitRuntimeEcrecoverMem3 baseMem digest v)
      (UInt256.ofNat 18) (by native_decide) mem_cost (by rfl)
      (by native_decide) (by evm_ov)]
  have rd5778 := evm_run rd5770 with [
    push2 ⟨418⟩, dup5, add, dup9, swap1,
    raw mstore 3 (permitRuntimeEcrecoverMem4 baseMem digest v r)
      (UInt256.ofNat 19) (by native_decide) mem_cost (by rfl)
      (by native_decide) (by evm_ov)]
  have rd5787 := evm_run rd5778 with [
    push2 ⟨450⟩, dup5, add, dup8, swap1,
    raw mstore 3 (permitRuntimeEcrecoverInputMem baseMem digest v r s)
      (UInt256.ofNat 20) (by native_decide) mem_cost (by rfl)
      (by native_decide) (by evm_ov)]
  obtain ⟨gasArg, rd5813₀⟩ := evm_run rd5787 with [
    raw mload 0 ⟨482⟩ (UInt256.ofNat 20) (by native_decide)
      mem_cost
      (permitRuntimeEcrecoverInputMem_mload64 digest v r s hbaseSize)
      (by native_decide) (by evm_ov),
    swap2, swap4, swap3, push2 ⟨482⟩, dup1, dup3, add, swap4, push1 ⟨31⟩,
    not, dup2, add, swap3, dup2, swap1, sub, swap1, swap2, add, swap1, dup6, gas]
  have hInSize :
      (⟨482⟩ : UInt256) + UInt256.sub (⟨128⟩ : UInt256) ⟨482⟩ = ⟨128⟩ := by
    native_decide
  have hOutOffset : (⟨482⟩ : UInt256) + UInt256.lnot ⟨31⟩ = ⟨450⟩ := by
    native_decide
  have hTail : (⟨128⟩ : UInt256) + ⟨482⟩ = ⟨610⟩ := by
    native_decide
  have rd5813 := rd5813₀
  rw [hInSize, hOutOffset, hTail] at rd5813
  obtain ⟨cA', σ', z, o, A_in, callGas, k', C', htheta, rd5814, houtSize⟩ :=
    RD.solcStaticcall rd5813 (by native_decide) hdepth
      (by simp only [List.length_cons]; omega)
  have haw : UInt256.ofNat
        (MachineState.M
          (MachineState.M (UInt256.ofNat 20).toNat (⟨482⟩ : UInt256).toNat
            (⟨128⟩ : UInt256).toNat)
          (⟨450⟩ : UInt256).toNat (⟨32⟩ : UInt256).toNat) =
      UInt256.ofNat 20 := by
    native_decide
  refine ⟨cA', σ', z, o, A_in, callGas, k', C', ?_, ?_, houtSize⟩
  · simpa using htheta
  · rw [haw] at rd5814
    simpa using rd5814

set_option maxHeartbeats 1000000 in
theorem RD.uniswapPermitEcrecoverStaticcallDepthReverts {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {digest s r v deadline value spender owner ret : UInt256}
    {R : List UInt256} {baseMem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5746⟩
      (digest :: ⟨64⟩ :: ⟨32⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨1⟩ :: ⟨450⟩ ::
        s :: r :: v :: deadline :: value :: spender :: owner :: ret :: R)
      baseMem (UInt256.ofNat 15) rdata (cA, σ) k C)
    (hbaseSize : baseMem.size = 450)
    (hvMask : UInt256.land (⟨255⟩ : UInt256) v = v)
    (hdepth : ee.depth = 1024)
    (hov : R.length + 24 ≤ 1024) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g s0 := by
  have rd5749 := evm_run h with [
    swap6, dup4, swap1,
    raw mstore 3 (permitRuntimeEcrecoverMem0 baseMem)
      (UInt256.ofNat 16) (by native_decide) mem_cost (by rfl)
      (by native_decide) (by evm_ov)]
  have rd5757 := evm_run rd5749 with [
    push2 ⟨354⟩, dup5, add, dup1, dup3,
    raw mstore 0 (permitRuntimeEcrecoverMem1 baseMem)
      (UInt256.ofNat 16) (by native_decide) mem_cost (by rfl)
      (by native_decide) (by evm_ov)]
  have rd5760 := evm_run rd5757 with [
    dup7, swap1,
    raw mstore 3 (permitRuntimeEcrecoverMem2 baseMem digest)
      (UInt256.ofNat 17) (by native_decide) mem_cost (by rfl)
      (by native_decide) (by evm_ov)]
  have rd5764₀ := evm_run rd5760 with [push1 ⟨255⟩, dup10, and]
  have rd5764 := rd5764₀
  rw [u256_land_comm v (⟨255⟩ : UInt256)] at rd5764
  rw [hvMask] at rd5764
  have rd5770 := evm_run rd5764 with [
    push2 ⟨386⟩, dup6, add,
    raw mstore 3 (permitRuntimeEcrecoverMem3 baseMem digest v)
      (UInt256.ofNat 18) (by native_decide) mem_cost (by rfl)
      (by native_decide) (by evm_ov)]
  have rd5778 := evm_run rd5770 with [
    push2 ⟨418⟩, dup5, add, dup9, swap1,
    raw mstore 3 (permitRuntimeEcrecoverMem4 baseMem digest v r)
      (UInt256.ofNat 19) (by native_decide) mem_cost (by rfl)
      (by native_decide) (by evm_ov)]
  have rd5787 := evm_run rd5778 with [
    push2 ⟨450⟩, dup5, add, dup8, swap1,
    raw mstore 3 (permitRuntimeEcrecoverInputMem baseMem digest v r s)
      (UInt256.ofNat 20) (by native_decide) mem_cost (by rfl)
      (by native_decide) (by evm_ov)]
  obtain ⟨gasArg, rd5813₀⟩ := evm_run rd5787 with [
    raw mload 0 ⟨482⟩ (UInt256.ofNat 20) (by native_decide)
      mem_cost
      (permitRuntimeEcrecoverInputMem_mload64 digest v r s hbaseSize)
      (by native_decide) (by evm_ov),
    swap2, swap4, swap3, push2 ⟨482⟩, dup1, dup3, add, swap4, push1 ⟨31⟩,
    not, dup2, add, swap3, dup2, swap1, sub, swap1, swap2, add, swap1, dup6, gas]
  have hInSize :
      (⟨482⟩ : UInt256) + UInt256.sub (⟨128⟩ : UInt256) ⟨482⟩ = ⟨128⟩ := by
    native_decide
  have hOutOffset : (⟨482⟩ : UInt256) + UInt256.lnot ⟨31⟩ = ⟨450⟩ := by
    native_decide
  have hTail : (⟨128⟩ : UInt256) + ⟨482⟩ = ⟨610⟩ := by
    native_decide
  have rd5813 := rd5813₀
  rw [hInSize, hOutOffset, hTail] at rd5813
  obtain ⟨k', C', rd5814₀⟩ :=
    RD.solcStaticcallDepthLimit rd5813 (by native_decide) hdepth
      (by simp only [List.length_cons]; omega)
  have haw : UInt256.ofNat
        (MachineState.M
          (MachineState.M (UInt256.ofNat 20).toNat (⟨482⟩ : UInt256).toNat
            (⟨128⟩ : UInt256).toNat)
          (⟨450⟩ : UInt256).toNat (⟨32⟩ : UInt256).toNat) =
      UInt256.ofNat 20 := by
    native_decide
  have rd5814 := rd5814₀
  rw [haw] at rd5814
  have rd5814' : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5814⟩
      (⟨0⟩ :: ⟨610⟩ :: ⟨1⟩ :: ⟨0⟩ :: digest :: s :: r :: v :: deadline ::
        value :: spender :: owner :: ret :: R)
      (permitRuntimeEcrecoverStaticcallMem baseMem digest v r s ByteArray.empty)
      (UInt256.ofNat 20) ByteArray.empty (cA, σ) k' C' := by
    simpa [permitRuntimeEcrecoverStaticcallMem] using rd5814
  exact RD.solcCallSuccessGuardMissing (okPc := ⟨5830⟩) rd5814' rfl
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
    (by simp only [List.length_cons]; omega)

set_option maxHeartbeats 1000000 in
theorem RD.uniswapPermitEcrecoverReturnWordDecoded {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {digest s r v deadline value spender owner ret : UInt256}
    {R : List UInt256} {baseMem o : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5832⟩
      (⟨610⟩ :: ⟨1⟩ :: ⟨0⟩ :: digest :: s :: r :: v :: deadline :: value ::
        spender :: owner :: ret :: R)
      (permitRuntimeEcrecoverStaticcallMem baseMem digest v r s o)
      (UInt256.ofNat 20) o acc k C)
    (hbaseSize : baseMem.size = 450)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hov : R.length + 13 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5844⟩
      (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)) :: digest :: s :: r :: v ::
        deadline :: value :: spender :: owner :: ret :: R)
      (permitRuntimeEcrecoverStaticcallMem baseMem digest v r s o)
      (UInt256.ofNat 20) o acc k' C' := by
  have rd5839₀ := evm_run h with [
    pop, push1 ⟨64⟩,
    raw mload 0 ⟨482⟩ (UInt256.ofNat 20) (by native_decide)
      mem_cost
      (permitRuntimeEcrecoverStaticcallMem_mload64_of_size_ge digest v r s o
        hbaseSize ho32 hoSize)
      (by native_decide) (by evm_ov),
    push1 ⟨31⟩, not, add]
  have hoff : UInt256.lnot (⟨31⟩ : UInt256) + ⟨482⟩ = ⟨450⟩ := by
    native_decide
  have rd5839 := rd5839₀
  rw [hoff] at rd5839
  have rd5844 := evm_run rd5839 with [
    raw mload 0 (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)))
      (UInt256.ofNat 20) (by native_decide) mem_cost
      (permitRuntimeEcrecoverStaticcallMem_mload450_of_size_ge digest v r s o
        hbaseSize ho32 hoSize)
      (by native_decide) (by evm_ov),
    swap2, pop, pop]
  exact ⟨_, _, rd5844⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapPermitEcrecoverReturnWordDecodedShort {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {digest s r v deadline value spender owner ret : UInt256}
    {R : List UInt256} {baseMem o : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5832⟩
      (⟨610⟩ :: ⟨1⟩ :: ⟨0⟩ :: digest :: s :: r :: v :: deadline :: value ::
        spender :: owner :: ret :: R)
      (permitRuntimeEcrecoverStaticcallMem baseMem digest v r s o)
      (UInt256.ofNat 20) o acc k C)
    (hbaseSize : baseMem.size = 450)
    (hshort : o.size < 32) (hoSize : o.size < UInt256.size)
    (hov : R.length + 13 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5844⟩
      (UInt256.ofNat (fromByteArrayBigEndian (o.readWithPadding 0 32)) ::
        digest :: s :: r :: v :: deadline :: value :: spender :: owner :: ret :: R)
      (permitRuntimeEcrecoverStaticcallMem baseMem digest v r s o)
      (UInt256.ofNat 20) o acc k' C' := by
  have rd5839₀ := evm_run h with [
    pop, push1 ⟨64⟩,
    raw mload 0 ⟨482⟩ (UInt256.ofNat 20) (by native_decide)
      mem_cost
      (permitRuntimeEcrecoverStaticcallMem_mload64_of_size_lt digest v r s o
        hbaseSize hshort hoSize)
      (by native_decide) (by evm_ov),
    push1 ⟨31⟩, not, add]
  have hoff : UInt256.lnot (⟨31⟩ : UInt256) + ⟨482⟩ = ⟨450⟩ := by
    native_decide
  have rd5839 := rd5839₀
  rw [hoff] at rd5839
  have rd5844 := evm_run rd5839 with [
    raw mload 0 (UInt256.ofNat (fromByteArrayBigEndian (o.readWithPadding 0 32)))
      (UInt256.ofNat 20) (by native_decide) mem_cost
      (permitRuntimeEcrecoverStaticcallMem_mload450_of_size_lt digest v r s o
        hbaseSize hshort hoSize)
      (by native_decide) (by evm_ov),
    swap2, pop, pop]
  exact ⟨_, _, rd5844⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapPermitEcrecoverSignatureGuardOk {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {recovered digest s r v deadline value spender owner ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5844⟩
      (recovered :: digest :: s :: r :: v :: deadline :: value :: spender :: owner :: ret :: R)
      mem (UInt256.ofNat 20) rdata acc k C)
    (hnz : UInt256.land recovered solcAddrMask ≠ ⟨0⟩)
    (hmatch : UInt256.land recovered solcAddrMask = UInt256.land owner solcAddrMask)
    (hov : R.length + 19 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5965⟩
      (recovered :: digest :: s :: r :: v :: deadline :: value :: spender :: owner :: ret :: R)
      mem (UInt256.ofNat 20) rdata acc k' C' := by
  have rd5861₀ := evm_run h with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup2, and, iszero, dup1,
    iszero, swap1, push2 ⟨5884⟩]
  have hmaskConst :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have hcond0 : UInt256.isZero (UInt256.land recovered
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)) = ⟨0⟩ := by
    rw [hmaskConst]
    exact Reasoning.Theory.isZero_eq_zero_of_ne hnz
  have rd5861 := rd5861₀
  rw [hcond0] at rd5861
  have rd5862 := evm_run rd5861 with [jumpiNT (by native_decide), pop]
  have rd5884₀ := evm_run rd5862 with [
    dup9, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and, dup2,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and, eq]
  have hmatch' :
      UInt256.land solcAddrMask recovered = UInt256.land solcAddrMask owner := by
    rw [u256_land_comm solcAddrMask recovered, u256_land_comm solcAddrMask owner]
    exact hmatch
  have heqWord : UInt256.eq
        (UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) recovered)
        (UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) owner) =
      ⟨1⟩ := by
    rw [hmaskConst, hmatch']
    exact u256_eq_refl _
  have rd5884 := rd5884₀
  rw [heqWord] at rd5884
  have rd5965 := evm_run rd5884 with [
    jumpdest, push2 ⟨5965⟩, jumpiT one_ne_zero_uint (by jump_dest)]
  exact ⟨_, _, rd5965⟩

theorem RD.uniswapPermitApproveSetup {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {recovered digest s r v deadline value spender owner ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5965⟩
      (recovered :: digest :: s :: r :: v :: deadline :: value :: spender :: owner :: ret :: R)
      mem (UInt256.ofNat 20) rdata (cA, σ) k C)
    (hov : R.length + 19 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7412⟩
      (value :: spender :: owner :: ⟨5976⟩ :: recovered :: digest :: s :: r :: v ::
        deadline :: value :: spender :: owner :: ret :: R)
      mem (UInt256.ofNat 20) rdata (cA, σ) k' C' := by
  have rd7412 := evm_run h with [
    jumpdest, push2 ⟨5976⟩, dup10, dup10, dup10, push2 ⟨7412⟩,
    jump (by jump_dest)]
  exact ⟨_, _, rd7412⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapPermitApproveInnerHash20 {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {value spender owner ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7412⟩
      (value :: spender :: owner :: ret :: R) mem (UInt256.ofNat 20) rdata (cA, σ) k C)
    (hmem : 96 ≤ mem.size)
    (hcanonOwner : owner.toNat < EVM.addressModulus)
    (hov : R.length + 13 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7441⟩
      (mapSlot owner ⟨2⟩ :: ⟨64⟩ :: ⟨32⟩ :: ⟨0⟩ :: owner :: solcAddrMask ::
        value :: spender :: owner :: ret :: R)
      (twoWordHashMem owner ⟨2⟩ mem)
      (UInt256.ofNat 20) rdata (cA, σ) k' C' := by
  have hwf : solcNestedMappingStoreInnerHashWf UniswapV2Pair.uniswapV2PairBytecode
      (⟨7412⟩ : UInt256) (⟨2⟩ : UInt256) := by
    unfold solcNestedMappingStoreInnerHashWf
    repeat' first | apply And.intro | native_decide
  rcases hwf with
    ⟨hd0, hd1, hd3, hd5, hd7, hd8, hd9, hd10, hd11, hd12, hd14, hd15, hd16,
      hd17, hd19, hd21, hd22, hd23, hd24, hd26, hd27, hd28⟩
  have hmask :
      UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) owner =
        owner := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean_left hcanonOwner
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem owner (⟨2⟩ : UInt256) mem).readWithPadding 0 64))) =
        mapSlot owner ⟨2⟩ :=
    twoWordHashMem_mapSlot_of_ge64 owner ⟨2⟩ (by omega)
  have rdMasked := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw push1 ⟨1⟩ hd1 (by evm_ov),
    raw push1 ⟨1⟩ hd3 (by evm_ov),
    raw push1 ⟨160⟩ hd5 (by evm_ov),
    raw shl hd7 (by evm_ov),
    raw sub hd8 (by evm_ov),
    raw dup1 hd9 (by evm_ov),
    raw dup5 hd10 (by evm_ov),
    raw and hd11 (by evm_ov)]
  rw [u256_land_comm owner
    (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩), hmask] at rdMasked
  have rdMstore0Prefix := evm_run rdMasked with [
    raw push1 ⟨0⟩ hd12 (by evm_ov),
    raw dup2 hd14 (by evm_ov),
    raw dup2 hd15 (by evm_ov)]
  have rdInnerKey := rdMstore0Prefix.mstore 0 (wordAt0Mem owner mem)
    (UInt256.ofNat 20) hd16 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdInnerMemPrefix := evm_run rdInnerKey with [
    raw push1 ⟨2⟩ hd17 (by evm_ov),
    raw push1 ⟨32⟩ hd19 (by evm_ov),
    raw swap1 hd21 (by evm_ov),
    raw dup2 hd22 (by evm_ov)]
  have rdInnerMem := rdInnerMemPrefix.mstore 0 (twoWordHashMem owner ⟨2⟩ mem)
    (UInt256.ofNat 20) hd23 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdInnerHashPrefix := evm_run rdInnerMem with [
    raw push1 ⟨64⟩ hd24 (by evm_ov),
    raw dup1 hd26 (by evm_ov),
    raw dup4 hd27 (by evm_ov)]
  exact ⟨_, _, by
    simpa [solcNestedMappingStoreInnerHashOutPc] using
      rdInnerHashPrefix.keccak256 0 (mapSlot owner ⟨2⟩)
        (UInt256.ofNat 20) hd28 mem_cost hslot (by native_decide) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapPermitApproveStore20 {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {value spender owner ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7441⟩
      (mapSlot owner ⟨2⟩ :: ⟨64⟩ :: ⟨32⟩ :: ⟨0⟩ :: owner :: solcAddrMask ::
        value :: spender :: owner :: ret :: R)
      mem (UInt256.ofNat 20) rdata (cA, σ) k C)
    (hmem : 96 ≤ mem.size)
    (hperm : ee.perm = true)
    (hcanonSpender : spender.toNat < EVM.addressModulus)
    (hov : R.length + 13 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7457⟩
      (⟨32⟩ :: ⟨64⟩ :: owner :: spender :: value :: spender :: owner :: ret :: R)
      (twoWordHashMem spender (mapSlot owner ⟨2⟩) mem)
      (UInt256.ofNat 20) rdata
      (cA, sstoreAccountMap ee.codeOwner σ (mapSlot spender (mapSlot owner ⟨2⟩)) value)
      k' C' := by
  have hwf : solcNestedMappingStoreOuterSstoreWf UniswapV2Pair.uniswapV2PairBytecode
      (⟨7441⟩ : UInt256) := by
    unfold solcNestedMappingStoreOuterSstoreWf
    repeat' first | apply And.intro | native_decide
  rcases hwf with
    ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10, hd11, hd12,
      hd13, hd14, hd15⟩
  have hmask : UInt256.land spender solcAddrMask = spender :=
    solcAddrMask_clean hcanonSpender
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem spender (mapSlot owner ⟨2⟩) mem).readWithPadding 0 64))) =
        mapSlot spender (mapSlot owner ⟨2⟩) :=
    twoWordHashMem_mapSlot_of_ge64 spender (mapSlot owner ⟨2⟩) (by omega)
  have rdMasked := evm_run h with [
    raw swap5 hd0 (by evm_ov),
    raw dup8 hd1 (by evm_ov),
    raw and hd2 (by evm_ov)]
  rw [hmask] at rdMasked
  have rdOuterKeyPrefix := evm_run rdMasked with [
    raw dup1 hd3 (by evm_ov),
    raw dup5 hd4 (by evm_ov)]
  have rdOuterKey := rdOuterKeyPrefix.mstore 0 (wordAt0Mem spender mem)
    (UInt256.ofNat 20) hd5 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdOuterMemPrefix := evm_run rdOuterKey with [
    raw swap5 hd6 (by evm_ov),
    raw dup3 hd7 (by evm_ov)]
  have rdOuterMem := rdOuterMemPrefix.mstore 0
    (twoWordHashMem spender (mapSlot owner ⟨2⟩) mem)
    (UInt256.ofNat 20) hd8 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdHashPrefix := evm_run rdOuterMem with [
    raw swap2 hd9 (by evm_ov),
    raw dup3 hd10 (by evm_ov),
    raw swap1 hd11 (by evm_ov)]
  have rdSlot := rdHashPrefix.keccak256 0 (mapSlot spender (mapSlot owner ⟨2⟩))
    (UInt256.ofNat 20) hd12 mem_cost hslot (by native_decide) (by evm_ov)
  have rdBeforeStore := evm_run rdSlot with [
    raw dup6 hd13 (by evm_ov),
    raw swap1 hd14 (by evm_ov)]
  obtain ⟨_, _, rdOut⟩ := rdBeforeStore.sstore hperm hd15
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, by simpa [solcNestedMappingStoreOuterSstoreOutPc] using rdOut⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapPermitApproveEmitAndJump20 {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {value spender owner ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7457⟩
      (⟨32⟩ :: ⟨64⟩ :: owner :: spender :: value :: spender :: owner :: ret :: R)
      mem (UInt256.ofNat 20) rdata acc k C)
    (hmem : 514 ≤ mem.size)
    (hfree : mem.readWithPadding 64 32 = UInt256.toByteArray (⟨482⟩ : UInt256))
    (hperm : ee.perm = true)
    (hret : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains ret = true)
    (hov : R.length + 11 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ret R
      ((UInt256.toByteArray value).write 0 mem 482 32)
      (UInt256.ofNat 20) rdata acc k' C' := by
  have hwf : solcPlainLog3AndJumpWf UniswapV2Pair.uniswapV2PairBytecode
      (⟨7457⟩ : UInt256) uniswapApprovalTopic := by
    unfold solcPlainLog3AndJumpWf
    repeat' first | apply And.intro | native_decide
  rcases hwf with
    ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd40, hd41, hd42, hd43, hd44,
      hd45, hd46, hd47, hd48, hd49, hd50, hd51, hd52⟩
  have hmload :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 20 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨482⟩ := by
    rw [if_neg]
    · rw [show (⟨64⟩ : UInt256).toNat = 64 from by native_decide, hfree]
      rw [fromByteArrayBigEndian_toByteArray]
      exact u256_ofNat_toNat (⟨482⟩ : UInt256)
    · rw [not_or]
      exact ⟨by rw [show (⟨64⟩ : UInt256).toNat = 64 from by native_decide]; omega,
        by native_decide⟩
  have hlogRead64 :
      ((UInt256.toByteArray value).write 0 mem 482 32).readWithPadding 64 32 =
        UInt256.toByteArray (⟨482⟩ : UInt256) := by
    rw [write32_read_below _ _ 482 64 (by rw [toByteArray_size])
      (by omega) (by omega)]
    exact hfree
  have hlogMload :
      (if (⟨64⟩ : UInt256).toNat ≥
            ((UInt256.toByteArray value).write 0 mem 482 32).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 20 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian
          (((UInt256.toByteArray value).write 0 mem 482 32).readWithPadding
            (⟨64⟩ : UInt256).toNat 32)))
        = ⟨482⟩ := by
    rw [if_neg]
    · rw [show (⟨64⟩ : UInt256).toNat = 64 from by native_decide, hlogRead64]
      rw [fromByteArrayBigEndian_toByteArray]
      exact u256_ofNat_toNat (⟨482⟩ : UInt256)
    · rw [not_or]
      constructor
      · have hsize :
            ((UInt256.toByteArray value).write 0 mem 482 32).size = mem.size := by
          exact toByteArray_write32_size_of_le mem value 482 mem.size mem.size rfl
            (by omega) (by omega)
        rw [hsize]
        rw [show (⟨64⟩ : UInt256).toNat = 64 from by native_decide]
        omega
      · native_decide
  have rd2 := evm_run h with [
    raw dup2 hd0 (by evm_ov),
    raw mload 0 ⟨482⟩ (UInt256.ofNat 20) hd1
      mem_cost hmload (by native_decide) (by evm_ov)]
  have rd4 := evm_run rd2 with [raw dup6 hd2 (by evm_ov), raw dup2 hd3 (by evm_ov)]
  have rd5 := rd4.mstore 0 ((UInt256.toByteArray value).write 0 mem 482 32)
    (UInt256.ofNat 20) hd4 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd7 := evm_run rd5 with [
    raw swap2 hd5 (by evm_ov),
    raw mload 0 ⟨482⟩ (UInt256.ofNat 20) hd6
      mem_cost hlogMload (by native_decide) (by evm_ov)]
  have rd40 := rd7.pushConst uniswapApprovalTopic (width := 32) (op := .PUSH32)
    (by decide) hd7 (by evm_ov)
  have rd48 := evm_run rd40 with [
    raw swap3 hd40 (by evm_ov),
    raw dup2 hd41 (by evm_ov),
    raw swap1 hd42 (by evm_ov),
    raw sub hd43 (by evm_ov),
    raw swap1 hd44 (by evm_ov),
    raw swap2 hd45 (by evm_ov),
    raw add hd46 (by evm_ov),
    raw swap1 hd47 (by evm_ov)]
  have rd49 := rd48.log3 0 (UInt256.ofNat 20) hd48 hperm mem_cost
    (by native_decide) (by simp only [List.length_cons]; omega)
  have rd52 := evm_run rd49 with [
    raw pop hd49 (by evm_ov),
    raw pop hd50 (by evm_ov),
    raw pop hd51 (by evm_ov)]
  exact ⟨_, _, rd52.jump hd52 hret (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapPermitApproveAndReturn20 {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {recovered digest s r v deadline value spender owner : UInt256}
    {R : List UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5965⟩
      (recovered :: digest :: s :: r :: v :: deadline :: value :: spender :: owner :: ⟨570⟩ :: R)
      mem (UInt256.ofNat 20) rdata (cA, σ) k C)
    (hmem : 514 ≤ mem.size)
    (hfree : mem.readWithPadding 64 32 = UInt256.toByteArray (⟨482⟩ : UInt256))
    (hperm : ee.perm = true)
    (hcanonOwner : owner.toNat < EVM.addressModulus)
    (hcanonSpender : spender.toNat < EVM.addressModulus)
    (hov : R.length + 23 ≤ 1024) :
    RDret UniswapV2Pair.uniswapV2PairBytecode g s0
      (cA, sstoreAccountMap ee.codeOwner σ (mapSlot spender (mapSlot owner ⟨2⟩)) value)
      ByteArray.empty := by
  obtain ⟨_, _, rd7412⟩ := RD.uniswapPermitApproveSetup
    (recovered := recovered) (digest := digest) (s := s) (r := r) (v := v)
    (deadline := deadline) (value := value) (spender := spender) (owner := owner)
    (ret := ⟨570⟩) (R := R) h (by omega)
  let Rtail := recovered :: digest :: s :: r :: v :: deadline :: value :: spender :: owner ::
    (⟨570⟩ : UInt256) :: R
  obtain ⟨_, _, rd7441⟩ := RD.uniswapPermitApproveInnerHash20
    (value := value) (spender := spender) (owner := owner) (ret := ⟨5976⟩)
    (R := Rtail) rd7412 (by omega) hcanonOwner
    (by simp only [Rtail, List.length_cons]; omega)
  have hinnerSize :
      96 ≤ (twoWordHashMem owner (⟨2⟩ : UInt256) mem).size := by
    rw [twoWordHashMem_size_of_ge64 owner ⟨2⟩ (by omega)]
    omega
  have hinnerFree :
      (twoWordHashMem owner (⟨2⟩ : UInt256) mem).readWithPadding 64 32 =
        UInt256.toByteArray (⟨482⟩ : UInt256) := by
    rw [twoWordHashMem_read64_of_ge96 owner ⟨2⟩ (by omega)]
    exact hfree
  obtain ⟨_, _, rd7457⟩ := RD.uniswapPermitApproveStore20
    (value := value) (spender := spender) (owner := owner) (ret := ⟨5976⟩)
    (R := Rtail) rd7441 hinnerSize hperm hcanonSpender
    (by simp only [Rtail, List.length_cons]; omega)
  have hstoreSize :
      514 ≤ (twoWordHashMem spender (mapSlot owner ⟨2⟩)
        (twoWordHashMem owner (⟨2⟩ : UInt256) mem)).size := by
    rw [twoWordHashMem_size_of_ge64 spender (mapSlot owner ⟨2⟩) (by omega)]
    rw [twoWordHashMem_size_of_ge64 owner ⟨2⟩ (by omega)]
    exact hmem
  have hstoreFree :
      (twoWordHashMem spender (mapSlot owner ⟨2⟩)
          (twoWordHashMem owner (⟨2⟩ : UInt256) mem)).readWithPadding 64 32 =
        UInt256.toByteArray (⟨482⟩ : UInt256) := by
    rw [twoWordHashMem_read64_of_ge96 spender (mapSlot owner ⟨2⟩) (by omega)]
    exact hinnerFree
  obtain ⟨_, _, rd5976⟩ := RD.uniswapPermitApproveEmitAndJump20
    (value := value) (spender := spender) (owner := owner) (ret := ⟨5976⟩)
    (R := recovered :: digest :: s :: r :: v :: deadline :: value :: spender :: owner ::
      (⟨570⟩ : UInt256) :: R)
    (by simpa [Rtail] using rd7457) hstoreSize hstoreFree hperm (by jump_dest)
    (by simp only [List.length_cons]; omega)
  have rd570 := evm_run rd5976 with [
    jumpdest, pop, pop, pop, pop, pop, pop, pop, pop, pop, jump (by jump_dest), jumpdest]
  exact rd570.stop (by native_decide) (by evm_ov)

set_option maxHeartbeats 1000000 in
theorem RD.uniswapPermitInvalidSignatureReverts {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {baseMem o rdata : ByteArray}
    {digest v r s : UInt256} {stk : List UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5889⟩ stk
      (permitRuntimeEcrecoverStaticcallMem baseMem digest v r s o)
      (UInt256.ofNat 20) rdata acc k C)
    (hbaseSize : baseMem.size = 450)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hov : stk.length + 9 ≤ 1024) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g s0 := by
  let mem := permitRuntimeEcrecoverStaticcallMem baseMem digest v r s o
  have hmem : mem.size = 610 := by
    simpa [mem] using
      permitRuntimeEcrecoverStaticcallMem_size_of_size_ge digest v r s o hbaseSize ho32 hoSize
  have hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray (⟨482⟩ : UInt256) := by
    simpa [mem] using
      permitRuntimeEcrecoverStaticcallMem_read64_of_size_ge digest v r s o hbaseSize ho32 hoSize
  have rd5893 := evm_run h with [
    push1 ⟨64⟩, dup1,
    raw mload 0 ⟨482⟩ (UInt256.ofNat 20) (by native_decide)
      mem_cost
      (permitRuntimeEcrecoverStaticcallMem_mload64_of_size_ge digest v r s o
        hbaseSize ho32 hoSize)
      (by native_decide) (by evm_ov)]
  let mem0 : ByteArray := (UInt256.toByteArray solcErrorStringSelector).write 0 mem 482 32
  have hmem0 : mem0.size = 610 := by
    unfold mem0
    exact toByteArray_write32_size_of_le mem solcErrorStringSelector 482 610 610
      hmem (by rw [hmem]; omega) (by omega)
  have rd5897 := rd5893.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by native_decide) (by native_decide) (by evm_ov)
  have rd5901 := evm_run rd5897 with [
    push1 ⟨229⟩, shl, dup2,
    raw mstore 0 mem0 (UInt256.ofNat 20)
      (by native_decide) mem_cost
      (by unfold mem0 solcErrorStringSelector; rfl) (by native_decide) (by evm_ov)]
  let mem1 : ByteArray := (UInt256.toByteArray (⟨32⟩ : UInt256)).write 0 mem0 486 32
  have hmem1 : mem1.size = 610 := by
    unfold mem1
    exact toByteArray_write32_size_of_le mem0 (⟨32⟩ : UInt256) 486 610 610
      hmem0 (by rw [hmem0]; omega) (by omega)
  have rd5908 := evm_run rd5901 with [
    push1 ⟨32⟩, push1 ⟨4⟩, dup3, add,
    raw mstore 0 mem1 (UInt256.ofNat 20)
      (by native_decide) mem_cost (by unfold mem1; rfl) (by native_decide) (by evm_ov)]
  let mem2 : ByteArray := (UInt256.toByteArray (⟨28⟩ : UInt256)).write 0 mem1 518 32
  have hmem2 : mem2.size = 610 := by
    unfold mem2
    exact toByteArray_write32_size_of_le mem1 (⟨28⟩ : UInt256) 518 610 610
      hmem1 (by rw [hmem1]; omega) (by omega)
  have rd5915 := evm_run rd5908 with [
    push1 ⟨28⟩, push1 ⟨36⟩, dup3, add,
    raw mstore 0 mem2 (UInt256.ofNat 20)
      (by native_decide) mem_cost (by unfold mem2; rfl) (by native_decide) (by evm_ov)]
  let invalidSignatureWord : UInt256 :=
    ⟨38641673103035791731704587899846419028922750264491344903186080211751768424448⟩
  let mem3 : ByteArray := (UInt256.toByteArray invalidSignatureWord).write 0 mem2 550 32
  have hmem3 : mem3.size = 610 := by
    unfold mem3
    exact toByteArray_write32_size_of_le mem2 invalidSignatureWord 550 610 610
      hmem2 (by rw [hmem2]; omega) (by omega)
  have hread64_mem0 :
      mem0.readWithPadding 64 32 = UInt256.toByteArray (⟨482⟩ : UInt256) := by
    unfold mem0
    rw [write32_read_below _ _ 482 64 (by rw [toByteArray_size])
      (by rw [hmem]; omega) (by omega)]
    exact hread64
  have hread64_mem1 :
      mem1.readWithPadding 64 32 = UInt256.toByteArray (⟨482⟩ : UInt256) := by
    unfold mem1
    rw [write32_read_below _ _ 486 64 (by rw [toByteArray_size])
      (by rw [hmem0]; omega) (by omega)]
    exact hread64_mem0
  have hread64_mem2 :
      mem2.readWithPadding 64 32 = UInt256.toByteArray (⟨482⟩ : UInt256) := by
    unfold mem2
    rw [write32_read_below _ _ 518 64 (by rw [toByteArray_size])
      (by rw [hmem1]; omega) (by omega)]
    exact hread64_mem1
  have hread64_mem3 :
      mem3.readWithPadding 64 32 = UInt256.toByteArray (⟨482⟩ : UInt256) := by
    unfold mem3
    rw [write32_read_below _ _ 550 64 (by rw [toByteArray_size])
      (by rw [hmem2]; omega) (by omega)]
    exact hread64_mem2
  have rd5949 := rd5915.pushConst invalidSignatureWord
    (width := 32) (op := .PUSH32) (by native_decide) (by native_decide) (by evm_ov)
  exact evm_run rd5949 with [
    push1 ⟨68⟩, dup3, add,
    raw mstore 0 mem3 (UInt256.ofNat 20)
      (by native_decide) mem_cost (by unfold mem3; rfl) (by native_decide) (by evm_ov),
    swap1,
    raw mload 0 ⟨482⟩ (UInt256.ofNat 20) (by native_decide)
      mem_cost
      (mloadWordValue_of_readWithPadding
        (by rw [hmem3]; decide) (by native_decide) hread64_mem3)
      (by native_decide) (by evm_ov),
    swap1, dup2, swap1, sub, push1 ⟨100⟩, add, swap1,
    raw rev 0 (by native_decide) mem_cost (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem RD.uniswapPermitInvalidSignatureRevertsShort {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {baseMem o rdata : ByteArray}
    {digest v r s : UInt256} {stk : List UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5889⟩ stk
      (permitRuntimeEcrecoverStaticcallMem baseMem digest v r s o)
      (UInt256.ofNat 20) rdata acc k C)
    (hbaseSize : baseMem.size = 450)
    (hshort : o.size < 32) (hoSize : o.size < UInt256.size)
    (hov : stk.length + 9 ≤ 1024) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g s0 := by
  let mem := permitRuntimeEcrecoverStaticcallMem baseMem digest v r s o
  have hmem : mem.size = 610 := by
    simpa [mem] using
      permitRuntimeEcrecoverStaticcallMem_size_of_size_lt digest v r s o hbaseSize hshort
        hoSize
  have hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray (⟨482⟩ : UInt256) := by
    simpa [mem] using
      permitRuntimeEcrecoverStaticcallMem_read64_of_size_lt digest v r s o hbaseSize hshort
        hoSize
  have rd5893 := evm_run h with [
    push1 ⟨64⟩, dup1,
    raw mload 0 ⟨482⟩ (UInt256.ofNat 20) (by native_decide)
      mem_cost
      (permitRuntimeEcrecoverStaticcallMem_mload64_of_size_lt digest v r s o
        hbaseSize hshort hoSize)
      (by native_decide) (by evm_ov)]
  let mem0 : ByteArray := (UInt256.toByteArray solcErrorStringSelector).write 0 mem 482 32
  have hmem0 : mem0.size = 610 := by
    unfold mem0
    exact toByteArray_write32_size_of_le mem solcErrorStringSelector 482 610 610
      hmem (by rw [hmem]; omega) (by omega)
  have rd5897 := rd5893.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by native_decide) (by native_decide) (by evm_ov)
  have rd5901 := evm_run rd5897 with [
    push1 ⟨229⟩, shl, dup2,
    raw mstore 0 mem0 (UInt256.ofNat 20)
      (by native_decide) mem_cost
      (by unfold mem0 solcErrorStringSelector; rfl) (by native_decide) (by evm_ov)]
  let mem1 : ByteArray := (UInt256.toByteArray (⟨32⟩ : UInt256)).write 0 mem0 486 32
  have hmem1 : mem1.size = 610 := by
    unfold mem1
    exact toByteArray_write32_size_of_le mem0 (⟨32⟩ : UInt256) 486 610 610
      hmem0 (by rw [hmem0]; omega) (by omega)
  have rd5908 := evm_run rd5901 with [
    push1 ⟨32⟩, push1 ⟨4⟩, dup3, add,
    raw mstore 0 mem1 (UInt256.ofNat 20)
      (by native_decide) mem_cost (by unfold mem1; rfl) (by native_decide) (by evm_ov)]
  let mem2 : ByteArray := (UInt256.toByteArray (⟨28⟩ : UInt256)).write 0 mem1 518 32
  have hmem2 : mem2.size = 610 := by
    unfold mem2
    exact toByteArray_write32_size_of_le mem1 (⟨28⟩ : UInt256) 518 610 610
      hmem1 (by rw [hmem1]; omega) (by omega)
  have rd5915 := evm_run rd5908 with [
    push1 ⟨28⟩, push1 ⟨36⟩, dup3, add,
    raw mstore 0 mem2 (UInt256.ofNat 20)
      (by native_decide) mem_cost (by unfold mem2; rfl) (by native_decide) (by evm_ov)]
  let invalidSignatureWord : UInt256 :=
    ⟨38641673103035791731704587899846419028922750264491344903186080211751768424448⟩
  let mem3 : ByteArray := (UInt256.toByteArray invalidSignatureWord).write 0 mem2 550 32
  have hmem3 : mem3.size = 610 := by
    unfold mem3
    exact toByteArray_write32_size_of_le mem2 invalidSignatureWord 550 610 610
      hmem2 (by rw [hmem2]; omega) (by omega)
  have hread64_mem0 :
      mem0.readWithPadding 64 32 = UInt256.toByteArray (⟨482⟩ : UInt256) := by
    unfold mem0
    rw [write32_read_below _ _ 482 64 (by rw [toByteArray_size])
      (by rw [hmem]; omega) (by omega)]
    exact hread64
  have hread64_mem1 :
      mem1.readWithPadding 64 32 = UInt256.toByteArray (⟨482⟩ : UInt256) := by
    unfold mem1
    rw [write32_read_below _ _ 486 64 (by rw [toByteArray_size])
      (by rw [hmem0]; omega) (by omega)]
    exact hread64_mem0
  have hread64_mem2 :
      mem2.readWithPadding 64 32 = UInt256.toByteArray (⟨482⟩ : UInt256) := by
    unfold mem2
    rw [write32_read_below _ _ 518 64 (by rw [toByteArray_size])
      (by rw [hmem1]; omega) (by omega)]
    exact hread64_mem1
  have hread64_mem3 :
      mem3.readWithPadding 64 32 = UInt256.toByteArray (⟨482⟩ : UInt256) := by
    unfold mem3
    rw [write32_read_below _ _ 550 64 (by rw [toByteArray_size])
      (by rw [hmem2]; omega) (by omega)]
    exact hread64_mem2
  have rd5949 := rd5915.pushConst invalidSignatureWord
    (width := 32) (op := .PUSH32) (by native_decide) (by native_decide) (by evm_ov)
  exact evm_run rd5949 with [
    push1 ⟨68⟩, dup3, add,
    raw mstore 0 mem3 (UInt256.ofNat 20)
      (by native_decide) mem_cost (by unfold mem3; rfl) (by native_decide) (by evm_ov),
    swap1,
    raw mload 0 ⟨482⟩ (UInt256.ofNat 20) (by native_decide)
      mem_cost
      (mloadWordValue_of_readWithPadding
        (by rw [hmem3]; decide) (by native_decide) hread64_mem3)
      (by native_decide) (by evm_ov),
    swap1, dup2, swap1, sub, push1 ⟨100⟩, add, swap1,
    raw rev 0 (by native_decide) mem_cost (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem RD.uniswapPermitEcrecoverSignatureGuardZeroReverts {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {baseMem o rdata : ByteArray}
    {recovered digest s r v deadline value spender owner ret : UInt256}
    {R : List UInt256} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5844⟩
      (recovered :: digest :: s :: r :: v :: deadline :: value :: spender :: owner :: ret :: R)
      (permitRuntimeEcrecoverStaticcallMem baseMem digest v r s o)
      (UInt256.ofNat 20) rdata acc k C)
    (hzero : UInt256.land recovered solcAddrMask = ⟨0⟩)
    (hbaseSize : baseMem.size = 450)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hov : R.length + 19 ≤ 1024) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g s0 := by
  have rd5861₀ := evm_run h with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup2, and, iszero, dup1,
    iszero, swap1, push2 ⟨5884⟩]
  have hmaskConst :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have hcond1 : UInt256.isZero (UInt256.land recovered
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)) = ⟨1⟩ := by
    rw [hmaskConst, hzero]
    decide
  have rd5861 := rd5861₀
  rw [hcond1] at rd5861
  have rd5884₀ := evm_run rd5861 with [jumpiT one_ne_zero_uint (by jump_dest)]
  have hzeroBit : UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ := by
    native_decide
  have rd5884 := rd5884₀
  rw [hzeroBit] at rd5884
  have rd5889 := evm_run rd5884 with [
    jumpdest, push2 ⟨5965⟩, jumpiNT (by native_decide)]
  exact RD.uniswapPermitInvalidSignatureReverts
    (baseMem := baseMem) (digest := digest) (v := v) (r := r) (s := s)
    (o := o) rd5889 hbaseSize ho32 hoSize
    (by simp only [List.length_cons]; omega)

set_option maxHeartbeats 1000000 in
theorem RD.uniswapPermitEcrecoverSignatureGuardMismatchReverts {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {baseMem o rdata : ByteArray}
    {recovered digest s r v deadline value spender owner ret : UInt256}
    {R : List UInt256} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5844⟩
      (recovered :: digest :: s :: r :: v :: deadline :: value :: spender :: owner :: ret :: R)
      (permitRuntimeEcrecoverStaticcallMem baseMem digest v r s o)
      (UInt256.ofNat 20) rdata acc k C)
    (hnz : UInt256.land recovered solcAddrMask ≠ ⟨0⟩)
    (hmismatch : UInt256.land recovered solcAddrMask ≠ UInt256.land owner solcAddrMask)
    (hbaseSize : baseMem.size = 450)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hov : R.length + 19 ≤ 1024) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g s0 := by
  have rd5861₀ := evm_run h with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup2, and, iszero, dup1,
    iszero, swap1, push2 ⟨5884⟩]
  have hmaskConst :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have hcond0 : UInt256.isZero (UInt256.land recovered
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)) = ⟨0⟩ := by
    rw [hmaskConst]
    exact Reasoning.Theory.isZero_eq_zero_of_ne hnz
  have rd5861 := rd5861₀
  rw [hcond0] at rd5861
  have rd5862 := evm_run rd5861 with [jumpiNT (by native_decide), pop]
  have rd5884₀ := evm_run rd5862 with [
    dup9, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and, dup2,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and, eq]
  have hneq' :
      UInt256.land solcAddrMask recovered ≠ UInt256.land solcAddrMask owner := by
    intro hsame
    apply hmismatch
    simpa [u256_land_comm] using hsame
  have heqWord : UInt256.eq
        (UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) recovered)
        (UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) owner) =
      ⟨0⟩ := by
    rw [hmaskConst]
    exact u256_eq_of_ne hneq'
  have rd5884 := rd5884₀
  rw [heqWord] at rd5884
  have rd5889 := evm_run rd5884 with [
    jumpdest, push2 ⟨5965⟩, jumpiNT (by native_decide)]
  exact RD.uniswapPermitInvalidSignatureReverts
    (baseMem := baseMem) (digest := digest) (v := v) (r := r) (s := s)
    (o := o) rd5889 hbaseSize ho32 hoSize
    (by simp only [List.length_cons]; omega)

set_option maxHeartbeats 1000000 in
theorem RD.uniswapPermitEcrecoverSignatureGuardZeroRevertsShort {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {baseMem o rdata : ByteArray}
    {recovered digest s r v deadline value spender owner ret : UInt256}
    {R : List UInt256} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5844⟩
      (recovered :: digest :: s :: r :: v :: deadline :: value :: spender :: owner :: ret :: R)
      (permitRuntimeEcrecoverStaticcallMem baseMem digest v r s o)
      (UInt256.ofNat 20) rdata acc k C)
    (hzero : UInt256.land recovered solcAddrMask = ⟨0⟩)
    (hbaseSize : baseMem.size = 450)
    (hshort : o.size < 32) (hoSize : o.size < UInt256.size)
    (hov : R.length + 19 ≤ 1024) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g s0 := by
  have rd5861₀ := evm_run h with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup2, and, iszero, dup1,
    iszero, swap1, push2 ⟨5884⟩]
  have hmaskConst :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have hcond1 : UInt256.isZero (UInt256.land recovered
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)) = ⟨1⟩ := by
    rw [hmaskConst, hzero]
    decide
  have rd5861 := rd5861₀
  rw [hcond1] at rd5861
  have rd5884₀ := evm_run rd5861 with [jumpiT one_ne_zero_uint (by jump_dest)]
  have hzeroBit : UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ := by
    native_decide
  have rd5884 := rd5884₀
  rw [hzeroBit] at rd5884
  have rd5889 := evm_run rd5884 with [
    jumpdest, push2 ⟨5965⟩, jumpiNT (by native_decide)]
  exact RD.uniswapPermitInvalidSignatureRevertsShort
    (baseMem := baseMem) (digest := digest) (v := v) (r := r) (s := s)
    (o := o) rd5889 hbaseSize hshort hoSize
    (by simp only [List.length_cons]; omega)

set_option maxHeartbeats 1000000 in
theorem RD.uniswapPermitEcrecoverSignatureGuardMismatchRevertsShort {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {baseMem o rdata : ByteArray}
    {recovered digest s r v deadline value spender owner ret : UInt256}
    {R : List UInt256} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5844⟩
      (recovered :: digest :: s :: r :: v :: deadline :: value :: spender :: owner :: ret :: R)
      (permitRuntimeEcrecoverStaticcallMem baseMem digest v r s o)
      (UInt256.ofNat 20) rdata acc k C)
    (hnz : UInt256.land recovered solcAddrMask ≠ ⟨0⟩)
    (hmismatch : UInt256.land recovered solcAddrMask ≠ UInt256.land owner solcAddrMask)
    (hbaseSize : baseMem.size = 450)
    (hshort : o.size < 32) (hoSize : o.size < UInt256.size)
    (hov : R.length + 19 ≤ 1024) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g s0 := by
  have rd5861₀ := evm_run h with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup2, and, iszero, dup1,
    iszero, swap1, push2 ⟨5884⟩]
  have hmaskConst :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have hcond0 : UInt256.isZero (UInt256.land recovered
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)) = ⟨0⟩ := by
    rw [hmaskConst]
    exact Reasoning.Theory.isZero_eq_zero_of_ne hnz
  have rd5861 := rd5861₀
  rw [hcond0] at rd5861
  have rd5862 := evm_run rd5861 with [jumpiNT (by native_decide), pop]
  have rd5884₀ := evm_run rd5862 with [
    dup9, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and, dup2,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and, eq]
  have hneq' :
      UInt256.land solcAddrMask recovered ≠ UInt256.land solcAddrMask owner := by
    intro hsame
    apply hmismatch
    simpa [u256_land_comm] using hsame
  have heqWord : UInt256.eq
        (UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) recovered)
        (UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) owner) =
      ⟨0⟩ := by
    rw [hmaskConst]
    exact u256_eq_of_ne hneq'
  have rd5884 := rd5884₀
  rw [heqWord] at rd5884
  have rd5889 := evm_run rd5884 with [
    jumpdest, push2 ⟨5965⟩, jumpiNT (by native_decide)]
  exact RD.uniswapPermitInvalidSignatureRevertsShort
    (baseMem := baseMem) (digest := digest) (v := v) (r := r) (s := s)
    (o := o) rd5889 hbaseSize hshort hoSize
    (by simp only [List.length_cons]; omega)

end UniswapV2Pair
