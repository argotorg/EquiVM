import Examples.UniswapV2Pair.PermitHashMemory
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000

namespace UniswapV2Pair

set_option maxHeartbeats 2000000 in
theorem RD.uniswapPermitStructHash {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {nonce owner spender value deadline domain s r v ret : UInt256}
    {R : List UInt256} {baseMem rdata : ByteArray}
    {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5589⟩
      (nonce :: ⟨1⟩ :: ⟨64⟩ :: ⟨32⟩ :: ⟨0⟩ :: owner :: solcAddrMask ::
        domain :: s :: r :: v :: deadline :: value :: spender :: owner :: ret :: R)
      baseMem (UInt256.ofNat 3) rdata σ k C)
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
      (UInt256.ofNat 11) rdata σ k' C' := by
  have hbaseMload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ baseMem.size then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          (baseMem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩ :=
    mloadWordValue_of_readWithPadding
      (by rw [hbaseSize]; decide)
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
    {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5688⟩
      (structHash :: ⟨64⟩ :: ⟨32⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨1⟩ ::
        domain :: s :: r :: v :: deadline :: value :: spender :: owner :: ret :: R)
      baseMem (UInt256.ofNat 11) rdata σ k C)
    (hbaseSize : baseMem.size = 352)
    (hbaseRead64 :
      baseMem.readWithPadding 64 32 = UInt256.toByteArray (⟨352⟩ : UInt256))
    (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5746⟩
      (permitRuntimeDigestWord baseMem domain structHash ::
        ⟨64⟩ :: ⟨32⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨1⟩ :: ⟨450⟩ ::
        s :: r :: v :: deadline :: value :: spender :: owner :: ret :: R)
      (permitRuntimeDigestMem baseMem domain structHash)
      (UInt256.ofNat 15) rdata σ k' C' := by
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
    {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5746⟩
      (digest :: ⟨64⟩ :: ⟨32⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨1⟩ :: ⟨450⟩ ::
        s :: r :: v :: deadline :: value :: spender :: owner :: ret :: R)
      baseMem (UInt256.ofNat 15) rdata σ k C)
    (hbaseSize : baseMem.size = 450)
    (hvMask : UInt256.land (⟨255⟩ : UInt256) v = v)
    (hdepth : ee.depth.val < 1024)
    (hov : R.length + 24 ≤ 1024) :
    ∃ (σ' : AccountMap)
      (z : Bool) (o : ByteArray) (A_in : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (σ', g'', A', z, o) = Ethereum.EVM.Θ σ s0.σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat ee.codeOwner)) ee.sender
          (AccountAddress.ofUInt256 (⟨1⟩ : UInt256))
          (toExecute σ (AccountAddress.ofUInt256 (⟨1⟩ : UInt256)))
          callGas (UInt256.ofNat ee.gasPrice) ⟨0⟩ ⟨0⟩
          ((permitRuntimeEcrecoverInputMem baseMem digest v r s).readWithPadding 482 128)
          (ee.depth + 1) ee.header ee.blobVersionedHashes ee.blocks false)
      ∧ RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5814⟩
          ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨610⟩ :: ⟨1⟩ :: ⟨0⟩ ::
            digest :: s :: r :: v :: deadline :: value :: spender :: owner :: ret :: R)
          (o.write 0 (permitRuntimeEcrecoverInputMem baseMem digest v r s) 450
            (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat)
          (UInt256.ofNat 20) o σ' k' C'
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
  obtain ⟨σ', z, o, A_in, callGas, k', C', htheta, rd5814, houtSize⟩ :=
    RD.solcStaticcall rd5813 (by native_decide) hdepth
      (by simp only [List.length_cons]; omega)
  have haw : UInt256.ofNat
        (MachineState.M
          (MachineState.M (UInt256.ofNat 20).toNat (⟨482⟩ : UInt256).toNat
            (⟨128⟩ : UInt256).toNat)
          (⟨450⟩ : UInt256).toNat (⟨32⟩ : UInt256).toNat) =
      UInt256.ofNat 20 := by
    native_decide
  refine ⟨σ', z, o, A_in, callGas, k', C', ?_, ?_, houtSize⟩
  · simpa using htheta
  · rw [haw] at rd5814
    simpa using rd5814

set_option maxHeartbeats 1000000 in
theorem RD.uniswapPermitEcrecoverStaticcallDepthReverts {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {digest s r v deadline value spender owner ret : UInt256}
    {R : List UInt256} {baseMem rdata : ByteArray}
    {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5746⟩
      (digest :: ⟨64⟩ :: ⟨32⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨1⟩ :: ⟨450⟩ ::
        s :: r :: v :: deadline :: value :: spender :: owner :: ret :: R)
      baseMem (UInt256.ofNat 15) rdata σ k C)
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
      (UInt256.ofNat 20) ByteArray.empty σ k' C' := by
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
    {acc : AccountMap}
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
    {acc : AccountMap}
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
    {acc : AccountMap}
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

end UniswapV2Pair
