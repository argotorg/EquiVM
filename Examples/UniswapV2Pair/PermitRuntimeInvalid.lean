import Examples.UniswapV2Pair.PermitRuntimeApprove
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000

namespace UniswapV2Pair

set_option maxHeartbeats 1000000 in
theorem RD.uniswapPermitInvalidSignatureReverts {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {baseMem o rdata : ByteArray}
    {digest v r s : UInt256} {stk : List UInt256}
    {acc : AccountMap}
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
        (by rw [hmem3]; decide) hread64_mem3)
      (by native_decide) (by evm_ov),
    swap1, dup2, swap1, sub, push1 ⟨100⟩, add, swap1,
    raw rev 0 (by native_decide) mem_cost (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem RD.uniswapPermitInvalidSignatureRevertsShort {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {baseMem o rdata : ByteArray}
    {digest v r s : UInt256} {stk : List UInt256}
    {acc : AccountMap}
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
        (by rw [hmem3]; decide) hread64_mem3)
      (by native_decide) (by evm_ov),
    swap1, dup2, swap1, sub, push1 ⟨100⟩, add, swap1,
    raw rev 0 (by native_decide) mem_cost (by evm_ov)]

end UniswapV2Pair
