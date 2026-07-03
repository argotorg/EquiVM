import Examples.UniswapV2Pair.MutatorDispatch
import Reasoning.MemCascade
import Reasoning.Refinement

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000

namespace UniswapV2Pair

/-! ## Permit runtime hashing helpers -/

abbrev permitRuntimeTypehashWord : UInt256 :=
  ⟨49955707469362902507454157297736832118868343942642399513960811609542965143241⟩

noncomputable def permitRuntimeStructHashDataWrites
    (owner spender value nonce deadline : UInt256) : List (Nat × UInt256) :=
  [ (160, permitRuntimeTypehashWord),
    (192, owner),
    (224, spender),
    (256, value),
    (288, nonce),
    (320, deadline) ]

noncomputable def permitRuntimeStructHashDataMem (baseMem : ByteArray)
    (owner spender value nonce deadline : UInt256) : ByteArray :=
  writeCascade baseMem (permitRuntimeStructHashDataWrites owner spender value nonce deadline)

noncomputable def permitRuntimeStructHashLenMem (baseMem : ByteArray)
    (owner spender value nonce deadline : UInt256) : ByteArray :=
  writeCascade (permitRuntimeStructHashDataMem baseMem owner spender value nonce deadline)
    [(128, (⟨192⟩ : UInt256))]

noncomputable def permitRuntimeStructHashMem (baseMem : ByteArray)
    (owner spender value nonce deadline : UInt256) : ByteArray :=
  writeCascade (permitRuntimeStructHashLenMem baseMem owner spender value nonce deadline)
    [(64, (⟨352⟩ : UInt256))]

noncomputable abbrev permitRuntimeStructHashWord (baseMem : ByteArray)
    (owner spender value nonce deadline : UInt256) : UInt256 :=
  UInt256.ofNat
    (fromByteArrayBigEndian
      (ffi.KEC
        ((permitRuntimeStructHashMem baseMem owner spender value nonce deadline).readWithPadding
          160 192)))

noncomputable def permitRuntimeStructHashDataMem0 (baseMem : ByteArray) : ByteArray :=
  writeCascade baseMem [(160, permitRuntimeTypehashWord)]

noncomputable def permitRuntimeStructHashDataMem1 (baseMem : ByteArray)
    (owner : UInt256) : ByteArray :=
  writeCascade baseMem [(160, permitRuntimeTypehashWord), (192, owner)]

noncomputable def permitRuntimeStructHashDataMem2 (baseMem : ByteArray)
    (owner spender : UInt256) : ByteArray :=
  writeCascade baseMem
    [(160, permitRuntimeTypehashWord), (192, owner), (224, spender)]

noncomputable def permitRuntimeStructHashDataMem3 (baseMem : ByteArray)
    (owner spender value : UInt256) : ByteArray :=
  writeCascade baseMem
    [(160, permitRuntimeTypehashWord), (192, owner), (224, spender), (256, value)]

noncomputable def permitRuntimeStructHashDataMem4 (baseMem : ByteArray)
    (owner spender value nonce : UInt256) : ByteArray :=
  writeCascade baseMem
    [(160, permitRuntimeTypehashWord), (192, owner), (224, spender), (256, value),
      (288, nonce)]

theorem permitRuntimeStructHashDataWrites_gaps
    (owner spender value nonce deadline : UInt256) :
    WriteGapsOk 96
      (permitRuntimeStructHashDataWrites owner spender value nonce deadline) := by
  simp [WriteGapsOk, permitRuntimeStructHashDataWrites]
  exact lt_usize _ (by norm_num)

theorem permitRuntimeStructHashDataWrites_size
    (owner spender value nonce deadline : UInt256) :
    writeCascadeSize 96
      (permitRuntimeStructHashDataWrites owner spender value nonce deadline) = 352 := by
  rfl

theorem permitRuntimeStructHashDataWrites_disjoint64
    (owner spender value nonce deadline : UInt256) :
    WindowDisjointFromWrites 96 64 32
      (permitRuntimeStructHashDataWrites owner spender value nonce deadline) := by
  simp [WindowDisjointFromWrites, permitRuntimeStructHashDataWrites]
  exact lt_usize _ (by norm_num)

theorem permitRuntimeStructHashDataMem_size {baseMem : ByteArray}
    (owner spender value nonce deadline : UInt256)
    (hbaseSize : baseMem.size = 96) :
    (permitRuntimeStructHashDataMem baseMem owner spender value nonce deadline).size = 352 := by
  unfold permitRuntimeStructHashDataMem
  exact writeCascade_size_of_base baseMem
    (permitRuntimeStructHashDataWrites owner spender value nonce deadline)
    hbaseSize
    (permitRuntimeStructHashDataWrites_gaps owner spender value nonce deadline)
    (permitRuntimeStructHashDataWrites_size owner spender value nonce deadline)

theorem permitRuntimeStructHashDataMem_read64 {baseMem : ByteArray}
    (owner spender value nonce deadline : UInt256)
    (hbaseSize : baseMem.size = 96)
    (hbaseRead64 :
      baseMem.readWithPadding 64 32 = UInt256.toByteArray (⟨128⟩ : UInt256)) :
    (permitRuntimeStructHashDataMem baseMem owner spender value nonce deadline).readWithPadding
        64 32 =
      UInt256.toByteArray (⟨128⟩ : UInt256) := by
  unfold permitRuntimeStructHashDataMem
  rw [writeCascade_read_preserved]
  · exact hbaseRead64
  · rw [hbaseSize]
    exact permitRuntimeStructHashDataWrites_disjoint64 owner spender value nonce deadline

theorem permitRuntimeStructHashDataMem_mload64 {baseMem : ByteArray}
    (owner spender value nonce deadline : UInt256)
    (hbaseSize : baseMem.size = 96)
    (hbaseRead64 :
      baseMem.readWithPadding 64 32 = UInt256.toByteArray (⟨128⟩ : UInt256)) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (permitRuntimeStructHashDataMem baseMem owner spender value nonce deadline).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 11 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((permitRuntimeStructHashDataMem baseMem owner spender value nonce deadline).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadWordValue_of_readWithPadding
    (by
      rw [permitRuntimeStructHashDataMem_size owner spender value nonce deadline hbaseSize]
      decide)
    (by native_decide)
    (permitRuntimeStructHashDataMem_read64 owner spender value nonce deadline hbaseSize
      hbaseRead64)

theorem permitRuntimeStructHashLenMem_size {baseMem : ByteArray}
    (owner spender value nonce deadline : UInt256)
    (hbaseSize : baseMem.size = 96) :
    (permitRuntimeStructHashLenMem baseMem owner spender value nonce deadline).size = 352 := by
  unfold permitRuntimeStructHashLenMem writeCascade Reasoning.Theory.writeWord
  exact toByteArray_write32_size_of_le
    (permitRuntimeStructHashDataMem baseMem owner spender value nonce deadline)
    (⟨192⟩ : UInt256) 128 352 352
    (permitRuntimeStructHashDataMem_size owner spender value nonce deadline hbaseSize)
    (by
      rw [permitRuntimeStructHashDataMem_size owner spender value nonce deadline hbaseSize]
      omega)
    (by norm_num)

theorem permitRuntimeStructHashMem_size {baseMem : ByteArray}
    (owner spender value nonce deadline : UInt256)
    (hbaseSize : baseMem.size = 96) :
    (permitRuntimeStructHashMem baseMem owner spender value nonce deadline).size = 352 := by
  unfold permitRuntimeStructHashMem writeCascade Reasoning.Theory.writeWord
  exact toByteArray_write32_size_of_le
    (permitRuntimeStructHashLenMem baseMem owner spender value nonce deadline)
    (⟨352⟩ : UInt256) 64 352 352
    (permitRuntimeStructHashLenMem_size owner spender value nonce deadline hbaseSize)
    (by
      rw [permitRuntimeStructHashLenMem_size owner spender value nonce deadline hbaseSize]
      omega)
    (by norm_num)

theorem permitRuntimeStructHashLenMem_read128 {baseMem : ByteArray}
    (owner spender value nonce deadline : UInt256)
    (hbaseSize : baseMem.size = 96) :
    (permitRuntimeStructHashLenMem baseMem owner spender value nonce deadline).readWithPadding
        128 32 =
      UInt256.toByteArray (⟨192⟩ : UInt256) := by
  unfold permitRuntimeStructHashLenMem writeCascade Reasoning.Theory.writeWord
  exact toByteArray_write32_read_back
    (permitRuntimeStructHashDataMem baseMem owner spender value nonce deadline)
    (⟨192⟩ : UInt256) 128
    (by
      rw [permitRuntimeStructHashDataMem_size owner spender value nonce deadline hbaseSize]
      omega)

theorem permitRuntimeStructHashMem_read128 {baseMem : ByteArray}
    (owner spender value nonce deadline : UInt256)
    (hbaseSize : baseMem.size = 96) :
    (permitRuntimeStructHashMem baseMem owner spender value nonce deadline).readWithPadding
        128 32 =
      UInt256.toByteArray (⟨192⟩ : UInt256) := by
  unfold permitRuntimeStructHashMem writeCascade Reasoning.Theory.writeWord
  simp only [writeCascade_nil]
  rw [write32_read_above _ _ 64 128 (by rw [toByteArray_size])
      (by
        rw [permitRuntimeStructHashLenMem_size owner spender value nonce deadline hbaseSize]
        omega)
      (by omega)
      (by
        rw [permitRuntimeStructHashLenMem_size owner spender value nonce deadline hbaseSize]
        omega)]
  exact permitRuntimeStructHashLenMem_read128 owner spender value nonce deadline hbaseSize

theorem permitRuntimeStructHashMem_mload128 {baseMem : ByteArray}
    (owner spender value nonce deadline : UInt256)
    (hbaseSize : baseMem.size = 96) :
    (if (⟨128⟩ : UInt256).toNat ≥
          (permitRuntimeStructHashMem baseMem owner spender value nonce deadline).size
        ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 11 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((permitRuntimeStructHashMem baseMem owner spender value nonce deadline).readWithPadding
          (⟨128⟩ : UInt256).toNat 32)))
      = ⟨192⟩ :=
  mloadWordValue_of_readWithPadding
    (by
      rw [permitRuntimeStructHashMem_size owner spender value nonce deadline hbaseSize]
      decide)
    (by native_decide)
    (permitRuntimeStructHashMem_read128 owner spender value nonce deadline hbaseSize)

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

end UniswapV2Pair
