import Examples.UniswapV2Pair.PermitRuntimeInvalid
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000

namespace UniswapV2Pair

set_option maxHeartbeats 1000000 in
theorem RD.uniswapPermitEcrecoverSignatureGuardZeroReverts {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {baseMem o rdata : ByteArray}
    {recovered digest s r v deadline value spender owner ret : UInt256}
    {R : List UInt256} {acc : AccountMap}
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
    {R : List UInt256} {acc : AccountMap}
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
    {R : List UInt256} {acc : AccountMap}
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
    {R : List UInt256} {acc : AccountMap}
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
