import Examples.UniswapV2Pair.PermitRuntimeCore
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000

namespace UniswapV2Pair

theorem RD.uniswapPermitApproveSetup {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {recovered digest s r v deadline value spender owner ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray}
    {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5965⟩
      (recovered :: digest :: s :: r :: v :: deadline :: value :: spender :: owner :: ret :: R)
      mem (UInt256.ofNat 20) rdata σ k C)
    (hov : R.length + 19 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7412⟩
      (value :: spender :: owner :: ⟨5976⟩ :: recovered :: digest :: s :: r :: v ::
        deadline :: value :: spender :: owner :: ret :: R)
      mem (UInt256.ofNat 20) rdata σ k' C' := by
  have rd7412 := evm_run h with [
    jumpdest, push2 ⟨5976⟩, dup10, dup10, dup10, push2 ⟨7412⟩,
    jump (by jump_dest)]
  exact ⟨_, _, rd7412⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapPermitApproveInnerHash20 {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {value spender owner ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray}
    {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7412⟩
      (value :: spender :: owner :: ret :: R) mem (UInt256.ofNat 20) rdata σ k C)
    (hmem : 96 ≤ mem.size)
    (hcanonOwner : owner.toNat < EVM.addressModulus)
    (hov : R.length + 13 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7441⟩
      (mapSlot owner ⟨2⟩ :: ⟨64⟩ :: ⟨32⟩ :: ⟨0⟩ :: owner :: solcAddrMask ::
        value :: spender :: owner :: ret :: R)
      (twoWordHashMem owner ⟨2⟩ mem)
      (UInt256.ofNat 20) rdata σ k' C' := by
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
          (KEC ((twoWordHashMem owner (⟨2⟩ : UInt256) mem).readWithPadding 0 64))) =
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
    {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7441⟩
      (mapSlot owner ⟨2⟩ :: ⟨64⟩ :: ⟨32⟩ :: ⟨0⟩ :: owner :: solcAddrMask ::
        value :: spender :: owner :: ret :: R)
      mem (UInt256.ofNat 20) rdata σ k C)
    (hmem : 96 ≤ mem.size)
    (hperm : ee.perm = true)
    (hcanonSpender : spender.toNat < EVM.addressModulus)
    (hov : R.length + 13 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7457⟩
      (⟨32⟩ :: ⟨64⟩ :: owner :: spender :: value :: spender :: owner :: ret :: R)
      (twoWordHashMem spender (mapSlot owner ⟨2⟩) mem)
      (UInt256.ofNat 20) rdata
      (sstoreAccountMap ee.codeOwner σ (mapSlot spender (mapSlot owner ⟨2⟩)) value)
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
          (KEC ((twoWordHashMem spender (mapSlot owner ⟨2⟩) mem).readWithPadding 0 64))) =
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
    {acc : AccountMap}
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
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨482⟩ := by
    rw [if_neg]
    · rw [show (⟨64⟩ : UInt256).toNat = 64 from by native_decide, hfree]
      rw [fromByteArrayBigEndian_toByteArray]
      exact u256_ofNat_toNat (⟨482⟩ : UInt256)
    · rw [show (⟨64⟩ : UInt256).toNat = 64 from by native_decide]
      omega
  have hlogRead64 :
      ((UInt256.toByteArray value).write 0 mem 482 32).readWithPadding 64 32 =
        UInt256.toByteArray (⟨482⟩ : UInt256) := by
    rw [write32_read_below _ _ 482 64 (by rw [toByteArray_size])
      (by omega) (by omega)]
    exact hfree
  have hlogMload :
      (if (⟨64⟩ : UInt256).toNat ≥
            ((UInt256.toByteArray value).write 0 mem 482 32).size then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian
          (((UInt256.toByteArray value).write 0 mem 482 32).readWithPadding
            (⟨64⟩ : UInt256).toNat 32)))
        = ⟨482⟩ := by
    rw [if_neg]
    · rw [show (⟨64⟩ : UInt256).toNat = 64 from by native_decide, hlogRead64]
      rw [fromByteArrayBigEndian_toByteArray]
      exact u256_ofNat_toNat (⟨482⟩ : UInt256)
    · have hsize :
          ((UInt256.toByteArray value).write 0 mem 482 32).size = mem.size := by
        exact toByteArray_write32_size_of_le mem value 482 mem.size mem.size rfl
          (by omega) (by omega)
      rw [hsize]
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by native_decide]
      omega
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
    {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5965⟩
      (recovered :: digest :: s :: r :: v :: deadline :: value :: spender :: owner :: ⟨570⟩ :: R)
      mem (UInt256.ofNat 20) rdata σ k C)
    (hmem : 514 ≤ mem.size)
    (hfree : mem.readWithPadding 64 32 = UInt256.toByteArray (⟨482⟩ : UInt256))
    (hperm : ee.perm = true)
    (hcanonOwner : owner.toNat < EVM.addressModulus)
    (hcanonSpender : spender.toNat < EVM.addressModulus)
    (hov : R.length + 23 ≤ 1024) :
    RDret UniswapV2Pair.uniswapV2PairBytecode g s0
      (sstoreAccountMap ee.codeOwner σ (mapSlot spender (mapSlot owner ⟨2⟩)) value)
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

end UniswapV2Pair
