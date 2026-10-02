import Examples.UniswapV2Pair.RoutinesTransferTail

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! ## Shared internal `_approve` routine prefix -/

def uniswapApprovalTopic : UInt256 :=
  ⟨0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925⟩

abbrev uniswapApproveHashMem (owner spender : UInt256) : ByteArray :=
  twoWordHashMem spender (mapSlot owner ⟨2⟩) (twoWordHashMem owner ⟨2⟩ solcFreePtrMem)

def uniswapApproveLogMem (owner spender value : UInt256) : ByteArray :=
  (UInt256.toByteArray value).write 0 (uniswapApproveHashMem owner spender) 128 32

def uniswapApproveReturnMem
    (owner spender logValue retValue : UInt256) : ByteArray :=
  (UInt256.toByteArray retValue).write 0
    (uniswapApproveLogMem owner spender logValue) 128 32

theorem uniswapApproveHashMem_size (owner spender : UInt256) :
    (uniswapApproveHashMem owner spender).size = 96 := by
  unfold uniswapApproveHashMem
  exact twoWordHashMem_size_96 spender (mapSlot owner ⟨2⟩)
    (twoWordHashMem_size_96 owner ⟨2⟩ solcFreePtrMem_size)

theorem uniswapApproveHashMem_read64 (owner spender : UInt256) :
    (uniswapApproveHashMem owner spender).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold uniswapApproveHashMem
  exact twoWordHashMem_read64 spender (mapSlot owner ⟨2⟩)
    (twoWordHashMem_size_96 owner ⟨2⟩ solcFreePtrMem_size)
    (twoWordHashMem_read64 owner ⟨2⟩ solcFreePtrMem_size solcFreePtrMem_read64)

theorem uniswapApproveHashMem_mload64 (owner spender : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (uniswapApproveHashMem owner spender).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((uniswapApproveHashMem owner spender).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [uniswapApproveHashMem_size]; decide)
    (uniswapApproveHashMem_read64 owner spender)

set_option maxHeartbeats 1000000 in
theorem RD.uniswapTransferFromAllowanceMaxBranch {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {value toWord src ret : UInt256}
    {R : List UInt256} {rdata : ByteArray}
    {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨2938⟩
      (value :: toWord :: src :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata σ k C)
    (hcanonSrc : src.toNat < EVM.addressModulus)
    (hmax :
      (uniswapCodeOwnerStorageWord ee σ
        (mapSlot (uniswapSourceWord ee) (mapSlot src ⟨2⟩))).toNat =
        UInt256.size - 1)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨3071⟩
      (⟨0⟩ :: value :: toWord :: src :: ret :: R)
      (uniswapApproveHashMem src (uniswapSourceWord ee))
      (UInt256.ofNat 3) rdata σ k' C' := by
  have hmax' :
      (solcSlotWord σ ee
        (solcMappingSlot (solcMappingSlot (⟨2⟩ : UInt256) src) (solcSourceWord ee))).toNat =
        UInt256.size - 1 := by
    simpa [uniswapCodeOwnerStorageWord, uniswapSourceWord, mapSlot, solcMappingSlot] using hmax
  obtain ⟨_, _, rd2975⟩ := RD.solcNestedMappingCallerLoad
    (code := UniswapV2Pair.uniswapV2PairBytecode) (pc := ⟨2938⟩)
    (baseSlot := ⟨2⟩) (value := value) (aux := toWord) (owner := src)
    (ret := ret) (R := R) (mem := solcFreePtrMem) h
    (by
      unfold solcNestedMappingCallerLoadWf
      repeat' first | apply And.intro | native_decide)
    solcFreePtrMem_size hcanonSrc hov
  obtain ⟨_, _, rd3071⟩ := RD.solcUintMaxEqBranchTrue
    (code := UniswapV2Pair.uniswapV2PairBytecode)
    (pc := solcNestedMappingCallerLoadOutPc (⟨2938⟩ : UInt256))
    (targetPc := ⟨3071⟩)
    (word :=
      solcSlotWord σ ee
        (solcMappingSlot (solcMappingSlot (⟨2⟩ : UInt256) src) (solcSourceWord ee)))
    (discard := ⟨0⟩) (R := value :: toWord :: src :: ret :: R)
    rd2975
    (by
      unfold solcUintMaxEqBranchWf solcNestedMappingCallerLoadOutPc
      repeat' first | apply And.intro | native_decide)
    hmax' (by jump_dest) (by simp only [List.length_cons]; omega)
  exact ⟨_, _, by
    simpa [solcNestedMappingCallerLoadOutPc, solcNestedMappingCallerHashMem,
      uniswapCodeOwnerStorageWord, uniswapApproveHashMem, uniswapSourceWord, mapSlot,
      solcMappingSlot] using rd3071⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapTransferFromMaxAllowanceToInternal {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {value toWord src ret discard : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨3071⟩
      (discard :: value :: toWord :: src :: ret :: R) mem aw rdata acc k C)
    (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7510⟩
      (value :: toWord :: src :: ⟨3082⟩ :: discard :: value :: toWord :: src :: ret :: R)
      mem aw rdata acc k' C' := by
  exact RD.solcInternalCallSetup3
    (pc := ⟨3071⟩) (contPc := ⟨3082⟩) (routinePc := ⟨7510⟩) h
    (by
      unfold solcInternalCallSetup3Wf
      repeat' first | apply And.intro | native_decide)
    (by jump_dest) hov

theorem uniswapApproveLogMem_size (owner spender value : UInt256) :
    (uniswapApproveLogMem owner spender value).size = 160 := by
  unfold uniswapApproveLogMem
  rw [toByteArray_write_eq _ _ _ (by rw [uniswapApproveHashMem_size]; omega)
      (by rw [uniswapApproveHashMem_size]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, uniswapApproveHashMem_size,
    ByteArray_zeroes_size,
    toByteArray_size]

theorem uniswapApproveLogMem_read64 (owner spender value : UInt256) :
    (uniswapApproveLogMem owner spender value).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold uniswapApproveLogMem
  rw [toByteArray_write_eq _ _ _ (by rw [uniswapApproveHashMem_size]; omega)
      (by rw [uniswapApproveHashMem_size]; exact lt_usize _ (by norm_num))]
  rw [readWithPadding_eq_extract _ 64 (by
      rw [ByteArray.size_append, ByteArray.size_append, uniswapApproveHashMem_size,
        ByteArray_zeroes_size, toByteArray_size]
      native_decide)]
  rw [extract_append_left _ _ _ _ (by
      rw [ByteArray.size_append, uniswapApproveHashMem_size, ByteArray_zeroes_size]
      omega)]
  rw [extract_append_left _ _ _ _ (by rw [uniswapApproveHashMem_size]),
    ← readWithPadding_eq_extract _ 64 (by rw [uniswapApproveHashMem_size]),
    uniswapApproveHashMem_read64]

theorem uniswapApproveLogMem_mload64 (owner spender value : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (uniswapApproveLogMem owner spender value).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((uniswapApproveLogMem owner spender value).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [uniswapApproveLogMem_size]; decide)
    (uniswapApproveLogMem_read64 owner spender value)

theorem uniswapApproveLogMem_read128 (owner spender value : UInt256) :
    (uniswapApproveLogMem owner spender value).readWithPadding 128 32 =
      UInt256.toByteArray value := by
  unfold uniswapApproveLogMem
  rw [toByteArray_write_eq _ _ _ (by rw [uniswapApproveHashMem_size]; omega)
      (by rw [uniswapApproveHashMem_size]; exact lt_usize _ (by norm_num))]
  rw [readWithPadding_eq_extract _ 128 (by
      rw [ByteArray.size_append, ByteArray.size_append, uniswapApproveHashMem_size,
        ByteArray_zeroes_size,
        toByteArray_size])]
  rw [extract_append_right_window
      (uniswapApproveHashMem owner spender ++
        ByteArray.zeroes ((128 - (uniswapApproveHashMem owner spender).size)))
      (UInt256.toByteArray value) 128 (128 + 32) (by
        rw [ByteArray.size_append, uniswapApproveHashMem_size, ByteArray_zeroes_size])]
  rw [ByteArray.size_append, uniswapApproveHashMem_size, ByteArray_zeroes_size]
  norm_num
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray value).size ≤ 32
    rw [toByteArray_size])

theorem uniswapApproveReturnMem_size (owner spender logValue retValue : UInt256) :
    (uniswapApproveReturnMem owner spender logValue retValue).size = 160 := by
  unfold uniswapApproveReturnMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [uniswapApproveLogMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, uniswapApproveLogMem_size,
    toByteArray_size]
  omega

theorem uniswapApproveReturnMem_read64 (owner spender logValue retValue : UInt256) :
    (uniswapApproveReturnMem owner spender logValue retValue).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold uniswapApproveReturnMem
  rw [write32_read_below _ _ 128 64 (by rw [toByteArray_size])
      (by rw [uniswapApproveLogMem_size]; omega) (by omega),
    uniswapApproveLogMem_read64]

theorem uniswapApproveReturnMem_mload64 (owner spender logValue retValue : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (uniswapApproveReturnMem owner spender logValue retValue).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((uniswapApproveReturnMem owner spender logValue retValue).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [uniswapApproveReturnMem_size]; decide)
    (uniswapApproveReturnMem_read64 owner spender logValue retValue)

theorem uniswapApproveReturnMem_read128 (owner spender logValue retValue : UInt256) :
    (uniswapApproveReturnMem owner spender logValue retValue).readWithPadding 128 32 =
      UInt256.toByteArray retValue := by
  unfold uniswapApproveReturnMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [uniswapApproveLogMem_size]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray retValue).size ≤ 32
    rw [toByteArray_size])

set_option maxHeartbeats 1000000 in
theorem RD.uniswapApproveInternalInnerHash {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {value spender owner ret : UInt256} {R : List UInt256} {rdata : ByteArray}
    {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7412⟩
        (value :: spender :: owner :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata σ k C)
    (hcanonOwner : owner.toNat < EVM.addressModulus)
    (hov : R.length + 13 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7441⟩
      (mapSlot owner ⟨2⟩ :: ⟨64⟩ :: ⟨32⟩ :: ⟨0⟩ :: owner :: solcAddrMask :: value ::
        spender :: owner :: ret :: R)
      (twoWordHashMem owner ⟨2⟩ solcFreePtrMem)
      (UInt256.ofNat 3) rdata σ k' C' := by
  simpa [solcNestedMappingStoreInnerHashOutPc, mapSlot, solcMappingSlot] using
    RD.solcNestedMappingStoreInnerHash
      (code := UniswapV2Pair.uniswapV2PairBytecode) (pc := ⟨7412⟩)
      (baseSlot := ⟨2⟩) (value := value) (spender := spender)
      (owner := owner) (ret := ret) (R := R) (mem := solcFreePtrMem) h
      (by
        unfold solcNestedMappingStoreInnerHashWf
        repeat' first | apply And.intro | native_decide)
      solcFreePtrMem_size hcanonOwner hov

set_option maxHeartbeats 1000000 in
theorem RD.uniswapApproveInternalStore {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {value spender owner ret : UInt256} {R : List UInt256} {rdata : ByteArray}
    {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7441⟩
      (mapSlot owner ⟨2⟩ :: ⟨64⟩ :: ⟨32⟩ :: ⟨0⟩ :: owner :: solcAddrMask ::
        value :: spender :: owner :: ret :: R)
      (twoWordHashMem owner ⟨2⟩ solcFreePtrMem)
      (UInt256.ofNat 3) rdata σ k C)
    (hperm : ee.perm = true)
    (hcanonSpender : spender.toNat < EVM.addressModulus)
    (hov : R.length + 13 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7457⟩
      (⟨32⟩ :: ⟨64⟩ :: owner :: spender :: value :: spender :: owner :: ret :: R)
      (twoWordHashMem spender (mapSlot owner ⟨2⟩)
        (twoWordHashMem owner ⟨2⟩ solcFreePtrMem))
      (UInt256.ofNat 3) rdata
      (sstoreAccountMap ee.codeOwner σ (mapSlot spender (mapSlot owner ⟨2⟩)) value)
      k' C' := by
  simpa [solcNestedMappingStoreOuterSstoreOutPc, mapSlot, solcMappingSlot] using
    RD.solcNestedMappingStoreOuterSstore
      (code := UniswapV2Pair.uniswapV2PairBytecode) (pc := ⟨7441⟩)
      (innerSlot := mapSlot owner ⟨2⟩) (value := value) (spender := spender)
      (owner := owner) (ret := ret) (R := R)
      (mem := twoWordHashMem owner ⟨2⟩ solcFreePtrMem) h
      (by
        unfold solcNestedMappingStoreOuterSstoreWf
        repeat' first | apply And.intro | native_decide)
      (twoWordHashMem_size_96 owner ⟨2⟩ solcFreePtrMem_size)
      hperm hcanonSpender hov

set_option maxHeartbeats 1000000 in
theorem RD.uniswapApproveInternalEmitAndJump {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {value spender owner ret : UInt256} {R : List UInt256} {rdata : ByteArray}
    {acc : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7457⟩
      (⟨32⟩ :: ⟨64⟩ :: owner :: spender :: value :: spender :: owner :: ret :: R)
      (uniswapApproveHashMem owner spender) (UInt256.ofNat 3) rdata acc k C)
    (hperm : ee.perm = true)
    (hret : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains ret = true)
    (hov : R.length + 11 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ret R
      (uniswapApproveLogMem owner spender value) (UInt256.ofNat 5) rdata acc k' C' := by
  simpa [uniswapApproveLogMem] using
    RD.solcPlainLog3AndJump
      (code := UniswapV2Pair.uniswapV2PairBytecode) (pc := ⟨7457⟩)
      (topic := uniswapApprovalTopic) (value := value) (topic1 := owner)
      (topic2 := spender) (ret := ret) (R := R)
      (mem := uniswapApproveHashMem owner spender) h
      (by
        unfold solcPlainLog3AndJumpWf
        repeat' first | apply And.intro | native_decide)
      (uniswapApproveHashMem_mload64 owner spender)
      (by simpa [uniswapApproveLogMem] using uniswapApproveLogMem_mload64 owner spender value)
      hperm hret hov

theorem RD.uniswapReturnBool797FromMem {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {val : UInt256} {R : List UInt256} {mem memout rdata : ByteArray}
    {acc : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨797⟩ (val :: R)
      mem (UInt256.ofNat 5) rdata acc k C)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hmemout :
      (UInt256.toByteArray (UInt256.isZero (UInt256.isZero val))).write 0 mem 128 32 =
        memout)
    (hmemoutLoad64 :
      (if (⟨64⟩ : UInt256).toNat ≥ memout.size then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (memout.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hread128 :
      memout.readWithPadding 128 32 =
        UInt256.toByteArray (UInt256.isZero (UInt256.isZero val)))
    (hov : R.length + 5 ≤ 1024) :
    RDret UniswapV2Pair.uniswapV2PairBytecode g s0 acc
      (UInt256.toByteArray (UInt256.isZero (UInt256.isZero val))) := by
  exact RD.solcReturnBoolFromMem h
    (by
      unfold solcReturnBoolFromMemWf
      repeat' first | apply And.intro | native_decide)
    hmload64
    hmemout
    hmemoutLoad64
    hread128
    hov


end UniswapV2Pair
