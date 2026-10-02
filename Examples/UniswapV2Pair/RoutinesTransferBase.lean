import Examples.UniswapV2Pair.RoutinesCheckedArithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! ## Shared internal `_transfer` routine prefix -/

abbrev uniswapCodeOwnerStorageWord (ee : ExecutionEnv) (σ : AccountMap)
    (slot : UInt256) : UInt256 :=
  codeOwnerStorageWord ee σ slot

theorem uniswapCodeOwnerStorageWord_initState {σ σ₀ A I} {g : Sat256}
    (slot : UInt256) :
    Solm.EVM.storageLoad (initState σ σ₀ g A I) I.codeOwner slot =
      uniswapCodeOwnerStorageWord I σ slot := by
  exact codeOwnerStorageWord_initState slot

set_option maxHeartbeats 1000000 in
theorem RD.uniswapTransferInternalFromBalanceLoadMem {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {value toWord src ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray}
    {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7510⟩
        (value :: toWord :: src :: ret :: R)
        mem (UInt256.ofNat 3) rdata σ k C)
    (hmem : mem.size = 96)
    (hcanonSrc : src.toNat < EVM.addressModulus)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6879⟩
      (value :: uniswapCodeOwnerStorageWord ee σ (mapSlot src ⟨1⟩) ::
        ⟨7551⟩ :: value :: toWord :: src :: ret :: R)
      (twoWordHashMem src ⟨1⟩ mem)
      (UInt256.ofNat 3) rdata σ k' C' := by
  simpa [uniswapCodeOwnerStorageWord, mapSlot, solcMappingSlot] using
    RD.solcSingleMappingLoadToRoutineMem
      (code := UniswapV2Pair.uniswapV2PairBytecode)
      (pc := ⟨7510⟩) (baseSlot := ⟨1⟩) (afterLoadPc := ⟨7551⟩)
      (routinePc := ⟨6879⟩) (value := value) (aux := toWord) (key := src)
      (ret := ret) (R := R) h
      (by
        unfold solcSingleMappingLoadToRoutineMemWf
        repeat' first | apply And.intro | native_decide)
      hmem hcanonSrc (by jump_dest) (by decide) hov

set_option maxHeartbeats 1000000 in
theorem RD.uniswapTransferInternalFromBalanceLoad {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {value toWord src ret : UInt256}
    {R : List UInt256} {rdata : ByteArray}
    {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7510⟩
        (value :: toWord :: src :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata σ k C)
    (hcanonSrc : src.toNat < EVM.addressModulus)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6879⟩
      (value :: uniswapCodeOwnerStorageWord ee σ (mapSlot src ⟨1⟩) ::
        ⟨7551⟩ :: value :: toWord :: src :: ret :: R)
      (twoWordHashMem src ⟨1⟩ solcFreePtrMem)
      (UInt256.ofNat 3) rdata σ k' C' := by
  simpa using RD.uniswapTransferInternalFromBalanceLoadMem
    (mem := solcFreePtrMem) h solcFreePtrMem_size hcanonSrc hov

set_option maxHeartbeats 1000000 in
theorem RD.uniswapTransferInternalAfterDebitMem {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {value toWord src ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray}
    {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7510⟩
        (value :: toWord :: src :: ret :: R)
        mem (UInt256.ofNat 3) rdata σ k C)
    (hmem : mem.size = 96)
    (hcanonSrc : src.toNat < EVM.addressModulus)
    (hbalance :
      value.toNat ≤ (uniswapCodeOwnerStorageWord ee σ (mapSlot src ⟨1⟩)).toNat)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7551⟩
      (UInt256.sub (uniswapCodeOwnerStorageWord ee σ (mapSlot src ⟨1⟩)) value ::
        value :: toWord :: src :: ret :: R)
      (twoWordHashMem src ⟨1⟩ mem)
      (UInt256.ofNat 3) rdata σ k' C' := by
  simpa [uniswapCodeOwnerStorageWord, mapSlot, solcMappingSlot] using
    RD.solcSingleMappingLoadCheckedSubMem
      (code := UniswapV2Pair.uniswapV2PairBytecode)
      (pc := ⟨7510⟩) (baseSlot := ⟨1⟩) (afterLoadPc := ⟨7551⟩)
      (routinePc := ⟨6879⟩) (checkedOkPc := ⟨2911⟩)
      (value := value) (aux := toWord) (key := src) (ret := ret) (R := R) h
      (by
        unfold solcSingleMappingLoadToRoutineMemWf
        repeat' first | apply And.intro | native_decide)
      (by
        unfold solcCheckedSubSuccessWf
        repeat' first | apply And.intro | native_decide)
      hmem hcanonSrc hbalance (by jump_dest) (by decide) (by jump_dest) (by jump_dest) hov

set_option maxHeartbeats 1000000 in
theorem RD.uniswapTransferInternalAfterDebit {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {value toWord src ret : UInt256}
    {R : List UInt256} {rdata : ByteArray}
    {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7510⟩
        (value :: toWord :: src :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata σ k C)
    (hcanonSrc : src.toNat < EVM.addressModulus)
    (hbalance :
      value.toNat ≤ (uniswapCodeOwnerStorageWord ee σ (mapSlot src ⟨1⟩)).toNat)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7551⟩
      (UInt256.sub (uniswapCodeOwnerStorageWord ee σ (mapSlot src ⟨1⟩)) value ::
        value :: toWord :: src :: ret :: R)
      (twoWordHashMem src ⟨1⟩ solcFreePtrMem)
      (UInt256.ofNat 3) rdata σ k' C' := by
  simpa using RD.uniswapTransferInternalAfterDebitMem
    (mem := solcFreePtrMem) h solcFreePtrMem_size hcanonSrc hbalance hov

abbrev uniswapTransferDebitHashMemOf (src : UInt256) (mem : ByteArray) :
    ByteArray :=
  twoWordHashMem src ⟨1⟩ (twoWordHashMem src ⟨1⟩ mem)

theorem uniswapTransferDebitHashMemOf_size (src : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (uniswapTransferDebitHashMemOf src mem).size = 96 := by
  unfold uniswapTransferDebitHashMemOf
  exact twoWordHashMem_size_96 src ⟨1⟩ (twoWordHashMem_size_96 src ⟨1⟩ hmem)

abbrev uniswapTransferDebitHashMem (src : UInt256) : ByteArray :=
  uniswapTransferDebitHashMemOf src solcFreePtrMem

theorem uniswapTransferDebitHashMem_size (src : UInt256) :
    (uniswapTransferDebitHashMem src).size = 96 := by
  exact uniswapTransferDebitHashMemOf_size src solcFreePtrMem_size

set_option maxHeartbeats 4000000 in
theorem RD.uniswapTransferInternalStoreDebitMem {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {debit value toWord src ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray}
    {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7551⟩
        (debit :: value :: toWord :: src :: ret :: R)
        (twoWordHashMem src ⟨1⟩ mem) (UInt256.ofNat 3) rdata σ k C)
    (hmem : mem.size = 96)
    (hperm : ee.perm = true)
    (hcanonSrc : src.toNat < EVM.addressModulus)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7582⟩
      (⟨0⟩ :: solcAddrMask :: ⟨64⟩ :: value :: toWord :: src :: ret :: R)
      (uniswapTransferDebitHashMemOf src mem) (UInt256.ofNat 3) rdata
      (sstoreAccountMap ee.codeOwner σ (mapSlot src ⟨1⟩) debit) k' C' := by
  simpa [uniswapTransferDebitHashMemOf, mapSlot, solcMappingSlot,
    solcSingleMappingStoreDebitOutPc] using
    RD.solcSingleMappingStoreDebitMem
      (code := UniswapV2Pair.uniswapV2PairBytecode)
      (pc := ⟨7551⟩) (baseSlot := ⟨1⟩) (newValue := debit)
      (value := value) (aux := toWord) (key := src) (ret := ret) (R := R) h
      (by
        unfold solcSingleMappingStoreDebitMemWf
        repeat' first | apply And.intro | native_decide)
      hmem hperm hcanonSrc hov

set_option maxHeartbeats 4000000 in
theorem RD.uniswapTransferInternalStoreDebit {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {debit value toWord src ret : UInt256}
    {R : List UInt256} {rdata : ByteArray}
    {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7551⟩
        (debit :: value :: toWord :: src :: ret :: R)
        (twoWordHashMem src ⟨1⟩ solcFreePtrMem) (UInt256.ofNat 3) rdata σ k C)
    (hperm : ee.perm = true)
    (hcanonSrc : src.toNat < EVM.addressModulus)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7582⟩
      (⟨0⟩ :: solcAddrMask :: ⟨64⟩ :: value :: toWord :: src :: ret :: R)
      (uniswapTransferDebitHashMem src) (UInt256.ofNat 3) rdata
      (sstoreAccountMap ee.codeOwner σ (mapSlot src ⟨1⟩) debit) k' C' := by
  simpa [uniswapTransferDebitHashMem] using RD.uniswapTransferInternalStoreDebitMem
    (mem := solcFreePtrMem) h solcFreePtrMem_size hperm hcanonSrc hov

abbrev uniswapTransferToHashMemOf (src toWord : UInt256) (mem : ByteArray) :
    ByteArray :=
  wordAt0Mem toWord (uniswapTransferDebitHashMemOf src mem)

theorem uniswapTransferToHashMemOf_size (src toWord : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (uniswapTransferToHashMemOf src toWord mem).size = 96 := by
  unfold uniswapTransferToHashMemOf
  exact wordAt0Mem_size_96 toWord (uniswapTransferDebitHashMemOf_size src hmem)

abbrev uniswapTransferToHashMem (src toWord : UInt256) : ByteArray :=
  uniswapTransferToHashMemOf src toWord solcFreePtrMem

theorem uniswapTransferToHashMem_size (src toWord : UInt256) :
    (uniswapTransferToHashMem src toWord).size = 96 := by
  exact uniswapTransferToHashMemOf_size src toWord solcFreePtrMem_size

set_option maxHeartbeats 1000000 in
theorem uniswapTransferToHashMemOf_read0_64 (src toWord : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (uniswapTransferToHashMemOf src toWord mem).readWithPadding 0 64 =
      UInt256.toByteArray toWord ++ UInt256.toByteArray ⟨1⟩ := by
  unfold uniswapTransferToHashMemOf wordAt0Mem
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num) (by
    rw [writeWord_size_of_96 _ _ 0 (by
      unfold uniswapTransferDebitHashMemOf
      exact twoWordHashMem_size_96 src ⟨1⟩ (twoWordHashMem_size_96 src ⟨1⟩ hmem))
      (by norm_num)]
    omega)]
  have hleft :
      ((UInt256.toByteArray toWord).write 0
        (uniswapTransferDebitHashMemOf src mem) 0 32).extract 0 32 =
        UInt256.toByteArray toWord := by
    rw [← readWithPadding_eq_extract _ 0 (by
      rw [writeWord_size_of_96 _ _ 0 (by
        unfold uniswapTransferDebitHashMemOf
        exact twoWordHashMem_size_96 src ⟨1⟩ (twoWordHashMem_size_96 src ⟨1⟩ hmem))
        (by norm_num)]
      omega)]
    rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by
      unfold uniswapTransferDebitHashMemOf
      rw [twoWordHashMem_size_96 src ⟨1⟩
        (twoWordHashMem_size_96 src ⟨1⟩ hmem)]
      omega)]
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_self_of_le (by
      change (UInt256.toByteArray toWord).size ≤ 32
      rw [toByteArray_size])
  have hright :
      ((UInt256.toByteArray toWord).write 0
        (uniswapTransferDebitHashMemOf src mem) 0 32).extract 32 64 =
        UInt256.toByteArray ⟨1⟩ := by
    rw [← readWithPadding_eq_extract _ 32 (by
      rw [writeWord_size_of_96 _ _ 0 (by
        unfold uniswapTransferDebitHashMemOf
        exact twoWordHashMem_size_96 src ⟨1⟩ (twoWordHashMem_size_96 src ⟨1⟩ hmem))
        (by norm_num)]
      omega)]
    rw [write32_read_above _ _ 0 32 (by rw [toByteArray_size]) (by
      unfold uniswapTransferDebitHashMemOf
      rw [twoWordHashMem_size_96 src ⟨1⟩
        (twoWordHashMem_size_96 src ⟨1⟩ hmem)]
      omega) (by omega) (by
      unfold uniswapTransferDebitHashMemOf
      rw [twoWordHashMem_size_96 src ⟨1⟩
        (twoWordHashMem_size_96 src ⟨1⟩ hmem)]
      omega)]
    unfold uniswapTransferDebitHashMemOf
    rw [twoWordHashMem_read32 src ⟨1⟩
      (twoWordHashMem_size_96 src ⟨1⟩ hmem)]
  rw [show ((UInt256.toByteArray toWord).write 0
        (uniswapTransferDebitHashMemOf src mem) 0 32).extract 0 64 =
      ((UInt256.toByteArray toWord).write 0
        (uniswapTransferDebitHashMemOf src mem) 0 32).extract 0 32 ++
      ((UInt256.toByteArray toWord).write 0
        (uniswapTransferDebitHashMemOf src mem) 0 32).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      norm_num]
  rw [hleft, hright]

theorem uniswapTransferToHashMem_read0_64 (src toWord : UInt256) :
    (uniswapTransferToHashMem src toWord).readWithPadding 0 64 =
      UInt256.toByteArray toWord ++ UInt256.toByteArray ⟨1⟩ := by
  exact uniswapTransferToHashMemOf_read0_64 src toWord solcFreePtrMem_size

theorem uniswapTransferToHashMemOf_slot (src toWord : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    UInt256.ofNat
        (fromByteArrayBigEndian (KEC ((uniswapTransferToHashMemOf src toWord mem).readWithPadding
          0 64))) =
      mapSlot toWord ⟨1⟩ := by
  rw [uniswapTransferToHashMemOf_read0_64 src toWord hmem]
  unfold mapSlot
  exact mappingSlot_single toWord ⟨1⟩

theorem uniswapTransferToHashMem_slot (src toWord : UInt256) :
    UInt256.ofNat
        (fromByteArrayBigEndian (KEC ((uniswapTransferToHashMem src toWord).readWithPadding
          0 64))) =
      mapSlot toWord ⟨1⟩ := by
  exact uniswapTransferToHashMemOf_slot src toWord solcFreePtrMem_size

end UniswapV2Pair
