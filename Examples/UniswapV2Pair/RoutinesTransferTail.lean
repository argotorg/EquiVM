import Examples.UniswapV2Pair.RoutinesTransferBase

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair

set_option maxHeartbeats 2000000 in
theorem RD.uniswapTransferInternalToBalanceLoadMem {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {value toWord src ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray}
    {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7582⟩
      (⟨0⟩ :: solcAddrMask :: ⟨64⟩ :: value :: toWord :: src :: ret :: R)
      (uniswapTransferDebitHashMemOf src mem) (UInt256.ofNat 3) rdata σ k C)
    (hmem : mem.size = 96)
    (hcanonTo : toWord.toNat < EVM.addressModulus)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨8515⟩
      (value :: uniswapCodeOwnerStorageWord ee σ (mapSlot toWord ⟨1⟩) ::
        ⟨7604⟩ :: value :: toWord :: src :: ret :: R)
      (uniswapTransferToHashMemOf src toWord mem) (UInt256.ofNat 3) rdata σ k' C' := by
  simpa [uniswapCodeOwnerStorageWord, uniswapTransferToHashMemOf, mapSlot, solcMappingSlot] using
    RD.solcPreparedSingleMappingLoadToRoutineMem
      (code := UniswapV2Pair.uniswapV2PairBytecode)
      (pc := ⟨7582⟩) (baseSlot := ⟨1⟩) (afterLoadPc := ⟨7604⟩)
      (routinePc := ⟨8515⟩) (value := value) (key := toWord) (other := src)
      (ret := ret) (R := R) h
      (by
        unfold solcPreparedSingleMappingLoadToRoutineMemWf
        repeat' first | apply And.intro | native_decide)
      (uniswapTransferToHashMemOf_slot src toWord hmem)
      hcanonTo (by jump_dest) (by decide) hov

set_option maxHeartbeats 2000000 in
theorem RD.uniswapTransferInternalToBalanceLoad {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {value toWord src ret : UInt256}
    {R : List UInt256} {rdata : ByteArray}
    {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7582⟩
      (⟨0⟩ :: solcAddrMask :: ⟨64⟩ :: value :: toWord :: src :: ret :: R)
      (uniswapTransferDebitHashMem src) (UInt256.ofNat 3) rdata σ k C)
    (hcanonTo : toWord.toNat < EVM.addressModulus)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨8515⟩
      (value :: uniswapCodeOwnerStorageWord ee σ (mapSlot toWord ⟨1⟩) ::
        ⟨7604⟩ :: value :: toWord :: src :: ret :: R)
      (uniswapTransferToHashMem src toWord) (UInt256.ofNat 3) rdata σ k' C' := by
  simpa [uniswapTransferDebitHashMem, uniswapTransferToHashMem] using
    RD.uniswapTransferInternalToBalanceLoadMem
      (mem := solcFreePtrMem) h solcFreePtrMem_size hcanonTo hov

set_option maxHeartbeats 2000000 in
theorem RD.uniswapTransferInternalAfterCreditCalcMem {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {value toWord src ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray}
    {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7582⟩
      (⟨0⟩ :: solcAddrMask :: ⟨64⟩ :: value :: toWord :: src :: ret :: R)
      (uniswapTransferDebitHashMemOf src mem) (UInt256.ofNat 3) rdata σ k C)
    (hmem : mem.size = 96)
    (hcanonTo : toWord.toNat < EVM.addressModulus)
    (hfit : (uniswapCodeOwnerStorageWord ee σ (mapSlot toWord ⟨1⟩)).toNat +
      value.toNat < UInt256.size)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7604⟩
      ((uniswapCodeOwnerStorageWord ee σ (mapSlot toWord ⟨1⟩) + value) ::
        value :: toWord :: src :: ret :: R)
      (uniswapTransferToHashMemOf src toWord mem) (UInt256.ofNat 3) rdata σ k' C' := by
  simpa [uniswapCodeOwnerStorageWord, uniswapTransferToHashMemOf, mapSlot, solcMappingSlot] using
    RD.solcPreparedSingleMappingLoadCheckedAddMem
      (code := UniswapV2Pair.uniswapV2PairBytecode)
      (pc := ⟨7582⟩) (baseSlot := ⟨1⟩) (afterLoadPc := ⟨7604⟩)
      (routinePc := ⟨8515⟩) (checkedOkPc := ⟨2911⟩)
      (value := value) (key := toWord) (other := src) (ret := ret) (R := R) h
      (by
        unfold solcPreparedSingleMappingLoadToRoutineMemWf
        repeat' first | apply And.intro | native_decide)
      (by
        unfold solcCheckedAddSuccessWf
        repeat' first | apply And.intro | native_decide)
      (uniswapTransferToHashMemOf_slot src toWord hmem)
      hcanonTo hfit (by jump_dest) (by decide) (by jump_dest) (by jump_dest) hov

set_option maxHeartbeats 2000000 in
theorem RD.uniswapTransferInternalAfterCreditCalc {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {value toWord src ret : UInt256}
    {R : List UInt256} {rdata : ByteArray}
    {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7582⟩
      (⟨0⟩ :: solcAddrMask :: ⟨64⟩ :: value :: toWord :: src :: ret :: R)
      (uniswapTransferDebitHashMem src) (UInt256.ofNat 3) rdata σ k C)
    (hcanonTo : toWord.toNat < EVM.addressModulus)
    (hfit : (uniswapCodeOwnerStorageWord ee σ (mapSlot toWord ⟨1⟩)).toNat +
      value.toNat < UInt256.size)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7604⟩
      ((uniswapCodeOwnerStorageWord ee σ (mapSlot toWord ⟨1⟩) + value) ::
        value :: toWord :: src :: ret :: R)
      (uniswapTransferToHashMem src toWord) (UInt256.ofNat 3) rdata σ k' C' := by
  simpa [uniswapTransferDebitHashMem, uniswapTransferToHashMem] using
    RD.uniswapTransferInternalAfterCreditCalcMem
      (mem := solcFreePtrMem) h solcFreePtrMem_size hcanonTo hfit hov

abbrev uniswapTransferCreditHashMem (src toWord : UInt256) : ByteArray :=
  twoWordHashMem toWord ⟨1⟩ (uniswapTransferToHashMem src toWord)

theorem uniswapTransferCreditHashMem_size (src toWord : UInt256) :
    (uniswapTransferCreditHashMem src toWord).size = 96 := by
  unfold uniswapTransferCreditHashMem
  exact twoWordHashMem_size_96 toWord ⟨1⟩ (uniswapTransferToHashMem_size src toWord)

theorem uniswapTransferCreditHashMem_slot (src toWord : UInt256) :
    UInt256.ofNat
        (fromByteArrayBigEndian (KEC ((uniswapTransferCreditHashMem src toWord).readWithPadding
          0 64))) =
      mapSlot toWord ⟨1⟩ := by
  unfold uniswapTransferCreditHashMem
  rw [twoWordHashMem_read0_64 toWord ⟨1⟩ (uniswapTransferToHashMem_size src toWord)]
  unfold mapSlot
  exact mappingSlot_single toWord ⟨1⟩

set_option maxHeartbeats 4000000 in
theorem RD.uniswapTransferInternalStoreCredit {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {newTo value toWord src ret : UInt256}
    {R : List UInt256} {rdata : ByteArray}
    {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7604⟩
      (newTo :: value :: toWord :: src :: ret :: R)
      (uniswapTransferToHashMem src toWord) (UInt256.ofNat 3) rdata σ k C)
    (hperm : ee.perm = true)
    (hcanonTo : toWord.toNat < EVM.addressModulus)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7638⟩
      (⟨64⟩ :: toWord :: solcAddrMask :: ⟨32⟩ :: value :: toWord :: src :: ret :: R)
      (uniswapTransferCreditHashMem src toWord) (UInt256.ofNat 3) rdata
      (sstoreAccountMap ee.codeOwner σ (mapSlot toWord ⟨1⟩) newTo) k' C' := by
  simpa [solcSingleMappingStoreCreditOutPc, uniswapTransferCreditHashMem,
    uniswapTransferToHashMem, mapSlot, solcMappingSlot] using
    RD.solcSingleMappingStoreCreditMem
      (code := UniswapV2Pair.uniswapV2PairBytecode) (pc := ⟨7604⟩)
      (baseSlot := ⟨1⟩) (newValue := newTo) (value := value) (key := toWord)
      (aux := src) (ret := ret) (R := R) (mem := uniswapTransferToHashMem src toWord)
      h
      (by
        unfold solcSingleMappingStoreCreditMemWf
        repeat' first | apply And.intro | native_decide)
      (by
        simpa [uniswapTransferCreditHashMem, mapSlot, solcMappingSlot] using
          uniswapTransferCreditHashMem_slot src toWord)
      hperm hcanonTo hov

def uniswapTransferTopic : UInt256 :=
  ⟨0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef⟩

theorem uniswapTransferDebitHashMem_read64 (src : UInt256) :
    (uniswapTransferDebitHashMem src).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold uniswapTransferDebitHashMem
  exact twoWordHashMem_read64 src ⟨1⟩
    (twoWordHashMem_size_96 src ⟨1⟩ solcFreePtrMem_size)
    (twoWordHashMem_read64 src ⟨1⟩ solcFreePtrMem_size solcFreePtrMem_read64)

theorem uniswapTransferToHashMem_read64 (src toWord : UInt256) :
    (uniswapTransferToHashMem src toWord).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold uniswapTransferToHashMem uniswapTransferToHashMemOf wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
      (by rw [uniswapTransferDebitHashMem_size]; omega) (by omega)
      (by rw [uniswapTransferDebitHashMem_size])]
  exact uniswapTransferDebitHashMem_read64 src

theorem uniswapTransferCreditHashMem_read64 (src toWord : UInt256) :
    (uniswapTransferCreditHashMem src toWord).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold uniswapTransferCreditHashMem
  exact twoWordHashMem_read64 toWord ⟨1⟩ (uniswapTransferToHashMem_size src toWord)
    (uniswapTransferToHashMem_read64 src toWord)

theorem uniswapTransferCreditHashMem_mload64 (src toWord : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (uniswapTransferCreditHashMem src toWord).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((uniswapTransferCreditHashMem src toWord).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [uniswapTransferCreditHashMem_size]; decide)
    (uniswapTransferCreditHashMem_read64 src toWord)

def uniswapTransferLogMem (src toWord value : UInt256) : ByteArray :=
  (UInt256.toByteArray value).write 0 (uniswapTransferCreditHashMem src toWord) 128 32

theorem uniswapTransferLogMem_size (src toWord value : UInt256) :
    (uniswapTransferLogMem src toWord value).size = 160 := by
  unfold uniswapTransferLogMem
  rw [toByteArray_write_eq _ _ _ (by rw [uniswapTransferCreditHashMem_size]; omega)
      (by rw [uniswapTransferCreditHashMem_size]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, uniswapTransferCreditHashMem_size,
    ByteArray_zeroes_size,
    toByteArray_size]

theorem uniswapTransferLogMem_read64 (src toWord value : UInt256) :
    (uniswapTransferLogMem src toWord value).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold uniswapTransferLogMem
  rw [toByteArray_write_eq _ _ _ (by rw [uniswapTransferCreditHashMem_size]; omega)
      (by rw [uniswapTransferCreditHashMem_size]; exact lt_usize _ (by norm_num))]
  rw [readWithPadding_eq_extract _ 64 (by
      rw [ByteArray.size_append, ByteArray.size_append, uniswapTransferCreditHashMem_size,
        ByteArray_zeroes_size, toByteArray_size]
      native_decide)]
  rw [extract_append_left _ _ _ _ (by
      rw [ByteArray.size_append, uniswapTransferCreditHashMem_size, ByteArray_zeroes_size]
      omega)]
  rw [extract_append_left _ _ _ _ (by rw [uniswapTransferCreditHashMem_size]),
    ← readWithPadding_eq_extract _ 64 (by rw [uniswapTransferCreditHashMem_size]),
    uniswapTransferCreditHashMem_read64]

theorem uniswapTransferLogMem_mload64 (src toWord value : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (uniswapTransferLogMem src toWord value).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((uniswapTransferLogMem src toWord value).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [uniswapTransferLogMem_size]; decide)
    (uniswapTransferLogMem_read64 src toWord value)

theorem uniswapTransferLogMem_read128 (src toWord value : UInt256) :
    (uniswapTransferLogMem src toWord value).readWithPadding 128 32 =
      UInt256.toByteArray value := by
  unfold uniswapTransferLogMem
  rw [toByteArray_write_eq _ _ _ (by rw [uniswapTransferCreditHashMem_size]; omega)
      (by rw [uniswapTransferCreditHashMem_size]; exact lt_usize _ (by norm_num))]
  rw [readWithPadding_eq_extract _ 128 (by
      rw [ByteArray.size_append, ByteArray.size_append, uniswapTransferCreditHashMem_size,
        ByteArray_zeroes_size,
        toByteArray_size])]
  rw [extract_append_right_window
      (uniswapTransferCreditHashMem src toWord ++
        ByteArray.zeroes ((128 - (uniswapTransferCreditHashMem src toWord).size)))
      (UInt256.toByteArray value) 128 (128 + 32) (by
        rw [ByteArray.size_append, uniswapTransferCreditHashMem_size, ByteArray_zeroes_size])]
  rw [ByteArray.size_append, uniswapTransferCreditHashMem_size, ByteArray_zeroes_size]
  norm_num
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray value).size ≤ 32
    rw [toByteArray_size])

def uniswapTransferReturnMem
    (src toWord logValue retValue : UInt256) : ByteArray :=
  (UInt256.toByteArray retValue).write 0
    (uniswapTransferLogMem src toWord logValue) 128 32

theorem uniswapTransferReturnMem_size (src toWord logValue retValue : UInt256) :
    (uniswapTransferReturnMem src toWord logValue retValue).size = 160 := by
  unfold uniswapTransferReturnMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [uniswapTransferLogMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, uniswapTransferLogMem_size,
    toByteArray_size]
  omega

theorem uniswapTransferReturnMem_read64 (src toWord logValue retValue : UInt256) :
    (uniswapTransferReturnMem src toWord logValue retValue).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold uniswapTransferReturnMem
  rw [write32_read_below _ _ 128 64 (by rw [toByteArray_size])
      (by rw [uniswapTransferLogMem_size]; omega) (by omega),
    uniswapTransferLogMem_read64]

theorem uniswapTransferReturnMem_mload64 (src toWord logValue retValue : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (uniswapTransferReturnMem src toWord logValue retValue).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((uniswapTransferReturnMem src toWord logValue retValue).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [uniswapTransferReturnMem_size]; decide)
    (uniswapTransferReturnMem_read64 src toWord logValue retValue)

theorem uniswapTransferReturnMem_read128 (src toWord logValue retValue : UInt256) :
    (uniswapTransferReturnMem src toWord logValue retValue).readWithPadding 128 32 =
      UInt256.toByteArray retValue := by
  unfold uniswapTransferReturnMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [uniswapTransferLogMem_size]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray retValue).size ≤ 32
    rw [toByteArray_size])

set_option maxHeartbeats 4000000 in
theorem RD.uniswapTransferInternalEmitAndJump {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {value toWord src ret : UInt256}
    {R : List UInt256} {rdata : ByteArray}
    {acc : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7638⟩
      (⟨64⟩ :: toWord :: solcAddrMask :: ⟨32⟩ :: value :: toWord :: src :: ret :: R)
      (uniswapTransferCreditHashMem src toWord) (UInt256.ofNat 3) rdata acc k C)
    (hperm : ee.perm = true)
    (hcanonSrc : src.toNat < EVM.addressModulus)
    (hret : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains ret = true)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ret R
      (uniswapTransferLogMem src toWord value) (UInt256.ofNat 5) rdata acc k' C' := by
  simpa [uniswapTransferLogMem] using
    RD.solcMaskedTransferLog3AndJump
      (code := UniswapV2Pair.uniswapV2PairBytecode) (pc := ⟨7638⟩)
      (topic := uniswapTransferTopic) (value := value) (toWord := toWord)
      (src := src) (ret := ret) (R := R)
      (mem := uniswapTransferCreditHashMem src toWord) h
      (by
        unfold solcMaskedTransferLog3AndJumpWf
        repeat' first | apply And.intro | native_decide)
      (uniswapTransferCreditHashMem_mload64 src toWord)
      (by simpa [uniswapTransferLogMem] using uniswapTransferLogMem_mload64 src toWord value)
      hperm hcanonSrc hret hov

set_option maxHeartbeats 1000000 in
theorem RD.uniswapInternalTransferReturnTrue {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {discard a b ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨2907⟩
      (discard :: a :: b :: ret :: R) mem aw rdata acc k C)
    (hret : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains ret = true)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ret
      (⟨1⟩ :: R) mem aw rdata acc k' C' := by
  exact RD.solcDiscard2ReturnTrue (pc := ⟨2907⟩) h
    (by
      unfold solcDiscard2ReturnTrueWf
      repeat' first | apply And.intro | native_decide)
    hret hov


end UniswapV2Pair
