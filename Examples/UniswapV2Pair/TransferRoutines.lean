import Examples.UniswapV2Pair.Routines
import Examples.UniswapV2Pair.LegacyABI

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! ## Shared `Error(string)` revert memory -/

def uniswapErrorStringSelector : UInt256 :=
  solcErrorStringSelector

noncomputable abbrev uniswapErrorStringMem0 (mem : ByteArray) : ByteArray :=
  solcErrorStringMem0 mem

noncomputable abbrev uniswapErrorStringMem1 (mem : ByteArray) : ByteArray :=
  solcErrorStringMem1 mem

noncomputable abbrev uniswapErrorStringMem2 (len : UInt256) (mem : ByteArray) : ByteArray :=
  solcErrorStringMem2 len mem

noncomputable abbrev uniswapErrorStringMem3 (len word : UInt256) (mem : ByteArray) : ByteArray :=
  solcErrorStringMem3 len word mem

theorem uniswapErrorStringMem0_size {mem : ByteArray} (hmem : mem.size = 96) :
    (uniswapErrorStringMem0 mem).size = 160 := by
  exact solcErrorStringMem0_size hmem

theorem uniswapErrorStringMem1_size {mem : ByteArray} (hmem : mem.size = 96) :
    (uniswapErrorStringMem1 mem).size = 164 := by
  exact solcErrorStringMem1_size hmem

theorem uniswapErrorStringMem2_size (len : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (uniswapErrorStringMem2 len mem).size = 196 := by
  exact solcErrorStringMem2_size len hmem

theorem uniswapErrorStringMem3_size (len word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (uniswapErrorStringMem3 len word mem).size = 228 := by
  exact solcErrorStringMem3_size len word hmem

theorem uniswapErrorStringMem3_read64 (len word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (uniswapErrorStringMem3 len word mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  exact solcErrorStringMem3_read64 len word hmem hread64

theorem uniswapErrorStringMem3_mload64 (len word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (uniswapErrorStringMem3 len word mem).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((uniswapErrorStringMem3 len word mem).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ := by
  exact solcErrorStringMem3_mload64 len word hmem hread64

theorem uniswapErrorStringMem0_size_of_size164 {mem : ByteArray} (hmem : mem.size = 164) :
    (uniswapErrorStringMem0 mem).size = 164 := by
  exact solcErrorStringMem0_size_of_size164 hmem

theorem uniswapErrorStringMem1_size_of_size164 {mem : ByteArray} (hmem : mem.size = 164) :
    (uniswapErrorStringMem1 mem).size = 164 := by
  exact solcErrorStringMem1_size_of_size164 hmem

theorem uniswapErrorStringMem2_size_of_size164 (len : UInt256) {mem : ByteArray}
    (hmem : mem.size = 164) :
    (uniswapErrorStringMem2 len mem).size = 196 := by
  exact solcErrorStringMem2_size_of_size164 len hmem

theorem uniswapErrorStringMem3_size_of_size164 (len word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 164) :
    (uniswapErrorStringMem3 len word mem).size = 228 := by
  exact solcErrorStringMem3_size_of_size164 len word hmem

theorem uniswapErrorStringMem3_read64_of_size164 (len word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (uniswapErrorStringMem3 len word mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  exact solcErrorStringMem3_read64_of_size164 len word hmem hread64

theorem uniswapErrorStringMem3_mload64_of_size164 (len word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (uniswapErrorStringMem3 len word mem).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((uniswapErrorStringMem3 len word mem).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  solcErrorStringMem3_mload64_of_size164 len word hmem hread64

def uniswapSafeMathSubUnderflowStringWord : UInt256 :=
  UInt256.shiftLeft
    (⟨146807710733670254765134916515197633279875231805303⟩ : UInt256) ⟨88⟩

def uniswapSafeMathAddOverflowStringWord : UInt256 :=
  UInt256.shiftLeft
    (⟨573467620053399432670716995166075968196518375287⟩ : UInt256) ⟨96⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSafeMathSubUnderflow {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {a b ret : UInt256} {R : List UInt256} {mem : ByteArray}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6879⟩ (b :: a :: ret :: R)
      mem (UInt256.ofNat 3) rdata acc k C)
    (hlt : a.toNat < b.toNat)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 9 ≤ 1024) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g s0 := by
  exact RD.solcCheckedSubStringRevert
    (code := UniswapV2Pair.uniswapV2PairBytecode) (pc := ⟨6879⟩) (okPc := ⟨2911⟩)
    (len := ⟨21⟩)
    (rawWord := (⟨146807710733670254765134916515197633279875231805303⟩ : UInt256))
    (shift := ⟨88⟩) (word := UniswapV2Pair.uniswapSafeMathSubUnderflowStringWord)
    (op := .PUSH21) (width := 21) (a := a) (b := b) (ret := ret)
    (R := R) (mem := mem) h
    (by
      unfold solcCheckedSubSuccessWf
      repeat' first | apply And.intro | decide +native)
    (by
      unfold solcErrorStringRevertTailWf solcCheckedArithmeticRevertPc
      repeat' first | apply And.intro | decide +native)
    (by decide) hlt (by rfl) hmem hread64 hov

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSafeMathSubUnderflow_aw6_size164 {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {a b ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6879⟩ (b :: a :: ret :: R)
      mem (UInt256.ofNat 6) rdata acc k C)
    (hlt : a.toNat < b.toNat)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 9 ≤ 1024) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g s0 := by
  have hsubNat : (UInt256.sub a b).toNat = UInt256.size + a.toNat - b.toNat :=
    usub_toNat_underflow hlt
  have hgt : UInt256.gt (UInt256.sub a b) a = ⟨1⟩ := by
    show UInt256.fromBool (decide (UInt256.sub a b > a)) = ⟨1⟩
    rw [decide_eq_true]
    · rfl
    · show (UInt256.sub a b).toNat > a.toNat
      rw [hsubNat]
      have hb : b.toNat < UInt256.size := b.val.isLt
      omega
  have rd6886 := evm_run h with [jumpdest, dup1, dup3, sub, dup3, dup2]
  have rd6887₀ := evm_run rd6886 with [gt]
  have rd6887 := rd6887₀
  rw [hgt] at rd6887
  have rd6888₀ := evm_run rd6887 with [iszero]
  have rd6888 := rd6888₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd6888
  have rd6891 := evm_run rd6888 with [
    push2 ⟨2911⟩, jumpiNT (by decide)]
  have rd6895 := evm_run rd6891 with [
    push1 ⟨64⟩, dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide)
      mem_cost
      (mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64)
      (by decide) (by evm_ov)]
  have rd6899 := rd6895.pushConst (⟨4594637⟩ : UInt256) (width := 3) (op := .PUSH3)
    (by decide) (by decide) (by evm_ov)
  have rd6918 := evm_run rd6899 with [
    push1 ⟨229⟩, shl, dup2,
    raw mstore 0 (UniswapV2Pair.uniswapErrorStringMem0 mem) (UInt256.ofNat 6)
      (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, push1 ⟨4⟩, dup3, add,
    raw mstore 0 (UniswapV2Pair.uniswapErrorStringMem1 mem) (UInt256.ofNat 6)
      (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    push1 ⟨21⟩, push1 ⟨36⟩, dup3, add,
    raw mstore 3
      (UniswapV2Pair.uniswapErrorStringMem2 (⟨21⟩ : UInt256) mem)
      (UInt256.ofNat 7) (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov)]
  have rd6940 := rd6918.pushConst
    (⟨146807710733670254765134916515197633279875231805303⟩ : UInt256)
    (width := 21) (op := .PUSH21) (by decide) (by decide) (by evm_ov)
  exact evm_run rd6940 with [
    push1 ⟨88⟩, shl, push1 ⟨68⟩, dup3, add,
    raw mstore 3
      (UniswapV2Pair.uniswapErrorStringMem3 (⟨21⟩ : UInt256)
        UniswapV2Pair.uniswapSafeMathSubUnderflowStringWord mem)
      (UInt256.ofNat 8) (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    swap1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by decide)
      mem_cost
      (UniswapV2Pair.uniswapErrorStringMem3_mload64_of_size164 (⟨21⟩ : UInt256)
        UniswapV2Pair.uniswapSafeMathSubUnderflowStringWord hmem hread64)
      (by decide) (by evm_ov),
    swap1, dup2, swap1, sub, push1 ⟨100⟩, add, swap1,
    raw rev 0 (by decide) mem_cost (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSafeMathAddOverflow {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {a b ret : UInt256} {R : List UInt256} {mem : ByteArray}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨8515⟩ (b :: a :: ret :: R)
      mem (UInt256.ofNat 3) rdata acc k C)
    (hover : UInt256.size ≤ a.toNat + b.toNat)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 9 ≤ 1024) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g s0 := by
  exact RD.solcCheckedAddStringRevert
    (code := UniswapV2Pair.uniswapV2PairBytecode) (pc := ⟨8515⟩) (okPc := ⟨2911⟩)
    (len := ⟨20⟩)
    (rawWord := (⟨573467620053399432670716995166075968196518375287⟩ : UInt256))
    (shift := ⟨96⟩) (word := UniswapV2Pair.uniswapSafeMathAddOverflowStringWord)
    (op := .PUSH20) (width := 20) (a := a) (b := b) (ret := ret)
    (R := R) (mem := mem) h
    (by
      unfold solcCheckedAddSuccessWf
      repeat' first | apply And.intro | decide +native)
    (by
      unfold solcErrorStringRevertTailWf solcCheckedArithmeticRevertPc
      repeat' first | apply And.intro | decide +native)
    (by decide) hover (by rfl) hmem hread64 hov

/-! # Shared `_transfer` suffix helpers

This file continues the shared `_transfer` routine lemmas once `Routines.lean` is close to the
2k-line iteration limit.
-/

noncomputable abbrev uniswapTransferCreditHashMemOf
    (src toWord : UInt256) (mem : ByteArray) : ByteArray :=
  twoWordHashMem toWord ⟨1⟩ (uniswapTransferToHashMemOf src toWord mem)

theorem uniswapTransferCreditHashMemOf_size (src toWord : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (uniswapTransferCreditHashMemOf src toWord mem).size = 96 := by
  unfold uniswapTransferCreditHashMemOf
  exact twoWordHashMem_size_96 toWord ⟨1⟩ (uniswapTransferToHashMemOf_size src toWord hmem)

theorem uniswapTransferCreditHashMemOf_slot (src toWord : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    UInt256.ofNat
        (fromByteArrayBigEndian
          (ffi.KEC ((uniswapTransferCreditHashMemOf src toWord mem).readWithPadding 0 64))) =
      mapSlot toWord ⟨1⟩ := by
  unfold uniswapTransferCreditHashMemOf
  rw [twoWordHashMem_read0_64 toWord ⟨1⟩ (uniswapTransferToHashMemOf_size src toWord hmem)]
  unfold mapSlot
  exact mappingSlot_single toWord ⟨1⟩

set_option maxHeartbeats 4000000 in
theorem RD.uniswapTransferInternalStoreCreditMem {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {newTo value toWord src ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7604⟩
      (newTo :: value :: toWord :: src :: ret :: R)
      (uniswapTransferToHashMemOf src toWord mem) (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hmem : mem.size = 96)
    (hperm : ee.perm = true)
    (hcanonTo : toWord.toNat < EVM.addressModulus)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7638⟩
      (⟨64⟩ :: toWord :: solcAddrMask :: ⟨32⟩ :: value :: toWord :: src :: ret :: R)
      (uniswapTransferCreditHashMemOf src toWord mem) (UInt256.ofNat 3) rdata
      (cA, sstoreAccountMap ee.codeOwner σ (mapSlot toWord ⟨1⟩) newTo) k' C' := by
  simpa [solcSingleMappingStoreCreditOutPc, uniswapTransferCreditHashMemOf,
    uniswapTransferToHashMemOf, mapSlot, solcMappingSlot] using
    RD.solcSingleMappingStoreCreditMem
      (code := UniswapV2Pair.uniswapV2PairBytecode) (pc := ⟨7604⟩)
      (baseSlot := ⟨1⟩) (newValue := newTo) (value := value) (key := toWord)
      (aux := src) (ret := ret) (R := R) (mem := uniswapTransferToHashMemOf src toWord mem)
      h
      (by
        unfold solcSingleMappingStoreCreditMemWf
        repeat' first | apply And.intro | decide +native)
      (by
        simpa [uniswapTransferCreditHashMemOf, mapSlot, solcMappingSlot] using
          uniswapTransferCreditHashMemOf_slot src toWord hmem)
      hperm hcanonTo hov

theorem uniswapTransferDebitHashMemOf_read64 (src : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (uniswapTransferDebitHashMemOf src mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold uniswapTransferDebitHashMemOf
  exact twoWordHashMem_read64 src ⟨1⟩ (twoWordHashMem_size_96 src ⟨1⟩ hmem)
    (twoWordHashMem_read64 src ⟨1⟩ hmem hmem64)

theorem uniswapTransferToHashMemOf_read64 (src toWord : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (uniswapTransferToHashMemOf src toWord mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold uniswapTransferToHashMemOf wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
      (by rw [uniswapTransferDebitHashMemOf_size src hmem]; omega) (by omega)
      (by rw [uniswapTransferDebitHashMemOf_size src hmem])]
  exact uniswapTransferDebitHashMemOf_read64 src hmem hmem64

theorem uniswapTransferCreditHashMemOf_read64 (src toWord : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (uniswapTransferCreditHashMemOf src toWord mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold uniswapTransferCreditHashMemOf
  exact twoWordHashMem_read64 toWord ⟨1⟩ (uniswapTransferToHashMemOf_size src toWord hmem)
    (uniswapTransferToHashMemOf_read64 src toWord hmem hmem64)

theorem uniswapTransferCreditHashMemOf_mload64 (src toWord : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (uniswapTransferCreditHashMemOf src toWord mem).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((uniswapTransferCreditHashMemOf src toWord mem).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [uniswapTransferCreditHashMemOf_size src toWord hmem]; decide)
    (by decide) (uniswapTransferCreditHashMemOf_read64 src toWord hmem hmem64)

noncomputable def uniswapTransferLogMemOf
    (src toWord value : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray value).write 0 (uniswapTransferCreditHashMemOf src toWord mem) 128 32

theorem uniswapTransferLogMemOf_size (src toWord value : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (uniswapTransferLogMemOf src toWord value mem).size = 160 := by
  unfold uniswapTransferLogMemOf
  rw [toByteArray_write_eq _ _ _ (by rw [uniswapTransferCreditHashMemOf_size src toWord hmem]; omega)
      (by rw [uniswapTransferCreditHashMemOf_size src toWord hmem]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, uniswapTransferCreditHashMemOf_size src toWord hmem,
    ByteArray_zeroes_size, toByteArray_size]

theorem uniswapTransferLogMemOf_read64 (src toWord value : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (uniswapTransferLogMemOf src toWord value mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold uniswapTransferLogMemOf
  rw [toByteArray_write_eq _ _ _ (by rw [uniswapTransferCreditHashMemOf_size src toWord hmem]; omega)
      (by rw [uniswapTransferCreditHashMemOf_size src toWord hmem]; exact lt_usize _ (by norm_num))]
  rw [readWithPadding_eq_extract _ 64 (by
      rw [ByteArray.size_append, ByteArray.size_append,
        uniswapTransferCreditHashMemOf_size src toWord hmem, ByteArray_zeroes_size,
        toByteArray_size]
      norm_num)]
  rw [extract_append_left _ _ _ _ (by
      rw [ByteArray.size_append, uniswapTransferCreditHashMemOf_size src toWord hmem,
        ByteArray_zeroes_size]
      omega)]
  rw [extract_append_left _ _ _ _ (by rw [uniswapTransferCreditHashMemOf_size src toWord hmem]),
    ← readWithPadding_eq_extract _ 64 (by rw [uniswapTransferCreditHashMemOf_size src toWord hmem]),
    uniswapTransferCreditHashMemOf_read64 src toWord hmem hmem64]

theorem uniswapTransferLogMemOf_mload64 (src toWord value : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (uniswapTransferLogMemOf src toWord value mem).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((uniswapTransferLogMemOf src toWord value mem).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [uniswapTransferLogMemOf_size src toWord value hmem]; decide)
    (by decide) (uniswapTransferLogMemOf_read64 src toWord value hmem hmem64)

noncomputable def uniswapTransferReturnMemOf
    (src toWord logValue retValue : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray retValue).write 0
    (uniswapTransferLogMemOf src toWord logValue mem) 128 32

theorem uniswapTransferReturnMemOf_size
    (src toWord logValue retValue : UInt256) {mem : ByteArray} (hmem : mem.size = 96) :
    (uniswapTransferReturnMemOf src toWord logValue retValue mem).size = 160 := by
  unfold uniswapTransferReturnMemOf
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [uniswapTransferLogMemOf_size src toWord logValue hmem]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract,
    uniswapTransferLogMemOf_size src toWord logValue hmem, toByteArray_size]
  omega

theorem uniswapTransferReturnMemOf_read64
    (src toWord logValue retValue : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (uniswapTransferReturnMemOf src toWord logValue retValue mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold uniswapTransferReturnMemOf
  rw [write32_read_below _ _ 128 64 (by rw [toByteArray_size])
      (by rw [uniswapTransferLogMemOf_size src toWord logValue hmem]; omega) (by omega),
    uniswapTransferLogMemOf_read64 src toWord logValue hmem hmem64]

theorem uniswapTransferReturnMemOf_mload64
    (src toWord logValue retValue : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (uniswapTransferReturnMemOf src toWord logValue retValue mem).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((uniswapTransferReturnMemOf src toWord logValue retValue mem).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue
    (by rw [uniswapTransferReturnMemOf_size src toWord logValue retValue hmem]; decide)
    (by decide) (uniswapTransferReturnMemOf_read64 src toWord logValue retValue hmem hmem64)

theorem uniswapTransferReturnMemOf_read128
    (src toWord logValue retValue : UInt256) {mem : ByteArray} (hmem : mem.size = 96) :
    (uniswapTransferReturnMemOf src toWord logValue retValue mem).readWithPadding 128 32 =
      UInt256.toByteArray retValue := by
  unfold uniswapTransferReturnMemOf
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [uniswapTransferLogMemOf_size src toWord logValue hmem]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray retValue).size ≤ 32
    rw [toByteArray_size])

set_option maxHeartbeats 4000000 in
theorem RD.uniswapTransferInternalEmitAndJumpMem {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {value toWord src ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7638⟩
      (⟨64⟩ :: toWord :: solcAddrMask :: ⟨32⟩ :: value :: toWord :: src :: ret :: R)
      (uniswapTransferCreditHashMemOf src toWord mem) (UInt256.ofNat 3) rdata acc k C)
    (hmem : mem.size = 96)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hperm : ee.perm = true)
    (hcanonSrc : src.toNat < EVM.addressModulus)
    (hret : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains ret = true)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ret R
      (uniswapTransferLogMemOf src toWord value mem) (UInt256.ofNat 5) rdata acc k' C' := by
  simpa [uniswapTransferLogMemOf] using
    RD.solcMaskedTransferLog3AndJump
      (code := UniswapV2Pair.uniswapV2PairBytecode) (pc := ⟨7638⟩)
      (topic := uniswapTransferTopic) (value := value) (toWord := toWord)
      (src := src) (ret := ret) (R := R)
      (mem := uniswapTransferCreditHashMemOf src toWord mem) h
      (by
        unfold solcMaskedTransferLog3AndJumpWf
        repeat' first | apply And.intro | decide +native)
      (uniswapTransferCreditHashMemOf_mload64 src toWord hmem hmem64)
      (by
        simpa [uniswapTransferLogMemOf] using
          uniswapTransferLogMemOf_mload64 src toWord value hmem hmem64)
      hperm hcanonSrc hret hov

set_option maxHeartbeats 1000000 in
theorem RD.uniswapTransferFromContinuationReturnTrue {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {discard value toWord src ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨3082⟩
      (discard :: value :: toWord :: src :: ret :: R) mem aw rdata acc k C)
    (hret : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains ret = true)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ret
      (⟨1⟩ :: R) mem aw rdata acc k' C' := by
  exact RD.solcDiscard4ReturnTrue (pc := ⟨3082⟩) h
    (by
      unfold solcDiscard4ReturnTrueWf
      repeat' first | apply And.intro | decide +native)
    hret hov

noncomputable abbrev uniswapTransferFromAllowanceStoreMemOf
    (src spender : UInt256) (mem : ByteArray) : ByteArray :=
  twoWordHashMem spender (mapSlot src ⟨2⟩) (twoWordHashMem src ⟨2⟩ mem)

noncomputable abbrev uniswapTransferFromAllowanceStoreMem (src spender : UInt256) : ByteArray :=
  uniswapTransferFromAllowanceStoreMemOf src spender (uniswapApproveHashMem src spender)

theorem uniswapTransferFromAllowanceStoreMemOf_size
    (src spender : UInt256) {mem : ByteArray} (hmem : mem.size = 96) :
    (uniswapTransferFromAllowanceStoreMemOf src spender mem).size = 96 := by
  unfold uniswapTransferFromAllowanceStoreMemOf
  exact twoWordHashMem_size_96 spender (mapSlot src ⟨2⟩)
    (twoWordHashMem_size_96 src ⟨2⟩ hmem)

theorem uniswapTransferFromAllowanceStoreMem_size (src spender : UInt256) :
    (uniswapTransferFromAllowanceStoreMem src spender).size = 96 :=
  uniswapTransferFromAllowanceStoreMemOf_size src spender (uniswapApproveHashMem_size src spender)

theorem uniswapTransferFromAllowanceStoreMemOf_read64
    (src spender : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (uniswapTransferFromAllowanceStoreMemOf src spender mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold uniswapTransferFromAllowanceStoreMemOf
  exact twoWordHashMem_read64 spender (mapSlot src ⟨2⟩)
    (twoWordHashMem_size_96 src ⟨2⟩ hmem)
    (twoWordHashMem_read64 src ⟨2⟩ hmem hmem64)

theorem uniswapTransferFromAllowanceStoreMem_read64 (src spender : UInt256) :
    (uniswapTransferFromAllowanceStoreMem src spender).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ :=
  uniswapTransferFromAllowanceStoreMemOf_read64 src spender
    (uniswapApproveHashMem_size src spender) (uniswapApproveHashMem_read64 src spender)

theorem uniswapTransferFromAllowanceStoreMemOf_slot
    (src spender : UInt256) {mem : ByteArray} (hmem : mem.size = 96) :
    UInt256.ofNat
        (fromByteArrayBigEndian
          (ffi.KEC ((uniswapTransferFromAllowanceStoreMemOf src spender mem).readWithPadding
            0 64))) =
      mapSlot spender (mapSlot src ⟨2⟩) := by
  unfold uniswapTransferFromAllowanceStoreMemOf
  rw [twoWordHashMem_read0_64 spender (mapSlot src ⟨2⟩)
    (twoWordHashMem_size_96 src ⟨2⟩ hmem)]
  unfold mapSlot
  exact mappingSlot_single spender (mapSlot src ⟨2⟩)

theorem uniswapTransferFromAllowanceStoreMem_slot (src spender : UInt256) :
    UInt256.ofNat
        (fromByteArrayBigEndian
          (ffi.KEC ((uniswapTransferFromAllowanceStoreMem src spender).readWithPadding 0 64))) =
      mapSlot spender (mapSlot src ⟨2⟩) :=
  uniswapTransferFromAllowanceStoreMemOf_slot src spender
    (uniswapApproveHashMem_size src spender)

set_option maxHeartbeats 4000000 in
theorem RD.uniswapTransferFromFiniteAllowanceStoreMem {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {newAllowance discard value toWord src ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨3034⟩
      (newAllowance :: discard :: value :: toWord :: src :: ret :: R)
      mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hmem : mem.size = 96)
    (hperm : ee.perm = true)
    (hcanonSrc : src.toNat < EVM.addressModulus)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨3071⟩
      (discard :: value :: toWord :: src :: ret :: R)
      (uniswapTransferFromAllowanceStoreMemOf src (uniswapSourceWord ee) mem)
      (UInt256.ofNat 3) rdata
      (cA, sstoreAccountMap ee.codeOwner σ
        (mapSlot (uniswapSourceWord ee) (mapSlot src ⟨2⟩)) newAllowance) k' C' := by
  simpa [solcNestedMappingCallerStoreMemOutPc, solcNestedMappingCallerHashMem,
    uniswapTransferFromAllowanceStoreMemOf, uniswapSourceWord, mapSlot, solcMappingSlot] using
    RD.solcNestedMappingCallerStoreMem
      (code := UniswapV2Pair.uniswapV2PairBytecode) (pc := ⟨3034⟩)
      (baseSlot := ⟨2⟩) (newValue := newAllowance) (discard := discard)
      (value := value) (aux := toWord) (owner := src) (ret := ret)
      (R := R) (mem := mem) h
      (by
        unfold solcNestedMappingCallerStoreMemWf
        repeat' first | apply And.intro | decide +native)
      hmem hperm hcanonSrc hov

set_option maxHeartbeats 1000000 in
theorem RD.uniswapTransferFromFiniteAllowanceStore {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {newAllowance discard value toWord src ret : UInt256}
    {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨3034⟩
      (newAllowance :: discard :: value :: toWord :: src :: ret :: R)
      (uniswapApproveHashMem src (uniswapSourceWord ee)) (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hperm : ee.perm = true)
    (hcanonSrc : src.toNat < EVM.addressModulus)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨3071⟩
      (discard :: value :: toWord :: src :: ret :: R)
      (uniswapTransferFromAllowanceStoreMem src (uniswapSourceWord ee))
      (UInt256.ofNat 3) rdata
      (cA, sstoreAccountMap ee.codeOwner σ
        (mapSlot (uniswapSourceWord ee) (mapSlot src ⟨2⟩)) newAllowance) k' C' := by
  obtain ⟨_, _, rd3071⟩ := RD.uniswapTransferFromFiniteAllowanceStoreMem
    h (uniswapApproveHashMem_size src (uniswapSourceWord ee)) hperm hcanonSrc hov
  exact ⟨_, _, by simpa [uniswapTransferFromAllowanceStoreMem] using rd3071⟩

set_option maxHeartbeats 4000000 in
theorem RD.uniswapTransferFromAllowanceBranchToSubRoutine {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {value toWord src ret : UInt256}
    {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨2938⟩
      (value :: toWord :: src :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hcanonSrc : src.toNat < EVM.addressModulus)
    (hnotMax :
      (uniswapCodeOwnerStorageWord ee σ
        (mapSlot (uniswapSourceWord ee) (mapSlot src ⟨2⟩))).toNat ≠
        UInt256.size - 1)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6879⟩
      (value ::
        uniswapCodeOwnerStorageWord ee σ
          (mapSlot (uniswapSourceWord ee) (mapSlot src ⟨2⟩)) ::
        ⟨3034⟩ :: ⟨0⟩ :: value :: toWord :: src :: ret :: R)
      (uniswapTransferFromAllowanceStoreMem src (uniswapSourceWord ee))
      (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  have hnotMax' :
      (solcSlotWord σ ee
        (solcMappingSlot (solcMappingSlot (⟨2⟩ : UInt256) src) (solcSourceWord ee))).toNat ≠
        UInt256.size - 1 := by
    simpa [uniswapCodeOwnerStorageWord, uniswapSourceWord, mapSlot, solcMappingSlot] using hnotMax
  obtain ⟨_, _, rd2975⟩ := RD.solcNestedMappingCallerLoad
    (code := UniswapV2Pair.uniswapV2PairBytecode) (pc := ⟨2938⟩)
    (baseSlot := ⟨2⟩) (value := value) (aux := toWord) (owner := src)
    (ret := ret) (R := R) (mem := solcFreePtrMem) h
    (by
      unfold solcNestedMappingCallerLoadWf
      repeat' first | apply And.intro | decide +native)
    solcFreePtrMem_size hcanonSrc hov
  obtain ⟨_, _, rd2983⟩ := RD.solcUintMaxEqBranchFalse
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
      repeat' first | apply And.intro | decide +native)
    hnotMax' (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rd6879⟩ := RD.solcNestedMappingCallerReloadToRoutineMem
    (code := UniswapV2Pair.uniswapV2PairBytecode)
    (pc :=
      solcUintMaxEqBranchFallthroughPc
        (solcNestedMappingCallerLoadOutPc (⟨2938⟩ : UInt256)))
    (baseSlot := ⟨2⟩) (contPc := ⟨3034⟩) (routinePc := ⟨6879⟩)
    (discard := ⟨0⟩) (value := value) (aux := toWord) (owner := src)
    (ret := ret) (R := R)
    (mem := uniswapApproveHashMem src (uniswapSourceWord ee))
    rd2983
    (by
      unfold solcNestedMappingCallerReloadToRoutineMemWf
        solcUintMaxEqBranchFallthroughPc solcNestedMappingCallerLoadOutPc
      repeat' first | apply And.intro | decide +native)
    (uniswapApproveHashMem_size src (uniswapSourceWord ee))
    hcanonSrc (by jump_dest) (by decide) hov
  exact ⟨_, _, by
    simpa [solcNestedMappingCallerLoadOutPc, solcUintMaxEqBranchFallthroughPc,
      solcNestedMappingCallerHashMem, uniswapCodeOwnerStorageWord,
      uniswapTransferFromAllowanceStoreMem, uniswapApproveHashMem, uniswapSourceWord,
      mapSlot, solcMappingSlot] using rd6879⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapTransferFromAllowanceFiniteBranch {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {value toWord src ret : UInt256}
    {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨2938⟩
      (value :: toWord :: src :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hcanonSrc : src.toNat < EVM.addressModulus)
    (hnotMax :
      (uniswapCodeOwnerStorageWord ee σ
        (mapSlot (uniswapSourceWord ee) (mapSlot src ⟨2⟩))).toNat ≠
        UInt256.size - 1)
    (hallowance : value.toNat ≤
      (uniswapCodeOwnerStorageWord ee σ
        (mapSlot (uniswapSourceWord ee) (mapSlot src ⟨2⟩))).toNat)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨3034⟩
      (UInt256.sub
          (uniswapCodeOwnerStorageWord ee σ
            (mapSlot (uniswapSourceWord ee) (mapSlot src ⟨2⟩))) value ::
        ⟨0⟩ :: value :: toWord :: src :: ret :: R)
      (uniswapTransferFromAllowanceStoreMem src (uniswapSourceWord ee))
      (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  let allowanceSlot := mapSlot (uniswapSourceWord ee) (mapSlot src ⟨2⟩)
  let allowanceWord := uniswapCodeOwnerStorageWord ee σ allowanceSlot
  have hallowance' : value.toNat ≤ allowanceWord.toNat := by
    simpa [allowanceWord, allowanceSlot] using hallowance
  obtain ⟨_, _, rd6879⟩ := RD.uniswapTransferFromAllowanceBranchToSubRoutine
    h hcanonSrc hnotMax hov
  obtain ⟨_, _, rd3034⟩ := RD.uniswapSafeMathSubSuccess
    (a := allowanceWord) (b := value) (ret := ⟨3034⟩)
    (R := ⟨0⟩ :: value :: toWord :: src :: ret :: R)
    rd6879 hallowance' (by jump_dest) (by simp only [List.length_cons]; omega)
  exact ⟨_, _, by simpa [allowanceWord, allowanceSlot] using rd3034⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapTransferFromAllowanceFailureBranch {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {value toWord src ret : UInt256}
    {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨2938⟩
      (value :: toWord :: src :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hcanonSrc : src.toNat < EVM.addressModulus)
    (hnotMax :
      (uniswapCodeOwnerStorageWord ee σ
        (mapSlot (uniswapSourceWord ee) (mapSlot src ⟨2⟩))).toNat ≠
        UInt256.size - 1)
    (hltAllowance :
      (uniswapCodeOwnerStorageWord ee σ
        (mapSlot (uniswapSourceWord ee) (mapSlot src ⟨2⟩))).toNat < value.toNat)
    (hov : R.length + 16 ≤ 1024) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g s0 := by
  let allowanceSlot := mapSlot (uniswapSourceWord ee) (mapSlot src ⟨2⟩)
  let allowanceWord := uniswapCodeOwnerStorageWord ee σ allowanceSlot
  have hltAllowance' : allowanceWord.toNat < value.toNat := by
    simpa [allowanceWord, allowanceSlot] using hltAllowance
  obtain ⟨_, _, rd6879⟩ := RD.uniswapTransferFromAllowanceBranchToSubRoutine
    h hcanonSrc hnotMax hov
  exact RD.uniswapSafeMathSubUnderflow
    (a := allowanceWord) (b := value) (ret := ⟨3034⟩)
    (R := ⟨0⟩ :: value :: toWord :: src :: ret :: R)
    rd6879 hltAllowance'
    (uniswapTransferFromAllowanceStoreMem_size src (uniswapSourceWord ee))
    (uniswapTransferFromAllowanceStoreMem_read64 src (uniswapSourceWord ee))
    (by simp only [List.length_cons]; omega)

-- Reusable Uniswap-local chain from the finite allowance branch into the shared internal
-- `_transfer` routine setup.
set_option maxHeartbeats 1000000 in
theorem RD.uniswapTransferFromAllowanceFiniteToInternal {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {value toWord src ret : UInt256}
    {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨2938⟩
      (value :: toWord :: src :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hperm : ee.perm = true)
    (hcanonSrc : src.toNat < EVM.addressModulus)
    (hnotMax :
      (uniswapCodeOwnerStorageWord ee σ
        (mapSlot (uniswapSourceWord ee) (mapSlot src ⟨2⟩))).toNat ≠
        UInt256.size - 1)
    (hallowance : value.toNat ≤
      (uniswapCodeOwnerStorageWord ee σ
        (mapSlot (uniswapSourceWord ee) (mapSlot src ⟨2⟩))).toNat)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7510⟩
      (value :: toWord :: src :: ⟨3082⟩ :: ⟨0⟩ :: value :: toWord :: src :: ret :: R)
      (uniswapTransferFromAllowanceStoreMemOf src (uniswapSourceWord ee)
        (uniswapTransferFromAllowanceStoreMem src (uniswapSourceWord ee)))
      (UInt256.ofNat 3) rdata
      (cA, sstoreAccountMap ee.codeOwner σ
        (mapSlot (uniswapSourceWord ee) (mapSlot src ⟨2⟩))
        (UInt256.sub
          (uniswapCodeOwnerStorageWord ee σ
            (mapSlot (uniswapSourceWord ee) (mapSlot src ⟨2⟩))) value)) k' C' := by
  obtain ⟨_, _, rd3034⟩ := RD.uniswapTransferFromAllowanceFiniteBranch
    h hcanonSrc hnotMax hallowance hov
  obtain ⟨_, _, rd3071⟩ := RD.uniswapTransferFromFiniteAllowanceStoreMem
    (mem := uniswapTransferFromAllowanceStoreMem src (uniswapSourceWord ee))
    rd3034
    (uniswapTransferFromAllowanceStoreMem_size src (uniswapSourceWord ee))
    hperm hcanonSrc hov
  obtain ⟨_, _, rd7510⟩ := RD.uniswapTransferFromMaxAllowanceToInternal
    (R := R) rd3071 (by omega)
  exact ⟨_, _, rd7510⟩

-- Reusable Uniswap-local chain from the finite-allowance store continuation into the shared
-- internal `_transfer` routine setup.
set_option maxHeartbeats 1000000 in
theorem RD.uniswapTransferFromFiniteAllowanceToInternal {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {newAllowance discard value toWord src ret : UInt256}
    {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨3034⟩
      (newAllowance :: discard :: value :: toWord :: src :: ret :: R)
      (uniswapApproveHashMem src (uniswapSourceWord ee)) (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hperm : ee.perm = true)
    (hcanonSrc : src.toNat < EVM.addressModulus)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7510⟩
      (value :: toWord :: src :: ⟨3082⟩ :: discard :: value :: toWord :: src :: ret :: R)
      (uniswapTransferFromAllowanceStoreMem src (uniswapSourceWord ee))
      (UInt256.ofNat 3) rdata
      (cA, sstoreAccountMap ee.codeOwner σ
        (mapSlot (uniswapSourceWord ee) (mapSlot src ⟨2⟩)) newAllowance) k' C' := by
  obtain ⟨_, _, rd3071⟩ := RD.uniswapTransferFromFiniteAllowanceStore
    h hperm hcanonSrc hov
  obtain ⟨_, _, rd7510⟩ := RD.uniswapTransferFromMaxAllowanceToInternal
    (R := R) rd3071 (by omega)
  exact ⟨_, _, rd7510⟩

end UniswapV2Pair
