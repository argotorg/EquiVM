import Examples.UniswapV2Pair.Routines
import Examples.UniswapV2Pair.LegacyABI

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! ## Shared `Error(string)` revert memory -/

def uniswapErrorStringSelector : UInt256 :=
  UInt256.shiftLeft (⟨4594637⟩ : UInt256) ⟨229⟩

-- LIBRARY CANDIDATE: Reasoning.Memory - generic solc `Error(string)` selector write over a
-- 96-byte scratch buffer that preserves the free pointer at `0x40`.
noncomputable def uniswapErrorStringMem0 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray uniswapErrorStringSelector).write 0 mem 128 32

-- LIBRARY CANDIDATE: Reasoning.Memory - generic solc `Error(string)` offset-word write over a
-- previously built selector buffer.
noncomputable def uniswapErrorStringMem1 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (⟨32⟩ : UInt256)).write 0 (uniswapErrorStringMem0 mem) 132 32

-- LIBRARY CANDIDATE: Reasoning.Memory - generic solc `Error(string)` length-word write.
noncomputable def uniswapErrorStringMem2 (len : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray len).write 0 (uniswapErrorStringMem1 mem) 164 32

-- LIBRARY CANDIDATE: Reasoning.Memory - generic solc `Error(string)` payload-word write.
noncomputable def uniswapErrorStringMem3 (len word : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray word).write 0 (uniswapErrorStringMem2 len mem) 196 32

theorem uniswapErrorStringMem0_size {mem : ByteArray} (hmem : mem.size = 96) :
    (uniswapErrorStringMem0 mem).size = 160 := by
  unfold uniswapErrorStringMem0
  rw [toByteArray_write_eq _ _ _ (by rw [hmem]; omega)
      (by rw [hmem]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, hmem, ByteArray_zeroes_size,
    show (USize.ofNat (128 - 96)).toNat = 32 from
      USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
    toByteArray_size]

theorem uniswapErrorStringMem1_size {mem : ByteArray} (hmem : mem.size = 96) :
    (uniswapErrorStringMem1 mem).size = 164 := by
  unfold uniswapErrorStringMem1
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [uniswapErrorStringMem0_size hmem]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, uniswapErrorStringMem0_size hmem,
    toByteArray_size]
  omega

theorem uniswapErrorStringMem2_size (len : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (uniswapErrorStringMem2 len mem).size = 196 := by
  unfold uniswapErrorStringMem2
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by simp [uniswapErrorStringMem1_size hmem]),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, uniswapErrorStringMem1_size hmem,
    toByteArray_size]
  omega

theorem uniswapErrorStringMem3_size (len word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (uniswapErrorStringMem3 len word mem).size = 228 := by
  unfold uniswapErrorStringMem3
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by simp [uniswapErrorStringMem2_size len hmem]),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, uniswapErrorStringMem2_size len hmem,
    toByteArray_size]
  omega

-- LIBRARY CANDIDATE: Reasoning.Memory - `Error(string)` memory construction preserves the solc
-- free pointer word at `0x40`.
theorem uniswapErrorStringMem3_read64 (len word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (uniswapErrorStringMem3 len word mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold uniswapErrorStringMem3
  rw [toByteArray_write_read_below_of_gap word _ 196 64
      (by rw [uniswapErrorStringMem2_size len hmem]; omega) (by omega)
      (by rw [uniswapErrorStringMem2_size len hmem]; exact lt_usize _ (by norm_num))]
  unfold uniswapErrorStringMem2
  rw [toByteArray_write_read_below_of_gap len _ 164 64
      (by rw [uniswapErrorStringMem1_size hmem]; omega) (by omega)
      (by rw [uniswapErrorStringMem1_size hmem]; exact lt_usize _ (by norm_num))]
  unfold uniswapErrorStringMem1
  rw [toByteArray_write_read_below_of_gap (⟨32⟩ : UInt256) _ 132 64
      (by rw [uniswapErrorStringMem0_size hmem]; omega) (by omega)
      (by rw [uniswapErrorStringMem0_size hmem]; exact lt_usize _ (by norm_num))]
  unfold uniswapErrorStringMem0
  rw [toByteArray_write_read_below_of_gap uniswapErrorStringSelector _ 128 64
      (by omega) (by omega) (by rw [hmem]; exact lt_usize _ (by norm_num))]
  exact hread64

-- LIBRARY CANDIDATE: Reasoning.Memory - `MLOAD 0x40` over generic solc `Error(string)` memory.
theorem uniswapErrorStringMem3_mload64 (len word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (uniswapErrorStringMem3 len word mem).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((uniswapErrorStringMem3 len word mem).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [uniswapErrorStringMem3_size len word hmem]; decide)
    (by decide) (uniswapErrorStringMem3_read64 len word hmem hread64)

def uniswapSafeMathSubUnderflowStringWord : UInt256 :=
  UInt256.shiftLeft
    (⟨146807710733670254765134916515197633279875231805303⟩ : UInt256) ⟨88⟩

def uniswapSafeMathAddOverflowStringWord : UInt256 :=
  UInt256.shiftLeft
    (⟨573467620053399432670716995166075968196518375287⟩ : UInt256) ⟨96⟩

-- GENERALIZES Examples.ERC20.Transfer.erc20RoutineCheckedSub_underflow - same checked-sub
-- underflow branch, but for Uniswap's optimizer-on DS-Math string-revert routine.
-- LIBRARY CANDIDATE: Reasoning.Reach - generic solc SafeMath/DS-Math checked-sub underflow
-- terminal branch, parameterized by bytecode, entry pc, success pc, and error-string payload.
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
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost
      (mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64)
      (by decide) (by evm_ov)]
  have rd6899 := rd6895.pushConst (⟨4594637⟩ : UInt256) (width := 3) (op := .PUSH3)
    (by decide) (by decide) (by evm_ov)
  have rd6918 := evm_run rd6899 with [
    push1 ⟨229⟩, shl, dup2,
    raw mstore 6 (UniswapV2Pair.uniswapErrorStringMem0 mem) (UInt256.ofNat 5)
      (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, push1 ⟨4⟩, dup3, add,
    raw mstore 3 (UniswapV2Pair.uniswapErrorStringMem1 mem) (UInt256.ofNat 6)
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
      (UniswapV2Pair.uniswapErrorStringMem3_mload64 (⟨21⟩ : UInt256)
        UniswapV2Pair.uniswapSafeMathSubUnderflowStringWord hmem hread64)
      (by decide) (by evm_ov),
    swap1, dup2, swap1, sub, push1 ⟨100⟩, add, swap1,
    raw rev 0 (by decide) mem_cost (by evm_ov)]

-- GENERALIZES Examples.ERC20.Transfer.erc20RoutineCheckedAdd_overflow - same checked-add
-- overflow branch, but for Uniswap's optimizer-on DS-Math string-revert routine.
-- LIBRARY CANDIDATE: Reasoning.Reach - generic solc SafeMath/DS-Math checked-add overflow
-- terminal branch, parameterized by bytecode, entry pc, success pc, and error-string payload.
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
  have hsum_lt2 : a.toNat + b.toNat < 2 * UInt256.size := by
    have ha : a.toNat < UInt256.size := a.val.isLt
    have hb : b.toNat < UInt256.size := b.val.isLt
    omega
  have hmod : (a.toNat + b.toNat) % UInt256.size =
      a.toNat + b.toNat - UInt256.size := by
    rw [Nat.mod_eq_sub_mod hover]
    exact Nat.mod_eq_of_lt (by omega)
  have haddNat : (a + b).toNat = a.toNat + b.toNat - UInt256.size := by
    rw [uadd_toNat, hmod]
  have hlt : UInt256.lt (a + b) a = ⟨1⟩ := by
    apply ult_one
    rw [haddNat]
    have hb : b.toNat < UInt256.size := b.val.isLt
    omega
  have rd8521 := evm_run h with [jumpdest, dup1, dup3, add, dup3, dup2]
  have rd8522₀ := evm_run rd8521 with [lt]
  have rd8522 := rd8522₀
  rw [hlt] at rd8522
  have rd8523₀ := evm_run rd8522 with [iszero]
  have rd8523 := rd8523₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd8523
  have rd8526 := evm_run rd8523 with [
    push2 ⟨2911⟩, jumpiNT (by decide)]
  have rd8530 := evm_run rd8526 with [
    push1 ⟨64⟩, dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost
      (mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64)
      (by decide) (by evm_ov)]
  have rd8534 := rd8530.pushConst (⟨4594637⟩ : UInt256) (width := 3) (op := .PUSH3)
    (by decide) (by decide) (by evm_ov)
  have rd8553 := evm_run rd8534 with [
    push1 ⟨229⟩, shl, dup2,
    raw mstore 6 (UniswapV2Pair.uniswapErrorStringMem0 mem) (UInt256.ofNat 5)
      (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, push1 ⟨4⟩, dup3, add,
    raw mstore 3 (UniswapV2Pair.uniswapErrorStringMem1 mem) (UInt256.ofNat 6)
      (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    push1 ⟨20⟩, push1 ⟨36⟩, dup3, add,
    raw mstore 3
      (UniswapV2Pair.uniswapErrorStringMem2 (⟨20⟩ : UInt256) mem)
      (UInt256.ofNat 7) (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov)]
  have rd8574 := rd8553.pushConst
    (⟨573467620053399432670716995166075968196518375287⟩ : UInt256)
    (width := 20) (op := .PUSH20) (by decide) (by decide) (by evm_ov)
  exact evm_run rd8574 with [
    push1 ⟨96⟩, shl, push1 ⟨68⟩, dup3, add,
    raw mstore 3
      (UniswapV2Pair.uniswapErrorStringMem3 (⟨20⟩ : UInt256)
        UniswapV2Pair.uniswapSafeMathAddOverflowStringWord mem)
      (UInt256.ofNat 8) (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    swap1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by decide)
      mem_cost
      (UniswapV2Pair.uniswapErrorStringMem3_mload64 (⟨20⟩ : UInt256)
        UniswapV2Pair.uniswapSafeMathAddOverflowStringWord hmem hread64)
      (by decide) (by evm_ov),
    swap1, dup2, swap1, sub, push1 ⟨100⟩, add, swap1,
    raw rev 0 (by decide) mem_cost (by evm_ov)]

/-! # Shared `_transfer` suffix helpers

This file continues the shared `_transfer` routine lemmas once `Routines.lean` is close to the
2k-line iteration limit.
-/

-- GENERALIZES Examples.UniswapV2Pair.Routines.uniswapTransferCreditHashMem —
-- parameterizes the initial 96-byte scratch memory.
-- LIBRARY CANDIDATE: Reasoning.Memory — second recipient-slot hash rewrite over an arbitrary
-- transfer scratch buffer.
noncomputable abbrev uniswapTransferCreditHashMemOf
    (src toWord : UInt256) (mem : ByteArray) : ByteArray :=
  twoWordHashMem toWord ⟨1⟩ (uniswapTransferToHashMemOf src toWord mem)

-- LIBRARY CANDIDATE: Reasoning.Memory — size preservation for the second recipient-slot hash
-- rewrite over an arbitrary transfer scratch buffer.
theorem uniswapTransferCreditHashMemOf_size (src toWord : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (uniswapTransferCreditHashMemOf src toWord mem).size = 96 := by
  unfold uniswapTransferCreditHashMemOf
  exact twoWordHashMem_size_96 toWord ⟨1⟩ (uniswapTransferToHashMemOf_size src toWord hmem)

-- LIBRARY CANDIDATE: Reasoning.Memory — slot computation for the second recipient-slot hash
-- rewrite over an arbitrary transfer scratch buffer.
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

-- GENERALIZES Examples.UniswapV2Pair.Routines.RD.uniswapTransferInternalStoreCredit —
-- parameterizes the initial 96-byte scratch memory.
-- LIBRARY CANDIDATE: Reasoning.Reach — optimizer-on solc single-mapping store suffix that
-- rewrites an address-keyed mapping slot in scratch memory and performs `SSTORE`, preserving the
-- stack tail needed by an event-log suffix.
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
  have hmask : UInt256.land toWord solcAddrMask = toWord :=
    solcAddrMask_clean hcanonTo
  have hmaskLiteral :
      UInt256.land toWord (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        toWord := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact hmask
  have rd7616 := evm_run h with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup1, dup5, and]
  rw [hmaskLiteral] at rd7616
  have rd7620 := evm_run rd7616 with [push1 ⟨0⟩, dup2, dup2]
  have rd7621 := rd7620.mstore 0
    (wordAt0Mem toWord (uniswapTransferToHashMemOf src toWord mem))
    (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd7627 := evm_run rd7621 with [push1 ⟨1⟩, push1 ⟨32⟩, swap1, dup2]
  have rd7628 := rd7627.mstore 0 (uniswapTransferCreditHashMemOf src toWord mem)
    (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd7633 := evm_run rd7628 with [push1 ⟨64⟩, swap2, dup3, swap1]
  have rd7634 := rd7633.keccak256 0 (mapSlot toWord ⟨1⟩) (UInt256.ofNat 3)
    (by decide) mem_cost (uniswapTransferCreditHashMemOf_slot src toWord hmem)
    (by native_decide) (by evm_ov)
  have rd7637 := evm_run rd7634 with [swap5, swap1, swap5]
  obtain ⟨_, _, rd7638⟩ := rd7637.sstore hperm (by decide)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, by simpa [uniswapTransferCreditHashMemOf] using rd7638⟩

-- LIBRARY CANDIDATE: Reasoning.Memory — free-pointer preservation across the double sender-slot
-- hash rewrite over an arbitrary 96-byte scratch buffer.
theorem uniswapTransferDebitHashMemOf_read64 (src : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (uniswapTransferDebitHashMemOf src mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold uniswapTransferDebitHashMemOf
  exact twoWordHashMem_read64 src ⟨1⟩ (twoWordHashMem_size_96 src ⟨1⟩ hmem)
    (twoWordHashMem_read64 src ⟨1⟩ hmem hmem64)

-- LIBRARY CANDIDATE: Reasoning.Memory — free-pointer preservation across the recipient-key
-- overwrite over an arbitrary transfer scratch buffer.
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

-- LIBRARY CANDIDATE: Reasoning.Memory — free-pointer preservation across the second
-- recipient-slot hash rewrite over an arbitrary transfer scratch buffer.
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

-- GENERALIZES Examples.UniswapV2Pair.Routines.uniswapTransferLogMem —
-- parameterizes the initial 96-byte scratch memory.
-- LIBRARY CANDIDATE: Reasoning.Memory — event data word write over a generalized transfer scratch
-- buffer.
noncomputable def uniswapTransferLogMemOf
    (src toWord value : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray value).write 0 (uniswapTransferCreditHashMemOf src toWord mem) 128 32

-- LIBRARY CANDIDATE: Reasoning.Memory — size of the event data word write over a generalized
-- transfer scratch buffer.
theorem uniswapTransferLogMemOf_size (src toWord value : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (uniswapTransferLogMemOf src toWord value mem).size = 160 := by
  unfold uniswapTransferLogMemOf
  rw [toByteArray_write_eq _ _ _ (by rw [uniswapTransferCreditHashMemOf_size src toWord hmem]; omega)
      (by rw [uniswapTransferCreditHashMemOf_size src toWord hmem]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, uniswapTransferCreditHashMemOf_size src toWord hmem,
    ByteArray_zeroes_size,
    show (USize.ofNat (128 - 96)).toNat = 32 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
    toByteArray_size]

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
        show (USize.ofNat (128 - 96)).toNat = 32 from by
          exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
        toByteArray_size]
      norm_num)]
  rw [extract_append_left _ _ _ _ (by
      rw [ByteArray.size_append, uniswapTransferCreditHashMemOf_size src toWord hmem,
        ByteArray_zeroes_size,
        show (USize.ofNat (128 - 96)).toNat = 32 from by
          exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
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

-- GENERALIZES Examples.UniswapV2Pair.Routines.uniswapTransferReturnMem —
-- parameterizes the initial 96-byte scratch memory.
-- LIBRARY CANDIDATE: Reasoning.Memory — boolean return word write over a generalized transfer
-- event scratch buffer.
noncomputable def uniswapTransferReturnMemOf
    (src toWord logValue retValue : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray retValue).write 0
    (uniswapTransferLogMemOf src toWord logValue mem) 128 32

-- LIBRARY CANDIDATE: Reasoning.Memory — size of the boolean return word write over a generalized
-- transfer event scratch buffer.
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

-- LIBRARY CANDIDATE: Reasoning.Memory — free-pointer preservation for the generalized transfer
-- return buffer.
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

-- GENERALIZES Examples.UniswapV2Pair.Routines.RD.uniswapTransferInternalEmitAndJump —
-- parameterizes the initial 96-byte scratch memory.
-- LIBRARY CANDIDATE: Reasoning.Reach — optimizer-on ERC20-style `Transfer` event suffix for a
-- shared internal transfer routine, parameterized by source/recipient/value, dynamic return pc,
-- and initial scratch memory.
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
  have hmask : UInt256.land src solcAddrMask = src :=
    solcAddrMask_clean hcanonSrc
  have rd7640 := evm_run h with [
    dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost
      (uniswapTransferCreditHashMemOf_mload64 src toWord hmem hmem64)
      (by decide) (by evm_ov)]
  have rd7642 := evm_run rd7640 with [dup6, dup2]
  have rd7643 := rd7642.mstore 6 (uniswapTransferLogMemOf src toWord value mem)
    (UInt256.ofNat 5) (by decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd7645 := evm_run rd7643 with [
    swap1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost
      (uniswapTransferLogMemOf_mload64 src toWord value hmem hmem64)
      (by decide) (by evm_ov),
    swap2, swap4, swap3, dup8, and]
  rw [hmask] at rd7645
  have rd7651 := evm_run rd7645 with [swap3]
  have rd7684₀ := rd7651.pushConst uniswapTransferTopic (width := 32) (op := .PUSH32)
    (by decide) (by decide) (by evm_ov)
  have rd7691 := evm_run rd7684₀ with [swap3, swap2, dup3, swap1, sub, add, swap1]
  have rd7692 := rd7691.log3 0 (UInt256.ofNat 5) (by decide) hperm mem_cost
    (by decide) (by simp only [List.length_cons]; omega)
  have rd7695 := evm_run rd7692 with [pop, pop, pop]
  exact ⟨_, _, rd7695.jump (by decide) hret (by evm_ov)⟩

-- GENERALIZES Examples.UniswapV2Pair.Routines.RD.uniswapInternalTransferReturnTrue —
-- handles the transferFrom continuation that discards four preserved routine arguments.
-- LIBRARY CANDIDATE: Reasoning.Reach — small solc continuation that discards preserved internal
-- call arguments, pushes boolean true, and jumps to a dynamic return wrapper.
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
  exact ⟨_, _, evm_run h with [
    jumpdest, pop, push1 ⟨1⟩, swap4, swap3, pop, pop, pop, jump hret]⟩

-- GENERALIZES Examples.UniswapV2Pair.Routines.uniswapApproveHashMem —
-- rebuilds the same nested allowance-mapping scratch buffer over an arbitrary 96-byte base.
-- LIBRARY CANDIDATE: Reasoning.Memory — nested mapping-slot scratch rewrite over a previous
-- 96-byte scratch buffer.
noncomputable abbrev uniswapTransferFromAllowanceStoreMemOf
    (src spender : UInt256) (mem : ByteArray) : ByteArray :=
  twoWordHashMem spender (mapSlot src ⟨2⟩) (twoWordHashMem src ⟨2⟩ mem)

noncomputable abbrev uniswapTransferFromAllowanceStoreMem (src spender : UInt256) : ByteArray :=
  uniswapTransferFromAllowanceStoreMemOf src spender (uniswapApproveHashMem src spender)

-- LIBRARY CANDIDATE: Reasoning.Memory — size preservation for rebuilding a nested mapping-slot
-- scratch buffer over a previous 96-byte scratch buffer.
theorem uniswapTransferFromAllowanceStoreMemOf_size
    (src spender : UInt256) {mem : ByteArray} (hmem : mem.size = 96) :
    (uniswapTransferFromAllowanceStoreMemOf src spender mem).size = 96 := by
  unfold uniswapTransferFromAllowanceStoreMemOf
  exact twoWordHashMem_size_96 spender (mapSlot src ⟨2⟩)
    (twoWordHashMem_size_96 src ⟨2⟩ hmem)

theorem uniswapTransferFromAllowanceStoreMem_size (src spender : UInt256) :
    (uniswapTransferFromAllowanceStoreMem src spender).size = 96 :=
  uniswapTransferFromAllowanceStoreMemOf_size src spender (uniswapApproveHashMem_size src spender)

-- LIBRARY CANDIDATE: Reasoning.Memory — free-pointer preservation after rebuilding a nested
-- allowance-mapping scratch buffer over a previous 96-byte scratch buffer.
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

-- LIBRARY CANDIDATE: Reasoning.Memory — nested allowance-mapping scratch buffer computes the
-- canonical Solidity mapping slot.
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

-- LIBRARY CANDIDATE: Reasoning.Reach — optimizer-on solc finite-allowance `transferFrom`
-- continuation that stores `allowance[from][caller] = allowance - value` before falling through
-- to the shared internal `_transfer` call setup.
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
  have hmask : UInt256.land src solcAddrMask = src :=
    solcAddrMask_clean hcanonSrc
  have hmaskLiteral :
      UInt256.land src (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        src := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact hmask
  have hinner :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem src ⟨2⟩ mem).readWithPadding 0 64))) =
        mapSlot src ⟨2⟩ := by
    rw [twoWordHashMem_read0_64 src ⟨2⟩ hmem]
    unfold mapSlot
    exact mappingSlot_single src ⟨2⟩
  have houter :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((uniswapTransferFromAllowanceStoreMemOf src
            (uniswapSourceWord ee) mem).readWithPadding 0 64))) =
        mapSlot (uniswapSourceWord ee) (mapSlot src ⟨2⟩) :=
    uniswapTransferFromAllowanceStoreMemOf_slot src (uniswapSourceWord ee) hmem
  have rd3044 := evm_run h with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup6, and]
  rw [hmaskLiteral] at rd3044
  have rd3048 := evm_run rd3044 with [push1 ⟨0⟩, swap1, dup2]
  have rd3049 := rd3048.mstore 0 (wordAt0Mem src mem)
    (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd3055 := evm_run rd3049 with [push1 ⟨2⟩, push1 ⟨32⟩, swap1, dup2]
  have rd3056 := rd3055.mstore 0 (twoWordHashMem src ⟨2⟩ mem)
    (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd3060 := evm_run rd3056 with [push1 ⟨64⟩, dup1, dup4]
  have rd3061 := rd3060.keccak256 0 (mapSlot src ⟨2⟩) (UInt256.ofNat 3)
    (by decide) mem_cost hinner (by native_decide) (by evm_ov)
  have rd3063 := evm_run rd3061 with [caller, dup5]
  have rd3064 := rd3063.mstore 0
    (wordAt0Mem (uniswapSourceWord ee) (twoWordHashMem src ⟨2⟩ mem))
    (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd3066 := evm_run rd3064 with [swap1, swap2]
  have rd3067 := rd3066.mstore 0
    (uniswapTransferFromAllowanceStoreMemOf src (uniswapSourceWord ee) mem)
    (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd3068 := evm_run rd3067 with [swap1]
  have rd3069 := rd3068.keccak256 0
    (mapSlot (uniswapSourceWord ee) (mapSlot src ⟨2⟩)) (UInt256.ofNat 3)
    (by decide) mem_cost houter (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3071⟩ := rd3069.sstore hperm (by decide)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, by simpa using rd3071⟩

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

-- GENERALIZES Examples.UniswapV2Pair.Routines.RD.uniswapTransferFromAllowanceMaxBranch —
-- shares the nested allowance-slot load, then stops at the checked-sub routine entry so both
-- success and underflow branches can reuse the same trace.
-- LIBRARY CANDIDATE: Reasoning.Reach — optimizer-on solc `transferFrom` finite-allowance branch
-- prefix that reloads a nested mapping slot and jumps to a checked-sub routine.
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
  let allowanceSlot := mapSlot (uniswapSourceWord ee) (mapSlot src ⟨2⟩)
  let allowanceWord := uniswapCodeOwnerStorageWord ee σ allowanceSlot
  have hmask : UInt256.land src solcAddrMask = src :=
    solcAddrMask_clean hcanonSrc
  have hmaskLiteral :
      UInt256.land src (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        src := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact hmask
  have hinner :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem src ⟨2⟩ solcFreePtrMem).readWithPadding 0 64))) =
        mapSlot src ⟨2⟩ := by
    rw [twoWordHashMem_read0_64 src ⟨2⟩ solcFreePtrMem_size]
    unfold mapSlot
    exact mappingSlot_single src ⟨2⟩
  have houter :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((uniswapApproveHashMem src (uniswapSourceWord ee)).readWithPadding 0 64))) =
        allowanceSlot := by
    unfold allowanceSlot uniswapApproveHashMem
    rw [twoWordHashMem_read0_64 (uniswapSourceWord ee) (mapSlot src ⟨2⟩)
      (twoWordHashMem_size_96 src ⟨2⟩ solcFreePtrMem_size)]
    unfold mapSlot
    exact mappingSlot_single (uniswapSourceWord ee) (mapSlot src ⟨2⟩)
  have hinner2 :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem src ⟨2⟩
            (uniswapApproveHashMem src (uniswapSourceWord ee))).readWithPadding 0 64))) =
        mapSlot src ⟨2⟩ := by
    rw [twoWordHashMem_read0_64 src ⟨2⟩
      (uniswapApproveHashMem_size src (uniswapSourceWord ee))]
    unfold mapSlot
    exact mappingSlot_single src ⟨2⟩
  have houter2 :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((uniswapTransferFromAllowanceStoreMem src
            (uniswapSourceWord ee)).readWithPadding 0 64))) =
        allowanceSlot := by
    simpa [allowanceSlot] using
      uniswapTransferFromAllowanceStoreMem_slot src (uniswapSourceWord ee)
  have hlnot0 : (UInt256.lnot (⟨0⟩ : UInt256)).toNat = UInt256.size - 1 := by
    unfold UInt256.lnot
    decide
  have hnotMax' : allowanceWord.toNat ≠ UInt256.size - 1 := by
    simpa [allowanceWord, allowanceSlot] using hnotMax
  have hneq : UInt256.lnot (⟨0⟩ : UInt256) ≠ allowanceWord := by
    intro hword
    apply hnotMax'
    rw [← hword, hlnot0]
  have heq : UInt256.eq (UInt256.lnot (⟨0⟩ : UInt256)) allowanceWord = ⟨0⟩ :=
    u256_eq_of_ne hneq
  have rd2949 := evm_run h with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup4, and]
  rw [hmaskLiteral] at rd2949
  have rd2953 := evm_run rd2949 with [push1 ⟨0⟩, swap1, dup2]
  have rd2954 := rd2953.mstore 0 (wordAt0Mem src solcFreePtrMem)
    (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd2961 := evm_run rd2954 with [push1 ⟨2⟩, push1 ⟨32⟩, swap1, dup2]
  have rd2962 := rd2961.mstore 0 (twoWordHashMem src ⟨2⟩ solcFreePtrMem)
    (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd2966 := evm_run rd2962 with [push1 ⟨64⟩, dup1, dup4]
  have rd2967 := rd2966.keccak256 0 (mapSlot src ⟨2⟩) (UInt256.ofNat 3)
    (by decide) mem_cost hinner (by native_decide) (by evm_ov)
  have rd2969 := evm_run rd2967 with [caller, dup5]
  have rd2970 := rd2969.mstore 0
    (wordAt0Mem (uniswapSourceWord ee) (twoWordHashMem src ⟨2⟩ solcFreePtrMem))
    (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd2972 := evm_run rd2970 with [swap1, swap2]
  have rd2973 := rd2972.mstore 0 (uniswapApproveHashMem src (uniswapSourceWord ee))
    (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd2974 := evm_run rd2973 with [dup2]
  have rd2975₀ := rd2974.keccak256 0 allowanceSlot (UInt256.ofNat 3)
    (by decide) mem_cost houter (by native_decide) (by evm_ov)
  obtain ⟨k2975, C2975, rd2975₁⟩ := rd2975₀.sload (by decide)
    (by simp only [List.length_cons]; omega)
  have rd2975 : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨2975⟩
      (allowanceWord :: ⟨0⟩ :: value :: toWord :: src :: ret :: R)
      (uniswapApproveHashMem src (uniswapSourceWord ee))
      (UInt256.ofNat 3) rdata (cA, σ) k2975 C2975 := by
    simpa [allowanceWord, allowanceSlot, uniswapCodeOwnerStorageWord] using rd2975₁
  have rd2979 := evm_run rd2975 with [push1 ⟨0⟩, not, eq]
  rw [heq] at rd2979
  have rd2983 := evm_run rd2979 with [push2 ⟨3071⟩, jumpiNT (by decide)]
  have rd2993 := evm_run rd2983 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup5, and]
  rw [hmaskLiteral] at rd2993
  have rd2997 := evm_run rd2993 with [push1 ⟨0⟩, swap1, dup2]
  have rd2998 := rd2997.mstore 0
    (wordAt0Mem src (uniswapApproveHashMem src (uniswapSourceWord ee)))
    (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd3005 := evm_run rd2998 with [push1 ⟨2⟩, push1 ⟨32⟩, swap1, dup2]
  have rd3006 := rd3005.mstore 0
    (twoWordHashMem src ⟨2⟩ (uniswapApproveHashMem src (uniswapSourceWord ee)))
    (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd3010 := evm_run rd3006 with [push1 ⟨64⟩, dup1, dup4]
  have rd3011 := rd3010.keccak256 0 (mapSlot src ⟨2⟩) (UInt256.ofNat 3)
    (by decide) mem_cost hinner2 (by native_decide) (by evm_ov)
  have rd3013 := evm_run rd3011 with [caller, dup5]
  have rd3014 := rd3013.mstore 0
    (wordAt0Mem (uniswapSourceWord ee)
      (twoWordHashMem src ⟨2⟩ (uniswapApproveHashMem src (uniswapSourceWord ee))))
    (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd3016 := evm_run rd3014 with [swap1, swap2]
  have rd3017 := rd3016.mstore 0
    (uniswapTransferFromAllowanceStoreMem src (uniswapSourceWord ee))
    (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd3018 := evm_run rd3017 with [swap1]
  have rd3019₀ := rd3018.keccak256 0 allowanceSlot (UInt256.ofNat 3)
    (by decide) mem_cost houter2 (by native_decide) (by evm_ov)
  obtain ⟨k3019, C3019, rd3019₁⟩ := rd3019₀.sload (by decide)
    (by simp only [List.length_cons]; omega)
  have rd3019 : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨3019⟩
      (allowanceWord :: ⟨0⟩ :: value :: toWord :: src :: ret :: R)
      (uniswapTransferFromAllowanceStoreMem src (uniswapSourceWord ee))
      (UInt256.ofNat 3) rdata (cA, σ) k3019 C3019 := by
    simpa [allowanceWord, allowanceSlot, uniswapCodeOwnerStorageWord] using rd3019₁
  have rd3034ret := evm_run rd3019 with [
    push2 ⟨3034⟩, swap1, dup4, push4 ⟨0xffffffff⟩, push2 ⟨6879⟩, and]
  have rd6879 := rd3034ret.jump (by decide) (by jump_dest) (by evm_ov)
  rw [show UInt256.land (⟨6879⟩ : UInt256) ⟨0xffffffff⟩ = ⟨6879⟩ from by decide]
    at rd6879
  exact ⟨_, _, by simpa [allowanceWord, allowanceSlot] using rd6879⟩

-- GENERALIZES Examples.UniswapV2Pair.Routines.RD.uniswapTransferFromAllowanceMaxBranch —
-- shares the nested allowance-slot load, then follows the finite-allowance branch through the
-- checked-sub routine return.
-- LIBRARY CANDIDATE: Reasoning.Reach — optimizer-on solc `transferFrom` finite-allowance branch
-- that reloads a nested mapping slot and jumps through a checked-sub routine.
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

-- GENERALIZES Examples.UniswapV2Pair.TransferRoutines.RD.uniswapTransferFromAllowanceFiniteBranch —
-- shares the nested allowance-slot reload and checked-sub routine entry, then follows underflow.
-- LIBRARY CANDIDATE: Reasoning.Reach — optimizer-on solc `transferFrom` finite-allowance failure
-- branch that reloads a nested mapping slot and reverts through checked-sub underflow.
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
