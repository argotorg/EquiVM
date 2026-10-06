import Solidity.Examples.ERC20.Common

/-!
# ERC20 — code shapes of the optimized bytecode shared by its functions

The pieces of `erc20Runtime` that several function bodies run through: the one-word return tail
(`0x95`, the encoder, then the return block at `0x83`).
-/

open _root_.Solidity Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Trace

set_option maxRecDepth 2000000

namespace ERC20.Opt

/-- A memory of at least 96 bytes holding the free pointer `0x80` at `0x40`, with a word written at
    `0x80`: the free pointer still reads `0x80`, and the word reads back. -/
theorem freePtr_after_write128 {mem : ByteArray} (val : UInt256) (hmem : 96 ≤ mem.size)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) (hgap : 128 - mem.size < USize.size) :
    64 < ((UInt256.toByteArray val).write 0 mem 128 32).size
    ∧ ((UInt256.toByteArray val).write 0 mem 128 32).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩
    ∧ ((UInt256.toByteArray val).write 0 mem 128 32).readWithPadding 128 32 = UInt256.toByteArray val := by
  refine ⟨?_, ?_, ?_⟩
  · have := toByteArray_write_size_ge_off_add32 val mem 128 hgap
    omega
  · rw [toByteArray_write_read_below_of_gap val mem 128 64 hmem (by decide) hgap]
    exact hread
  · exact toByteArray_write_read_back_of_gap val mem 128 hgap

theorem solcFreePtrMem_gap : 128 - solcFreePtrMem.size < USize.size := by
  rw [solcFreePtrMem_size]; exact lt_usize _ (by norm_num)

/-- The one-word return tail at `0x95` (`JUMPDEST; PUSH1 0x40; MLOAD; SWAP1; DUP2; MSTORE; PUSH1 0x20;
    ADD; PUSH2 0x83; JUMP` into the return block): the word on top of the stack is returned.  The
    memory holds the free pointer `0x80` at `0x40` (scratch words below it are allowed). -/
theorem retWord {s0 : State} {val ret : UInt256} {R : List UInt256} {mem rdata : ByteArray} {w : World} {k C : ℕ}
    (h : Run erc20Runtime s0 ⟨⟨0x95⟩, val :: ret :: R, mem, UInt256.ofNat 3, rdata, w⟩ k C)
    (hmem : 96 ≤ mem.size) (hread : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hgap : 128 - mem.size < USize.size) (hov : R.length + 4 ≤ 1024) :
    Returned erc20Runtime s0 w (UInt256.toByteArray val) := by
  obtain ⟨_, _, h1⟩ := Run.solcEncodeWordRoutine h
    (by dsimp only [solcEncodeWordRoutineWf]; repeat' first | apply And.intro | decide)
    (mloadFreePtrValue (by omega) (by decide) hread) hov
  have h2 := evm_run h1 with [push2 ⟨0x83⟩, jump (by jump_dest)]
  obtain ⟨hsz, hread', hback⟩ := freePtr_after_write128 val hmem hread hgap
  have hret := Run.solcReturnBlock h2 (by dsimp only [solcReturnBlockWf]; repeat' first | apply And.intro | decide)
    (mloadFreePtrValue hsz (by decide) hread') (by evm_ov)
  rw [show (UInt256.sub (⟨32⟩ + ⟨128⟩) ⟨128⟩).toNat = 32 from by decide, hback] at hret
  exact hret

/-! ## The calldata length checks of the decoders

`calldatasize - 4` compared with the static size of the arguments by `SLT`: a size below the
need and a size of `2^255 + 4` or more (a negative difference) both fail. -/

theorem sub4_eq {n : ℕ} (h4 : 4 ≤ n) (hn : n < UInt256.size) :
    UInt256.sub (UInt256.ofNat n) ⟨4⟩ = UInt256.ofNat (n - 4) := by
  apply u256_inj
  rw [usub_ofNat_word_toNat (by rw [show (⟨4⟩ : UInt256).toNat = 4 from rfl]; exact h4) hn,
    ulit_toNat' _ (by omega)]
  rfl

theorem lenCheck_ok {n need : ℕ} (hneed : need < 2 ^ 255) (hok : need + 4 ≤ n) (hbig : n < 2 ^ 255 + 4) :
    UInt256.slt (UInt256.sub (UInt256.ofNat n) ⟨4⟩) (UInt256.ofNat need) = ⟨0⟩ := by
  rw [sub4_eq (by omega) (by rw [UInt256.size]; omega)]
  exact slt_ofNat_lit_zero hneed (by omega) (by omega)

theorem lenCheck_short {n need : ℕ} (hneed : need < 2 ^ 255) (h4 : 4 ≤ n) (hshort : n < need + 4) :
    UInt256.slt (UInt256.sub (UInt256.ofNat n) ⟨4⟩) (UInt256.ofNat need) = ⟨1⟩ := by
  rw [sub4_eq h4 (by rw [UInt256.size]; omega)]
  exact slt_ofNat_lit_one_low hneed (by omega)

theorem lenCheck_huge {n need : ℕ} (hneed : need < 2 ^ 255) (hhuge : 2 ^ 255 + 4 ≤ n) (hn : n < UInt256.size) :
    UInt256.slt (UInt256.sub (UInt256.ofNat n) ⟨4⟩) (UInt256.ofNat need) = ⟨1⟩ := by
  rw [sub4_eq (by omega) hn]
  exact slt_lit_one_high hneed (by rw [ulit_toNat' _ (by omega)]; omega)

/-! ## The argument decoders

Each decoder is entered with `4 :: calldatasize :: ret :: …` on the stack, checks the length
(`PUSH0 …; PUSH1 need; DUP; DUP; SUB; SLT; ISZERO; PUSH2 ok; JUMPI; PUSH0; PUSH0; REVERT`), reads
each address through the validator at `0x41c` (a word that is not canonical reverts with empty
data), and jumps to `ret` with the arguments on the stack. -/

/-- `abi_decode_tuple_address` at `0x499`: one canonical address. -/
theorem decAddrOk {s0 : State} {ret : UInt256} {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256} {w : World}
    {k C : ℕ}
    (h : Run erc20Runtime s0 ⟨⟨0x499⟩, ⟨4⟩ :: UInt256.ofNat s0.executionEnv.calldata.size :: ret :: R, mem, aw, rdata, w⟩ k C)
    (hsz : 36 ≤ s0.executionEnv.calldata.size) (hbig : s0.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hcanon : (calldataWord s0.executionEnv.calldata 4).toNat < EVM.addressModulus)
    (hret : (D_J erc20Runtime 0).contains ret = true) (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', Run erc20Runtime s0 ⟨ret, calldataWord s0.executionEnv.calldata 4 :: R, mem, aw, rdata, w⟩ k' C' := by
  have h1 := evm_run h with [jumpdest, push0, push1 ⟨0x20⟩, dup3, dup5, sub, slt]
  rw [show (⟨0x20⟩ : UInt256) = UInt256.ofNat 32 from rfl, lenCheck_ok (by norm_num) (by omega) hbig] at h1
  have h2 := evm_run h1 with [iszero]
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at h2
  have h3 := evm_run h2 with [push2 ⟨0x4a9⟩, jumpiT (by decide) (by jump_dest), jumpdest, push2 ⟨0x4b2⟩, dup3,
    push2 ⟨0x41c⟩, jump (by jump_dest)]
  obtain ⟨_, _, h4⟩ := Run.solcInlinedDecodeAddrOk h3 (by exact hcanon) (by jump_dest) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by jump_dest) (by decide) (by decide) (by decide) (by decide)
    (by evm_ov)
  exact ⟨_, _, evm_run h4 with [jumpdest, swap4, swap3, pop, pop, pop, jump hret]⟩

/-- The decoder at `0x499` with a calldata too short for its argument, or of `2^255 + 4` bytes or
    more: empty revert. -/
theorem decAddrLenRevert {s0 : State} {ret : UInt256} {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {w : World} {k C : ℕ}
    (h : Run erc20Runtime s0 ⟨⟨0x499⟩, ⟨4⟩ :: UInt256.ofNat s0.executionEnv.calldata.size :: ret :: R, mem, aw, rdata, w⟩ k C)
    (hslt : UInt256.slt (UInt256.sub (UInt256.ofNat s0.executionEnv.calldata.size) ⟨4⟩) (UInt256.ofNat 32) = ⟨1⟩)
    (hov : R.length + 8 ≤ 1024) :
    Reverted erc20Runtime s0 ByteArray.empty := by
  have h1 := evm_run h with [jumpdest, push0, push1 ⟨0x20⟩, dup3, dup5, sub, slt]
  rw [show (⟨0x20⟩ : UInt256) = UInt256.ofNat 32 from rfl, hslt] at h1
  have h2 := evm_run h1 with [iszero]
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at h2
  exact (evm_run h2 with [push2 ⟨0x4a9⟩, jumpiNT rfl]).revertStub (by decide) (by decide) (by decide) (by evm_ov)

/-- The decoder at `0x499` with an address word that is not canonical: empty revert. -/
theorem decAddrDirtyRevert {s0 : State} {ret : UInt256} {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {w : World} {k C : ℕ}
    (h : Run erc20Runtime s0 ⟨⟨0x499⟩, ⟨4⟩ :: UInt256.ofNat s0.executionEnv.calldata.size :: ret :: R, mem, aw, rdata, w⟩ k C)
    (hsz : 36 ≤ s0.executionEnv.calldata.size) (hbig : s0.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (calldataWord s0.executionEnv.calldata 4).toNat < EVM.addressModulus)
    (hov : R.length + 10 ≤ 1024) :
    Reverted erc20Runtime s0 ByteArray.empty := by
  have h1 := evm_run h with [jumpdest, push0, push1 ⟨0x20⟩, dup3, dup5, sub, slt]
  rw [show (⟨0x20⟩ : UInt256) = UInt256.ofNat 32 from rfl, lenCheck_ok (by norm_num) (by omega) hbig] at h1
  have h2 := evm_run h1 with [iszero]
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at h2
  have h3 := evm_run h2 with [push2 ⟨0x4a9⟩, jumpiT (by decide) (by jump_dest), jumpdest, push2 ⟨0x4b2⟩, dup3,
    push2 ⟨0x41c⟩, jump (by jump_dest)]
  exact Run.solcInlinedDecodeAddrRevert h3
    (uInt256_eq_zero_of_ne fun he => hnc (solcAddrCanonical_of_clean he))
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by evm_ov)

/-! ## Scratch-memory mapping hashes

The optimized code writes the slot at `0x20` first, then the key at `0x00`, over a 96-byte memory
holding the free pointer, and hashes `mem[0x00 .. 0x40)`. -/

/-- `mstore(0x20, slot); mstore(0, key)`. -/
noncomputable abbrev hashMem (key slot : UInt256) (mem : ByteArray) : ByteArray := wordAt0Mem key (wordAt32Mem slot mem)

theorem hashMem_size {mem : ByteArray} (key slot : UInt256) (hmem : mem.size = 96) : (hashMem key slot mem).size = 96 :=
  wordAt0Mem_size_96 key (wordAt32Mem_size_96 slot hmem)

theorem wordAt32Mem_read32 {mem : ByteArray} (slot : UInt256) (hmem : mem.size = 96) :
    (wordAt32Mem slot mem).readWithPadding 32 32 = UInt256.toByteArray slot := by
  unfold wordAt32Mem
  rw [write32_read_back _ _ 32 (by rw [toByteArray_size]) (by omega), toByteArray_extract_all]

theorem wordAt32Mem_read64 {mem : ByteArray} (slot : UInt256) (hmem : mem.size = 96) :
    (wordAt32Mem slot mem).readWithPadding 64 32 = mem.readWithPadding 64 32 := by
  unfold wordAt32Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size]) (by omega) (by omega) (by omega)]

theorem hashMem_read0 {mem : ByteArray} (key slot : UInt256) (hmem : mem.size = 96) :
    (hashMem key slot mem).readWithPadding 0 32 = UInt256.toByteArray key := by
  unfold hashMem wordAt0Mem
  rw [write32_read_back _ _ 0 (by rw [toByteArray_size]) (by rw [wordAt32Mem_size_96 slot hmem]; omega),
    toByteArray_extract_all]

theorem hashMem_read32 {mem : ByteArray} (key slot : UInt256) (hmem : mem.size = 96) :
    (hashMem key slot mem).readWithPadding 32 32 = UInt256.toByteArray slot := by
  unfold hashMem wordAt0Mem
  rw [write32_read_above _ _ 0 32 (by rw [toByteArray_size]) (by rw [wordAt32Mem_size_96 slot hmem]; omega) (by omega)
    (by simp [wordAt32Mem_size_96 slot hmem]), wordAt32Mem_read32 slot hmem]

theorem hashMem_read64 {mem : ByteArray} (key slot : UInt256) (hmem : mem.size = 96)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (hashMem key slot mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold hashMem wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size]) (by rw [wordAt32Mem_size_96 slot hmem]; omega) (by omega)
    (by simp [wordAt32Mem_size_96 slot hmem]), wordAt32Mem_read64 slot hmem, hread]

theorem hashMem_read0_64 {mem : ByteArray} (key slot : UInt256) (hmem : mem.size = 96) :
    (hashMem key slot mem).readWithPadding 0 64 = UInt256.toByteArray key ++ UInt256.toByteArray slot := by
  have hsz := hashMem_size key slot hmem
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num) (by rw [hsz]; omega)]
  have hleft : (hashMem key slot mem).extract 0 32 = UInt256.toByteArray key := by
    rw [← readWithPadding_eq_extract _ 0 (by rw [hsz]; omega), hashMem_read0 key slot hmem]
  have hright : (hashMem key slot mem).extract 32 64 = UInt256.toByteArray slot := by
    rw [← readWithPadding_eq_extract _ 32 (by rw [hsz]; omega), hashMem_read32 key slot hmem]
  rw [show (hashMem key slot mem).extract 0 64 =
      (hashMem key slot mem).extract 0 32 ++ (hashMem key slot mem).extract 32 64 by
    rw [ByteArray.extract_append_extract]; norm_num]
  rw [hleft, hright]

/-- `KECCAK256 0 0x40` over it: the mapping slot `keccak256(key ++ slot)`. -/
theorem hashMem_keccak {mem : ByteArray} (key slot : UInt256) (hmem : mem.size = 96) :
    UInt256.ofNat (fromByteArrayBigEndian (ffi.KEC ((hashMem key slot mem).readWithPadding 0 64))) =
      solcMappingSlot slot key := by
  rw [hashMem_read0_64 key slot hmem]
  exact mappingSlot_single key slot

/-- The address validator at `0x41c` on a canonical word (`off :: ret :: …` on the stack). -/
macro "inlAddrOk" h:term:max hc:term:max : term =>
  `(Run.solcInlinedDecodeAddrOk $h $hc (by jump_dest) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by jump_dest) (by decide) (by decide) (by decide) (by decide) (by evm_ov))

/-- The address validator at `0x41c` on a word that is not canonical: empty revert. -/
macro "inlAddrRevert" h:term:max hnc:term:max : term =>
  `(Run.solcInlinedDecodeAddrRevert $h (uInt256_eq_zero_of_ne fun he => $hnc (solcAddrCanonical_of_clean he))
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by evm_ov))

/-- `abi_decode_tuple_address_address` at `0x4b9`: two canonical addresses, the second on top. -/
theorem decAddrAddrOk {s0 : State} {ret : UInt256} {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256} {w : World}
    {k C : ℕ}
    (h : Run erc20Runtime s0 ⟨⟨0x4b9⟩, ⟨4⟩ :: UInt256.ofNat s0.executionEnv.calldata.size :: ret :: R, mem, aw, rdata, w⟩ k C)
    (hsz : 68 ≤ s0.executionEnv.calldata.size) (hbig : s0.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hc0 : (calldataWord s0.executionEnv.calldata 4).toNat < EVM.addressModulus)
    (hc1 : (calldataWord s0.executionEnv.calldata 36).toNat < EVM.addressModulus)
    (hret : (D_J erc20Runtime 0).contains ret = true) (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', Run erc20Runtime s0
      ⟨ret, calldataWord s0.executionEnv.calldata 36 :: calldataWord s0.executionEnv.calldata 4 :: R, mem, aw, rdata, w⟩
      k' C' := by
  have h1 := evm_run h with [jumpdest, push0, push0, push1 ⟨0x40⟩, dup4, dup6, sub, slt]
  rw [show (⟨0x40⟩ : UInt256) = UInt256.ofNat 64 from rfl, lenCheck_ok (by norm_num) (by omega) hbig] at h1
  have h2 := evm_run h1 with [iszero]
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at h2
  have h3 := evm_run h2 with [push2 ⟨0x4ca⟩, jumpiT (by decide) (by jump_dest), jumpdest, push2 ⟨0x4d3⟩, dup4,
    push2 ⟨0x41c⟩, jump (by jump_dest)]
  obtain ⟨_, _, h4⟩ := inlAddrOk h3 (by exact hc0)
  have h5 := evm_run h4 with [jumpdest, swap2, pop, push2 ⟨0x4e1⟩, push1 ⟨0x20⟩, dup5, add, push2 ⟨0x41c⟩,
    jump (by jump_dest)]
  rw [show (⟨4⟩ + ⟨0x20⟩ : UInt256) = ⟨36⟩ from by decide] at h5
  obtain ⟨_, _, h6⟩ := inlAddrOk h5 (by exact hc1)
  exact ⟨_, _, evm_run h6 with [jumpdest, swap1, pop, swap3, pop, swap3, swap1, pop, jump hret]⟩

theorem decAddrAddrLenRevert {s0 : State} {ret : UInt256} {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {w : World} {k C : ℕ}
    (h : Run erc20Runtime s0 ⟨⟨0x4b9⟩, ⟨4⟩ :: UInt256.ofNat s0.executionEnv.calldata.size :: ret :: R, mem, aw, rdata, w⟩ k C)
    (hslt : UInt256.slt (UInt256.sub (UInt256.ofNat s0.executionEnv.calldata.size) ⟨4⟩) (UInt256.ofNat 64) = ⟨1⟩)
    (hov : R.length + 12 ≤ 1024) :
    Reverted erc20Runtime s0 ByteArray.empty := by
  have h1 := evm_run h with [jumpdest, push0, push0, push1 ⟨0x40⟩, dup4, dup6, sub, slt]
  rw [show (⟨0x40⟩ : UInt256) = UInt256.ofNat 64 from rfl, hslt] at h1
  have h2 := evm_run h1 with [iszero]
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at h2
  exact (evm_run h2 with [push2 ⟨0x4ca⟩, jumpiNT rfl]).revertStub (by decide) (by decide) (by decide) (by evm_ov)

theorem decAddrAddrDirty0Revert {s0 : State} {ret : UInt256} {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {w : World} {k C : ℕ}
    (h : Run erc20Runtime s0 ⟨⟨0x4b9⟩, ⟨4⟩ :: UInt256.ofNat s0.executionEnv.calldata.size :: ret :: R, mem, aw, rdata, w⟩ k C)
    (hsz : 68 ≤ s0.executionEnv.calldata.size) (hbig : s0.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hnc0 : ¬ (calldataWord s0.executionEnv.calldata 4).toNat < EVM.addressModulus)
    (hov : R.length + 12 ≤ 1024) :
    Reverted erc20Runtime s0 ByteArray.empty := by
  have h1 := evm_run h with [jumpdest, push0, push0, push1 ⟨0x40⟩, dup4, dup6, sub, slt]
  rw [show (⟨0x40⟩ : UInt256) = UInt256.ofNat 64 from rfl, lenCheck_ok (by norm_num) (by omega) hbig] at h1
  have h2 := evm_run h1 with [iszero]
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at h2
  have h3 := evm_run h2 with [push2 ⟨0x4ca⟩, jumpiT (by decide) (by jump_dest), jumpdest, push2 ⟨0x4d3⟩, dup4,
    push2 ⟨0x41c⟩, jump (by jump_dest)]
  exact inlAddrRevert h3 hnc0

theorem decAddrAddrDirty1Revert {s0 : State} {ret : UInt256} {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {w : World} {k C : ℕ}
    (h : Run erc20Runtime s0 ⟨⟨0x4b9⟩, ⟨4⟩ :: UInt256.ofNat s0.executionEnv.calldata.size :: ret :: R, mem, aw, rdata, w⟩ k C)
    (hsz : 68 ≤ s0.executionEnv.calldata.size) (hbig : s0.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hc0 : (calldataWord s0.executionEnv.calldata 4).toNat < EVM.addressModulus)
    (hnc1 : ¬ (calldataWord s0.executionEnv.calldata 36).toNat < EVM.addressModulus)
    (hov : R.length + 12 ≤ 1024) :
    Reverted erc20Runtime s0 ByteArray.empty := by
  have h1 := evm_run h with [jumpdest, push0, push0, push1 ⟨0x40⟩, dup4, dup6, sub, slt]
  rw [show (⟨0x40⟩ : UInt256) = UInt256.ofNat 64 from rfl, lenCheck_ok (by norm_num) (by omega) hbig] at h1
  have h2 := evm_run h1 with [iszero]
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at h2
  have h3 := evm_run h2 with [push2 ⟨0x4ca⟩, jumpiT (by decide) (by jump_dest), jumpdest, push2 ⟨0x4d3⟩, dup4,
    push2 ⟨0x41c⟩, jump (by jump_dest)]
  obtain ⟨_, _, h4⟩ := inlAddrOk h3 (by exact hc0)
  have h5 := evm_run h4 with [jumpdest, swap2, pop, push2 ⟨0x4e1⟩, push1 ⟨0x20⟩, dup5, add, push2 ⟨0x41c⟩,
    jump (by jump_dest)]
  rw [show (⟨4⟩ + ⟨0x20⟩ : UInt256) = ⟨36⟩ from by decide] at h5
  exact inlAddrRevert h5 hnc1

/-! ## Address words -/

/-- `msg.sender` as the word `CALLER` pushes. -/
abbrev callerW (I : ExecutionEnv) : UInt256 := UInt256.ofNat I.source.val

/-- A canonical address word is unchanged by solc's `AND` with the 160-bit mask. -/
theorem land_solcAddrMask_of_canon {w : UInt256} (hc : w.toNat < EVM.addressModulus) :
    UInt256.land w solcAddrMask = w := by
  apply u256_inj
  show Nat.land w.toNat solcAddrMask.toNat % EVM.twoPow 256 = w.toNat
  rw [show solcAddrMask.toNat = 2 ^ 160 - 1 from by decide,
    land_mask160 _ (by rw [show EVM.addressModulus = 2 ^ 160 from by decide] at hc; exact hc)]
  exact Nat.mod_eq_of_lt (by change w.val.val < EVM.twoPow 256; exact w.val.isLt)

/-- The address of a canonical word, back as a word. -/
theorem addrWord_canon {w : UInt256} (hc : w.toNat < EVM.addressModulus) :
    UInt256.ofNat (AccountAddress.ofNat w.toNat).toNat = w := by
  have h := keyValueToWord_address_of_canonical w hc
  rw [keyValueToWord_address] at h
  exact h

/-! ## The `(address, uint256)` decoder at `0x437` -/

/-- `abi_decode_tuple_address_uint256`: the integer ends on top, the address below it. -/
theorem decAddrU256Ok {s0 : State} {ret : UInt256} {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256} {w : World}
    {k C : ℕ}
    (h : Run erc20Runtime s0 ⟨⟨0x437⟩, ⟨4⟩ :: UInt256.ofNat s0.executionEnv.calldata.size :: ret :: R, mem, aw, rdata, w⟩ k C)
    (hsz : 68 ≤ s0.executionEnv.calldata.size) (hbig : s0.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hc : (calldataWord s0.executionEnv.calldata 4).toNat < EVM.addressModulus)
    (hret : (D_J erc20Runtime 0).contains ret = true) (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', Run erc20Runtime s0
      ⟨ret, calldataWord s0.executionEnv.calldata 36 :: calldataWord s0.executionEnv.calldata 4 :: R, mem, aw, rdata, w⟩
      k' C' := by
  have h1 := evm_run h with [jumpdest, push0, push0, push1 ⟨0x40⟩, dup4, dup6, sub, slt]
  rw [show (⟨0x40⟩ : UInt256) = UInt256.ofNat 64 from rfl, lenCheck_ok (by norm_num) (by omega) hbig] at h1
  have h2 := evm_run h1 with [iszero]
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at h2
  have h3 := evm_run h2 with [push2 ⟨0x448⟩, jumpiT (by decide) (by jump_dest), jumpdest, push2 ⟨0x451⟩, dup4,
    push2 ⟨0x41c⟩, jump (by jump_dest)]
  obtain ⟨_, _, h4⟩ := inlAddrOk h3 (by exact hc)
  have h5 := evm_run h4 with [jumpdest, swap5, push1 ⟨0x20⟩, swap4, swap1, swap4, add]
  rw [show (⟨0x20⟩ + ⟨4⟩ : UInt256) = ⟨36⟩ from by decide] at h5
  exact ⟨_, _, evm_run h5 with [calldataload, swap4, pop, pop, pop, jump hret]⟩

theorem decAddrU256LenRevert {s0 : State} {ret : UInt256} {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {w : World} {k C : ℕ}
    (h : Run erc20Runtime s0 ⟨⟨0x437⟩, ⟨4⟩ :: UInt256.ofNat s0.executionEnv.calldata.size :: ret :: R, mem, aw, rdata, w⟩ k C)
    (hslt : UInt256.slt (UInt256.sub (UInt256.ofNat s0.executionEnv.calldata.size) ⟨4⟩) (UInt256.ofNat 64) = ⟨1⟩)
    (hov : R.length + 12 ≤ 1024) :
    Reverted erc20Runtime s0 ByteArray.empty := by
  have h1 := evm_run h with [jumpdest, push0, push0, push1 ⟨0x40⟩, dup4, dup6, sub, slt]
  rw [show (⟨0x40⟩ : UInt256) = UInt256.ofNat 64 from rfl, hslt] at h1
  have h2 := evm_run h1 with [iszero]
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at h2
  exact (evm_run h2 with [push2 ⟨0x448⟩, jumpiNT rfl]).revertStub (by decide) (by decide) (by decide) (by evm_ov)

theorem decAddrU256DirtyRevert {s0 : State} {ret : UInt256} {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {w : World} {k C : ℕ}
    (h : Run erc20Runtime s0 ⟨⟨0x437⟩, ⟨4⟩ :: UInt256.ofNat s0.executionEnv.calldata.size :: ret :: R, mem, aw, rdata, w⟩ k C)
    (hsz : 68 ≤ s0.executionEnv.calldata.size) (hbig : s0.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (calldataWord s0.executionEnv.calldata 4).toNat < EVM.addressModulus)
    (hov : R.length + 12 ≤ 1024) :
    Reverted erc20Runtime s0 ByteArray.empty := by
  have h1 := evm_run h with [jumpdest, push0, push0, push1 ⟨0x40⟩, dup4, dup6, sub, slt]
  rw [show (⟨0x40⟩ : UInt256) = UInt256.ofNat 64 from rfl, lenCheck_ok (by norm_num) (by omega) hbig] at h1
  have h2 := evm_run h1 with [iszero]
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at h2
  have h3 := evm_run h2 with [push2 ⟨0x448⟩, jumpiT (by decide) (by jump_dest), jumpdest, push2 ⟨0x451⟩, dup4,
    push2 ⟨0x41c⟩, jump (by jump_dest)]
  exact inlAddrRevert h3 hnc

/-! ## The `bool` return tail at `0x77` -/

/-- `JUMPDEST; PUSH1 0x40; MLOAD; SWAP1; ISZERO; ISZERO; DUP2; MSTORE; PUSH1 0x20; ADD` into the return
    block: `true` is returned as one word.  The memory holds the free pointer `0x80` at `0x40` and
    has at least 96 bytes; five words are active. -/
theorem retBoolTrue {s0 : State} {R : List UInt256} {mem rdata : ByteArray} {w : World} {k C : ℕ}
    (h : Run erc20Runtime s0 ⟨⟨0x77⟩, ⟨1⟩ :: R, mem, UInt256.ofNat 5, rdata, w⟩ k C)
    (hmem : 96 ≤ mem.size) (hread : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hgap : 128 - mem.size < USize.size) (hov : R.length + 3 ≤ 1024) :
    Returned erc20Runtime s0 w (UInt256.toByteArray ⟨1⟩) := by
  have h1 := evm_run h with [jumpdest, push1 ⟨0x40⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide) mem_cost (mloadFreePtrValue (by omega) (by decide) hread)
      (by decide) (by evm_ov),
    swap1, iszero, iszero]
  rw [show UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256)) = ⟨1⟩ from by decide] at h1
  have h2 := evm_run h1 with [dup2,
    raw mstore 0 ((UInt256.toByteArray ⟨1⟩).write 0 mem 128 32) (UInt256.ofNat 5) (by native_decide) mem_cost rfl
      (by decide) (by evm_ov),
    push1 ⟨0x20⟩, add]
  obtain ⟨hsz, hread', hback⟩ := freePtr_after_write128 ⟨1⟩ hmem hread hgap
  have hret := Run.solcReturnBlock h2 (by dsimp only [solcReturnBlockWf]; repeat' first | apply And.intro | decide)
    (mloadFreePtrValue hsz (by decide) hread') (by evm_ov)
  rw [show (UInt256.sub (⟨32⟩ + ⟨128⟩) ⟨128⟩).toNat = 32 from by decide, hback] at hret
  exact hret

/-! ## The `Error(string)` reverts

`PUSH1 0x40; MLOAD; PUSH3 0x461bcd; PUSH1 0xe5; SHL; DUP2; MSTORE; PUSH1 0x20; PUSH1 4; DUP3; ADD;
MSTORE; PUSH1 len; PUSH1 0x24; DUP3; ADD; MSTORE; PUSH32 word; PUSH1 0x44; DUP3; ADD; MSTORE; PUSH1 0x64;
ADD; PUSH2 0x1ed; JUMP` builds the `Error(string)` payload at `0x80`; the block at `0x1ed` reverts
with the 100 bytes there. -/

@[reducible] def errTailWf (code : ByteArray) (pc len word : UInt256) : Prop :=
  let p2 := pc + UInt256.ofNat 2
  let p3 := p2 + ⟨1⟩
  let p7 := p3 + UInt256.ofNat 4
  let p9 := p7 + UInt256.ofNat 2
  let p10 := p9 + ⟨1⟩
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  let p14 := p12 + UInt256.ofNat 2
  let p16 := p14 + UInt256.ofNat 2
  let p17 := p16 + ⟨1⟩
  let p18 := p17 + ⟨1⟩
  let p19 := p18 + ⟨1⟩
  let p21 := p19 + UInt256.ofNat 2
  let p23 := p21 + UInt256.ofNat 2
  let p24 := p23 + ⟨1⟩
  let p25 := p24 + ⟨1⟩
  let p26 := p25 + ⟨1⟩
  let p59 := p26 + UInt256.ofNat 33
  let p61 := p59 + UInt256.ofNat 2
  let p62 := p61 + ⟨1⟩
  let p63 := p62 + ⟨1⟩
  let p64 := p63 + ⟨1⟩
  let p66 := p64 + UInt256.ofNat 2
  let p67 := p66 + ⟨1⟩
  let p70 := p67 + UInt256.ofNat 3
  decode code pc = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p2 = some (.MLOAD, .none)
  ∧ decode code p3 = some (.Push .PUSH3, some (⟨4594637⟩, 3))
  ∧ decode code p7 = some (.Push .PUSH1, some (⟨229⟩, 1))
  ∧ decode code p9 = some (.SHL, .none)
  ∧ decode code p10 = some (.DUP2, .none)
  ∧ decode code p11 = some (.MSTORE, .none)
  ∧ decode code p12 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p14 = some (.Push .PUSH1, some (⟨4⟩, 1))
  ∧ decode code p16 = some (.DUP3, .none)
  ∧ decode code p17 = some (.ADD, .none)
  ∧ decode code p18 = some (.MSTORE, .none)
  ∧ decode code p19 = some (.Push .PUSH1, some (len, 1))
  ∧ decode code p21 = some (.Push .PUSH1, some (⟨36⟩, 1))
  ∧ decode code p23 = some (.DUP3, .none)
  ∧ decode code p24 = some (.ADD, .none)
  ∧ decode code p25 = some (.MSTORE, .none)
  ∧ decode code p26 = some (.Push .PUSH32, some (word, 32))
  ∧ decode code p59 = some (.Push .PUSH1, some (⟨68⟩, 1))
  ∧ decode code p61 = some (.DUP3, .none)
  ∧ decode code p62 = some (.ADD, .none)
  ∧ decode code p63 = some (.MSTORE, .none)
  ∧ decode code p64 = some (.Push .PUSH1, some (⟨100⟩, 1))
  ∧ decode code p66 = some (.ADD, .none)
  ∧ decode code p67 = some (.Push .PUSH2, some (⟨0x1ed⟩, 2))
  ∧ decode code p70 = some (.JUMP, .none)

/-- The shared `Error(string)` revert block at `0x1ed`: `REVERT(0x80, 100)`. -/
theorem errBlock {s0 : State} {pc len word : UInt256} {stk : List UInt256} {mem rdata : ByteArray} {w : World} {k C : ℕ}
    (h : Run erc20Runtime s0 ⟨pc, (⟨100⟩ + ⟨128⟩) :: stk, solcErrorStringMem3 len word mem, UInt256.ofNat 8, rdata, w⟩ k C)
    (hpc : pc = ⟨0x1ed⟩) (hmem : mem.size = 96) (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : stk.length + 4 ≤ 1024) :
    Reverted erc20Runtime s0 (solcErrorStringPayload len word mem) := by
  subst hpc
  have h6 := evm_run h with [jumpdest, push1 ⟨0x40⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide) mem_cost (solcErrorStringMem3_mload64 len word hmem hread64)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1]
  rw [show UInt256.sub (⟨100⟩ + ⟨128⟩) ⟨128⟩ = ⟨100⟩ from by decide] at h6
  have hrev := h6.revVar (by native_decide) (by evm_ov)
  rw [show (⟨128⟩ : UInt256).toNat = 128 from rfl, show (⟨100⟩ : UInt256).toNat = 100 from rfl] at hrev
  exact hrev

theorem errTail {s0 : State} {pc len word : UInt256} {stk : List UInt256} {mem rdata : ByteArray} {w : World} {k C : ℕ}
    (h : Run erc20Runtime s0 ⟨pc, stk, mem, UInt256.ofNat 3, rdata, w⟩ k C)
    (hwf : errTailWf erc20Runtime pc len word) (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) (hov : stk.length + 4 ≤ 1024) :
    Reverted erc20Runtime s0 (solcErrorStringPayload len word mem) := by
  rcases hwf with ⟨hd0, hd2, hd3, hd7, hd9, hd10, hd11, hd12, hd14, hd16, hd17, hd18, hd19, hd21, hd23, hd24, hd25,
    hd26, hd59, hd61, hd62, hd63, hd64, hd66, hd67, hd70⟩
  have h1 := evm_run h with [
    raw push1 ⟨64⟩ hd0 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) hd2 mem_cost (mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64)
      (by decide) (by evm_ov)]
  have h2 := h1.pushConst (⟨4594637⟩ : UInt256) (width := 3) (op := .PUSH3) (by decide) hd3 (by evm_ov)
  have h3 := evm_run h2 with [
    raw push1 ⟨229⟩ hd7 (by evm_ov),
    raw shl hd9 (by evm_ov),
    raw dup2 hd10 (by evm_ov),
    raw mstore 6 (solcErrorStringMem0 mem) (UInt256.ofNat 5) hd11 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ hd12 (by evm_ov),
    raw push1 ⟨4⟩ hd14 (by evm_ov),
    raw dup3 hd16 (by evm_ov),
    raw add hd17 (by evm_ov),
    raw mstore 3 (solcErrorStringMem1 mem) (UInt256.ofNat 6) hd18 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 len hd19 (by evm_ov),
    raw push1 ⟨36⟩ hd21 (by evm_ov),
    raw dup3 hd23 (by evm_ov),
    raw add hd24 (by evm_ov),
    raw mstore 3 (solcErrorStringMem2 len mem) (UInt256.ofNat 7) hd25 mem_cost (by rfl) (by decide) (by evm_ov)]
  have h4 := h3.pushConst word (width := 32) (op := .PUSH32) (by decide) hd26 (by evm_ov)
  have h5 := evm_run h4 with [
    raw push1 ⟨68⟩ hd59 (by evm_ov),
    raw dup3 hd61 (by evm_ov),
    raw add hd62 (by evm_ov),
    raw mstore 3 (solcErrorStringMem3 len word mem) (UInt256.ofNat 8) hd63 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨100⟩ hd64 (by evm_ov),
    raw add hd66 (by evm_ov),
    raw push2 ⟨0x1ed⟩ hd67 (by evm_ov),
    raw jump hd70 (by jump_dest) (by evm_ov)]
  exact errBlock h5 rfl hmem hread64 hov

/-! ## The checked arithmetic routines and the `Panic(0x11)` block -/

/-- The shared `Panic(0x11)` block at `0x4ea`. -/
theorem panicTail {s0 : State} {stk : List UInt256} {mem rdata : ByteArray} {aw : UInt256} {w : World} {k C : ℕ}
    (h : Run erc20Runtime s0 ⟨⟨0x4ea⟩, stk, mem, aw, rdata, w⟩ k C) (hov : stk.length + 2 ≤ 1024) :
    Reverted erc20Runtime s0 (solcPanicPayload ⟨0x11⟩) :=
  Run.solcPanicTail (evm_run h with [jumpdest])
    (by dsimp only [solcPanicTailWf]; repeat' first | apply And.intro | native_decide) hov

/-- `checked_sub` at `0x4fe` on `x :: y :: ret :: …`: `x - y` when `y ≤ x`. -/
theorem checkedSubOk {s0 : State} {x y ret : UInt256} {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256} {w : World}
    {k C : ℕ}
    (h : Run erc20Runtime s0 ⟨⟨0x4fe⟩, x :: y :: ret :: R, mem, aw, rdata, w⟩ k C)
    (hle : y.toNat ≤ x.toNat) (hret : (D_J erc20Runtime 0).contains ret = true) (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', Run erc20Runtime s0 ⟨ret, UInt256.sub x y :: R, mem, aw, rdata, w⟩ k' C' := by
  have h1 := evm_run h with [jumpdest, dup2, dup2, sub, dup2, dup2, gt]
  rw [ugt_zero (by rw [usub_toNat hle]; omega)] at h1
  have h2 := evm_run h1 with [iszero]
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at h2
  exact ⟨_, _, evm_run h2 with [push2 ⟨0x178⟩, jumpiT (by decide) (by jump_dest), jumpdest, swap3, swap2, pop, pop,
    jump hret]⟩

/-- `checked_add` at `0x511` on `b :: a :: ret :: …`: `a + b` when it fits. -/
theorem checkedAddOk {s0 : State} {a b ret : UInt256} {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256} {w : World}
    {k C : ℕ}
    (h : Run erc20Runtime s0 ⟨⟨0x511⟩, b :: a :: ret :: R, mem, aw, rdata, w⟩ k C)
    (hfit : a.toNat + b.toNat < UInt256.size) (hret : (D_J erc20Runtime 0).contains ret = true)
    (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', Run erc20Runtime s0 ⟨ret, (a + b) :: R, mem, aw, rdata, w⟩ k' C' :=
  Run.solcCheckedAddPanicSuccess (okPc := ⟨0x178⟩) h
    (by dsimp only [solcCheckedAddPanicWf]; repeat' first | apply And.intro | native_decide) hfit hret (by jump_dest) hov

/-- `checked_add` at `0x511` overflowing: the `Panic(0x11)` block. -/
theorem checkedAddOverflow {s0 : State} {a b ret : UInt256} {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {w : World} {k C : ℕ}
    (h : Run erc20Runtime s0 ⟨⟨0x511⟩, b :: a :: ret :: R, mem, aw, rdata, w⟩ k C)
    (hover : UInt256.size ≤ a.toNat + b.toNat) (hov : R.length + 9 ≤ 1024) :
    Reverted erc20Runtime s0 (solcPanicPayload ⟨0x11⟩) := by
  have h1 := evm_run h with [jumpdest, dup1, dup3, add, dup1, dup3, gt]
  have hgt : UInt256.gt b (a + b) = ⟨1⟩ := by
    apply ugt_one
    have ha : a.toNat < UInt256.size := a.val.isLt
    have hb : b.toNat < UInt256.size := b.val.isLt
    rw [uadd_toNat, Nat.mod_eq_sub_mod hover, Nat.mod_eq_of_lt (by omega)]
    omega
  rw [hgt] at h1
  have h2 := evm_run h1 with [iszero]
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at h2
  exact panicTail (evm_run h2 with [push2 ⟨0x178⟩, jumpiNT rfl, push2 ⟨0x178⟩, push2 ⟨0x4ea⟩, jump (by jump_dest)])
    (by evm_ov)

/-- `checked_sub` at `0x4fe` underflowing (`x < y`): the `Panic(0x11)` block. -/
theorem checkedSubUnderflow {s0 : State} {x y ret : UInt256} {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {w : World} {k C : ℕ}
    (h : Run erc20Runtime s0 ⟨⟨0x4fe⟩, x :: y :: ret :: R, mem, aw, rdata, w⟩ k C)
    (hlt : x.toNat < y.toNat) (hov : R.length + 8 ≤ 1024) :
    Reverted erc20Runtime s0 (solcPanicPayload ⟨0x11⟩) := by
  have h1 := evm_run h with [jumpdest, dup2, dup2, sub, dup2, dup2, gt]
  have hgt : UInt256.gt (UInt256.sub x y) x = ⟨1⟩ := by
    apply ugt_one
    have hy : y.toNat < UInt256.size := y.val.isLt
    rw [usub_toNat_underflow hlt]
    omega
  rw [hgt] at h1
  have h2 := evm_run h1 with [iszero]
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at h2
  exact panicTail (evm_run h2 with [push2 ⟨0x178⟩, jumpiNT rfl, push2 ⟨0x178⟩, push2 ⟨0x4ea⟩, jump (by jump_dest)])
    (by evm_ov)

/-! ## The `(address, address, uint256)` decoder at `0x45f` -/

theorem decAddrAddrU256Ok {s0 : State} {ret : UInt256} {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256} {w : World}
    {k C : ℕ}
    (h : Run erc20Runtime s0 ⟨⟨0x45f⟩, ⟨4⟩ :: UInt256.ofNat s0.executionEnv.calldata.size :: ret :: R, mem, aw, rdata, w⟩ k C)
    (hsz : 100 ≤ s0.executionEnv.calldata.size) (hbig : s0.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hc0 : (calldataWord s0.executionEnv.calldata 4).toNat < EVM.addressModulus)
    (hc1 : (calldataWord s0.executionEnv.calldata 36).toNat < EVM.addressModulus)
    (hret : (D_J erc20Runtime 0).contains ret = true) (hov : R.length + 14 ≤ 1024) :
    ∃ k' C', Run erc20Runtime s0
      ⟨ret, calldataWord s0.executionEnv.calldata 68 :: calldataWord s0.executionEnv.calldata 36 ::
        calldataWord s0.executionEnv.calldata 4 :: R, mem, aw, rdata, w⟩ k' C' := by
  have h1 := evm_run h with [jumpdest, push0, push0, push0, push1 ⟨0x60⟩, dup5, dup7, sub, slt]
  rw [show (⟨0x60⟩ : UInt256) = UInt256.ofNat 96 from rfl, lenCheck_ok (by norm_num) (by omega) hbig] at h1
  have h2 := evm_run h1 with [iszero]
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at h2
  have h3 := evm_run h2 with [push2 ⟨0x471⟩, jumpiT (by decide) (by jump_dest), jumpdest, push2 ⟨0x47a⟩, dup5,
    push2 ⟨0x41c⟩, jump (by jump_dest)]
  obtain ⟨_, _, h4⟩ := inlAddrOk h3 (by exact hc0)
  have h5 := evm_run h4 with [jumpdest, swap3, pop, push2 ⟨0x488⟩, push1 ⟨0x20⟩, dup6, add, push2 ⟨0x41c⟩,
    jump (by jump_dest)]
  rw [show (⟨4⟩ + ⟨0x20⟩ : UInt256) = ⟨36⟩ from by decide] at h5
  obtain ⟨_, _, h6⟩ := inlAddrOk h5 (by exact hc1)
  have h7 := evm_run h6 with [jumpdest, swap3, swap6, swap3, swap5, pop, pop, pop, push1 ⟨0x40⟩, swap2, swap1, swap2, add]
  rw [show (⟨0x40⟩ + ⟨4⟩ : UInt256) = ⟨68⟩ from by decide] at h7
  exact ⟨_, _, evm_run h7 with [calldataload, swap1, jump hret]⟩

theorem decAddrAddrU256LenRevert {s0 : State} {ret : UInt256} {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {w : World} {k C : ℕ}
    (h : Run erc20Runtime s0 ⟨⟨0x45f⟩, ⟨4⟩ :: UInt256.ofNat s0.executionEnv.calldata.size :: ret :: R, mem, aw, rdata, w⟩ k C)
    (hslt : UInt256.slt (UInt256.sub (UInt256.ofNat s0.executionEnv.calldata.size) ⟨4⟩) (UInt256.ofNat 96) = ⟨1⟩)
    (hov : R.length + 14 ≤ 1024) :
    Reverted erc20Runtime s0 ByteArray.empty := by
  have h1 := evm_run h with [jumpdest, push0, push0, push0, push1 ⟨0x60⟩, dup5, dup7, sub, slt]
  rw [show (⟨0x60⟩ : UInt256) = UInt256.ofNat 96 from rfl, hslt] at h1
  have h2 := evm_run h1 with [iszero]
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at h2
  exact (evm_run h2 with [push2 ⟨0x471⟩, jumpiNT rfl]).revertStub (by decide) (by decide) (by decide) (by evm_ov)

theorem decAddrAddrU256Dirty0Revert {s0 : State} {ret : UInt256} {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {w : World} {k C : ℕ}
    (h : Run erc20Runtime s0 ⟨⟨0x45f⟩, ⟨4⟩ :: UInt256.ofNat s0.executionEnv.calldata.size :: ret :: R, mem, aw, rdata, w⟩ k C)
    (hsz : 100 ≤ s0.executionEnv.calldata.size) (hbig : s0.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hnc0 : ¬ (calldataWord s0.executionEnv.calldata 4).toNat < EVM.addressModulus)
    (hov : R.length + 14 ≤ 1024) :
    Reverted erc20Runtime s0 ByteArray.empty := by
  have h1 := evm_run h with [jumpdest, push0, push0, push0, push1 ⟨0x60⟩, dup5, dup7, sub, slt]
  rw [show (⟨0x60⟩ : UInt256) = UInt256.ofNat 96 from rfl, lenCheck_ok (by norm_num) (by omega) hbig] at h1
  have h2 := evm_run h1 with [iszero]
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at h2
  have h3 := evm_run h2 with [push2 ⟨0x471⟩, jumpiT (by decide) (by jump_dest), jumpdest, push2 ⟨0x47a⟩, dup5,
    push2 ⟨0x41c⟩, jump (by jump_dest)]
  exact inlAddrRevert h3 hnc0

theorem decAddrAddrU256Dirty1Revert {s0 : State} {ret : UInt256} {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {w : World} {k C : ℕ}
    (h : Run erc20Runtime s0 ⟨⟨0x45f⟩, ⟨4⟩ :: UInt256.ofNat s0.executionEnv.calldata.size :: ret :: R, mem, aw, rdata, w⟩ k C)
    (hsz : 100 ≤ s0.executionEnv.calldata.size) (hbig : s0.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hc0 : (calldataWord s0.executionEnv.calldata 4).toNat < EVM.addressModulus)
    (hnc1 : ¬ (calldataWord s0.executionEnv.calldata 36).toNat < EVM.addressModulus)
    (hov : R.length + 14 ≤ 1024) :
    Reverted erc20Runtime s0 ByteArray.empty := by
  have h1 := evm_run h with [jumpdest, push0, push0, push0, push1 ⟨0x60⟩, dup5, dup7, sub, slt]
  rw [show (⟨0x60⟩ : UInt256) = UInt256.ofNat 96 from rfl, lenCheck_ok (by norm_num) (by omega) hbig] at h1
  have h2 := evm_run h1 with [iszero]
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at h2
  have h3 := evm_run h2 with [push2 ⟨0x471⟩, jumpiT (by decide) (by jump_dest), jumpdest, push2 ⟨0x47a⟩, dup5,
    push2 ⟨0x41c⟩, jump (by jump_dest)]
  obtain ⟨_, _, h4⟩ := inlAddrOk h3 (by exact hc0)
  have h5 := evm_run h4 with [jumpdest, swap3, pop, push2 ⟨0x488⟩, push1 ⟨0x20⟩, dup6, add, push2 ⟨0x41c⟩,
    jump (by jump_dest)]
  rw [show (⟨4⟩ + ⟨0x20⟩ : UInt256) = ⟨36⟩ from by decide] at h5
  exact inlAddrRevert h5 hnc1

end ERC20.Opt
