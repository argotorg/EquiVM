import Benchmarks.WETH9.StringLayout
import Benchmarks.WETH9.Routines
import Reasoning.MemCascade

/-!
# WETH9 dynamic-string getter — config-independent EVM/byte machinery

`name()`/`symbol()` read a Solidity compact dynamic string from storage slot 0/1 and ABI-return it.
Both dispatch (via the non-payable guard) into a shared string-load routine (pc 839 reading slot 0
for `name`, pc 1571 reading slot 1 for `symbol`), which decodes the compact header, copies the data
into memory as a `[len ; data]` object, and returns to the shared ABI-string return encoder (pc 187)
which reallocates the object as an ABI `(offset, len, paddeddata)` triple and `RETURN`s it.

This module proves the reusable, **config-independent** facts: driving the RD symbolic executor from
the routine entry to an `RDret` returning exactly `weth9StringAbiEncode len data` (or `OutOfGass`).
The final `runtimeEquivalenceFor` connect (dispatch/decode/body) is wired separately in
`Name.lean`/`Symbol.lean`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000

namespace Benchmarks.WETH9

/-- Raw storage header word at `slot` for the code owner (the compact-string length header). -/
def weth9StringSlotWord (σ : AccountMap) (I : ExecutionEnv) (slot : UInt256) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD slot ⟨0⟩)

/-! ## Config-independent decode/shape expressions

These mirror **exactly** the terms the runtime builds at `runtime.hex` 0x347–0x381 (verified against
the symbolic executor).  `weth9StringMask` is `0xff` for the short flag and `~0` for the long flag;
`weth9StringLen` is the decoded byte length; `weth9StringWC` the data word count `⌈len/32⌉`;
`weth9StringNewFp` the bumped free pointer `0xa0 + 32·wc`. -/

/-- Runtime length mask: `~0 + 256·isZero(header & 1)` = `0xff` (short flag) or `~0` (long flag). -/
def weth9StringMask (header : UInt256) : UInt256 :=
  UInt256.lnot ⟨0⟩ + UInt256.mul ⟨256⟩ (UInt256.isZero (UInt256.land header ⟨1⟩))

/-- Decoded byte length `(header & mask) / 2`, matching `weth9DecodeBytesLengthHeader`. -/
def weth9StringLen (header : UInt256) : UInt256 :=
  UInt256.div (UInt256.land header (weth9StringMask header)) ⟨2⟩

/-- Data word count `⌈len/32⌉ = (len + 31) / 32`. -/
def weth9StringWC (header : UInt256) : UInt256 :=
  UInt256.div (weth9StringLen header + ⟨31⟩) ⟨32⟩

/-- Bumped free pointer after allocating the `[len ; data]` object: `0x20 + (0x80 + 32·wc)`. -/
def weth9StringNewFp (header : UInt256) : UInt256 :=
  ⟨32⟩ + (⟨128⟩ + UInt256.mul ⟨32⟩ (weth9StringWC header))

/-- Memory after the routine writes the bumped free pointer at `0x40` and the length word at `0x80`. -/
def weth9RoutineMem (header : UInt256) : ByteArray :=
  (UInt256.toByteArray (weth9StringLen header)).write 0
    ((UInt256.toByteArray (weth9StringNewFp header)).write 0 solcFreePtrMem (⟨64⟩ : UInt256).toNat 32)
    (⟨128⟩ : UInt256).toNat 32

/-- ABI encoding of the empty dynamic string/bytes: offset word `0x20` then length word `0`. -/
def weth9EmptyStringAbi : ByteArray :=
  UInt256.toByteArray ⟨32⟩ ++ UInt256.toByteArray ⟨0⟩

theorem weth9StringNewFp_zero {header : UInt256} (h : weth9StringLen header = ⟨0⟩) :
    weth9StringNewFp header = ⟨160⟩ := by
  unfold weth9StringNewFp weth9StringWC; rw [h]; decide +native

theorem weth9RoutineMem_zero {header : UInt256} (h : weth9StringLen header = ⟨0⟩) :
    weth9RoutineMem header =
      (UInt256.toByteArray ⟨0⟩).write 0
        ((UInt256.toByteArray ⟨160⟩).write 0 solcFreePtrMem (⟨64⟩ : UInt256).toNat 32)
        (⟨128⟩ : UInt256).toNat 32 := by
  unfold weth9RoutineMem; rw [h, weth9StringNewFp_zero h]

/-! ## Short-string case (`0 < len < 32`) shape/arithmetic -/

/-- The inline data word the runtime stores for a short string: `(header / 256) · 256` — the header
    with its low length byte cleared (the string bytes left-aligned). -/
def weth9StringShortDataWord (header : UInt256) : UInt256 :=
  UInt256.mul (UInt256.div header ⟨256⟩) ⟨256⟩

theorem weth9StringLen_toNat_le31 {header : UInt256}
    (hlt31 : UInt256.lt ⟨31⟩ (weth9StringLen header) = ⟨0⟩) :
    (weth9StringLen header).toNat ≤ 31 := by
  by_contra h
  have hone : UInt256.lt ⟨31⟩ (weth9StringLen header) = ⟨1⟩ :=
    ult_one (by rw [show (⟨31⟩ : UInt256).toNat = 31 from by decide]; omega)
  rw [hone] at hlt31; exact absurd hlt31 (by decide)

theorem weth9StringLen_toNat_pos {header : UInt256}
    (hne : weth9StringLen header ≠ ⟨0⟩) :
    1 ≤ (weth9StringLen header).toNat := by
  rcases Nat.eq_zero_or_pos (weth9StringLen header).toNat with h | h
  · exact absurd (uint256_toNat_eq_zero h) hne
  · exact h

theorem weth9StringWC_short {header : UInt256} (hne : weth9StringLen header ≠ ⟨0⟩)
    (hlt31 : UInt256.lt ⟨31⟩ (weth9StringLen header) = ⟨0⟩) :
    weth9StringWC header = ⟨1⟩ := by
  have hlo := weth9StringLen_toNat_pos hne
  have hhi := weth9StringLen_toNat_le31 hlt31
  apply u256_inj
  unfold weth9StringWC
  rw [udiv_toNat, uadd_toNat, show (⟨31⟩ : UInt256).toNat = 31 from by decide,
    show (⟨32⟩ : UInt256).toNat = 32 from by decide,
    Nat.mod_eq_of_lt (by norm_num [UInt256.size]; omega),
    show (⟨1⟩ : UInt256).toNat = 1 from by decide]
  omega

theorem weth9StringNewFp_short {header : UInt256} (hne : weth9StringLen header ≠ ⟨0⟩)
    (hlt31 : UInt256.lt ⟨31⟩ (weth9StringLen header) = ⟨0⟩) :
    weth9StringNewFp header = ⟨192⟩ := by
  unfold weth9StringNewFp; rw [weth9StringWC_short hne hlt31]; decide +native

theorem weth9RoutineMem_short {header : UInt256} (hne : weth9StringLen header ≠ ⟨0⟩)
    (hlt31 : UInt256.lt ⟨31⟩ (weth9StringLen header) = ⟨0⟩) :
    weth9RoutineMem header =
      (UInt256.toByteArray (weth9StringLen header)).write 0
        ((UInt256.toByteArray ⟨192⟩).write 0 solcFreePtrMem (⟨64⟩ : UInt256).toNat 32)
        (⟨128⟩ : UInt256).toNat 32 := by
  unfold weth9RoutineMem; rw [weth9StringNewFp_short hne hlt31]

/-- Memory holding the short `[len ; data]` object: length word at `0x80`, inline data at `0xa0`,
    bumped free pointer `0xc0` at `0x40` — as a chronological write cascade over `solcFreePtrMem`. -/
def weth9ShortObjMem (header : UInt256) : ByteArray :=
  (UInt256.toByteArray (weth9StringShortDataWord header)).write 0
    ((UInt256.toByteArray (weth9StringLen header)).write 0
      ((UInt256.toByteArray ⟨192⟩).write 0 solcFreePtrMem 64 32)
      128 32)
    160 32

/-! ### Read-back lemmas for `weth9ShortObjMem`

The short encoder's `MLOAD`s read symbolic words (length at `0x80`, data at `0xa0`) from a memory
tower with a zero gap `[0x60, 0x80)`.  `decide +native` cannot discharge these (free header); instead
we view each `.write` layer as a `Reasoning.Theory.writeWord` and read back with
`writeWord_read_preserved` (disjoint upper writes) / `writeWord_read_back` (both gap-tolerant). -/

/-- `weth9ShortObjMem` as an explicit `writeWord` tower. -/
theorem weth9ShortObjMem_eq (header : UInt256) :
    weth9ShortObjMem header =
      writeWord (writeWord (writeWord solcFreePtrMem 64 ⟨192⟩) 128 (weth9StringLen header))
        160 (weth9StringShortDataWord header) := rfl

theorem weth9ShortL1_size (v : UInt256) : (writeWord solcFreePtrMem 64 v).size = 96 := by
  rw [writeWord_size solcFreePtrMem 64 v (by rw [solcFreePtrMem_size]; exact lt_usize _ (by norm_num)),
    solcFreePtrMem_size]; omega

theorem weth9ShortL2_size (v w : UInt256) :
    (writeWord (writeWord solcFreePtrMem 64 v) 128 w).size = 160 := by
  rw [writeWord_size _ 128 w (by rw [weth9ShortL1_size]; exact lt_usize _ (by norm_num)),
    weth9ShortL1_size]; omega

theorem weth9ShortObjMem_size (header : UInt256) : (weth9ShortObjMem header).size = 192 := by
  rw [weth9ShortObjMem_eq,
    writeWord_size _ 160 _ (by rw [weth9ShortL2_size]; exact lt_usize _ (by norm_num)),
    weth9ShortL2_size]; omega

theorem weth9ShortObjMem_read160 (header : UInt256) :
    (weth9ShortObjMem header).readWithPadding 160 32 =
      UInt256.toByteArray (weth9StringShortDataWord header) := by
  rw [weth9ShortObjMem_eq]
  exact writeWord_read_back _ 160 _ (by rw [weth9ShortL2_size]; exact lt_usize _ (by norm_num))

theorem weth9ShortObjMem_read128 (header : UInt256) :
    (weth9ShortObjMem header).readWithPadding 128 32 =
      UInt256.toByteArray (weth9StringLen header) := by
  rw [weth9ShortObjMem_eq,
    writeWord_read_preserved _ 160 128 _ (by rw [weth9ShortL2_size]; exact lt_usize _ (by norm_num))
      (Or.inl ⟨by decide, by rw [weth9ShortL2_size]⟩)]
  exact writeWord_read_back _ 128 _ (by rw [weth9ShortL1_size]; exact lt_usize _ (by norm_num))

theorem weth9ShortObjMem_read64 (header : UInt256) :
    (weth9ShortObjMem header).readWithPadding 64 32 = UInt256.toByteArray ⟨192⟩ := by
  rw [weth9ShortObjMem_eq,
    writeWord_read_preserved _ 160 64 _ (by rw [weth9ShortL2_size]; exact lt_usize _ (by norm_num))
      (Or.inl ⟨by decide, by rw [weth9ShortL2_size]; decide⟩),
    writeWord_read_preserved _ 128 64 _ (by rw [weth9ShortL1_size]; exact lt_usize _ (by norm_num))
      (Or.inl ⟨by decide, by rw [weth9ShortL1_size]⟩)]
  exact writeWord_read_back _ 64 _ (by rw [solcFreePtrMem_size]; exact lt_usize _ (by norm_num))

/-! ## Reach the shared string-load routine

`name()` enters at pc 166; the non-payable guard (gt = 178) peels to pc 180, whose
`PUSH2 187; PUSH2 839; JUMP` lands at the routine (pc 839) with `[187, sel]`. -/

theorem weth9ReachName839 {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = weth9Bytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (weth9SelBytes 0)) :
    ∃ k C, RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨839⟩
      [⟨187⟩, weth9SelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h166⟩ := weth9ReachName (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz4 hsize hsel
  obtain ⟨_, _, h180⟩ := weth9GuardPeelOk (gt := ⟨178⟩) h166 hwv
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by jump_dest) (by decide +native) (by decide +native)
  have h839 := h180.push2 ⟨187⟩ (by decide +native) (by simp)
    |>.push2 ⟨839⟩ (by decide +native) (by simp)
    |>.jump (by decide +native) (by jump_dest) (by simp)
  exact ⟨_, _, h839⟩

/-! ## Shared string-load routine prefix (pc 839 → 897)

Drives the compact-header decode + allocation, writing the bumped free pointer at `0x40` and the
length word at `0x80`, reaching pc 897 (the `DUP1` before the empty/short/long dispatch) with the
data pointer `0xa0` and the decoded length on the stack.  Config-independent, symbolic header. -/

set_option maxHeartbeats 8000000 in
theorem weth9NameRoutineReach897 {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = weth9Bytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (weth9SelBytes 0)) :
    ∃ k C, RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨897⟩
      [weth9StringLen (weth9StringSlotWord σ I ⟨0⟩), ⟨0⟩, ⟨160⟩,
       weth9StringLen (weth9StringSlotWord σ I ⟨0⟩), ⟨0⟩, ⟨128⟩, ⟨187⟩, weth9SelWord I]
      (weth9RoutineMem (weth9StringSlotWord σ I ⟨0⟩)) (UInt256.ofNat 5)
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h839⟩ := weth9ReachName839 (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz4 hsize hsel
  obtain ⟨_, _, h844⟩ := (evm_run h839 with [jumpdest, push1 ⟨0⟩, dup1]).sload
    (by decide +native) (by evm_ov)
  have h886 := evm_run h844 with [
    push1 ⟨64⟩, dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide +native) mem_cost
      solcFreePtrMem_mload64 (by decide) (by evm_ov),
    push1 ⟨32⟩, push1 ⟨2⟩, push1 ⟨1⟩, dup6, and, iszero, push2 ⟨256⟩, mul,
    push1 ⟨0⟩, not, add, swap1, swap5, and, swap4, swap1, swap4, div,
    push1 ⟨31⟩, dup2, add, dup5, swap1, div, dup5, mul, dup3, add, dup5, add, swap1, swap3]
  have h897 := evm_run h886 with [
    raw mstore 0 ((UInt256.toByteArray (weth9StringNewFp (weth9StringSlotWord σ I ⟨0⟩))).write 0
        solcFreePtrMem (⟨64⟩ : UInt256).toNat 32) (UInt256.ofNat 3)
      (by decide +native) mem_cost rfl (by decide +native) (by evm_ov),
    dup2, dup2,
    raw mstore 6 (weth9RoutineMem (weth9StringSlotWord σ I ⟨0⟩)) (UInt256.ofNat 5)
      (by decide +native) mem_cost rfl (by decide +native) (by evm_ov),
    swap3, swap2, dup4, add, dup3, dup3]
  exact ⟨_, _, h897⟩

/-! ## Empty-string case (`len = 0`) -/

set_option maxHeartbeats 8000000 in
theorem weth9NameStringEmptyReturns {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = weth9Bytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (weth9SelBytes 0))
    (hlen0 : weth9StringLen (weth9StringSlotWord σ I ⟨0⟩) = ⟨0⟩) :
    RDret weth9Bytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ) weth9EmptyStringAbi := by
  obtain ⟨_, _, h897⟩ := weth9NameRoutineReach897 (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz4 hsize hsel
  rw [hlen0, weth9RoutineMem_zero hlen0] at h897
  have h187 := evm_run h897 with [
    dup1, iszero, push2 ⟨973⟩, jumpiT (by decide) (by jump_dest),
    jumpdest, pop, pop, pop, pop, pop, dup2, jump (by jump_dest)]
  have h196 := evm_run h187 with [
    jumpdest, push1 ⟨64⟩, dup1,
    raw mload 0 ⟨160⟩ (UInt256.ofNat 5) (by decide +native) mem_cost
      (by decide +native) (by decide +native) (by evm_ov),
    push1 ⟨32⟩, dup1, dup3,
    raw mstore 3 _ (UInt256.ofNat 6) (by decide +native) mem_cost rfl
      (by decide +native) (by evm_ov)]
  have h221 := evm_run h196 with [
    dup4,
    raw mload 0 ⟨0⟩ (UInt256.ofNat 6) (by decide +native) mem_cost
      (by decide +native) (by decide +native) (by evm_ov),
    dup2, dup4, add,
    raw mstore 3 _ (UInt256.ofNat 7) (by decide +native) mem_cost rfl
      (by decide +native) (by evm_ov),
    dup4,
    raw mload 0 ⟨0⟩ (UInt256.ofNat 7) (by decide +native) mem_cost
      (by decide +native) (by decide +native) (by evm_ov),
    swap2, swap3, dup4, swap3, swap1, dup4, add, swap2, dup6, add, swap1,
    dup1, dup4, dup4, push1 ⟨0⟩]
  have hret := evm_run h221 with [
    jumpdest, dup4, dup2, lt, iszero, push2 ⟨245⟩, jumpiT (by decide) (by jump_dest),
    jumpdest, pop, pop, pop, pop, swap1, pop, swap1, dup2, add, swap1,
    push1 ⟨31⟩, and, dup1, iszero, push2 ⟨290⟩, jumpiT (by decide) (by jump_dest),
    jumpdest, pop, swap3, pop, pop, pop, push1 ⟨64⟩,
    raw mload 0 ⟨160⟩ (UInt256.ofNat 7) (by decide +native) mem_cost
      (by decide +native) (by decide +native) (by evm_ov),
    dup1, swap2, sub, swap1]
  exact evm_run hret with [
    raw ret 0 weth9EmptyStringAbi (by decide +native) mem_cost (by decide +native) (by evm_ov)]

/-! ## Short-string load routine (pc 897 → encoder entry 187) -/

set_option maxHeartbeats 8000000 in
theorem weth9NameShortLoadReach187 {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = weth9Bytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (weth9SelBytes 0))
    (hne : weth9StringLen (weth9StringSlotWord σ I ⟨0⟩) ≠ ⟨0⟩)
    (hlt31 : UInt256.lt ⟨31⟩ (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)) = ⟨0⟩) :
    ∃ k C, RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨187⟩
      [⟨128⟩, ⟨187⟩, weth9SelWord I]
      (weth9ShortObjMem (weth9StringSlotWord σ I ⟨0⟩)) (UInt256.ofNat 6)
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h897⟩ := weth9NameRoutineReach897 (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz4 hsize hsel
  rw [weth9RoutineMem_short hne hlt31] at h897
  have h915 := evm_run h897 with [
    dup1, iszero, push2 ⟨973⟩, jumpiNT (isZero_eq_zero_of_ne hne),
    dup1, push1 ⟨31⟩, lt, push2 ⟨930⟩, jumpiNT hlt31,
    push2 ⟨256⟩, dup1, dup4]
  obtain ⟨_, _, h916⟩ := h915.sload (by decide +native) (by evm_ov)
  have h187 := evm_run h916 with [
    div, mul, dup4,
    raw mstore 3 (weth9ShortObjMem (weth9StringSlotWord σ I ⟨0⟩)) (UInt256.ofNat 6)
      (by decide +native) mem_cost rfl (by decide +native) (by evm_ov),
    swap2, push1 ⟨32⟩, add, swap2, push2 ⟨973⟩, jump (by jump_dest),
    jumpdest, pop, pop, pop, pop, pop, dup2, jump (by jump_dest)]
  exact ⟨_, _, h187⟩

/-! ## Short-string ABI return encoder (pc 187 → RDret) -/

/-- A low read `[read, read+32)` is unchanged by a later word write at `off ≥ read+32`. -/
theorem weth9EncLowRead {mem : ByteArray} {off read : Nat} {word w : UInt256}
    (hbase : mem.readWithPadding read 32 = UInt256.toByteArray w)
    (hsz : read + 32 ≤ mem.size) (_hoff : mem.size ≤ off) (hgap : off - mem.size < USize.size)
    (hro : read + 32 ≤ off) :
    (writeWord mem off word).readWithPadding read 32 = UInt256.toByteArray w := by
  rw [writeWord_read_preserved mem off read word hgap (Or.inl ⟨hro, hsz⟩)]; exact hbase

theorem weth9ShortLtEnter {H : UInt256} (hne : weth9StringLen H ≠ ⟨0⟩) :
    UInt256.isZero (UInt256.lt ⟨0⟩ (weth9StringLen H)) = ⟨0⟩ := by
  have hp := weth9StringLen_toNat_pos hne
  have h0 : (⟨0⟩ : UInt256).toNat = 0 := by decide
  rw [ult_one (by omega)]; decide

theorem weth9ShortLtExit {H : UInt256} (hlt31 : UInt256.lt ⟨31⟩ (weth9StringLen H) = ⟨0⟩) :
    UInt256.isZero (UInt256.lt ⟨32⟩ (weth9StringLen H)) ≠ ⟨0⟩ := by
  have hle := weth9StringLen_toNat_le31 hlt31
  have h32 : (⟨32⟩ : UInt256).toNat = 32 := by decide
  rw [ult_zero (by omega)]; decide

/-- Encoder memory after `mstore(0xc0, 0x20)` (the ABI offset word). -/
noncomputable def weth9ShortMemA (H : UInt256) : ByteArray := writeWord (weth9ShortObjMem H) 192 ⟨32⟩
/-- Encoder memory after `mstore(0xe0, len)` (the ABI length word). -/
noncomputable def weth9ShortMemB (H : UInt256) : ByteArray :=
  writeWord (weth9ShortMemA H) 224 (weth9StringLen H)
/-- Encoder memory after the copy loop's `mstore(0x100, data)`. -/
noncomputable def weth9ShortMemC (H : UInt256) : ByteArray :=
  writeWord (weth9ShortMemB H) 256 (weth9StringShortDataWord H)

theorem weth9ShortMemA_size (H : UInt256) : (weth9ShortMemA H).size = 224 := by
  rw [weth9ShortMemA, writeWord_size _ 192 _
    (by rw [weth9ShortObjMem_size]; exact lt_usize _ (by norm_num)), weth9ShortObjMem_size]; omega

theorem weth9ShortMemB_size (H : UInt256) : (weth9ShortMemB H).size = 256 := by
  rw [weth9ShortMemB, writeWord_size _ 224 _
    (by rw [weth9ShortMemA_size]; exact lt_usize _ (by norm_num)), weth9ShortMemA_size]; omega

theorem weth9ShortMemC_size (H : UInt256) : (weth9ShortMemC H).size = 288 := by
  rw [weth9ShortMemC, writeWord_size _ 256 _
    (by rw [weth9ShortMemB_size]; exact lt_usize _ (by norm_num)), weth9ShortMemB_size]; omega

/-- Read back the object data word at `0xa0` through the two ABI-header writes (both above). -/
theorem weth9ShortMemB_read160 (H : UInt256) :
    (weth9ShortMemB H).readWithPadding 160 32 =
      UInt256.toByteArray (weth9StringShortDataWord H) := by
  rw [weth9ShortMemB]
  refine weth9EncLowRead ?_ (by rw [weth9ShortMemA_size]; decide) (by rw [weth9ShortMemA_size])
    (by rw [weth9ShortMemA_size]; exact lt_usize _ (by norm_num)) (by decide)
  rw [weth9ShortMemA]
  exact weth9EncLowRead (weth9ShortObjMem_read160 H) (by rw [weth9ShortObjMem_size])
    (by rw [weth9ShortObjMem_size]) (by rw [weth9ShortObjMem_size]; exact lt_usize _ (by norm_num))
    (by decide)

theorem weth9ShortMemA_read128 (H : UInt256) :
    (weth9ShortMemA H).readWithPadding 128 32 = UInt256.toByteArray (weth9StringLen H) := by
  rw [weth9ShortMemA]
  exact weth9EncLowRead (weth9ShortObjMem_read128 H) (by rw [weth9ShortObjMem_size]; decide)
    (by rw [weth9ShortObjMem_size]) (by rw [weth9ShortObjMem_size]; exact lt_usize _ (by norm_num))
    (by decide)

theorem weth9ShortMemB_read128 (H : UInt256) :
    (weth9ShortMemB H).readWithPadding 128 32 = UInt256.toByteArray (weth9StringLen H) := by
  rw [weth9ShortMemB]
  exact weth9EncLowRead (weth9ShortMemA_read128 H) (by rw [weth9ShortMemA_size]; decide)
    (by rw [weth9ShortMemA_size]) (by rw [weth9ShortMemA_size]; exact lt_usize _ (by norm_num))
    (by decide)

/-- Read back the loop-copied data word at `0x100` (the last write in `weth9ShortMemC`). -/
theorem weth9ShortMemC_read256 (H : UInt256) :
    (weth9ShortMemC H).readWithPadding 256 32 =
      UInt256.toByteArray (weth9StringShortDataWord H) := by
  rw [weth9ShortMemC]
  exact writeWord_read_back _ 256 _ (by rw [weth9ShortMemB_size]; exact lt_usize _ (by norm_num))

theorem weth9ShortMemA_read64 (H : UInt256) :
    (weth9ShortMemA H).readWithPadding 64 32 = UInt256.toByteArray ⟨192⟩ := by
  rw [weth9ShortMemA]
  exact weth9EncLowRead (weth9ShortObjMem_read64 H) (by rw [weth9ShortObjMem_size]; decide)
    (by rw [weth9ShortObjMem_size]) (by rw [weth9ShortObjMem_size]; exact lt_usize _ (by norm_num))
    (by decide)

theorem weth9ShortMemB_read64 (H : UInt256) :
    (weth9ShortMemB H).readWithPadding 64 32 = UInt256.toByteArray ⟨192⟩ := by
  rw [weth9ShortMemB]
  exact weth9EncLowRead (weth9ShortMemA_read64 H) (by rw [weth9ShortMemA_size]; decide)
    (by rw [weth9ShortMemA_size]) (by rw [weth9ShortMemA_size]; exact lt_usize _ (by norm_num))
    (by decide)

theorem weth9ShortMemC_read64 (H : UInt256) :
    (weth9ShortMemC H).readWithPadding 64 32 = UInt256.toByteArray ⟨192⟩ := by
  rw [weth9ShortMemC]
  exact weth9EncLowRead (weth9ShortMemB_read64 H) (by rw [weth9ShortMemB_size]; decide)
    (by rw [weth9ShortMemB_size]) (by rw [weth9ShortMemB_size]; exact lt_usize _ (by norm_num))
    (by decide)

/-- `31 & len = len` for a short length (`len < 32`), so the runtime's tail offset arithmetic
    `(0x100 + len) - (31 & len)` collapses to `0x100`. -/
theorem weth9StringLand31_eq {H : UInt256} (hlt31 : UInt256.lt ⟨31⟩ (weth9StringLen H) = ⟨0⟩) :
    UInt256.land ⟨31⟩ (weth9StringLen H) = weth9StringLen H := by
  apply u256_inj
  rw [uland_toNat, show (⟨31⟩ : UInt256).toNat = 31 from rfl,
    Nat.and_comm 31 (weth9StringLen H).toNat, show (31 : Nat) = 2 ^ 5 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt (by have := weth9StringLen_toNat_le31 hlt31; omega)

theorem weth9ShortMaskCond {H : UInt256} (hne : weth9StringLen H ≠ ⟨0⟩)
    (hlt31 : UInt256.lt ⟨31⟩ (weth9StringLen H) = ⟨0⟩) :
    UInt256.isZero (UInt256.land ⟨31⟩ (weth9StringLen H)) = ⟨0⟩ := by
  rw [weth9StringLand31_eq hlt31]; exact isZero_eq_zero_of_ne hne

/-- The runtime's tail-clean address `(len + 0x100) - (31 & len) = 0x100`. -/
theorem weth9ShortMaskAddr {H : UInt256} (hlt31 : UInt256.lt ⟨31⟩ (weth9StringLen H) = ⟨0⟩) :
    UInt256.sub (weth9StringLen H + ((⟨192⟩ : UInt256) + ⟨64⟩)) (UInt256.land ⟨31⟩ (weth9StringLen H)) =
      ⟨256⟩ := by
  rw [weth9StringLand31_eq hlt31]
  apply u256_inj
  have hle := weth9StringLen_toNat_le31 hlt31
  have hadd : (weth9StringLen H + ((⟨192⟩ : UInt256) + ⟨64⟩)).toNat = (weth9StringLen H).toNat + 256 := by
    rw [uadd_toNat, show ((⟨192⟩ : UInt256) + ⟨64⟩).toNat = 256 from by decide,
      Nat.mod_eq_of_lt (by norm_num [UInt256.size]; omega)]
  rw [usub_toNat (by rw [hadd]; omega), hadd, show (⟨256⟩ : UInt256).toNat = 256 from rfl]; omega

/-- The masked last data word: `~(2^(8·(32 - 31&len)) - 1) & data` (zeroing the trailing garbage). -/
def weth9ShortMaskWord (header : UInt256) : UInt256 :=
  UInt256.land
    (UInt256.lnot (UInt256.sub
      (UInt256.exp ⟨256⟩ (UInt256.sub ⟨32⟩ (UInt256.land ⟨31⟩ (weth9StringLen header)))) ⟨1⟩))
    (weth9StringShortDataWord header)

/-- Encoder memory after the tail mask re-stores the last word at `0x100`. -/
noncomputable def weth9ShortMemD (header : UInt256) : ByteArray :=
  writeWord (weth9ShortMemC header) 256 (weth9ShortMaskWord header)

/-- The ABI encoding a short-string getter returns: `offset 0x20 ‖ len ‖ masked-data`. -/
def weth9ShortStringAbi (header : UInt256) : ByteArray :=
  UInt256.toByteArray ⟨32⟩ ++ (UInt256.toByteArray (weth9StringLen header) ++
    UInt256.toByteArray (weth9ShortMaskWord header))

theorem weth9ShortMemD_size (H : UInt256) : (weth9ShortMemD H).size = 288 := by
  rw [weth9ShortMemD, writeWord_size _ 256 _
    (by rw [weth9ShortMemC_size]; exact lt_usize _ (by norm_num)), weth9ShortMemC_size]; omega

theorem weth9ShortMemD_read64 (H : UInt256) :
    (weth9ShortMemD H).readWithPadding 64 32 = UInt256.toByteArray ⟨192⟩ := by
  rw [weth9ShortMemD,
    writeWord_read_preserved _ 256 64 _ (by rw [weth9ShortMemC_size]; exact lt_usize _ (by norm_num))
      (Or.inl ⟨by decide, by rw [weth9ShortMemC_size]; decide⟩)]
  exact weth9ShortMemC_read64 H

theorem weth9ShortMemA_read192 (H : UInt256) :
    (weth9ShortMemA H).readWithPadding 192 32 = UInt256.toByteArray ⟨32⟩ := by
  rw [weth9ShortMemA]
  exact writeWord_read_back _ 192 _ (by rw [weth9ShortObjMem_size]; exact lt_usize _ (by norm_num))

theorem weth9ShortMemB_read224 (H : UInt256) :
    (weth9ShortMemB H).readWithPadding 224 32 = UInt256.toByteArray (weth9StringLen H) := by
  rw [weth9ShortMemB]
  exact writeWord_read_back _ 224 _ (by rw [weth9ShortMemA_size]; exact lt_usize _ (by norm_num))

theorem weth9ShortMemD_read192 (H : UInt256) :
    (weth9ShortMemD H).readWithPadding 192 32 = UInt256.toByteArray ⟨32⟩ := by
  rw [weth9ShortMemD,
    writeWord_read_preserved _ 256 192 _ (by rw [weth9ShortMemC_size]; exact lt_usize _ (by norm_num))
      (Or.inl ⟨by decide, by rw [weth9ShortMemC_size]; decide⟩), weth9ShortMemC,
    writeWord_read_preserved _ 256 192 _ (by rw [weth9ShortMemB_size]; exact lt_usize _ (by norm_num))
      (Or.inl ⟨by decide, by rw [weth9ShortMemB_size]; decide⟩), weth9ShortMemB,
    writeWord_read_preserved _ 224 192 _ (by rw [weth9ShortMemA_size]; exact lt_usize _ (by norm_num))
      (Or.inl ⟨by decide, by rw [weth9ShortMemA_size]⟩)]
  exact weth9ShortMemA_read192 H

theorem weth9ShortMemD_read224 (H : UInt256) :
    (weth9ShortMemD H).readWithPadding 224 32 = UInt256.toByteArray (weth9StringLen H) := by
  rw [weth9ShortMemD,
    writeWord_read_preserved _ 256 224 _ (by rw [weth9ShortMemC_size]; exact lt_usize _ (by norm_num))
      (Or.inl ⟨by decide, by rw [weth9ShortMemC_size]; decide⟩), weth9ShortMemC,
    writeWord_read_preserved _ 256 224 _ (by rw [weth9ShortMemB_size]; exact lt_usize _ (by norm_num))
      (Or.inl ⟨by decide, by rw [weth9ShortMemB_size]⟩)]
  exact weth9ShortMemB_read224 H

theorem weth9ShortMemD_read256 (H : UInt256) :
    (weth9ShortMemD H).readWithPadding 256 32 =
      UInt256.toByteArray (weth9ShortMaskWord H) := by
  rw [weth9ShortMemD]
  exact writeWord_read_back _ 256 _ (by rw [weth9ShortMemC_size]; exact lt_usize _ (by norm_num))

/-- The `RETURN(0xc0, 0x60)` window over the finished encoder memory is exactly the ABI encoding. -/
theorem weth9ShortMemD_readAbi (H : UInt256) :
    (weth9ShortMemD H).readWithPadding 192 96 = weth9ShortStringAbi H := by
  rw [weth9ShortStringAbi, show (96 : ℕ) = 32 + 64 from rfl,
    byteArray_readWithPadding_split _ 192 32 64 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by rw [weth9ShortMemD_size]),
    show (192 : ℕ) + 32 = 224 from rfl,
    byteArray_readWithPadding_split _ 224 32 32 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by rw [weth9ShortMemD_size]),
    show (224 : ℕ) + 32 = 256 from rfl,
    weth9ShortMemD_read192, weth9ShortMemD_read224, weth9ShortMemD_read256]

/-- The short-string ABI return encoder (pc 187 → `RETURN`): from the `[len ; data]` object it
    writes the ABI `(offset, len, data)` triple, copies the data word (loop, once), zeroes the trailing
    garbage (tail mask), and `RETURN`s `weth9ShortStringAbi`.  Config-independent, symbolic `len`. -/
theorem weth9NameShortEncoder {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ} (H : UInt256)
    (hne : weth9StringLen H ≠ ⟨0⟩)
    (hlt31 : UInt256.lt ⟨31⟩ (weth9StringLen H) = ⟨0⟩)
    (h : RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨187⟩
      [⟨128⟩, ⟨187⟩, weth9SelWord I] (weth9ShortObjMem H) (UInt256.ofNat 6)
      ByteArray.empty (cA, σ) k C) :
    RDret weth9Bytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ) (weth9ShortStringAbi H) := by
  have h196 := evm_run h with [
    jumpdest, push1 ⟨64⟩, dup1,
    raw mload 0 ⟨192⟩ (UInt256.ofNat 6) (by decide +native) mem_cost
      (mloadWordValue_of_readWithPadding (by rw [weth9ShortObjMem_size]; decide)
        (by decide) (weth9ShortObjMem_read64 H)) (by decide +native) (by evm_ov),
    push1 ⟨32⟩, dup1, dup3,
    raw mstore 3 (weth9ShortMemA H) (UInt256.ofNat 7)
      (by decide +native) mem_cost rfl (by decide +native) (by evm_ov)]
  have h221 := evm_run h196 with [
    dup4,
    raw mload 0 (weth9StringLen H) (UInt256.ofNat 7) (by decide +native) mem_cost
      (mloadWordValue_of_readWithPadding (by rw [weth9ShortMemA_size]; decide) (by decide)
        (weth9ShortMemA_read128 H)) (by decide +native) (by evm_ov),
    dup2, dup4, add,
    raw mstore 3 (weth9ShortMemB H) (UInt256.ofNat 8)
      (by decide +native) mem_cost rfl (by decide +native) (by evm_ov),
    dup4,
    raw mload 0 (weth9StringLen H) (UInt256.ofNat 8) (by decide +native) mem_cost
      (mloadWordValue_of_readWithPadding (by rw [weth9ShortMemB_size]; decide) (by decide)
        (weth9ShortMemB_read128 H)) (by decide +native) (by evm_ov),
    swap2, swap3, dup4, swap3, swap1, dup4, add, swap2, dup6, add, swap1,
    dup1, dup4, dup4, push1 ⟨0⟩]
  have h245 := evm_run h221 with [
    jumpdest, dup4, dup2, lt, iszero, push2 ⟨245⟩, jumpiNT (weth9ShortLtEnter hne),
    dup2, dup2, add,
    raw mload 0 (weth9StringShortDataWord H) (UInt256.ofNat 8) (by decide +native) mem_cost
      (mloadWordValue_of_readWithPadding (by rw [weth9ShortMemB_size]; decide) (by decide)
        (weth9ShortMemB_read160 H)) (by decide +native) (by evm_ov),
    dup4, dup3, add,
    raw mstore 3 (weth9ShortMemC H) (UInt256.ofNat 9) (by decide +native) mem_cost rfl
      (by decide +native) (by evm_ov),
    push1 ⟨32⟩, add, push2 ⟨221⟩, jump (by jump_dest),
    jumpdest, dup4, dup2, lt, iszero, push2 ⟨245⟩, jumpiT (weth9ShortLtExit hlt31) (by jump_dest)]
  have h267 := evm_run h245 with [
    jumpdest, pop, pop, pop, pop, swap1, pop, swap1, dup2, add, swap1,
    push1 ⟨31⟩, and, dup1, iszero, push2 ⟨290⟩, jumpiNT (weth9ShortMaskCond hne hlt31),
    dup1, dup3, sub]
  rw [weth9ShortMaskAddr hlt31] at h267
  have h295 := evm_run h267 with [
    dup1,
    raw mload 0 (weth9StringShortDataWord H) (UInt256.ofNat 9) (by decide +native) mem_cost
      (mloadWordValue_of_readWithPadding (by rw [weth9ShortMemC_size]; decide) (by decide)
        (weth9ShortMemC_read256 H)) (by decide +native) (by evm_ov),
    push1 ⟨1⟩, dup4, push1 ⟨32⟩, sub, push2 ⟨256⟩, exp, sub, not, and, dup2,
    raw mstore 0 (weth9ShortMemD H) (UInt256.ofNat 9) (by decide +native) mem_cost rfl
      (by decide +native) (by evm_ov),
    push1 ⟨32⟩, add, swap2, pop,
    jumpdest, pop, swap3, pop, pop, pop]
  exact evm_run h295 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨192⟩ (UInt256.ofNat 9) (by decide +native) mem_cost
      (mloadWordValue_of_readWithPadding (by rw [weth9ShortMemD_size]; decide) (by decide)
        (weth9ShortMemD_read64 H)) (by decide +native) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (weth9ShortStringAbi H) (by decide +native) mem_cost
      (weth9ShortMemD_readAbi H) (by evm_ov)]

/-- **Full short-string `name()` getter** (`0 < len < 32`): from the getter entry, reach the routine,
    decode + copy the compact string, ABI-encode it, and `RETURN` `weth9ShortStringAbi`.  For an
    arbitrary storage header whose decoded length is short — the reachable "Wrapped Ether"/"WETH"
    case.  Config-independent (no wired config). -/
theorem weth9NameStringShortReturns {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = weth9Bytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (weth9SelBytes 0))
    (hne : weth9StringLen (weth9StringSlotWord σ I ⟨0⟩) ≠ ⟨0⟩)
    (hlt31 : UInt256.lt ⟨31⟩ (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)) = ⟨0⟩) :
    RDret weth9Bytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (weth9ShortStringAbi (weth9StringSlotWord σ I ⟨0⟩)) := by
  obtain ⟨_, _, h187⟩ := weth9NameShortLoadReach187 (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz4 hsize hsel hne hlt31
  exact weth9NameShortEncoder (weth9StringSlotWord σ I ⟨0⟩) hne hlt31 h187

end Benchmarks.WETH9
