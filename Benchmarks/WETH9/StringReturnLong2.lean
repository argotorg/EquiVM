import Benchmarks.WETH9.StringReturnLong

/-!
# WETH9 dynamic-string getter — LONG case ABI return encoder (`len ≥ 32`)

`Benchmarks/WETH9/StringReturnLong.lean` drove the getter's long branch through the
storage→memory copy loop to the ABI-return encoder entry (pc 187), leaving the string data words
in memory at `0xa0` (`weth9NameLongReach187`, memory `weth9LongFinalMem`).

This module finishes the long case: it drives the symbolic-offset ABI encoder (pc 187 → `RETURN`),
including the second **mem→mem copy loop** (pc 221–244, `wc` iterations) and the trailing-word
zero-mask (pc 245–289), and concludes `RDret … (weth9LongStringAbi σ I)` — the ABI encoding
`offset(0x20) ‖ len ‖ dataWords(last masked)`.

It mirrors the SHORT encoder `weth9NameShortEncoder` (`StringReturn.lean`) generalized to `wc`
data words, and reuses the Loop-1 fuel-recursion template + symbolic cost witnesses from
`StringReturnLong.lean`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000

namespace Benchmarks.WETH9

/-! ## Word-concatenation helper

The ABI data region is a chronological concatenation of 32-byte words.  `wordConcat f idx n`
concatenates `n` words `f idx, …, f (idx+n-1)`, right-nested (matching `byteArray_readWithPadding_split`). -/

/-- Right-nested concatenation of the 32-byte encodings of `f idx, …, f (idx+n-1)`. -/
noncomputable def wordConcat (f : Nat → UInt256) (idx : Nat) : Nat → ByteArray
  | 0 => ByteArray.empty
  | n + 1 => (f idx).toByteArray ++ wordConcat f (idx + 1) n

@[simp] theorem wordConcat_zero (f : Nat → UInt256) (idx : Nat) :
    wordConcat f idx 0 = ByteArray.empty := rfl

theorem wordConcat_succ (f : Nat → UInt256) (idx n : Nat) :
    wordConcat f idx (n + 1) = (f idx).toByteArray ++ wordConcat f (idx + 1) n := rfl

/-- Append-at-end: peel the last word off the front-nested concatenation. -/
theorem wordConcat_append_last (f : Nat → UInt256) :
    ∀ (n idx : Nat),
      wordConcat f idx (n + 1) = wordConcat f idx n ++ (f (idx + n)).toByteArray
  | 0, idx => by
      rw [wordConcat_succ, wordConcat_zero, wordConcat_zero, empty_append, Nat.add_zero,
        ByteArray.append_empty]
  | n + 1, idx => by
      rw [wordConcat_succ, wordConcat_append_last f n (idx + 1), wordConcat_succ,
        ByteArray.append_assoc, show idx + 1 + n = idx + (n + 1) from by omega]

/-- `wordConcat` only depends on `f` at indices `idx, …, idx+n-1`. -/
theorem wordConcat_congr (f g : Nat → UInt256) :
    ∀ (n idx : Nat), (∀ k, k < n → f (idx + k) = g (idx + k)) →
      wordConcat f idx n = wordConcat g idx n
  | 0, _, _ => rfl
  | n + 1, idx, h => by
      rw [wordConcat_succ, wordConcat_succ]
      have h0 : f idx = g idx := by simpa using h 0 (Nat.zero_lt_succ n)
      rw [h0, wordConcat_congr f g n (idx + 1) (by
        intro k hk
        have := h (k + 1) (Nat.succ_lt_succ hk)
        simpa [Nat.add_assoc, Nat.add_comm 1 k] using this)]

/-- Read a run of `n` words from memory as a `wordConcat`, given each word reads back. -/
theorem readWithPadding_wordConcat (mem : ByteArray) (f : Nat → UInt256) (base : Nat) :
    ∀ (n idx : Nat), 32 * n < 2 ^ 64 → base + 32 * idx + 32 * n ≤ mem.size →
      (∀ k, k < n → mem.readWithPadding (base + 32 * (idx + k)) 32 = (f (idx + k)).toByteArray) →
      mem.readWithPadding (base + 32 * idx) (32 * n) = wordConcat f idx n
  | 0, idx, _, _, _ => by
      rw [Nat.mul_zero, byteArray_readWithPadding_zero, wordConcat_zero]
  | n + 1, idx, hlt, hin, hread => by
      have hsplit :
          mem.readWithPadding (base + 32 * idx) (32 + 32 * n) =
            mem.readWithPadding (base + 32 * idx) 32 ++
              mem.readWithPadding (base + 32 * idx + 32) (32 * n) := by
        rcases Nat.eq_zero_or_pos n with hn | hn
        · subst hn
          rw [Nat.mul_zero, Nat.add_zero, byteArray_readWithPadding_zero, ByteArray.append_empty]
        · exact byteArray_readWithPadding_split mem (base + 32 * idx) 32 (32 * n)
            (by norm_num) (by omega) (by norm_num) (by omega) (by omega)
            (by rw [Nat.mul_succ] at hin; omega)
      rw [Nat.mul_succ, Nat.add_comm (32 * n) 32, hsplit, wordConcat_succ]
      have hw0 : mem.readWithPadding (base + 32 * idx) 32 = (f idx).toByteArray := by
        have := hread 0 (Nat.zero_lt_succ n)
        simpa using this
      have htail : mem.readWithPadding (base + 32 * idx + 32) (32 * n) =
          wordConcat f (idx + 1) n := by
        have hbase' : base + 32 * idx + 32 = base + 32 * (idx + 1) := by ring
        rw [hbase']
        exact readWithPadding_wordConcat mem f base n (idx + 1)
          (by rw [Nat.mul_succ] at hlt; omega)
          (by rw [Nat.mul_succ] at hin; rw [show base + 32 * (idx + 1) = base + 32 * idx + 32 from by ring]; omega)
          (by intro k hk
              have := hread (k + 1) (Nat.succ_lt_succ hk)
              rw [show idx + 1 + k = idx + (k + 1) from by omega]
              rw [show base + 32 * (idx + (k + 1)) = base + 32 * (idx + 1 + k) from by ring] at *
              exact this)
      rw [hw0, htail]

/-! ## Data-word characterization

The `k`-th string data word is the storage word copied by Loop-1 into `mem[0xa0+32·k]`.  We extend
the Loop-1 read-preservation lemmas (`weth9LongFinalMem_read64/_read128`) to the data region. -/

/-- The `k`-th long-string data word: the storage word copied by Loop-1 into `mem[0xa0 + 32·k]`. -/
noncomputable def weth9LongDataWordAt (σ : AccountMap) (I : ExecutionEnv) (k : Nat) : UInt256 :=
  weth9LongStorageWord σ I (weth9LongGeneratedLoopState σ I k).slot

/-- Loop-1 memory at step `i` holds data word `k` at `0xa0 + 32·k` for every `k < i`. -/
theorem weth9LongMem_readData_of_bound {σ : AccountMap} {I : ExecutionEnv} (k : Nat) :
    ∀ i : Nat, k < i → 160 + 32 * i < UInt256.size →
      (weth9LongGeneratedLoopState σ I i).mem.readWithPadding (160 + 32 * k) 32 =
        (weth9LongDataWordAt σ I k).toByteArray
  | 0, hki, _ => absurd hki (by omega)
  | i + 1, hki, hbound => by
      have hprevPtr : (weth9LongGeneratedLoopState σ I i).ptr.toNat = 160 + 32 * i :=
        weth9LongPtr_toNat_of_bound i (by omega)
      have hprevSize : (weth9LongGeneratedLoopState σ I i).mem.size = 160 + 32 * i :=
        weth9LongMem_size_of_bound i (by omega)
      rw [weth9LongGeneratedLoopState_succ]
      show (weth9LongCopyMem (weth9LongGeneratedLoopState σ I i).mem
        (weth9LongGeneratedLoopState σ I i).ptr _).readWithPadding (160 + 32 * k) 32 = _
      rw [weth9LongCopyMem]
      rcases Nat.lt_or_ge k i with hlt | hge
      · rw [writeWord_read_preserved _ _ (160 + 32 * k) _
            (by rw [hprevPtr, hprevSize]; exact lt_usize _ (by norm_num))
            (Or.inl ⟨by rw [hprevPtr]; omega, by rw [hprevSize]; omega⟩)]
        exact weth9LongMem_readData_of_bound k i hlt (by omega)
      · have hk : k = i := by omega
        subst hk
        rw [hprevPtr, writeWord_read_back _ _ _ (by rw [hprevSize]; exact lt_usize _ (by norm_num))]
        rfl

/-- The finished Loop-1 memory holds data word `k` at `0xa0 + 32·k` for every `k ≤ wc-1`. -/
theorem weth9LongFinalMem_readData {σ : AccountMap} {I : ExecutionEnv} (k : Nat)
    (hk : k ≤ weth9LongWC σ I) :
    (weth9LongFinalMem σ I).readWithPadding (160 + 32 * k) 32 =
      (weth9LongDataWordAt σ I k).toByteArray := by
  have hbnd := weth9LongWC_size_bound σ I
  have hptr : (weth9LongGeneratedLoopState σ I (weth9LongWC σ I)).ptr.toNat =
      160 + 32 * weth9LongWC σ I := weth9LongPtr_toNat_of_bound _ (by omega)
  have hsize : (weth9LongGeneratedLoopState σ I (weth9LongWC σ I)).mem.size =
      160 + 32 * weth9LongWC σ I := weth9LongMem_size_of_bound _ (by omega)
  rw [weth9LongFinalMem, weth9LongCopyMem]
  rcases Nat.lt_or_ge k (weth9LongWC σ I) with hlt | hge
  · rw [writeWord_read_preserved _ _ (160 + 32 * k) _
        (by rw [hptr, hsize]; exact lt_usize _ (by norm_num))
        (Or.inl ⟨by rw [hptr]; omega, by rw [hsize]; omega⟩)]
    exact weth9LongMem_readData_of_bound k (weth9LongWC σ I) hlt (by omega)
  · have hk' : k = weth9LongWC σ I := by omega
    subst hk'
    rw [hptr, writeWord_read_back _ _ _ (by rw [hsize]; exact lt_usize _ (by norm_num))]
    rfl

/-! ## The long-string ABI encoding

Mirrors `weth9ShortStringAbi` generalized to `wc = wc-1 + 1` data words: offset word `0x20`, the
length word, then `wc-1` unmasked data words and the trailing masked word.  When `len` is a multiple
of `32` the trailing word is full (no masking), so `weth9LongMaskWord` is a `land`-of-`lnot` only in
the partial case. -/

/-- The trailing data word as returned: masked (`~(2^(8·(32-31&len))-1) & data`) when `len` is not a
    multiple of 32, else the full last data word (the mask store is skipped by the runtime). -/
noncomputable def weth9LongMaskWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  if UInt256.land ⟨31⟩ (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)) = ⟨0⟩ then
    weth9LongDataWordAt σ I (weth9LongWC σ I)
  else
    UInt256.land
      (UInt256.lnot (UInt256.sub
        (UInt256.exp ⟨256⟩ (UInt256.sub ⟨32⟩
          (UInt256.land ⟨31⟩ (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩))))) ⟨1⟩))
      (weth9LongDataWordAt σ I (weth9LongWC σ I))

/-- The ABI encoding a long-string getter returns: `offset 0x20 ‖ len ‖ (wc-1) data words ‖ masked
    last word`. -/
noncomputable def weth9LongStringAbi (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  UInt256.toByteArray ⟨32⟩ ++
    (UInt256.toByteArray (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)) ++
      (wordConcat (weth9LongDataWordAt σ I) 0 (weth9LongWC σ I) ++
        UInt256.toByteArray (weth9LongMaskWord σ I)))

/-! ## Free-pointer / active-words arithmetic

`newFp = 0xa0 + 32·wc = 0xa0 + 32·(wc-1) + 32 = 0xc0 + 32·(wc-1)`, and equals `weth9LongFinalMem`'s
size.  The active words after the copy loop are `6 + (wc-1)`. -/

/-- `len ≥ 32` (from the long-branch hypothesis). -/
theorem weth9LongLen_ge32 {σ : AccountMap} {I : ExecutionEnv}
    (hge31 : UInt256.lt ⟨31⟩ (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)) ≠ ⟨0⟩) :
    31 < (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat := by
  simpa [show (⟨31⟩ : UInt256).toNat = 31 from by decide] using ult_ne_zero_toNat_lt hge31

/-- Word count as `Nat`: `(weth9StringWC H).toNat = wc-1 + 1`. -/
theorem weth9StringWC_toNat {σ : AccountMap} {I : ExecutionEnv}
    (hpos : 1 ≤ (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat) :
    (weth9StringWC (weth9StringSlotWord σ I ⟨0⟩)).toNat = weth9LongWC σ I + 1 := by
  set H := weth9StringSlotWord σ I ⟨0⟩ with hH
  have hlt := weth9StringLen_toNat_lt_sign H
  rw [weth9StringWC, udiv_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
    uadd_toNat, show (⟨31⟩ : UInt256).toNat = 31 from by decide,
    Nat.mod_eq_of_lt (by norm_num [UInt256.size]; omega), weth9LongWC, hH]
  rw [show (weth9StringLen H).toNat + 31 = ((weth9StringLen H).toNat - 1) + 32 from by omega,
    Nat.add_div_right _ (by norm_num)]

/-- `newFp.toNat = 0xc0 + 32·(wc-1) = 0xa0 + 32·wc`, equal to the copied memory's size. -/
theorem weth9StringNewFp_toNat_long {σ : AccountMap} {I : ExecutionEnv}
    (hpos : 1 ≤ (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat) :
    (weth9StringNewFp (weth9StringSlotWord σ I ⟨0⟩)).toNat = 192 + 32 * weth9LongWC σ I := by
  set H := weth9StringSlotWord σ I ⟨0⟩ with hH
  have hwc := weth9StringWC_toNat (σ := σ) (I := I) hpos
  have hbnd := weth9LongWC_size_bound σ I
  have hmul : (UInt256.mul ⟨32⟩ (weth9StringWC H)).toNat = 32 * (weth9LongWC σ I + 1) := by
    rw [u256_mul_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide, hwc,
      Nat.mod_eq_of_lt (by omega)]
  have hinner : ((⟨128⟩ : UInt256) + UInt256.mul ⟨32⟩ (weth9StringWC H)).toNat =
      128 + 32 * (weth9LongWC σ I + 1) := by
    rw [uadd_toNat, hmul, show (⟨128⟩ : UInt256).toNat = 128 from by decide,
      Nat.mod_eq_of_lt (by omega)]
  rw [weth9StringNewFp, uadd_toNat, hinner, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
    Nat.mod_eq_of_lt (by omega)]
  omega

/-- `weth9LongFinalMem`'s size in the `192 + 32·(wc-1)` form (matching `newFp.toNat`). -/
theorem weth9LongFinalMem_size' (σ : AccountMap) (I : ExecutionEnv) :
    (weth9LongFinalMem σ I).size = 192 + 32 * weth9LongWC σ I := by
  rw [weth9LongFinalMem_size]; omega

/-- An end-write at offset `32·aw` (extending memory by one word) bumps active words to `aw+1`. -/
theorem machineState_M_endWrite (aw : Nat) : MachineState.M aw (32 * aw) 32 = aw + 1 := by
  show max aw ((32 * aw + 32 + 31) / 32) = aw + 1
  rw [show 32 * aw + 32 + 31 = 32 * (aw + 1) + 31 from by ring,
    Nat.mul_add_div (by norm_num), show (31 : Nat) / 32 = 0 from by norm_num]
  omega

/-- A read fully inside memory (`f+l ≤ 32·s`) does not change active words. -/
theorem machineState_M_inBounds {s f l : Nat} (h : f + l ≤ 32 * s) : MachineState.M s f l = s := by
  rcases Nat.eq_zero_or_pos l with hl | hl
  · simp [MachineState.M, hl]
  · obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
    show max s ((f + (l' + 1) + 31) / 32) = s
    have hlt : (f + (l' + 1) + 31) / 32 < s + 1 := by
      rw [Nat.div_lt_iff_lt_mul (by norm_num)]; omega
    omega

/-- Symbolic `¬ off ≥ aw·32` from `off < aw.toNat·32` (no `aw·32` overflow). -/
theorem wordMul32_not_ge_of_lt {off aw : UInt256} (hlt : off.toNat < aw.toNat * 32)
    (hNoWrap : aw.toNat * 32 < UInt256.size) : ¬ off ≥ aw * ⟨32⟩ := by
  have hmul : (aw * (⟨32⟩ : UInt256)).toNat = aw.toNat * 32 := by
    simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using
      umul_toNat (a := aw) (b := (⟨32⟩ : UInt256)) hNoWrap
  intro hge
  have h : off.toNat ≥ (aw * (⟨32⟩ : UInt256)).toNat := hge
  rw [hmul] at h; omega

/-- Loop-1 active words after `i` copies: `5 + i` (each copy is an at-end word write). -/
theorem weth9LongGeneratedLoopState_aw_toNat {σ : AccountMap} {I : ExecutionEnv} :
    ∀ i : Nat, 160 + 32 * i < UInt256.size →
      (weth9LongGeneratedLoopState σ I i).aw.toNat = 5 + i
  | 0, _ => by
      rw [weth9LongGeneratedLoopState_zero]
      exact ulit_toNat' 5 (by norm_num [UInt256.size])
  | i + 1, hb => by
      have hprevAw : (weth9LongGeneratedLoopState σ I i).aw.toNat = 5 + i :=
        weth9LongGeneratedLoopState_aw_toNat i (by omega)
      have hprevPtr : (weth9LongGeneratedLoopState σ I i).ptr.toNat = 160 + 32 * i :=
        weth9LongPtr_toNat_of_bound i (by omega)
      rw [weth9LongGeneratedLoopState_succ]
      show (UInt256.ofNat (MachineState.M (weth9LongGeneratedLoopState σ I i).aw.toNat
        (weth9LongGeneratedLoopState σ I i).ptr.toNat 32)).toNat = 5 + (i + 1)
      rw [hprevAw, hprevPtr, show (160 + 32 * i : Nat) = 32 * (5 + i) from by ring,
        machineState_M_endWrite, ulit_toNat' _ (by omega)]
      omega

/-- Active words after the Loop-1 copy: `6 + (wc-1)` (equals `newFp.toNat / 32`). -/
theorem weth9LongFinalAw_toNat (σ : AccountMap) (I : ExecutionEnv) :
    (weth9LongFinalAw σ I).toNat = 6 + weth9LongWC σ I := by
  have hbnd := weth9LongWC_size_bound σ I
  have haw : (weth9LongGeneratedLoopState σ I (weth9LongWC σ I)).aw.toNat = 5 + weth9LongWC σ I :=
    weth9LongGeneratedLoopState_aw_toNat _ (by omega)
  have hptr : (weth9LongGeneratedLoopState σ I (weth9LongWC σ I)).ptr.toNat =
      160 + 32 * weth9LongWC σ I := weth9LongPtr_toNat_of_bound _ (by omega)
  rw [weth9LongFinalAw, haw, hptr, show (160 + 32 * weth9LongWC σ I : Nat) =
    32 * (5 + weth9LongWC σ I) from by ring, machineState_M_endWrite, ulit_toNat' _ (by omega)]
  omega

/-- The copied memory's size equals the free pointer `newFp` (the object fills `[0, newFp)`). -/
theorem weth9LongFinalMem_size_eq_newFp {σ : AccountMap} {I : ExecutionEnv}
    (hpos : 1 ≤ (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat) :
    (weth9LongFinalMem σ I).size = (weth9StringNewFp (weth9StringSlotWord σ I ⟨0⟩)).toNat := by
  rw [weth9LongFinalMem_size', weth9StringNewFp_toNat_long hpos]

/-! ## Encoder memory states (pc 187 → loop head)

`MemA` = finished object memory with the ABI offset word `0x20` written at `newFp`; `MemB` = also the
length word at `newFp+0x20`.  Both writes are at the running end, so the free pointer (`0x40`), length
word (`0x80`), and the source data region `[0xa0, newFp)` all survive. -/

/-- Object memory with the ABI offset word `0x20` at `newFp`. -/
noncomputable def weth9LongEncMemA (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  writeWord (weth9LongFinalMem σ I) (weth9StringNewFp (weth9StringSlotWord σ I ⟨0⟩)).toNat ⟨32⟩

/-- `MemA` plus the ABI length word at `newFp+0x20`. -/
noncomputable def weth9LongEncMemB (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  writeWord (weth9LongEncMemA σ I)
    ((weth9StringNewFp (weth9StringSlotWord σ I ⟨0⟩)).toNat + 32)
    (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩))

/-- Loop-2 memory after `j` mem→mem copies: `MemB` with data words `0..j-1` written into the ABI
    data region at `newFp+0x40 + 32·k = 0x100 + 32·(wc-1) + 32·k`. -/
noncomputable def weth9Long2Mem (σ : AccountMap) (I : ExecutionEnv) : Nat → ByteArray
  | 0 => weth9LongEncMemB σ I
  | j + 1 =>
      writeWord (weth9Long2Mem σ I j) (256 + 32 * weth9LongWC σ I + 32 * j)
        (weth9LongDataWordAt σ I j)

theorem weth9Long2Mem_zero (σ : AccountMap) (I : ExecutionEnv) :
    weth9Long2Mem σ I 0 = weth9LongEncMemB σ I := rfl

theorem weth9Long2Mem_succ (σ : AccountMap) (I : ExecutionEnv) (j : Nat) :
    weth9Long2Mem σ I (j + 1) =
      writeWord (weth9Long2Mem σ I j) (256 + 32 * weth9LongWC σ I + 32 * j)
        (weth9LongDataWordAt σ I j) := rfl

section EncMem
variable {σ : AccountMap} {I : ExecutionEnv}
  (hpos : 1 ≤ (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat)
include hpos

theorem weth9LongEncMemA_size : (weth9LongEncMemA σ I).size =
    (weth9StringNewFp (weth9StringSlotWord σ I ⟨0⟩)).toNat + 32 := by
  rw [weth9LongEncMemA, writeWord_size _ _ _
    (by rw [weth9LongFinalMem_size_eq_newFp hpos]; exact lt_usize _ (by norm_num)),
    weth9LongFinalMem_size_eq_newFp hpos]; omega

theorem weth9LongEncMemA_read64 : (weth9LongEncMemA σ I).readWithPadding 64 32 =
    (weth9StringNewFp (weth9StringSlotWord σ I ⟨0⟩)).toByteArray := by
  rw [weth9LongEncMemA]
  exact weth9EncLowRead (weth9LongFinalMem_read64 σ I)
    (by rw [weth9LongFinalMem_size_eq_newFp hpos, weth9StringNewFp_toNat_long hpos]; omega)
    (by rw [weth9LongFinalMem_size_eq_newFp hpos])
    (by rw [weth9LongFinalMem_size_eq_newFp hpos]; exact lt_usize _ (by norm_num))
    (by rw [weth9StringNewFp_toNat_long hpos]; omega)

theorem weth9LongEncMemA_read128 : (weth9LongEncMemA σ I).readWithPadding 128 32 =
    (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toByteArray := by
  rw [weth9LongEncMemA]
  exact weth9EncLowRead (weth9LongFinalMem_read128 σ I)
    (by rw [weth9LongFinalMem_size_eq_newFp hpos, weth9StringNewFp_toNat_long hpos]; omega)
    (by rw [weth9LongFinalMem_size_eq_newFp hpos])
    (by rw [weth9LongFinalMem_size_eq_newFp hpos]; exact lt_usize _ (by norm_num))
    (by rw [weth9StringNewFp_toNat_long hpos]; omega)

theorem weth9LongEncMemA_readData (k : Nat) (hk : k ≤ weth9LongWC σ I) :
    (weth9LongEncMemA σ I).readWithPadding (160 + 32 * k) 32 =
      (weth9LongDataWordAt σ I k).toByteArray := by
  rw [weth9LongEncMemA]
  exact weth9EncLowRead (weth9LongFinalMem_readData k hk)
    (by rw [weth9LongFinalMem_size_eq_newFp hpos, weth9StringNewFp_toNat_long hpos]; omega)
    (by rw [weth9LongFinalMem_size_eq_newFp hpos])
    (by rw [weth9LongFinalMem_size_eq_newFp hpos]; exact lt_usize _ (by norm_num))
    (by rw [weth9StringNewFp_toNat_long hpos]; omega)

theorem weth9LongEncMemA_readOffset : (weth9LongEncMemA σ I).readWithPadding
    (weth9StringNewFp (weth9StringSlotWord σ I ⟨0⟩)).toNat 32 = UInt256.toByteArray ⟨32⟩ := by
  rw [weth9LongEncMemA]
  exact writeWord_read_back _ _ _
    (by rw [weth9LongFinalMem_size_eq_newFp hpos]; exact lt_usize _ (by norm_num))

theorem weth9LongEncMemB_size : (weth9LongEncMemB σ I).size =
    (weth9StringNewFp (weth9StringSlotWord σ I ⟨0⟩)).toNat + 64 := by
  rw [weth9LongEncMemB, writeWord_size _ _ _
    (by rw [weth9LongEncMemA_size hpos]; exact lt_usize _ (by norm_num)),
    weth9LongEncMemA_size hpos]; omega

theorem weth9LongEncMemB_read64 : (weth9LongEncMemB σ I).readWithPadding 64 32 =
    (weth9StringNewFp (weth9StringSlotWord σ I ⟨0⟩)).toByteArray := by
  rw [weth9LongEncMemB]
  exact weth9EncLowRead (weth9LongEncMemA_read64 hpos)
    (by rw [weth9LongEncMemA_size hpos, weth9StringNewFp_toNat_long hpos]; omega)
    (by rw [weth9LongEncMemA_size hpos])
    (by rw [weth9LongEncMemA_size hpos]; exact lt_usize _ (by norm_num))
    (by rw [weth9StringNewFp_toNat_long hpos]; omega)

theorem weth9LongEncMemB_read128 : (weth9LongEncMemB σ I).readWithPadding 128 32 =
    (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toByteArray := by
  rw [weth9LongEncMemB]
  exact weth9EncLowRead (weth9LongEncMemA_read128 hpos)
    (by rw [weth9LongEncMemA_size hpos, weth9StringNewFp_toNat_long hpos]; omega)
    (by rw [weth9LongEncMemA_size hpos])
    (by rw [weth9LongEncMemA_size hpos]; exact lt_usize _ (by norm_num))
    (by rw [weth9StringNewFp_toNat_long hpos]; omega)

theorem weth9LongEncMemB_readData (k : Nat) (hk : k ≤ weth9LongWC σ I) :
    (weth9LongEncMemB σ I).readWithPadding (160 + 32 * k) 32 =
      (weth9LongDataWordAt σ I k).toByteArray := by
  rw [weth9LongEncMemB]
  exact weth9EncLowRead (weth9LongEncMemA_readData hpos k hk)
    (by rw [weth9LongEncMemA_size hpos, weth9StringNewFp_toNat_long hpos]; omega)
    (by rw [weth9LongEncMemA_size hpos])
    (by rw [weth9LongEncMemA_size hpos]; exact lt_usize _ (by norm_num))
    (by rw [weth9StringNewFp_toNat_long hpos]; omega)

theorem weth9LongEncMemB_readOffset : (weth9LongEncMemB σ I).readWithPadding
    (weth9StringNewFp (weth9StringSlotWord σ I ⟨0⟩)).toNat 32 = UInt256.toByteArray ⟨32⟩ := by
  rw [weth9LongEncMemB]
  exact weth9EncLowRead (weth9LongEncMemA_readOffset hpos)
    (by rw [weth9LongEncMemA_size hpos])
    (by rw [weth9LongEncMemA_size hpos])
    (by rw [weth9LongEncMemA_size hpos]; exact lt_usize _ (by norm_num))
    (le_refl _)

theorem weth9LongEncMemB_readLen : (weth9LongEncMemB σ I).readWithPadding
    ((weth9StringNewFp (weth9StringSlotWord σ I ⟨0⟩)).toNat + 32) 32 =
      (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toByteArray := by
  rw [weth9LongEncMemB]
  exact writeWord_read_back _ _ _
    (by rw [weth9LongEncMemA_size hpos]; exact lt_usize _ (by norm_num))

/-- Loop-2 memory size after `j` copies: `0x100 + 32·(wc-1) + 32·j`. -/
theorem weth9Long2Mem_size :
    ∀ j : Nat, (weth9Long2Mem σ I j).size = 256 + 32 * weth9LongWC σ I + 32 * j
  | 0 => by
      rw [weth9Long2Mem_zero, weth9LongEncMemB_size hpos, weth9StringNewFp_toNat_long hpos]; omega
  | j + 1 => by
      rw [weth9Long2Mem_succ,
        writeWord_size _ _ _ (by rw [weth9Long2Mem_size j, Nat.sub_self]; exact lt_usize 0 (by norm_num)),
        weth9Long2Mem_size j]; omega

/-- Any read window below the ABI data region survives every Loop-2 copy. -/
theorem weth9Long2Mem_read_low (r : Nat) (hr : r + 32 ≤ 256 + 32 * weth9LongWC σ I) :
    ∀ j : Nat, (weth9Long2Mem σ I j).readWithPadding r 32 =
      (weth9LongEncMemB σ I).readWithPadding r 32
  | 0 => by rw [weth9Long2Mem_zero]
  | j + 1 => by
      rw [weth9Long2Mem_succ, writeWord_read_preserved _ _ r _
        (by rw [weth9Long2Mem_size hpos j, Nat.sub_self]; exact lt_usize 0 (by norm_num))
        (Or.inl ⟨by omega, by rw [weth9Long2Mem_size hpos j]; omega⟩)]
      exact weth9Long2Mem_read_low r hr j

theorem weth9Long2Mem_read64 (j : Nat) :
    (weth9Long2Mem σ I j).readWithPadding 64 32 =
      (weth9StringNewFp (weth9StringSlotWord σ I ⟨0⟩)).toByteArray := by
  rw [weth9Long2Mem_read_low hpos 64 (by omega) j, weth9LongEncMemB_read64 hpos]

theorem weth9Long2Mem_readOffset (j : Nat) :
    (weth9Long2Mem σ I j).readWithPadding (weth9StringNewFp (weth9StringSlotWord σ I ⟨0⟩)).toNat 32 =
      UInt256.toByteArray ⟨32⟩ := by
  rw [weth9Long2Mem_read_low hpos _ (by rw [weth9StringNewFp_toNat_long hpos]; omega) j,
    weth9LongEncMemB_readOffset hpos]

theorem weth9Long2Mem_readLen (j : Nat) :
    (weth9Long2Mem σ I j).readWithPadding
      ((weth9StringNewFp (weth9StringSlotWord σ I ⟨0⟩)).toNat + 32) 32 =
      (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toByteArray := by
  rw [weth9Long2Mem_read_low hpos _ (by rw [weth9StringNewFp_toNat_long hpos]; omega) j,
    weth9LongEncMemB_readLen hpos]

theorem weth9Long2Mem_readSrc (j k : Nat) (hk : k ≤ weth9LongWC σ I) :
    (weth9Long2Mem σ I j).readWithPadding (160 + 32 * k) 32 =
      (weth9LongDataWordAt σ I k).toByteArray := by
  rw [weth9Long2Mem_read_low hpos (160 + 32 * k) (by omega) j, weth9LongEncMemB_readData hpos k hk]

/-- Loop-2 memory holds copied data word `k` at `newFp+0x40 + 32·k` for every `k < j`. -/
theorem weth9Long2Mem_readDest (k : Nat) :
    ∀ j : Nat, k < j → (weth9Long2Mem σ I j).readWithPadding (256 + 32 * weth9LongWC σ I + 32 * k) 32 =
      (weth9LongDataWordAt σ I k).toByteArray
  | 0, hkj => absurd hkj (by omega)
  | j + 1, hkj => by
      rw [weth9Long2Mem_succ]
      rcases Nat.lt_or_ge k j with hlt | hge
      · rw [writeWord_read_preserved _ _ (256 + 32 * weth9LongWC σ I + 32 * k) _
          (by rw [weth9Long2Mem_size hpos j, Nat.sub_self]; exact lt_usize 0 (by norm_num))
          (Or.inl ⟨by omega, by rw [weth9Long2Mem_size hpos j]; omega⟩)]
        exact weth9Long2Mem_readDest k j hlt
      · have hk : k = j := by omega
        subst hk
        rw [writeWord_read_back _ _ _
          (by rw [weth9Long2Mem_size hpos k, Nat.sub_self]; exact lt_usize 0 (by norm_num))]

end EncMem

/-- The Loop-2 head/exit stack at counter `i` (offset into the ABI data region). -/
def weth9Long2LoopStack (σ : AccountMap) (I : ExecutionEnv) (i : UInt256) : List UInt256 :=
  [i, (⟨128⟩ : UInt256) + ⟨32⟩, weth9StringNewFp (weth9StringSlotWord σ I ⟨0⟩) + ⟨64⟩,
   weth9StringLen (weth9StringSlotWord σ I ⟨0⟩), weth9StringLen (weth9StringSlotWord σ I ⟨0⟩),
   (⟨128⟩ : UInt256) + ⟨32⟩, weth9StringNewFp (weth9StringSlotWord σ I ⟨0⟩) + ⟨64⟩,
   weth9StringNewFp (weth9StringSlotWord σ I ⟨0⟩), weth9StringNewFp (weth9StringSlotWord σ I ⟨0⟩),
   ⟨128⟩, ⟨187⟩, weth9SelWord I]

set_option maxHeartbeats 8000000 in
/-- Setup (pc 187 → 221): write the ABI offset + length words and reach the Loop-2 head. -/
theorem weth9NameLong2ReachLoopHead {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = weth9Bytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (weth9SelBytes 0))
    (hge31 : UInt256.lt ⟨31⟩ (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)) ≠ ⟨0⟩)
    (hfit : 96 + 32 * weth9LongWC σ I < 2 ^ 64) :
    ∃ k C, RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨221⟩
      (weth9Long2LoopStack σ I ⟨0⟩)
      (weth9Long2Mem σ I 0) (UInt256.ofNat (8 + weth9LongWC σ I)) ByteArray.empty (cA, σ) k C := by
  have hpos : 1 ≤ (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat := by
    have := weth9LongLen_ge32 hge31; omega
  have h66 : (2 : Nat) ^ 66 < UInt256.size := by norm_num [UInt256.size]
  have hbig : 288 + 64 * weth9LongWC σ I < UInt256.size := by omega
  have hfpN : (weth9StringNewFp (weth9StringSlotWord σ I ⟨0⟩)).toNat = 192 + 32 * weth9LongWC σ I :=
    weth9StringNewFp_toNat_long hpos
  have haddr32 : ((weth9StringNewFp (weth9StringSlotWord σ I ⟨0⟩)) + ⟨32⟩).toNat =
      (weth9StringNewFp (weth9StringSlotWord σ I ⟨0⟩)).toNat + 32 := by
    rw [uadd_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
      Nat.mod_eq_of_lt (by rw [hfpN]; omega)]
  obtain ⟨_, _, h187⟩ := weth9NameLongReach187 (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz4 hsize hsel hge31
  have h221 := evm_run h187 with [
    jumpdest, push1 ⟨64⟩, dup1,
    raw mload _ (weth9StringNewFp (weth9StringSlotWord σ I ⟨0⟩)) (UInt256.ofNat (6 + weth9LongWC σ I))
      (by native_decide) weth9MloadCostSpec
      (mloadWordValue_of_readWithPadding
        (by rw [weth9LongFinalMem_size', show (⟨64⟩ : UInt256).toNat = 64 from by decide]; omega)
        (wordMul32_not_ge_of_lt (by rw [weth9LongFinalAw_toNat, show (⟨64⟩ : UInt256).toNat = 64 from by decide]; omega)
          (by rw [weth9LongFinalAw_toNat]; omega))
        (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; exact weth9LongFinalMem_read64 σ I))
      (by rw [weth9LongFinalAw_toNat, show (⟨64⟩ : UInt256).toNat = 64 from by decide,
        machineState_M_inBounds (show (64 : Nat) + 32 ≤ 32 * (6 + weth9LongWC σ I) from by omega)])
      (by evm_ov),
    push1 ⟨32⟩, dup1, dup3,
    raw mstore _ (weth9LongEncMemA σ I) (UInt256.ofNat (7 + weth9LongWC σ I))
      (by native_decide) weth9MstoreCostSpec rfl
      (by rw [ulit_toNat' _ (by omega), hfpN,
        show (192 + 32 * weth9LongWC σ I : Nat) = 32 * (6 + weth9LongWC σ I) from by ring,
        machineState_M_endWrite]; congr 1; omega) (by evm_ov),
    dup4,
    raw mload _ (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)) (UInt256.ofNat (7 + weth9LongWC σ I))
      (by native_decide) weth9MloadCostSpec
      (mloadWordValue_of_readWithPadding
        (by rw [weth9LongEncMemA_size hpos, hfpN, show (⟨128⟩ : UInt256).toNat = 128 from by decide]; omega)
        (wordMul32_not_ge_of_lt (by rw [ulit_toNat' _ (by omega), show (⟨128⟩ : UInt256).toNat = 128 from by decide]; omega)
          (by rw [ulit_toNat' _ (by omega)]; omega))
        (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; exact weth9LongEncMemA_read128 hpos))
      (by rw [ulit_toNat' _ (by omega), show (⟨128⟩ : UInt256).toNat = 128 from by decide,
        machineState_M_inBounds (show (128 : Nat) + 32 ≤ 32 * (7 + weth9LongWC σ I) from by omega)])
      (by evm_ov),
    dup2, dup4, add,
    raw mstore _ (weth9LongEncMemB σ I) (UInt256.ofNat (8 + weth9LongWC σ I))
      (by native_decide) weth9MstoreCostSpec
      (by rw [weth9LongEncMemB, Reasoning.Theory.writeWord, haddr32])
      (by rw [ulit_toNat' _ (by omega), haddr32, hfpN,
        show (192 + 32 * weth9LongWC σ I + 32 : Nat) = 32 * (7 + weth9LongWC σ I) from by ring,
        machineState_M_endWrite]; congr 1; omega) (by evm_ov),
    dup4,
    raw mload _ (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)) (UInt256.ofNat (8 + weth9LongWC σ I))
      (by native_decide) weth9MloadCostSpec
      (mloadWordValue_of_readWithPadding
        (by rw [weth9LongEncMemB_size hpos, hfpN, show (⟨128⟩ : UInt256).toNat = 128 from by decide]; omega)
        (wordMul32_not_ge_of_lt (by rw [ulit_toNat' _ (by omega), show (⟨128⟩ : UInt256).toNat = 128 from by decide]; omega)
          (by rw [ulit_toNat' _ (by omega)]; omega))
        (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; exact weth9LongEncMemB_read128 hpos))
      (by rw [ulit_toNat' _ (by omega), show (⟨128⟩ : UInt256).toNat = 128 from by decide,
        machineState_M_inBounds (show (128 : Nat) + 32 ≤ 32 * (8 + weth9LongWC σ I) from by omega)])
      (by evm_ov),
    swap2, swap3, dup4, swap3, swap1, dup4, add, swap2, dup6, add, swap1,
    dup1, dup4, dup4, push1 ⟨0⟩]
  rw [weth9Long2Mem_zero, weth9Long2LoopStack]
  exact ⟨_, _, h221⟩

set_option maxHeartbeats 8000000 in
/-- One Loop-2 iteration (pc 221 → 221): copy `mem[0xa0+i] → mem[newFp+0x40+i]`, `i += 32`. -/
theorem weth9NameLong2Continue {cA gh bl σ σ₀ A I} {g : Sat256} (j : Nat)
    (hpos : 1 ≤ (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat)
    (hfit : 96 + 32 * weth9LongWC σ I < 2 ^ 64)
    (hjlt : j < weth9LongWC σ I + 1)
    (h : ∃ k C, RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨221⟩
      (weth9Long2LoopStack σ I (UInt256.ofNat (32 * j)))
      (weth9Long2Mem σ I j) (UInt256.ofNat (8 + weth9LongWC σ I + j)) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨221⟩
      (weth9Long2LoopStack σ I (UInt256.ofNat (32 * (j + 1))))
      (weth9Long2Mem σ I (j + 1)) (UInt256.ofNat (8 + weth9LongWC σ I + (j + 1)))
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd221⟩ := h
  rw [weth9Long2LoopStack] at rd221
  have h66 : (2 : Nat) ^ 66 < UInt256.size := by norm_num [UInt256.size]
  have hbig : 288 + 64 * weth9LongWC σ I < UInt256.size := by omega
  have hfpN : (weth9StringNewFp (weth9StringSlotWord σ I ⟨0⟩)).toNat = 192 + 32 * weth9LongWC σ I :=
    weth9StringNewFp_toNat_long hpos
  -- length lower bound so the continue guard holds.
  have hlenGt : 32 * weth9LongWC σ I < (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat := by
    have := Nat.div_mul_le_self ((weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat - 1) 32
    rw [weth9LongWC]; omega
  have hi : (UInt256.ofNat (32 * j)).toNat = 32 * j := ulit_toNat' _ (by omega)
  have haddr64 : (weth9StringNewFp (weth9StringSlotWord σ I ⟨0⟩) + ⟨64⟩).toNat =
      256 + 32 * weth9LongWC σ I := by
    rw [uadd_toNat, hfpN, show (⟨64⟩ : UInt256).toNat = 64 from by decide,
      Nat.mod_eq_of_lt (by omega)]; omega
  have hsrc : (UInt256.ofNat (32 * j) + ((⟨128⟩ : UInt256) + ⟨32⟩)).toNat = 160 + 32 * j := by
    rw [uadd_toNat, hi, show ((⟨128⟩ : UInt256) + ⟨32⟩).toNat = 160 from by decide,
      Nat.mod_eq_of_lt (by omega)]; omega
  have hdst : (UInt256.ofNat (32 * j) + (weth9StringNewFp (weth9StringSlotWord σ I ⟨0⟩) + ⟨64⟩)).toNat =
      256 + 32 * weth9LongWC σ I + 32 * j := by
    rw [uadd_toNat, hi, haddr64, Nat.mod_eq_of_lt (by omega)]; omega
  have hincr : (⟨32⟩ : UInt256) + UInt256.ofNat (32 * j) = UInt256.ofNat (32 * (j + 1)) := by
    apply u256_inj
    rw [uadd_toNat, hi, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
      Nat.mod_eq_of_lt (by omega), ulit_toNat' _ (by omega)]; ring
  have hcont : UInt256.isZero (UInt256.lt (UInt256.ofNat (32 * j))
      (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩))) = ⟨0⟩ := by
    rw [ult_one (by rw [hi]; omega)]; decide
  have rd := evm_run rd221 with [
    jumpdest, dup4, dup2, lt, iszero, push2 ⟨245⟩, jumpiNT hcont,
    dup2, dup2, add,
    raw mload _ (weth9LongDataWordAt σ I j) (UInt256.ofNat (8 + weth9LongWC σ I + j))
      (by native_decide) weth9MloadCostSpec
      (mloadWordValue_of_readWithPadding
        (by rw [hsrc, weth9Long2Mem_size hpos]; omega)
        (wordMul32_not_ge_of_lt (by rw [hsrc, ulit_toNat' _ (by omega)]; omega)
          (by rw [ulit_toNat' _ (by omega)]; omega))
        (by rw [hsrc]; exact weth9Long2Mem_readSrc hpos j j (by omega)))
      (by rw [hsrc, ulit_toNat' _ (by omega),
        machineState_M_inBounds (show (160 + 32 * j) + 32 ≤ 32 * (8 + weth9LongWC σ I + j) from by omega)])
      (by evm_ov),
    dup4, dup3, add,
    raw mstore _ (weth9Long2Mem σ I (j + 1)) (UInt256.ofNat (8 + weth9LongWC σ I + (j + 1)))
      (by native_decide) weth9MstoreCostSpec
      (by rw [weth9Long2Mem_succ, Reasoning.Theory.writeWord, hdst])
      (by rw [ulit_toNat' _ (by omega), hdst,
        show (256 + 32 * weth9LongWC σ I + 32 * j : Nat) = 32 * (8 + weth9LongWC σ I + j) from by ring,
        machineState_M_endWrite, show 8 + weth9LongWC σ I + j + 1 = 8 + weth9LongWC σ I + (j + 1) from by omega]) (by evm_ov),
    push1 ⟨32⟩, add, push2 ⟨221⟩, jump (by jump_dest)]
  rw [hincr] at rd
  exact ⟨_, _, rd⟩

set_option maxHeartbeats 8000000 in
/-- Run the Loop-2 mem→mem copy (pc 221) to exhaustion (`wc` iterations), reaching the exit (pc 245)
    with all data words copied. -/
theorem weth9NameLong2CopyLoop {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpos : 1 ≤ (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat)
    (hfit : 96 + 32 * weth9LongWC σ I < 2 ^ 64)
    (h : ∃ k C, RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨221⟩
      (weth9Long2LoopStack σ I ⟨0⟩)
      (weth9Long2Mem σ I 0) (UInt256.ofNat (8 + weth9LongWC σ I)) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨245⟩
      (weth9Long2LoopStack σ I (UInt256.ofNat (32 * (weth9LongWC σ I + 1))))
      (weth9Long2Mem σ I (weth9LongWC σ I + 1))
      (UInt256.ofNat (8 + weth9LongWC σ I + (weth9LongWC σ I + 1))) ByteArray.empty (cA, σ) k C := by
  have h66 : (2 : Nat) ^ 66 < UInt256.size := by norm_num [UInt256.size]
  have hbig : 288 + 64 * weth9LongWC σ I < UInt256.size := by omega
  have hdone : (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat ≤ 32 * (weth9LongWC σ I + 1) := by
    have := weth9LongFuel_done_nat (show 0 < (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat from by omega)
    rw [weth9LongWC]; omega
  -- exit rule
  have hexit : ∀ a : ℕ, a + 0 = weth9LongWC σ I + 1 → ∀ k C,
      RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨221⟩
        (weth9Long2LoopStack σ I (UInt256.ofNat (32 * a)))
        (weth9Long2Mem σ I a) (UInt256.ofNat (8 + weth9LongWC σ I + a)) ByteArray.empty (cA, σ) k C →
      ∃ k' C', RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨245⟩
        (weth9Long2LoopStack σ I (UInt256.ofNat (32 * a)))
        (weth9Long2Mem σ I a) (UInt256.ofNat (8 + weth9LongWC σ I + a)) ByteArray.empty (cA, σ) k' C' := by
    intro a hInv k C hrd
    have ha : a = weth9LongWC σ I + 1 := by omega
    subst ha
    rw [weth9Long2LoopStack] at hrd
    have hcond : UInt256.isZero (UInt256.lt (UInt256.ofNat (32 * (weth9LongWC σ I + 1)))
        (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩))) ≠ ⟨0⟩ := by
      rw [ult_zero (by rw [ulit_toNat' _ (by omega)]; omega)]; decide
    have rd := evm_run hrd with [
      jumpdest, dup4, dup2, lt, iszero, push2 ⟨245⟩, jumpiT hcond (by jump_dest)]
    exact ⟨_, _, rd⟩
  -- body rule
  have hbody : ∀ (v a : ℕ), a + (v + 1) = weth9LongWC σ I + 1 → ∀ k C,
      RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨221⟩
        (weth9Long2LoopStack σ I (UInt256.ofNat (32 * a)))
        (weth9Long2Mem σ I a) (UInt256.ofNat (8 + weth9LongWC σ I + a)) ByteArray.empty (cA, σ) k C →
      ∃ a' k' C', a' + v = weth9LongWC σ I + 1 ∧
        RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨221⟩
          (weth9Long2LoopStack σ I (UInt256.ofNat (32 * a')))
          (weth9Long2Mem σ I a') (UInt256.ofNat (8 + weth9LongWC σ I + a')) ByteArray.empty (cA, σ) k' C' := by
    intro v a hInv k C hrd
    obtain ⟨k', C', rd'⟩ := weth9NameLong2Continue a hpos hfit (by omega) ⟨k, C, hrd⟩
    exact ⟨a + 1, k', C', by omega, rd'⟩
  obtain ⟨k0, C0, h0⟩ := h
  have h0' : RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨221⟩
      (weth9Long2LoopStack σ I (UInt256.ofNat (32 * 0)))
      (weth9Long2Mem σ I 0) (UInt256.ofNat (8 + weth9LongWC σ I + 0)) ByteArray.empty (cA, σ) k0 C0 := by
    simpa using h0
  obtain ⟨a', k', C', hInv0, hexitRD⟩ :=
    RD.whileLoopCarry ⟨221⟩ ⟨245⟩ (fun v j => j + v = weth9LongWC σ I + 1)
      (fun j => weth9Long2LoopStack σ I (UInt256.ofNat (32 * j)))
      (fun j => weth9Long2Mem σ I j) (fun j => UInt256.ofNat (8 + weth9LongWC σ I + j))
      (fun j => weth9Long2LoopStack σ I (UInt256.ofNat (32 * j)))
      hexit hbody (weth9LongWC σ I + 1) 0 (by omega) k0 C0 h0'
  have ha' : a' = weth9LongWC σ I + 1 := by omega
  subst ha'
  exact ⟨_, _, hexitRD⟩

/-! ## Final memory (after the trailing-word mask) and the RETURN window -/

/-- Memory at the RETURN: the Loop-2 output, with the trailing data word replaced by its masked value
    (the mask store is skipped when `len` is a multiple of 32, in which case the last word is full). -/
noncomputable def weth9Long2FinalMem (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  if UInt256.land ⟨31⟩ (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)) = ⟨0⟩ then
    weth9Long2Mem σ I (weth9LongWC σ I + 1)
  else
    writeWord (weth9Long2Mem σ I (weth9LongWC σ I + 1)) (256 + 64 * weth9LongWC σ I)
      (weth9LongMaskWord σ I)

section FinalMem
variable {σ : AccountMap} {I : ExecutionEnv}
  (hpos : 1 ≤ (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat)
  (hfit : 96 + 32 * weth9LongWC σ I < 2 ^ 64)
include hpos hfit

omit hfit in
theorem weth9Long2FinalMem_size : (weth9Long2FinalMem σ I).size = 288 + 64 * weth9LongWC σ I := by
  have hmem : (weth9Long2Mem σ I (weth9LongWC σ I + 1)).size = 288 + 64 * weth9LongWC σ I := by
    rw [weth9Long2Mem_size hpos]; omega
  unfold weth9Long2FinalMem
  split
  · exact hmem
  · rw [writeWord_size _ _ _ (by rw [hmem]; exact lt_usize _ (by omega)), hmem]; omega

theorem weth9Long2FinalMem_read64 : (weth9Long2FinalMem σ I).readWithPadding 64 32 =
    (weth9StringNewFp (weth9StringSlotWord σ I ⟨0⟩)).toByteArray := by
  have hfpN := weth9StringNewFp_toNat_long hpos
  unfold weth9Long2FinalMem
  split
  · exact weth9Long2Mem_read64 hpos _
  · rw [writeWord_read_preserved _ _ _ _
      (by rw [weth9Long2Mem_size hpos]; exact lt_usize _ (by omega))
      (Or.inl ⟨by omega, by rw [weth9Long2Mem_size hpos]; omega⟩)]
    exact weth9Long2Mem_read64 hpos _

theorem weth9Long2FinalMem_readOffset : (weth9Long2FinalMem σ I).readWithPadding
    (weth9StringNewFp (weth9StringSlotWord σ I ⟨0⟩)).toNat 32 = UInt256.toByteArray ⟨32⟩ := by
  have hfpN := weth9StringNewFp_toNat_long hpos
  unfold weth9Long2FinalMem
  split
  · exact weth9Long2Mem_readOffset hpos _
  · rw [writeWord_read_preserved _ _ _ _
      (by rw [weth9Long2Mem_size hpos]; exact lt_usize _ (by omega))
      (Or.inl ⟨by rw [hfpN]; omega, by rw [weth9Long2Mem_size hpos, hfpN]; omega⟩)]
    exact weth9Long2Mem_readOffset hpos _

theorem weth9Long2FinalMem_readLen : (weth9Long2FinalMem σ I).readWithPadding
    ((weth9StringNewFp (weth9StringSlotWord σ I ⟨0⟩)).toNat + 32) 32 =
      (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toByteArray := by
  have hfpN := weth9StringNewFp_toNat_long hpos
  unfold weth9Long2FinalMem
  split
  · exact weth9Long2Mem_readLen hpos _
  · rw [writeWord_read_preserved _ _ _ _
      (by rw [weth9Long2Mem_size hpos]; exact lt_usize _ (by omega))
      (Or.inl ⟨by rw [hfpN]; omega, by rw [weth9Long2Mem_size hpos, hfpN]; omega⟩)]
    exact weth9Long2Mem_readLen hpos _

omit hfit in
theorem weth9Long2FinalMem_readDest (k : Nat) (hk : k < weth9LongWC σ I) :
    (weth9Long2FinalMem σ I).readWithPadding (256 + 32 * weth9LongWC σ I + 32 * k) 32 =
      (weth9LongDataWordAt σ I k).toByteArray := by
  unfold weth9Long2FinalMem
  split
  · exact weth9Long2Mem_readDest hpos k _ (by omega)
  · rw [writeWord_read_preserved _ _ _ _
      (by rw [weth9Long2Mem_size hpos]; exact lt_usize _ (by omega))
      (Or.inl ⟨by omega, by rw [weth9Long2Mem_size hpos]; omega⟩)]
    exact weth9Long2Mem_readDest hpos k _ (by omega)

omit hfit in
theorem weth9Long2FinalMem_readLast :
    (weth9Long2FinalMem σ I).readWithPadding (256 + 64 * weth9LongWC σ I) 32 =
      (weth9LongMaskWord σ I).toByteArray := by
  unfold weth9Long2FinalMem weth9LongMaskWord
  split
  · have := weth9Long2Mem_readDest hpos (weth9LongWC σ I) (weth9LongWC σ I + 1) (by omega)
    rw [show 256 + 32 * weth9LongWC σ I + 32 * weth9LongWC σ I = 256 + 64 * weth9LongWC σ I from by ring] at this
    exact this
  · exact writeWord_read_back _ _ _
      (by rw [weth9Long2Mem_size hpos]; exact lt_usize _ (by omega))

/-- The `RETURN(newFp, 0x40 + 32·wc)` window over the finished memory is exactly `weth9LongStringAbi`. -/
theorem weth9Long2FinalMem_readAbi :
    (weth9Long2FinalMem σ I).readWithPadding (weth9StringNewFp (weth9StringSlotWord σ I ⟨0⟩)).toNat
      (64 + 32 * (weth9LongWC σ I + 1)) = weth9LongStringAbi σ I := by
  have hfpN := weth9StringNewFp_toNat_long hpos
  have hsz := weth9Long2FinalMem_size hpos
  -- word function for the data region: unmasked words, masked last
  set fLast : Nat → UInt256 := fun k =>
    if k = weth9LongWC σ I then weth9LongMaskWord σ I else weth9LongDataWordAt σ I k with hfL
  have hdata : (weth9Long2FinalMem σ I).readWithPadding (256 + 32 * weth9LongWC σ I)
      (32 * (weth9LongWC σ I + 1)) = wordConcat fLast 0 (weth9LongWC σ I + 1) := by
    have := readWithPadding_wordConcat (weth9Long2FinalMem σ I) fLast (256 + 32 * weth9LongWC σ I)
      (weth9LongWC σ I + 1) 0 (by omega) (by rw [hsz]; omega)
      (by intro k hk
          simp only [Nat.zero_add, hfL]
          rcases Nat.lt_or_ge k (weth9LongWC σ I) with hlt | hge
          · rw [if_neg (by omega)]
            exact weth9Long2FinalMem_readDest hpos k hlt
          · have hkeq : k = weth9LongWC σ I := by omega
            subst hkeq
            rw [if_pos rfl,
              show 256 + 32 * weth9LongWC σ I + 32 * weth9LongWC σ I = 256 + 64 * weth9LongWC σ I from by ring]
            exact weth9Long2FinalMem_readLast hpos)
    simpa using this
  have hlast : fLast (weth9LongWC σ I) = weth9LongMaskWord σ I := by rw [hfL]; simp
  have hconcat : wordConcat fLast 0 (weth9LongWC σ I + 1) =
      wordConcat (weth9LongDataWordAt σ I) 0 (weth9LongWC σ I) ++
        (weth9LongMaskWord σ I).toByteArray := by
    rw [wordConcat_append_last fLast (weth9LongWC σ I) 0, Nat.zero_add, hlast]
    congr 1
    apply wordConcat_congr
    intro k hk
    show (if 0 + k = weth9LongWC σ I then weth9LongMaskWord σ I
      else weth9LongDataWordAt σ I (0 + k)) = weth9LongDataWordAt σ I (0 + k)
    rw [if_neg (by omega)]
  rw [weth9LongStringAbi]
  rw [show (64 + 32 * (weth9LongWC σ I + 1)) = 32 + (32 + 32 * (weth9LongWC σ I + 1)) from by ring,
    byteArray_readWithPadding_split _ _ 32 (32 + 32 * (weth9LongWC σ I + 1)) (by norm_num)
      (by omega) (by norm_num) (by omega) (by omega) (by rw [hsz, hfpN]; omega),
    byteArray_readWithPadding_split _ _ 32 (32 * (weth9LongWC σ I + 1)) (by norm_num)
      (by omega) (by norm_num) (by omega) (by omega) (by rw [hsz, hfpN]; omega),
    weth9Long2FinalMem_readOffset hpos hfit]
  congr 1
  rw [show (weth9StringNewFp (weth9StringSlotWord σ I ⟨0⟩)).toNat + 32 =
      (weth9StringNewFp (weth9StringSlotWord σ I ⟨0⟩)).toNat + 32 from rfl,
    weth9Long2FinalMem_readLen hpos hfit]
  congr 1
  rw [show (weth9StringNewFp (weth9StringSlotWord σ I ⟨0⟩)).toNat + 32 + 32 =
      256 + 32 * weth9LongWC σ I from by rw [hfpN]; ring, hdata, hconcat]

end FinalMem

/-- `(31 & len).toNat = len.toNat % 32`. -/
theorem weth9Long2Land31_toNat (H : UInt256) :
    (UInt256.land ⟨31⟩ (weth9StringLen H)).toNat = (weth9StringLen H).toNat % 32 := by
  rw [uland_toNat, show (⟨31⟩ : UInt256).toNat = 31 from by decide,
    Nat.and_comm 31 (weth9StringLen H).toNat, show (31 : Nat) = 2 ^ 5 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

/-- When `len` is not a multiple of 32, `32·(wc-1) + (len % 32) = len` (`wc-1 = weth9LongWC`). -/
theorem weth9Long2Len_sub_mod {σ : AccountMap} {I : ExecutionEnv}
    (hr : (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat % 32 ≠ 0) :
    32 * weth9LongWC σ I + (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat % 32 =
      (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat := by
  rw [weth9LongWC]; omega

set_option maxHeartbeats 8000000 in
/-- **Full long-string `name()` ABI return encoder** (`len ≥ 32`): from the encoder entry (pc 187,
    the string data already copied into memory), write the ABI `(offset, len, data)` triple, copy the
    data words (Loop-2), zero the trailing garbage (tail mask, when `len % 32 ≠ 0`), and `RETURN`
    `weth9LongStringAbi`.  Config-independent, symbolic `len ≥ 32`; `hfit` bounds the returned object
    to a 64-bit-addressable size (EVM cannot return `≥ 2⁶⁴` bytes). -/
theorem weth9NameStringLongReturns {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = weth9Bytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (weth9SelBytes 0))
    (hge31 : UInt256.lt ⟨31⟩ (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)) ≠ ⟨0⟩)
    (hfit : 96 + 32 * weth9LongWC σ I < 2 ^ 64) :
    RDret weth9Bytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ) (weth9LongStringAbi σ I) := by
  have hpos : 1 ≤ (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat := by
    have := weth9LongLen_ge32 hge31; omega
  have h66 : (2 : Nat) ^ 66 < UInt256.size := by norm_num [UInt256.size]
  have hbig : 288 + 64 * weth9LongWC σ I < UInt256.size := by omega
  have hfpN := weth9StringNewFp_toNat_long hpos
  have hlandN := weth9Long2Land31_toNat (weth9StringSlotWord σ I ⟨0⟩)
  have haddr64 : (weth9StringNewFp (weth9StringSlotWord σ I ⟨0⟩) + ⟨64⟩).toNat =
      256 + 32 * weth9LongWC σ I := by
    rw [uadd_toNat, hfpN, show (⟨64⟩ : UInt256).toNat = 64 from by decide,
      Nat.mod_eq_of_lt (by omega)]; omega
  have hawnorm : 8 + weth9LongWC σ I + (weth9LongWC σ I + 1) = 9 + 2 * weth9LongWC σ I := by omega
  obtain ⟨_, _, h245⟩ := weth9NameLong2CopyLoop (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hpos hfit
    (weth9NameLong2ReachLoopHead (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) hcode hwv hsz4 hsize hsel hge31 hfit)
  rw [weth9Long2LoopStack] at h245
  -- common prefix: pops, tail-offset arithmetic, tail-mask decision.
  have hpre := evm_run h245 with [
    jumpdest, pop, pop, pop, pop, swap1, pop, swap1, dup2, add, swap1,
    push1 ⟨31⟩, and, dup1, iszero, push2 ⟨290⟩]
  by_cases hmask : UInt256.land ⟨31⟩ (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)) = ⟨0⟩
  · -- len is a multiple of 32: skip the mask; last word is full.
    have hlen32 : (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat = 32 * (weth9LongWC σ I + 1) := by
      have hz : (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat % 32 = 0 := by
        have := congrArg UInt256.toNat hmask; rw [hlandN] at this; simpa using this
      rw [weth9LongWC]; omega
    have hcond : UInt256.isZero (UInt256.land ⟨31⟩ (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩))) ≠ ⟨0⟩ := by
      rw [hmask]; decide
    have hretlen : (UInt256.sub (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩) +
        (weth9StringNewFp (weth9StringSlotWord σ I ⟨0⟩) + ⟨64⟩))
        (weth9StringNewFp (weth9StringSlotWord σ I ⟨0⟩))).toNat = 64 + 32 * (weth9LongWC σ I + 1) := by
      rw [usub_toNat (by rw [uadd_toNat, haddr64, Nat.mod_eq_of_lt (by omega), hfpN]; omega),
        uadd_toNat, haddr64, Nat.mod_eq_of_lt (by omega), hfpN, hlen32]; omega
    have hmem : weth9Long2Mem σ I (weth9LongWC σ I + 1) = weth9Long2FinalMem σ I := by
      rw [weth9Long2FinalMem, if_pos hmask]
    exact evm_run hpre with [
      jumpiT hcond (by jump_dest),
      jumpdest, pop, swap3, pop, pop, pop, push1 ⟨64⟩,
      raw mload _ (weth9StringNewFp (weth9StringSlotWord σ I ⟨0⟩)) (UInt256.ofNat (9 + 2 * weth9LongWC σ I))
        (by native_decide) weth9MloadCostSpec
        (mloadWordValue_of_readWithPadding
          (by rw [weth9Long2Mem_size hpos, show (⟨64⟩ : UInt256).toNat = 64 from by decide]; omega)
          (wordMul32_not_ge_of_lt (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, ulit_toNat' _ (by omega)]; omega)
            (by rw [ulit_toNat' _ (by omega)]; omega))
          (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; exact weth9Long2Mem_read64 hpos _))
        (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, ulit_toNat' _ (by omega), hawnorm,
          machineState_M_inBounds (show (64 : Nat) + 32 ≤ 32 * (9 + 2 * weth9LongWC σ I) from by omega)]) (by evm_ov),
      dup1, swap2, sub, swap1,
      raw ret _ (weth9LongStringAbi σ I) (by native_decide) weth9ReturnCostSpec
        (by rw [hmem, hretlen]; exact weth9Long2FinalMem_readAbi hpos hfit) (by evm_ov)]
  · -- len not a multiple of 32: apply the trailing-word mask.
    have hcond : UInt256.isZero (UInt256.land ⟨31⟩ (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩))) = ⟨0⟩ :=
      isZero_eq_zero_of_ne hmask
    have hr : (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat % 32 ≠ 0 := by
      intro hz
      apply hmask; apply u256_inj; rw [hlandN, hz]; decide
    have hsubmod := weth9Long2Len_sub_mod (σ := σ) (I := I) hr
    have hmaskAddr : (UInt256.sub (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩) +
        (weth9StringNewFp (weth9StringSlotWord σ I ⟨0⟩) + ⟨64⟩))
        (UInt256.land ⟨31⟩ (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)))).toNat =
        256 + 64 * weth9LongWC σ I := by
      rw [usub_toNat (by rw [uadd_toNat, haddr64, Nat.mod_eq_of_lt (by omega), hlandN]; omega),
        uadd_toNat, haddr64, Nat.mod_eq_of_lt (by omega), hlandN]; omega
    have hmaskVal : UInt256.land
        (UInt256.lnot (UInt256.sub (UInt256.exp ⟨256⟩ (UInt256.sub ⟨32⟩
          (UInt256.land ⟨31⟩ (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩))))) ⟨1⟩))
        (weth9LongDataWordAt σ I (weth9LongWC σ I)) = weth9LongMaskWord σ I := by
      rw [weth9LongMaskWord, if_neg hmask]
    have hmemMask : writeWord (weth9Long2Mem σ I (weth9LongWC σ I + 1)) (256 + 64 * weth9LongWC σ I)
        (weth9LongMaskWord σ I) = weth9Long2FinalMem σ I := by
      rw [weth9Long2FinalMem, if_neg hmask]
    have hretlen : (UInt256.sub ((⟨32⟩ : UInt256) + UInt256.sub (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩) +
        (weth9StringNewFp (weth9StringSlotWord σ I ⟨0⟩) + ⟨64⟩))
        (UInt256.land ⟨31⟩ (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩))))
        (weth9StringNewFp (weth9StringSlotWord σ I ⟨0⟩))).toNat = 64 + 32 * (weth9LongWC σ I + 1) := by
      rw [usub_toNat (by rw [uadd_toNat, hmaskAddr, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
          Nat.mod_eq_of_lt (by omega), hfpN]; omega),
        uadd_toNat, hmaskAddr, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
        Nat.mod_eq_of_lt (by omega), hfpN]; omega
    exact evm_run hpre with [
      jumpiNT hcond,
      dup1, dup3, sub, dup1,
      raw mload _ (weth9LongDataWordAt σ I (weth9LongWC σ I)) (UInt256.ofNat (9 + 2 * weth9LongWC σ I))
        (by native_decide) weth9MloadCostSpec
        (mloadWordValue_of_readWithPadding
          (by rw [hmaskAddr, weth9Long2Mem_size hpos]; omega)
          (wordMul32_not_ge_of_lt (by rw [hmaskAddr, ulit_toNat' _ (by omega)]; omega)
            (by rw [ulit_toNat' _ (by omega)]; omega))
          (by rw [hmaskAddr]
              have := weth9Long2Mem_readDest hpos (weth9LongWC σ I) (weth9LongWC σ I + 1) (by omega)
              rwa [show 256 + 32 * weth9LongWC σ I + 32 * weth9LongWC σ I = 256 + 64 * weth9LongWC σ I from by ring] at this))
        (by rw [hmaskAddr, ulit_toNat' _ (by omega), hawnorm,
          machineState_M_inBounds (show (256 + 64 * weth9LongWC σ I) + 32 ≤ 32 * (9 + 2 * weth9LongWC σ I) from by omega)])
        (by evm_ov),
      push1 ⟨1⟩, dup4, push1 ⟨32⟩, sub, push2 ⟨256⟩, exp, sub, not, and, dup2,
      raw mstore _ (weth9Long2FinalMem σ I) (UInt256.ofNat (9 + 2 * weth9LongWC σ I))
        (by native_decide) weth9MstoreCostSpec
        (by rw [hmaskAddr, hmaskVal]; exact hmemMask)
        (by rw [hmaskAddr, ulit_toNat' _ (by omega),
          machineState_M_inBounds (show (256 + 64 * weth9LongWC σ I) + 32 ≤ 32 * (9 + 2 * weth9LongWC σ I) from by omega)])
        (by evm_ov),
      push1 ⟨32⟩, add, swap2, pop,
      jumpdest, pop, swap3, pop, pop, pop, push1 ⟨64⟩,
      raw mload _ (weth9StringNewFp (weth9StringSlotWord σ I ⟨0⟩)) (UInt256.ofNat (9 + 2 * weth9LongWC σ I))
        (by native_decide) weth9MloadCostSpec
        (mloadWordValue_of_readWithPadding
          (by rw [weth9Long2FinalMem_size hpos, show (⟨64⟩ : UInt256).toNat = 64 from by decide]; omega)
          (wordMul32_not_ge_of_lt (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, ulit_toNat' _ (by omega)]; omega)
            (by rw [ulit_toNat' _ (by omega)]; omega))
          (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; exact weth9Long2FinalMem_read64 hpos hfit))
        (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, ulit_toNat' _ (by omega),
          machineState_M_inBounds (show (64 : Nat) + 32 ≤ 32 * (9 + 2 * weth9LongWC σ I) from by omega)]) (by evm_ov),
      dup1, swap2, sub, swap1,
      raw ret _ (weth9LongStringAbi σ I) (by native_decide) weth9ReturnCostSpec
        (by rw [hretlen]; exact weth9Long2FinalMem_readAbi hpos hfit) (by evm_ov)]

end Benchmarks.WETH9
