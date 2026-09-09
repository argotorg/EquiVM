import Benchmarks.WETH9.StringReturnSymbol

/-!
# WETH9 `symbol()` dynamic-string getter — LONG case ABI return encoder (slot 1, `len ≥ 32`)

`Benchmarks/WETH9/StringReturnSymbol.lean` drove `symbol()`'s long branch through the storage→memory
copy loop to the shared ABI-return encoder entry (pc 187), leaving the string data words in memory at
`0xa0` (`weth9SymNameLongReach187`, memory `weth9SymLongFinalMem`).

This module finishes the long case: it drives the shared symbolic-offset ABI encoder (pc 187 →
`RETURN`), including the second mem→mem copy loop (pc 221–244) and the trailing-word zero-mask
(pc 245–289), concluding `RDret … (weth9SymLongStringAbi σ I)`.  It mirrors
`Benchmarks/WETH9/StringReturnLong2.lean` verbatim with storage slot 1, reusing the slot-agnostic
`wordConcat`/`readWithPadding_wordConcat`, `machineState_M_*`, `wordMul32_not_ge_of_lt`,
`weth9Long2Land31_toNat` and the symbolic mem-cost witnesses.  The encoder carries no storage-slot
marker on its stack (the slot value was popped at the Loop-1 exit), so this is a pure
re-parameterization by the slot-1 header.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000

namespace Benchmarks.WETH9



/-! ## Data-word characterization

The `k`-th string data word is the storage word copied by Loop-1 into `mem[0xa0+32·k]`.  We extend
the Loop-1 read-preservation lemmas (`weth9SymLongFinalMem_read64/_read128`) to the data region. -/

/-- The `k`-th long-string data word: the storage word copied by Loop-1 into `mem[0xa0 + 32·k]`. -/
noncomputable def weth9SymLongDataWordAt (σ : AccountMap) (I : ExecutionEnv) (k : Nat) : UInt256 :=
  weth9LongStorageWord σ I (weth9SymLongGeneratedLoopState σ I k).slot

/-- Loop-1 memory at step `i` holds data word `k` at `0xa0 + 32·k` for every `k < i`. -/
theorem weth9SymLongMem_readData_of_bound {σ : AccountMap} {I : ExecutionEnv} (k : Nat) :
    ∀ i : Nat, k < i → 160 + 32 * i < UInt256.size →
      (weth9SymLongGeneratedLoopState σ I i).mem.readWithPadding (160 + 32 * k) 32 =
        (weth9SymLongDataWordAt σ I k).toByteArray
  | 0, hki, _ => absurd hki (by omega)
  | i + 1, hki, hbound => by
      have hprevPtr : (weth9SymLongGeneratedLoopState σ I i).ptr.toNat = 160 + 32 * i :=
        weth9SymLongPtr_toNat_of_bound i (by omega)
      have hprevSize : (weth9SymLongGeneratedLoopState σ I i).mem.size = 160 + 32 * i :=
        weth9SymLongMem_size_of_bound i (by omega)
      rw [weth9SymLongGeneratedLoopState_succ]
      show (weth9LongCopyMem (weth9SymLongGeneratedLoopState σ I i).mem
        (weth9SymLongGeneratedLoopState σ I i).ptr _).readWithPadding (160 + 32 * k) 32 = _
      rw [weth9LongCopyMem]
      rcases Nat.lt_or_ge k i with hlt | hge
      · rw [writeWord_read_preserved _ _ (160 + 32 * k) _
            (by rw [hprevPtr, hprevSize]; exact lt_usize _ (by norm_num))
            (Or.inl ⟨by rw [hprevPtr]; omega, by rw [hprevSize]; omega⟩)]
        exact weth9SymLongMem_readData_of_bound k i hlt (by omega)
      · have hk : k = i := by omega
        subst hk
        rw [hprevPtr, writeWord_read_back _ _ _ (by rw [hprevSize]; exact lt_usize _ (by norm_num))]
        rfl

/-- The finished Loop-1 memory holds data word `k` at `0xa0 + 32·k` for every `k ≤ wc-1`. -/
theorem weth9SymLongFinalMem_readData {σ : AccountMap} {I : ExecutionEnv} (k : Nat)
    (hk : k ≤ weth9SymLongWC σ I) :
    (weth9SymLongFinalMem σ I).readWithPadding (160 + 32 * k) 32 =
      (weth9SymLongDataWordAt σ I k).toByteArray := by
  have hbnd := weth9SymLongWC_size_bound σ I
  have hptr : (weth9SymLongGeneratedLoopState σ I (weth9SymLongWC σ I)).ptr.toNat =
      160 + 32 * weth9SymLongWC σ I := weth9SymLongPtr_toNat_of_bound _ (by omega)
  have hsize : (weth9SymLongGeneratedLoopState σ I (weth9SymLongWC σ I)).mem.size =
      160 + 32 * weth9SymLongWC σ I := weth9SymLongMem_size_of_bound _ (by omega)
  rw [weth9SymLongFinalMem, weth9LongCopyMem]
  rcases Nat.lt_or_ge k (weth9SymLongWC σ I) with hlt | hge
  · rw [writeWord_read_preserved _ _ (160 + 32 * k) _
        (by rw [hptr, hsize]; exact lt_usize _ (by norm_num))
        (Or.inl ⟨by rw [hptr]; omega, by rw [hsize]; omega⟩)]
    exact weth9SymLongMem_readData_of_bound k (weth9SymLongWC σ I) hlt (by omega)
  · have hk' : k = weth9SymLongWC σ I := by omega
    subst hk'
    rw [hptr, writeWord_read_back _ _ _ (by rw [hsize]; exact lt_usize _ (by norm_num))]
    rfl

/-! ## The long-string ABI encoding

Mirrors `weth9ShortStringAbi` generalized to `wc = wc-1 + 1` data words: offset word `0x20`, the
length word, then `wc-1` unmasked data words and the trailing masked word.  When `len` is a multiple
of `32` the trailing word is full (no masking), so `weth9SymLongMaskWord` is a `land`-of-`lnot` only in
the partial case. -/

/-- The trailing data word as returned: masked (`~(2^(8·(32-31&len))-1) & data`) when `len` is not a
    multiple of 32, else the full last data word (the mask store is skipped by the runtime). -/
noncomputable def weth9SymLongMaskWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  if UInt256.land ⟨31⟩ (weth9StringLen (weth9StringSlotWord σ I ⟨1⟩)) = ⟨0⟩ then
    weth9SymLongDataWordAt σ I (weth9SymLongWC σ I)
  else
    UInt256.land
      (UInt256.lnot (UInt256.sub
        (UInt256.exp ⟨256⟩ (UInt256.sub ⟨32⟩
          (UInt256.land ⟨31⟩ (weth9StringLen (weth9StringSlotWord σ I ⟨1⟩))))) ⟨1⟩))
      (weth9SymLongDataWordAt σ I (weth9SymLongWC σ I))

/-- The ABI encoding a long-string getter returns: `offset 0x20 ‖ len ‖ (wc-1) data words ‖ masked
    last word`. -/
noncomputable def weth9SymLongStringAbi (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  UInt256.toByteArray ⟨32⟩ ++
    (UInt256.toByteArray (weth9StringLen (weth9StringSlotWord σ I ⟨1⟩)) ++
      (wordConcat (weth9SymLongDataWordAt σ I) 0 (weth9SymLongWC σ I) ++
        UInt256.toByteArray (weth9SymLongMaskWord σ I)))

/-! ## Free-pointer / active-words arithmetic

`newFp = 0xa0 + 32·wc = 0xa0 + 32·(wc-1) + 32 = 0xc0 + 32·(wc-1)`, and equals `weth9SymLongFinalMem`'s
size.  The active words after the copy loop are `6 + (wc-1)`. -/

/-- `len ≥ 32` (from the long-branch hypothesis). -/
theorem weth9SymLongLen_ge32 {σ : AccountMap} {I : ExecutionEnv}
    (hge31 : UInt256.lt ⟨31⟩ (weth9StringLen (weth9StringSlotWord σ I ⟨1⟩)) ≠ ⟨0⟩) :
    31 < (weth9StringLen (weth9StringSlotWord σ I ⟨1⟩)).toNat := by
  simpa [show (⟨31⟩ : UInt256).toNat = 31 from by decide] using ult_ne_zero_toNat_lt hge31

/-- Word count as `Nat`: `(weth9StringWC H).toNat = wc-1 + 1`. -/
theorem weth9SymStringWC_toNat {σ : AccountMap} {I : ExecutionEnv}
    (hpos : 1 ≤ (weth9StringLen (weth9StringSlotWord σ I ⟨1⟩)).toNat) :
    (weth9StringWC (weth9StringSlotWord σ I ⟨1⟩)).toNat = weth9SymLongWC σ I + 1 := by
  set H := weth9StringSlotWord σ I ⟨1⟩ with hH
  have hlt := weth9StringLen_toNat_lt_sign H
  rw [weth9StringWC, udiv_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
    uadd_toNat, show (⟨31⟩ : UInt256).toNat = 31 from by decide,
    Nat.mod_eq_of_lt (by norm_num [UInt256.size]; omega), weth9SymLongWC, hH]
  rw [show (weth9StringLen H).toNat + 31 = ((weth9StringLen H).toNat - 1) + 32 from by omega,
    Nat.add_div_right _ (by norm_num)]

/-- `newFp.toNat = 0xc0 + 32·(wc-1) = 0xa0 + 32·wc`, equal to the copied memory's size. -/
theorem weth9SymStringNewFp_toNat_long {σ : AccountMap} {I : ExecutionEnv}
    (hpos : 1 ≤ (weth9StringLen (weth9StringSlotWord σ I ⟨1⟩)).toNat) :
    (weth9StringNewFp (weth9StringSlotWord σ I ⟨1⟩)).toNat = 192 + 32 * weth9SymLongWC σ I := by
  set H := weth9StringSlotWord σ I ⟨1⟩ with hH
  have hwc := weth9SymStringWC_toNat (σ := σ) (I := I) hpos
  have hbnd := weth9SymLongWC_size_bound σ I
  have hmul : (UInt256.mul ⟨32⟩ (weth9StringWC H)).toNat = 32 * (weth9SymLongWC σ I + 1) := by
    rw [u256_mul_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide, hwc,
      Nat.mod_eq_of_lt (by omega)]
  have hinner : ((⟨128⟩ : UInt256) + UInt256.mul ⟨32⟩ (weth9StringWC H)).toNat =
      128 + 32 * (weth9SymLongWC σ I + 1) := by
    rw [uadd_toNat, hmul, show (⟨128⟩ : UInt256).toNat = 128 from by decide,
      Nat.mod_eq_of_lt (by omega)]
  rw [weth9StringNewFp, uadd_toNat, hinner, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
    Nat.mod_eq_of_lt (by omega)]
  omega

/-- `weth9SymLongFinalMem`'s size in the `192 + 32·(wc-1)` form (matching `newFp.toNat`). -/
theorem weth9SymLongFinalMem_size' (σ : AccountMap) (I : ExecutionEnv) :
    (weth9SymLongFinalMem σ I).size = 192 + 32 * weth9SymLongWC σ I := by
  rw [weth9SymLongFinalMem_size]; omega

/-- Loop-1 active words after `i` copies: `5 + i` (each copy is an at-end word write). -/
theorem weth9SymLongGeneratedLoopState_aw_toNat {σ : AccountMap} {I : ExecutionEnv} :
    ∀ i : Nat, 160 + 32 * i < UInt256.size →
      (weth9SymLongGeneratedLoopState σ I i).aw.toNat = 5 + i
  | 0, _ => by
      rw [weth9SymLongGeneratedLoopState_zero]
      exact ulit_toNat' 5 (by norm_num [UInt256.size])
  | i + 1, hb => by
      have hprevAw : (weth9SymLongGeneratedLoopState σ I i).aw.toNat = 5 + i :=
        weth9SymLongGeneratedLoopState_aw_toNat i (by omega)
      have hprevPtr : (weth9SymLongGeneratedLoopState σ I i).ptr.toNat = 160 + 32 * i :=
        weth9SymLongPtr_toNat_of_bound i (by omega)
      rw [weth9SymLongGeneratedLoopState_succ]
      show (UInt256.ofNat (MachineState.M (weth9SymLongGeneratedLoopState σ I i).aw.toNat
        (weth9SymLongGeneratedLoopState σ I i).ptr.toNat 32)).toNat = 5 + (i + 1)
      rw [hprevAw, hprevPtr, show (160 + 32 * i : Nat) = 32 * (5 + i) from by ring,
        machineState_M_endWrite, ulit_toNat' _ (by omega)]
      omega

/-- Active words after the Loop-1 copy: `6 + (wc-1)` (equals `newFp.toNat / 32`). -/
theorem weth9SymLongFinalAw_toNat (σ : AccountMap) (I : ExecutionEnv) :
    (weth9SymLongFinalAw σ I).toNat = 6 + weth9SymLongWC σ I := by
  have hbnd := weth9SymLongWC_size_bound σ I
  have haw : (weth9SymLongGeneratedLoopState σ I (weth9SymLongWC σ I)).aw.toNat = 5 + weth9SymLongWC σ I :=
    weth9SymLongGeneratedLoopState_aw_toNat _ (by omega)
  have hptr : (weth9SymLongGeneratedLoopState σ I (weth9SymLongWC σ I)).ptr.toNat =
      160 + 32 * weth9SymLongWC σ I := weth9SymLongPtr_toNat_of_bound _ (by omega)
  rw [weth9SymLongFinalAw, haw, hptr, show (160 + 32 * weth9SymLongWC σ I : Nat) =
    32 * (5 + weth9SymLongWC σ I) from by ring, machineState_M_endWrite, ulit_toNat' _ (by omega)]
  omega

/-- The copied memory's size equals the free pointer `newFp` (the object fills `[0, newFp)`). -/
theorem weth9SymLongFinalMem_size_eq_newFp {σ : AccountMap} {I : ExecutionEnv}
    (hpos : 1 ≤ (weth9StringLen (weth9StringSlotWord σ I ⟨1⟩)).toNat) :
    (weth9SymLongFinalMem σ I).size = (weth9StringNewFp (weth9StringSlotWord σ I ⟨1⟩)).toNat := by
  rw [weth9SymLongFinalMem_size', weth9SymStringNewFp_toNat_long hpos]

/-! ## Encoder memory states (pc 187 → loop head)

`MemA` = finished object memory with the ABI offset word `0x20` written at `newFp`; `MemB` = also the
length word at `newFp+0x20`.  Both writes are at the running end, so the free pointer (`0x40`), length
word (`0x80`), and the source data region `[0xa0, newFp)` all survive. -/

/-- Object memory with the ABI offset word `0x20` at `newFp`. -/
noncomputable def weth9SymLongEncMemA (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  writeWord (weth9SymLongFinalMem σ I) (weth9StringNewFp (weth9StringSlotWord σ I ⟨1⟩)).toNat ⟨32⟩

/-- `MemA` plus the ABI length word at `newFp+0x20`. -/
noncomputable def weth9SymLongEncMemB (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  writeWord (weth9SymLongEncMemA σ I)
    ((weth9StringNewFp (weth9StringSlotWord σ I ⟨1⟩)).toNat + 32)
    (weth9StringLen (weth9StringSlotWord σ I ⟨1⟩))

/-- Loop-2 memory after `j` mem→mem copies: `MemB` with data words `0..j-1` written into the ABI
    data region at `newFp+0x40 + 32·k = 0x100 + 32·(wc-1) + 32·k`. -/
noncomputable def weth9SymLong2Mem (σ : AccountMap) (I : ExecutionEnv) : Nat → ByteArray
  | 0 => weth9SymLongEncMemB σ I
  | j + 1 =>
      writeWord (weth9SymLong2Mem σ I j) (256 + 32 * weth9SymLongWC σ I + 32 * j)
        (weth9SymLongDataWordAt σ I j)

theorem weth9SymLong2Mem_zero (σ : AccountMap) (I : ExecutionEnv) :
    weth9SymLong2Mem σ I 0 = weth9SymLongEncMemB σ I := rfl

theorem weth9SymLong2Mem_succ (σ : AccountMap) (I : ExecutionEnv) (j : Nat) :
    weth9SymLong2Mem σ I (j + 1) =
      writeWord (weth9SymLong2Mem σ I j) (256 + 32 * weth9SymLongWC σ I + 32 * j)
        (weth9SymLongDataWordAt σ I j) := rfl

section EncMem
variable {σ : AccountMap} {I : ExecutionEnv}
  (hpos : 1 ≤ (weth9StringLen (weth9StringSlotWord σ I ⟨1⟩)).toNat)
include hpos

theorem weth9SymLongEncMemA_size : (weth9SymLongEncMemA σ I).size =
    (weth9StringNewFp (weth9StringSlotWord σ I ⟨1⟩)).toNat + 32 := by
  rw [weth9SymLongEncMemA, writeWord_size _ _ _
    (by rw [weth9SymLongFinalMem_size_eq_newFp hpos]; exact lt_usize _ (by norm_num)),
    weth9SymLongFinalMem_size_eq_newFp hpos]; omega

theorem weth9SymLongEncMemA_read64 : (weth9SymLongEncMemA σ I).readWithPadding 64 32 =
    (weth9StringNewFp (weth9StringSlotWord σ I ⟨1⟩)).toByteArray := by
  rw [weth9SymLongEncMemA]
  exact weth9EncLowRead (weth9SymLongFinalMem_read64 σ I)
    (by rw [weth9SymLongFinalMem_size_eq_newFp hpos, weth9SymStringNewFp_toNat_long hpos]; omega)
    (by rw [weth9SymLongFinalMem_size_eq_newFp hpos])
    (by rw [weth9SymLongFinalMem_size_eq_newFp hpos]; exact lt_usize _ (by norm_num))
    (by rw [weth9SymStringNewFp_toNat_long hpos]; omega)

theorem weth9SymLongEncMemA_read128 : (weth9SymLongEncMemA σ I).readWithPadding 128 32 =
    (weth9StringLen (weth9StringSlotWord σ I ⟨1⟩)).toByteArray := by
  rw [weth9SymLongEncMemA]
  exact weth9EncLowRead (weth9SymLongFinalMem_read128 σ I)
    (by rw [weth9SymLongFinalMem_size_eq_newFp hpos, weth9SymStringNewFp_toNat_long hpos]; omega)
    (by rw [weth9SymLongFinalMem_size_eq_newFp hpos])
    (by rw [weth9SymLongFinalMem_size_eq_newFp hpos]; exact lt_usize _ (by norm_num))
    (by rw [weth9SymStringNewFp_toNat_long hpos]; omega)

theorem weth9SymLongEncMemA_readData (k : Nat) (hk : k ≤ weth9SymLongWC σ I) :
    (weth9SymLongEncMemA σ I).readWithPadding (160 + 32 * k) 32 =
      (weth9SymLongDataWordAt σ I k).toByteArray := by
  rw [weth9SymLongEncMemA]
  exact weth9EncLowRead (weth9SymLongFinalMem_readData k hk)
    (by rw [weth9SymLongFinalMem_size_eq_newFp hpos, weth9SymStringNewFp_toNat_long hpos]; omega)
    (by rw [weth9SymLongFinalMem_size_eq_newFp hpos])
    (by rw [weth9SymLongFinalMem_size_eq_newFp hpos]; exact lt_usize _ (by norm_num))
    (by rw [weth9SymStringNewFp_toNat_long hpos]; omega)

theorem weth9SymLongEncMemA_readOffset : (weth9SymLongEncMemA σ I).readWithPadding
    (weth9StringNewFp (weth9StringSlotWord σ I ⟨1⟩)).toNat 32 = UInt256.toByteArray ⟨32⟩ := by
  rw [weth9SymLongEncMemA]
  exact writeWord_read_back _ _ _
    (by rw [weth9SymLongFinalMem_size_eq_newFp hpos]; exact lt_usize _ (by norm_num))

theorem weth9SymLongEncMemB_size : (weth9SymLongEncMemB σ I).size =
    (weth9StringNewFp (weth9StringSlotWord σ I ⟨1⟩)).toNat + 64 := by
  rw [weth9SymLongEncMemB, writeWord_size _ _ _
    (by rw [weth9SymLongEncMemA_size hpos]; exact lt_usize _ (by norm_num)),
    weth9SymLongEncMemA_size hpos]; omega

theorem weth9SymLongEncMemB_read64 : (weth9SymLongEncMemB σ I).readWithPadding 64 32 =
    (weth9StringNewFp (weth9StringSlotWord σ I ⟨1⟩)).toByteArray := by
  rw [weth9SymLongEncMemB]
  exact weth9EncLowRead (weth9SymLongEncMemA_read64 hpos)
    (by rw [weth9SymLongEncMemA_size hpos, weth9SymStringNewFp_toNat_long hpos]; omega)
    (by rw [weth9SymLongEncMemA_size hpos])
    (by rw [weth9SymLongEncMemA_size hpos]; exact lt_usize _ (by norm_num))
    (by rw [weth9SymStringNewFp_toNat_long hpos]; omega)

theorem weth9SymLongEncMemB_read128 : (weth9SymLongEncMemB σ I).readWithPadding 128 32 =
    (weth9StringLen (weth9StringSlotWord σ I ⟨1⟩)).toByteArray := by
  rw [weth9SymLongEncMemB]
  exact weth9EncLowRead (weth9SymLongEncMemA_read128 hpos)
    (by rw [weth9SymLongEncMemA_size hpos, weth9SymStringNewFp_toNat_long hpos]; omega)
    (by rw [weth9SymLongEncMemA_size hpos])
    (by rw [weth9SymLongEncMemA_size hpos]; exact lt_usize _ (by norm_num))
    (by rw [weth9SymStringNewFp_toNat_long hpos]; omega)

theorem weth9SymLongEncMemB_readData (k : Nat) (hk : k ≤ weth9SymLongWC σ I) :
    (weth9SymLongEncMemB σ I).readWithPadding (160 + 32 * k) 32 =
      (weth9SymLongDataWordAt σ I k).toByteArray := by
  rw [weth9SymLongEncMemB]
  exact weth9EncLowRead (weth9SymLongEncMemA_readData hpos k hk)
    (by rw [weth9SymLongEncMemA_size hpos, weth9SymStringNewFp_toNat_long hpos]; omega)
    (by rw [weth9SymLongEncMemA_size hpos])
    (by rw [weth9SymLongEncMemA_size hpos]; exact lt_usize _ (by norm_num))
    (by rw [weth9SymStringNewFp_toNat_long hpos]; omega)

theorem weth9SymLongEncMemB_readOffset : (weth9SymLongEncMemB σ I).readWithPadding
    (weth9StringNewFp (weth9StringSlotWord σ I ⟨1⟩)).toNat 32 = UInt256.toByteArray ⟨32⟩ := by
  rw [weth9SymLongEncMemB]
  exact weth9EncLowRead (weth9SymLongEncMemA_readOffset hpos)
    (by rw [weth9SymLongEncMemA_size hpos])
    (by rw [weth9SymLongEncMemA_size hpos])
    (by rw [weth9SymLongEncMemA_size hpos]; exact lt_usize _ (by norm_num))
    (le_refl _)

theorem weth9SymLongEncMemB_readLen : (weth9SymLongEncMemB σ I).readWithPadding
    ((weth9StringNewFp (weth9StringSlotWord σ I ⟨1⟩)).toNat + 32) 32 =
      (weth9StringLen (weth9StringSlotWord σ I ⟨1⟩)).toByteArray := by
  rw [weth9SymLongEncMemB]
  exact writeWord_read_back _ _ _
    (by rw [weth9SymLongEncMemA_size hpos]; exact lt_usize _ (by norm_num))

/-- Loop-2 memory size after `j` copies: `0x100 + 32·(wc-1) + 32·j`. -/
theorem weth9SymLong2Mem_size :
    ∀ j : Nat, (weth9SymLong2Mem σ I j).size = 256 + 32 * weth9SymLongWC σ I + 32 * j
  | 0 => by
      rw [weth9SymLong2Mem_zero, weth9SymLongEncMemB_size hpos, weth9SymStringNewFp_toNat_long hpos]; omega
  | j + 1 => by
      rw [weth9SymLong2Mem_succ,
        writeWord_size _ _ _ (by rw [weth9SymLong2Mem_size j, Nat.sub_self]; exact lt_usize 0 (by norm_num)),
        weth9SymLong2Mem_size j]; omega

/-- Any read window below the ABI data region survives every Loop-2 copy. -/
theorem weth9SymLong2Mem_read_low (r : Nat) (hr : r + 32 ≤ 256 + 32 * weth9SymLongWC σ I) :
    ∀ j : Nat, (weth9SymLong2Mem σ I j).readWithPadding r 32 =
      (weth9SymLongEncMemB σ I).readWithPadding r 32
  | 0 => by rw [weth9SymLong2Mem_zero]
  | j + 1 => by
      rw [weth9SymLong2Mem_succ, writeWord_read_preserved _ _ r _
        (by rw [weth9SymLong2Mem_size hpos j, Nat.sub_self]; exact lt_usize 0 (by norm_num))
        (Or.inl ⟨by omega, by rw [weth9SymLong2Mem_size hpos j]; omega⟩)]
      exact weth9SymLong2Mem_read_low r hr j

theorem weth9SymLong2Mem_read64 (j : Nat) :
    (weth9SymLong2Mem σ I j).readWithPadding 64 32 =
      (weth9StringNewFp (weth9StringSlotWord σ I ⟨1⟩)).toByteArray := by
  rw [weth9SymLong2Mem_read_low hpos 64 (by omega) j, weth9SymLongEncMemB_read64 hpos]

theorem weth9SymLong2Mem_readOffset (j : Nat) :
    (weth9SymLong2Mem σ I j).readWithPadding (weth9StringNewFp (weth9StringSlotWord σ I ⟨1⟩)).toNat 32 =
      UInt256.toByteArray ⟨32⟩ := by
  rw [weth9SymLong2Mem_read_low hpos _ (by rw [weth9SymStringNewFp_toNat_long hpos]; omega) j,
    weth9SymLongEncMemB_readOffset hpos]

theorem weth9SymLong2Mem_readLen (j : Nat) :
    (weth9SymLong2Mem σ I j).readWithPadding
      ((weth9StringNewFp (weth9StringSlotWord σ I ⟨1⟩)).toNat + 32) 32 =
      (weth9StringLen (weth9StringSlotWord σ I ⟨1⟩)).toByteArray := by
  rw [weth9SymLong2Mem_read_low hpos _ (by rw [weth9SymStringNewFp_toNat_long hpos]; omega) j,
    weth9SymLongEncMemB_readLen hpos]

theorem weth9SymLong2Mem_readSrc (j k : Nat) (hk : k ≤ weth9SymLongWC σ I) :
    (weth9SymLong2Mem σ I j).readWithPadding (160 + 32 * k) 32 =
      (weth9SymLongDataWordAt σ I k).toByteArray := by
  rw [weth9SymLong2Mem_read_low hpos (160 + 32 * k) (by omega) j, weth9SymLongEncMemB_readData hpos k hk]

/-- Loop-2 memory holds copied data word `k` at `newFp+0x40 + 32·k` for every `k < j`. -/
theorem weth9SymLong2Mem_readDest (k : Nat) :
    ∀ j : Nat, k < j → (weth9SymLong2Mem σ I j).readWithPadding (256 + 32 * weth9SymLongWC σ I + 32 * k) 32 =
      (weth9SymLongDataWordAt σ I k).toByteArray
  | 0, hkj => absurd hkj (by omega)
  | j + 1, hkj => by
      rw [weth9SymLong2Mem_succ]
      rcases Nat.lt_or_ge k j with hlt | hge
      · rw [writeWord_read_preserved _ _ (256 + 32 * weth9SymLongWC σ I + 32 * k) _
          (by rw [weth9SymLong2Mem_size hpos j, Nat.sub_self]; exact lt_usize 0 (by norm_num))
          (Or.inl ⟨by omega, by rw [weth9SymLong2Mem_size hpos j]; omega⟩)]
        exact weth9SymLong2Mem_readDest k j hlt
      · have hk : k = j := by omega
        subst hk
        rw [writeWord_read_back _ _ _
          (by rw [weth9SymLong2Mem_size hpos k, Nat.sub_self]; exact lt_usize 0 (by norm_num))]

end EncMem

/-- The Loop-2 head/exit stack at counter `i` (offset into the ABI data region). -/
def weth9SymLong2LoopStack (σ : AccountMap) (I : ExecutionEnv) (i : UInt256) : List UInt256 :=
  [i, (⟨128⟩ : UInt256) + ⟨32⟩, weth9StringNewFp (weth9StringSlotWord σ I ⟨1⟩) + ⟨64⟩,
   weth9StringLen (weth9StringSlotWord σ I ⟨1⟩), weth9StringLen (weth9StringSlotWord σ I ⟨1⟩),
   (⟨128⟩ : UInt256) + ⟨32⟩, weth9StringNewFp (weth9StringSlotWord σ I ⟨1⟩) + ⟨64⟩,
   weth9StringNewFp (weth9StringSlotWord σ I ⟨1⟩), weth9StringNewFp (weth9StringSlotWord σ I ⟨1⟩),
   ⟨128⟩, ⟨187⟩, weth9SelWord I]

set_option maxHeartbeats 8000000 in
/-- Setup (pc 187 → 221): write the ABI offset + length words and reach the Loop-2 head. -/
theorem weth9SymNameLong2ReachLoopHead {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = weth9Bytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (weth9SelBytes 7))
    (hge31 : UInt256.lt ⟨31⟩ (weth9StringLen (weth9StringSlotWord σ I ⟨1⟩)) ≠ ⟨0⟩)
    (hfit : 96 + 32 * weth9SymLongWC σ I < 2 ^ 64) :
    ∃ k C, RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨221⟩
      (weth9SymLong2LoopStack σ I ⟨0⟩)
      (weth9SymLong2Mem σ I 0) (UInt256.ofNat (8 + weth9SymLongWC σ I)) ByteArray.empty (cA, σ) k C := by
  have hpos : 1 ≤ (weth9StringLen (weth9StringSlotWord σ I ⟨1⟩)).toNat := by
    have := weth9SymLongLen_ge32 hge31; omega
  have h66 : (2 : Nat) ^ 66 < UInt256.size := by norm_num [UInt256.size]
  have hbig : 288 + 64 * weth9SymLongWC σ I < UInt256.size := by omega
  have hfpN : (weth9StringNewFp (weth9StringSlotWord σ I ⟨1⟩)).toNat = 192 + 32 * weth9SymLongWC σ I :=
    weth9SymStringNewFp_toNat_long hpos
  have haddr32 : ((weth9StringNewFp (weth9StringSlotWord σ I ⟨1⟩)) + ⟨32⟩).toNat =
      (weth9StringNewFp (weth9StringSlotWord σ I ⟨1⟩)).toNat + 32 := by
    rw [uadd_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
      Nat.mod_eq_of_lt (by rw [hfpN]; omega)]
  obtain ⟨_, _, h187⟩ := weth9SymNameLongReach187 (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz4 hsize hsel hge31
  have h221 := evm_run h187 with [
    jumpdest, push1 ⟨64⟩, dup1,
    raw mload _ (weth9StringNewFp (weth9StringSlotWord σ I ⟨1⟩)) (UInt256.ofNat (6 + weth9SymLongWC σ I))
      (by decide +native) weth9MloadCostSpec
      (mloadWordValue_of_readWithPadding
        (by rw [weth9SymLongFinalMem_size', show (⟨64⟩ : UInt256).toNat = 64 from by decide]; omega)
        (wordMul32_not_ge_of_lt (by rw [weth9SymLongFinalAw_toNat, show (⟨64⟩ : UInt256).toNat = 64 from by decide]; omega)
          (by rw [weth9SymLongFinalAw_toNat]; omega))
        (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; exact weth9SymLongFinalMem_read64 σ I))
      (by rw [weth9SymLongFinalAw_toNat, show (⟨64⟩ : UInt256).toNat = 64 from by decide,
        machineState_M_inBounds (show (64 : Nat) + 32 ≤ 32 * (6 + weth9SymLongWC σ I) from by omega)])
      (by evm_ov),
    push1 ⟨32⟩, dup1, dup3,
    raw mstore _ (weth9SymLongEncMemA σ I) (UInt256.ofNat (7 + weth9SymLongWC σ I))
      (by decide +native) weth9MstoreCostSpec rfl
      (by rw [ulit_toNat' _ (by omega), hfpN,
        show (192 + 32 * weth9SymLongWC σ I : Nat) = 32 * (6 + weth9SymLongWC σ I) from by ring,
        machineState_M_endWrite]; congr 1; omega) (by evm_ov),
    dup4,
    raw mload _ (weth9StringLen (weth9StringSlotWord σ I ⟨1⟩)) (UInt256.ofNat (7 + weth9SymLongWC σ I))
      (by decide +native) weth9MloadCostSpec
      (mloadWordValue_of_readWithPadding
        (by rw [weth9SymLongEncMemA_size hpos, hfpN, show (⟨128⟩ : UInt256).toNat = 128 from by decide]; omega)
        (wordMul32_not_ge_of_lt (by rw [ulit_toNat' _ (by omega), show (⟨128⟩ : UInt256).toNat = 128 from by decide]; omega)
          (by rw [ulit_toNat' _ (by omega)]; omega))
        (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; exact weth9SymLongEncMemA_read128 hpos))
      (by rw [ulit_toNat' _ (by omega), show (⟨128⟩ : UInt256).toNat = 128 from by decide,
        machineState_M_inBounds (show (128 : Nat) + 32 ≤ 32 * (7 + weth9SymLongWC σ I) from by omega)])
      (by evm_ov),
    dup2, dup4, add,
    raw mstore _ (weth9SymLongEncMemB σ I) (UInt256.ofNat (8 + weth9SymLongWC σ I))
      (by decide +native) weth9MstoreCostSpec
      (by rw [weth9SymLongEncMemB, Reasoning.Theory.writeWord, haddr32])
      (by rw [ulit_toNat' _ (by omega), haddr32, hfpN,
        show (192 + 32 * weth9SymLongWC σ I + 32 : Nat) = 32 * (7 + weth9SymLongWC σ I) from by ring,
        machineState_M_endWrite]; congr 1; omega) (by evm_ov),
    dup4,
    raw mload _ (weth9StringLen (weth9StringSlotWord σ I ⟨1⟩)) (UInt256.ofNat (8 + weth9SymLongWC σ I))
      (by decide +native) weth9MloadCostSpec
      (mloadWordValue_of_readWithPadding
        (by rw [weth9SymLongEncMemB_size hpos, hfpN, show (⟨128⟩ : UInt256).toNat = 128 from by decide]; omega)
        (wordMul32_not_ge_of_lt (by rw [ulit_toNat' _ (by omega), show (⟨128⟩ : UInt256).toNat = 128 from by decide]; omega)
          (by rw [ulit_toNat' _ (by omega)]; omega))
        (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; exact weth9SymLongEncMemB_read128 hpos))
      (by rw [ulit_toNat' _ (by omega), show (⟨128⟩ : UInt256).toNat = 128 from by decide,
        machineState_M_inBounds (show (128 : Nat) + 32 ≤ 32 * (8 + weth9SymLongWC σ I) from by omega)])
      (by evm_ov),
    swap2, swap3, dup4, swap3, swap1, dup4, add, swap2, dup6, add, swap1,
    dup1, dup4, dup4, push1 ⟨0⟩]
  rw [weth9SymLong2Mem_zero, weth9SymLong2LoopStack]
  exact ⟨_, _, h221⟩

set_option maxHeartbeats 8000000 in
/-- One Loop-2 iteration (pc 221 → 221): copy `mem[0xa0+i] → mem[newFp+0x40+i]`, `i += 32`. -/
theorem weth9SymNameLong2Continue {cA gh bl σ σ₀ A I} {g : Sat256} (j : Nat)
    (hpos : 1 ≤ (weth9StringLen (weth9StringSlotWord σ I ⟨1⟩)).toNat)
    (hfit : 96 + 32 * weth9SymLongWC σ I < 2 ^ 64)
    (hjlt : j < weth9SymLongWC σ I + 1)
    (h : ∃ k C, RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨221⟩
      (weth9SymLong2LoopStack σ I (UInt256.ofNat (32 * j)))
      (weth9SymLong2Mem σ I j) (UInt256.ofNat (8 + weth9SymLongWC σ I + j)) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨221⟩
      (weth9SymLong2LoopStack σ I (UInt256.ofNat (32 * (j + 1))))
      (weth9SymLong2Mem σ I (j + 1)) (UInt256.ofNat (8 + weth9SymLongWC σ I + (j + 1)))
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd221⟩ := h
  rw [weth9SymLong2LoopStack] at rd221
  have h66 : (2 : Nat) ^ 66 < UInt256.size := by norm_num [UInt256.size]
  have hbig : 288 + 64 * weth9SymLongWC σ I < UInt256.size := by omega
  have hfpN : (weth9StringNewFp (weth9StringSlotWord σ I ⟨1⟩)).toNat = 192 + 32 * weth9SymLongWC σ I :=
    weth9SymStringNewFp_toNat_long hpos
  -- length lower bound so the continue guard holds.
  have hlenGt : 32 * weth9SymLongWC σ I < (weth9StringLen (weth9StringSlotWord σ I ⟨1⟩)).toNat := by
    have := Nat.div_mul_le_self ((weth9StringLen (weth9StringSlotWord σ I ⟨1⟩)).toNat - 1) 32
    rw [weth9SymLongWC]; omega
  have hi : (UInt256.ofNat (32 * j)).toNat = 32 * j := ulit_toNat' _ (by omega)
  have haddr64 : (weth9StringNewFp (weth9StringSlotWord σ I ⟨1⟩) + ⟨64⟩).toNat =
      256 + 32 * weth9SymLongWC σ I := by
    rw [uadd_toNat, hfpN, show (⟨64⟩ : UInt256).toNat = 64 from by decide,
      Nat.mod_eq_of_lt (by omega)]; omega
  have hsrc : (UInt256.ofNat (32 * j) + ((⟨128⟩ : UInt256) + ⟨32⟩)).toNat = 160 + 32 * j := by
    rw [uadd_toNat, hi, show ((⟨128⟩ : UInt256) + ⟨32⟩).toNat = 160 from by decide,
      Nat.mod_eq_of_lt (by omega)]; omega
  have hdst : (UInt256.ofNat (32 * j) + (weth9StringNewFp (weth9StringSlotWord σ I ⟨1⟩) + ⟨64⟩)).toNat =
      256 + 32 * weth9SymLongWC σ I + 32 * j := by
    rw [uadd_toNat, hi, haddr64, Nat.mod_eq_of_lt (by omega)]; omega
  have hincr : (⟨32⟩ : UInt256) + UInt256.ofNat (32 * j) = UInt256.ofNat (32 * (j + 1)) := by
    apply u256_inj
    rw [uadd_toNat, hi, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
      Nat.mod_eq_of_lt (by omega), ulit_toNat' _ (by omega)]; ring
  have hcont : UInt256.isZero (UInt256.lt (UInt256.ofNat (32 * j))
      (weth9StringLen (weth9StringSlotWord σ I ⟨1⟩))) = ⟨0⟩ := by
    rw [ult_one (by rw [hi]; omega)]; decide
  have rd := evm_run rd221 with [
    jumpdest, dup4, dup2, lt, iszero, push2 ⟨245⟩, jumpiNT hcont,
    dup2, dup2, add,
    raw mload _ (weth9SymLongDataWordAt σ I j) (UInt256.ofNat (8 + weth9SymLongWC σ I + j))
      (by decide +native) weth9MloadCostSpec
      (mloadWordValue_of_readWithPadding
        (by rw [hsrc, weth9SymLong2Mem_size hpos]; omega)
        (wordMul32_not_ge_of_lt (by rw [hsrc, ulit_toNat' _ (by omega)]; omega)
          (by rw [ulit_toNat' _ (by omega)]; omega))
        (by rw [hsrc]; exact weth9SymLong2Mem_readSrc hpos j j (by omega)))
      (by rw [hsrc, ulit_toNat' _ (by omega),
        machineState_M_inBounds (show (160 + 32 * j) + 32 ≤ 32 * (8 + weth9SymLongWC σ I + j) from by omega)])
      (by evm_ov),
    dup4, dup3, add,
    raw mstore _ (weth9SymLong2Mem σ I (j + 1)) (UInt256.ofNat (8 + weth9SymLongWC σ I + (j + 1)))
      (by decide +native) weth9MstoreCostSpec
      (by rw [weth9SymLong2Mem_succ, Reasoning.Theory.writeWord, hdst])
      (by rw [ulit_toNat' _ (by omega), hdst,
        show (256 + 32 * weth9SymLongWC σ I + 32 * j : Nat) = 32 * (8 + weth9SymLongWC σ I + j) from by ring,
        machineState_M_endWrite, show 8 + weth9SymLongWC σ I + j + 1 = 8 + weth9SymLongWC σ I + (j + 1) from by omega]) (by evm_ov),
    push1 ⟨32⟩, add, push2 ⟨221⟩, jump (by jump_dest)]
  rw [hincr] at rd
  exact ⟨_, _, rd⟩

set_option maxHeartbeats 8000000 in
/-- Run the Loop-2 mem→mem copy (pc 221) to exhaustion (`wc` iterations), reaching the exit (pc 245)
    with all data words copied. -/
theorem weth9SymNameLong2CopyLoop {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpos : 1 ≤ (weth9StringLen (weth9StringSlotWord σ I ⟨1⟩)).toNat)
    (hfit : 96 + 32 * weth9SymLongWC σ I < 2 ^ 64)
    (h : ∃ k C, RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨221⟩
      (weth9SymLong2LoopStack σ I ⟨0⟩)
      (weth9SymLong2Mem σ I 0) (UInt256.ofNat (8 + weth9SymLongWC σ I)) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨245⟩
      (weth9SymLong2LoopStack σ I (UInt256.ofNat (32 * (weth9SymLongWC σ I + 1))))
      (weth9SymLong2Mem σ I (weth9SymLongWC σ I + 1))
      (UInt256.ofNat (8 + weth9SymLongWC σ I + (weth9SymLongWC σ I + 1))) ByteArray.empty (cA, σ) k C := by
  have h66 : (2 : Nat) ^ 66 < UInt256.size := by norm_num [UInt256.size]
  have hbig : 288 + 64 * weth9SymLongWC σ I < UInt256.size := by omega
  have hdone : (weth9StringLen (weth9StringSlotWord σ I ⟨1⟩)).toNat ≤ 32 * (weth9SymLongWC σ I + 1) := by
    have := weth9LongFuel_done_nat (show 0 < (weth9StringLen (weth9StringSlotWord σ I ⟨1⟩)).toNat from by omega)
    rw [weth9SymLongWC]; omega
  -- exit rule
  have hexit : ∀ a : ℕ, a + 0 = weth9SymLongWC σ I + 1 → ∀ k C,
      RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨221⟩
        (weth9SymLong2LoopStack σ I (UInt256.ofNat (32 * a)))
        (weth9SymLong2Mem σ I a) (UInt256.ofNat (8 + weth9SymLongWC σ I + a)) ByteArray.empty (cA, σ) k C →
      ∃ k' C', RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨245⟩
        (weth9SymLong2LoopStack σ I (UInt256.ofNat (32 * a)))
        (weth9SymLong2Mem σ I a) (UInt256.ofNat (8 + weth9SymLongWC σ I + a)) ByteArray.empty (cA, σ) k' C' := by
    intro a hInv k C hrd
    have ha : a = weth9SymLongWC σ I + 1 := by omega
    subst ha
    rw [weth9SymLong2LoopStack] at hrd
    have hcond : UInt256.isZero (UInt256.lt (UInt256.ofNat (32 * (weth9SymLongWC σ I + 1)))
        (weth9StringLen (weth9StringSlotWord σ I ⟨1⟩))) ≠ ⟨0⟩ := by
      rw [ult_zero (by rw [ulit_toNat' _ (by omega)]; omega)]; decide
    have rd := evm_run hrd with [
      jumpdest, dup4, dup2, lt, iszero, push2 ⟨245⟩, jumpiT hcond (by jump_dest)]
    exact ⟨_, _, rd⟩
  -- body rule
  have hbody : ∀ (v a : ℕ), a + (v + 1) = weth9SymLongWC σ I + 1 → ∀ k C,
      RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨221⟩
        (weth9SymLong2LoopStack σ I (UInt256.ofNat (32 * a)))
        (weth9SymLong2Mem σ I a) (UInt256.ofNat (8 + weth9SymLongWC σ I + a)) ByteArray.empty (cA, σ) k C →
      ∃ a' k' C', a' + v = weth9SymLongWC σ I + 1 ∧
        RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨221⟩
          (weth9SymLong2LoopStack σ I (UInt256.ofNat (32 * a')))
          (weth9SymLong2Mem σ I a') (UInt256.ofNat (8 + weth9SymLongWC σ I + a')) ByteArray.empty (cA, σ) k' C' := by
    intro v a hInv k C hrd
    obtain ⟨k', C', rd'⟩ := weth9SymNameLong2Continue a hpos hfit (by omega) ⟨k, C, hrd⟩
    exact ⟨a + 1, k', C', by omega, rd'⟩
  obtain ⟨k0, C0, h0⟩ := h
  have h0' : RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨221⟩
      (weth9SymLong2LoopStack σ I (UInt256.ofNat (32 * 0)))
      (weth9SymLong2Mem σ I 0) (UInt256.ofNat (8 + weth9SymLongWC σ I + 0)) ByteArray.empty (cA, σ) k0 C0 := by
    simpa using h0
  obtain ⟨a', k', C', hInv0, hexitRD⟩ :=
    RD.whileLoopCarry ⟨221⟩ ⟨245⟩ (fun v j => j + v = weth9SymLongWC σ I + 1)
      (fun j => weth9SymLong2LoopStack σ I (UInt256.ofNat (32 * j)))
      (fun j => weth9SymLong2Mem σ I j) (fun j => UInt256.ofNat (8 + weth9SymLongWC σ I + j))
      (fun j => weth9SymLong2LoopStack σ I (UInt256.ofNat (32 * j)))
      hexit hbody (weth9SymLongWC σ I + 1) 0 (by omega) k0 C0 h0'
  have ha' : a' = weth9SymLongWC σ I + 1 := by omega
  subst ha'
  exact ⟨_, _, hexitRD⟩

/-! ## Final memory (after the trailing-word mask) and the RETURN window -/

/-- Memory at the RETURN: the Loop-2 output, with the trailing data word replaced by its masked value
    (the mask store is skipped when `len` is a multiple of 32, in which case the last word is full). -/
noncomputable def weth9SymLong2FinalMem (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  if UInt256.land ⟨31⟩ (weth9StringLen (weth9StringSlotWord σ I ⟨1⟩)) = ⟨0⟩ then
    weth9SymLong2Mem σ I (weth9SymLongWC σ I + 1)
  else
    writeWord (weth9SymLong2Mem σ I (weth9SymLongWC σ I + 1)) (256 + 64 * weth9SymLongWC σ I)
      (weth9SymLongMaskWord σ I)

section FinalMem
variable {σ : AccountMap} {I : ExecutionEnv}
  (hpos : 1 ≤ (weth9StringLen (weth9StringSlotWord σ I ⟨1⟩)).toNat)
  (hfit : 96 + 32 * weth9SymLongWC σ I < 2 ^ 64)
include hpos hfit

omit hfit in
theorem weth9SymLong2FinalMem_size : (weth9SymLong2FinalMem σ I).size = 288 + 64 * weth9SymLongWC σ I := by
  have hmem : (weth9SymLong2Mem σ I (weth9SymLongWC σ I + 1)).size = 288 + 64 * weth9SymLongWC σ I := by
    rw [weth9SymLong2Mem_size hpos]; omega
  unfold weth9SymLong2FinalMem
  split
  · exact hmem
  · rw [writeWord_size _ _ _ (by rw [hmem]; exact lt_usize _ (by omega)), hmem]; omega

theorem weth9SymLong2FinalMem_read64 : (weth9SymLong2FinalMem σ I).readWithPadding 64 32 =
    (weth9StringNewFp (weth9StringSlotWord σ I ⟨1⟩)).toByteArray := by
  have hfpN := weth9SymStringNewFp_toNat_long hpos
  unfold weth9SymLong2FinalMem
  split
  · exact weth9SymLong2Mem_read64 hpos _
  · rw [writeWord_read_preserved _ _ _ _
      (by rw [weth9SymLong2Mem_size hpos]; exact lt_usize _ (by omega))
      (Or.inl ⟨by omega, by rw [weth9SymLong2Mem_size hpos]; omega⟩)]
    exact weth9SymLong2Mem_read64 hpos _

theorem weth9SymLong2FinalMem_readOffset : (weth9SymLong2FinalMem σ I).readWithPadding
    (weth9StringNewFp (weth9StringSlotWord σ I ⟨1⟩)).toNat 32 = UInt256.toByteArray ⟨32⟩ := by
  have hfpN := weth9SymStringNewFp_toNat_long hpos
  unfold weth9SymLong2FinalMem
  split
  · exact weth9SymLong2Mem_readOffset hpos _
  · rw [writeWord_read_preserved _ _ _ _
      (by rw [weth9SymLong2Mem_size hpos]; exact lt_usize _ (by omega))
      (Or.inl ⟨by rw [hfpN]; omega, by rw [weth9SymLong2Mem_size hpos, hfpN]; omega⟩)]
    exact weth9SymLong2Mem_readOffset hpos _

theorem weth9SymLong2FinalMem_readLen : (weth9SymLong2FinalMem σ I).readWithPadding
    ((weth9StringNewFp (weth9StringSlotWord σ I ⟨1⟩)).toNat + 32) 32 =
      (weth9StringLen (weth9StringSlotWord σ I ⟨1⟩)).toByteArray := by
  have hfpN := weth9SymStringNewFp_toNat_long hpos
  unfold weth9SymLong2FinalMem
  split
  · exact weth9SymLong2Mem_readLen hpos _
  · rw [writeWord_read_preserved _ _ _ _
      (by rw [weth9SymLong2Mem_size hpos]; exact lt_usize _ (by omega))
      (Or.inl ⟨by rw [hfpN]; omega, by rw [weth9SymLong2Mem_size hpos, hfpN]; omega⟩)]
    exact weth9SymLong2Mem_readLen hpos _

omit hfit in
theorem weth9SymLong2FinalMem_readDest (k : Nat) (hk : k < weth9SymLongWC σ I) :
    (weth9SymLong2FinalMem σ I).readWithPadding (256 + 32 * weth9SymLongWC σ I + 32 * k) 32 =
      (weth9SymLongDataWordAt σ I k).toByteArray := by
  unfold weth9SymLong2FinalMem
  split
  · exact weth9SymLong2Mem_readDest hpos k _ (by omega)
  · rw [writeWord_read_preserved _ _ _ _
      (by rw [weth9SymLong2Mem_size hpos]; exact lt_usize _ (by omega))
      (Or.inl ⟨by omega, by rw [weth9SymLong2Mem_size hpos]; omega⟩)]
    exact weth9SymLong2Mem_readDest hpos k _ (by omega)

omit hfit in
theorem weth9SymLong2FinalMem_readLast :
    (weth9SymLong2FinalMem σ I).readWithPadding (256 + 64 * weth9SymLongWC σ I) 32 =
      (weth9SymLongMaskWord σ I).toByteArray := by
  unfold weth9SymLong2FinalMem weth9SymLongMaskWord
  split
  · have := weth9SymLong2Mem_readDest hpos (weth9SymLongWC σ I) (weth9SymLongWC σ I + 1) (by omega)
    rw [show 256 + 32 * weth9SymLongWC σ I + 32 * weth9SymLongWC σ I = 256 + 64 * weth9SymLongWC σ I from by ring] at this
    exact this
  · exact writeWord_read_back _ _ _
      (by rw [weth9SymLong2Mem_size hpos]; exact lt_usize _ (by omega))

/-- The `RETURN(newFp, 0x40 + 32·wc)` window over the finished memory is exactly `weth9SymLongStringAbi`. -/
theorem weth9SymLong2FinalMem_readAbi :
    (weth9SymLong2FinalMem σ I).readWithPadding (weth9StringNewFp (weth9StringSlotWord σ I ⟨1⟩)).toNat
      (64 + 32 * (weth9SymLongWC σ I + 1)) = weth9SymLongStringAbi σ I := by
  have hfpN := weth9SymStringNewFp_toNat_long hpos
  have hsz := weth9SymLong2FinalMem_size hpos
  -- word function for the data region: unmasked words, masked last
  set fLast : Nat → UInt256 := fun k =>
    if k = weth9SymLongWC σ I then weth9SymLongMaskWord σ I else weth9SymLongDataWordAt σ I k with hfL
  have hdata : (weth9SymLong2FinalMem σ I).readWithPadding (256 + 32 * weth9SymLongWC σ I)
      (32 * (weth9SymLongWC σ I + 1)) = wordConcat fLast 0 (weth9SymLongWC σ I + 1) := by
    have := readWithPadding_wordConcat (weth9SymLong2FinalMem σ I) fLast (256 + 32 * weth9SymLongWC σ I)
      (weth9SymLongWC σ I + 1) 0 (by omega) (by rw [hsz]; omega)
      (by intro k hk
          simp only [Nat.zero_add, hfL]
          rcases Nat.lt_or_ge k (weth9SymLongWC σ I) with hlt | hge
          · rw [if_neg (by omega)]
            exact weth9SymLong2FinalMem_readDest hpos k hlt
          · have hkeq : k = weth9SymLongWC σ I := by omega
            subst hkeq
            rw [if_pos rfl,
              show 256 + 32 * weth9SymLongWC σ I + 32 * weth9SymLongWC σ I = 256 + 64 * weth9SymLongWC σ I from by ring]
            exact weth9SymLong2FinalMem_readLast hpos)
    simpa using this
  have hlast : fLast (weth9SymLongWC σ I) = weth9SymLongMaskWord σ I := by rw [hfL]; simp
  have hconcat : wordConcat fLast 0 (weth9SymLongWC σ I + 1) =
      wordConcat (weth9SymLongDataWordAt σ I) 0 (weth9SymLongWC σ I) ++
        (weth9SymLongMaskWord σ I).toByteArray := by
    rw [wordConcat_append_last fLast (weth9SymLongWC σ I) 0, Nat.zero_add, hlast]
    congr 1
    apply wordConcat_congr
    intro k hk
    show (if 0 + k = weth9SymLongWC σ I then weth9SymLongMaskWord σ I
      else weth9SymLongDataWordAt σ I (0 + k)) = weth9SymLongDataWordAt σ I (0 + k)
    rw [if_neg (by omega)]
  rw [weth9SymLongStringAbi]
  rw [show (64 + 32 * (weth9SymLongWC σ I + 1)) = 32 + (32 + 32 * (weth9SymLongWC σ I + 1)) from by ring,
    byteArray_readWithPadding_split _ _ 32 (32 + 32 * (weth9SymLongWC σ I + 1)) (by norm_num)
      (by omega) (by norm_num) (by omega) (by omega) (by rw [hsz, hfpN]; omega),
    byteArray_readWithPadding_split _ _ 32 (32 * (weth9SymLongWC σ I + 1)) (by norm_num)
      (by omega) (by norm_num) (by omega) (by omega) (by rw [hsz, hfpN]; omega),
    weth9SymLong2FinalMem_readOffset hpos hfit]
  congr 1
  rw [show (weth9StringNewFp (weth9StringSlotWord σ I ⟨1⟩)).toNat + 32 =
      (weth9StringNewFp (weth9StringSlotWord σ I ⟨1⟩)).toNat + 32 from rfl,
    weth9SymLong2FinalMem_readLen hpos hfit]
  congr 1
  rw [show (weth9StringNewFp (weth9StringSlotWord σ I ⟨1⟩)).toNat + 32 + 32 =
      256 + 32 * weth9SymLongWC σ I from by rw [hfpN]; ring, hdata, hconcat]

end FinalMem

/-- When `len` is not a multiple of 32, `32·(wc-1) + (len % 32) = len` (`wc-1 = weth9SymLongWC`). -/
theorem weth9SymLong2Len_sub_mod {σ : AccountMap} {I : ExecutionEnv}
    (hr : (weth9StringLen (weth9StringSlotWord σ I ⟨1⟩)).toNat % 32 ≠ 0) :
    32 * weth9SymLongWC σ I + (weth9StringLen (weth9StringSlotWord σ I ⟨1⟩)).toNat % 32 =
      (weth9StringLen (weth9StringSlotWord σ I ⟨1⟩)).toNat := by
  rw [weth9SymLongWC]; omega

set_option maxHeartbeats 8000000 in
/-- **Full long-string `name()` ABI return encoder** (`len ≥ 32`): from the encoder entry (pc 187,
    the string data already copied into memory), write the ABI `(offset, len, data)` triple, copy the
    data words (Loop-2), zero the trailing garbage (tail mask, when `len % 32 ≠ 0`), and `RETURN`
    `weth9SymLongStringAbi`.  Config-independent, symbolic `len ≥ 32`; `hfit` bounds the returned object
    to a 64-bit-addressable size (EVM cannot return `≥ 2⁶⁴` bytes). -/
theorem weth9SymbolStringLongReturns {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = weth9Bytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (weth9SelBytes 7))
    (hge31 : UInt256.lt ⟨31⟩ (weth9StringLen (weth9StringSlotWord σ I ⟨1⟩)) ≠ ⟨0⟩)
    (hfit : 96 + 32 * weth9SymLongWC σ I < 2 ^ 64) :
    RDret weth9Bytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ) (weth9SymLongStringAbi σ I) := by
  have hpos : 1 ≤ (weth9StringLen (weth9StringSlotWord σ I ⟨1⟩)).toNat := by
    have := weth9SymLongLen_ge32 hge31; omega
  have h66 : (2 : Nat) ^ 66 < UInt256.size := by norm_num [UInt256.size]
  have hbig : 288 + 64 * weth9SymLongWC σ I < UInt256.size := by omega
  have hfpN := weth9SymStringNewFp_toNat_long hpos
  have hlandN := weth9Long2Land31_toNat (weth9StringSlotWord σ I ⟨1⟩)
  have haddr64 : (weth9StringNewFp (weth9StringSlotWord σ I ⟨1⟩) + ⟨64⟩).toNat =
      256 + 32 * weth9SymLongWC σ I := by
    rw [uadd_toNat, hfpN, show (⟨64⟩ : UInt256).toNat = 64 from by decide,
      Nat.mod_eq_of_lt (by omega)]; omega
  have hawnorm : 8 + weth9SymLongWC σ I + (weth9SymLongWC σ I + 1) = 9 + 2 * weth9SymLongWC σ I := by omega
  obtain ⟨_, _, h245⟩ := weth9SymNameLong2CopyLoop (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hpos hfit
    (weth9SymNameLong2ReachLoopHead (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) hcode hwv hsz4 hsize hsel hge31 hfit)
  rw [weth9SymLong2LoopStack] at h245
  -- common prefix: pops, tail-offset arithmetic, tail-mask decision.
  have hpre := evm_run h245 with [
    jumpdest, pop, pop, pop, pop, swap1, pop, swap1, dup2, add, swap1,
    push1 ⟨31⟩, and, dup1, iszero, push2 ⟨290⟩]
  by_cases hmask : UInt256.land ⟨31⟩ (weth9StringLen (weth9StringSlotWord σ I ⟨1⟩)) = ⟨0⟩
  · -- len is a multiple of 32: skip the mask; last word is full.
    have hlen32 : (weth9StringLen (weth9StringSlotWord σ I ⟨1⟩)).toNat = 32 * (weth9SymLongWC σ I + 1) := by
      have hz : (weth9StringLen (weth9StringSlotWord σ I ⟨1⟩)).toNat % 32 = 0 := by
        have := congrArg UInt256.toNat hmask; rw [hlandN] at this; simpa using this
      rw [weth9SymLongWC]; omega
    have hcond : UInt256.isZero (UInt256.land ⟨31⟩ (weth9StringLen (weth9StringSlotWord σ I ⟨1⟩))) ≠ ⟨0⟩ := by
      rw [hmask]; decide
    have hretlen : (UInt256.sub (weth9StringLen (weth9StringSlotWord σ I ⟨1⟩) +
        (weth9StringNewFp (weth9StringSlotWord σ I ⟨1⟩) + ⟨64⟩))
        (weth9StringNewFp (weth9StringSlotWord σ I ⟨1⟩))).toNat = 64 + 32 * (weth9SymLongWC σ I + 1) := by
      rw [usub_toNat (by rw [uadd_toNat, haddr64, Nat.mod_eq_of_lt (by omega), hfpN]; omega),
        uadd_toNat, haddr64, Nat.mod_eq_of_lt (by omega), hfpN, hlen32]; omega
    have hmem : weth9SymLong2Mem σ I (weth9SymLongWC σ I + 1) = weth9SymLong2FinalMem σ I := by
      rw [weth9SymLong2FinalMem, if_pos hmask]
    exact evm_run hpre with [
      jumpiT hcond (by jump_dest),
      jumpdest, pop, swap3, pop, pop, pop, push1 ⟨64⟩,
      raw mload _ (weth9StringNewFp (weth9StringSlotWord σ I ⟨1⟩)) (UInt256.ofNat (9 + 2 * weth9SymLongWC σ I))
        (by decide +native) weth9MloadCostSpec
        (mloadWordValue_of_readWithPadding
          (by rw [weth9SymLong2Mem_size hpos, show (⟨64⟩ : UInt256).toNat = 64 from by decide]; omega)
          (wordMul32_not_ge_of_lt (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, ulit_toNat' _ (by omega)]; omega)
            (by rw [ulit_toNat' _ (by omega)]; omega))
          (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; exact weth9SymLong2Mem_read64 hpos _))
        (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, ulit_toNat' _ (by omega), hawnorm,
          machineState_M_inBounds (show (64 : Nat) + 32 ≤ 32 * (9 + 2 * weth9SymLongWC σ I) from by omega)]) (by evm_ov),
      dup1, swap2, sub, swap1,
      raw ret _ (weth9SymLongStringAbi σ I) (by decide +native) weth9ReturnCostSpec
        (by rw [hmem, hretlen]; exact weth9SymLong2FinalMem_readAbi hpos hfit) (by evm_ov)]
  · -- len not a multiple of 32: apply the trailing-word mask.
    have hcond : UInt256.isZero (UInt256.land ⟨31⟩ (weth9StringLen (weth9StringSlotWord σ I ⟨1⟩))) = ⟨0⟩ :=
      isZero_eq_zero_of_ne hmask
    have hr : (weth9StringLen (weth9StringSlotWord σ I ⟨1⟩)).toNat % 32 ≠ 0 := by
      intro hz
      apply hmask; apply u256_inj; rw [hlandN, hz]; decide
    have hsubmod := weth9SymLong2Len_sub_mod (σ := σ) (I := I) hr
    have hmaskAddr : (UInt256.sub (weth9StringLen (weth9StringSlotWord σ I ⟨1⟩) +
        (weth9StringNewFp (weth9StringSlotWord σ I ⟨1⟩) + ⟨64⟩))
        (UInt256.land ⟨31⟩ (weth9StringLen (weth9StringSlotWord σ I ⟨1⟩)))).toNat =
        256 + 64 * weth9SymLongWC σ I := by
      rw [usub_toNat (by rw [uadd_toNat, haddr64, Nat.mod_eq_of_lt (by omega), hlandN]; omega),
        uadd_toNat, haddr64, Nat.mod_eq_of_lt (by omega), hlandN]; omega
    have hmaskVal : UInt256.land
        (UInt256.lnot (UInt256.sub (UInt256.exp ⟨256⟩ (UInt256.sub ⟨32⟩
          (UInt256.land ⟨31⟩ (weth9StringLen (weth9StringSlotWord σ I ⟨1⟩))))) ⟨1⟩))
        (weth9SymLongDataWordAt σ I (weth9SymLongWC σ I)) = weth9SymLongMaskWord σ I := by
      rw [weth9SymLongMaskWord, if_neg hmask]
    have hmemMask : writeWord (weth9SymLong2Mem σ I (weth9SymLongWC σ I + 1)) (256 + 64 * weth9SymLongWC σ I)
        (weth9SymLongMaskWord σ I) = weth9SymLong2FinalMem σ I := by
      rw [weth9SymLong2FinalMem, if_neg hmask]
    have hretlen : (UInt256.sub ((⟨32⟩ : UInt256) + UInt256.sub (weth9StringLen (weth9StringSlotWord σ I ⟨1⟩) +
        (weth9StringNewFp (weth9StringSlotWord σ I ⟨1⟩) + ⟨64⟩))
        (UInt256.land ⟨31⟩ (weth9StringLen (weth9StringSlotWord σ I ⟨1⟩))))
        (weth9StringNewFp (weth9StringSlotWord σ I ⟨1⟩))).toNat = 64 + 32 * (weth9SymLongWC σ I + 1) := by
      rw [usub_toNat (by rw [uadd_toNat, hmaskAddr, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
          Nat.mod_eq_of_lt (by omega), hfpN]; omega),
        uadd_toNat, hmaskAddr, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
        Nat.mod_eq_of_lt (by omega), hfpN]; omega
    exact evm_run hpre with [
      jumpiNT hcond,
      dup1, dup3, sub, dup1,
      raw mload _ (weth9SymLongDataWordAt σ I (weth9SymLongWC σ I)) (UInt256.ofNat (9 + 2 * weth9SymLongWC σ I))
        (by decide +native) weth9MloadCostSpec
        (mloadWordValue_of_readWithPadding
          (by rw [hmaskAddr, weth9SymLong2Mem_size hpos]; omega)
          (wordMul32_not_ge_of_lt (by rw [hmaskAddr, ulit_toNat' _ (by omega)]; omega)
            (by rw [ulit_toNat' _ (by omega)]; omega))
          (by rw [hmaskAddr]
              have := weth9SymLong2Mem_readDest hpos (weth9SymLongWC σ I) (weth9SymLongWC σ I + 1) (by omega)
              rwa [show 256 + 32 * weth9SymLongWC σ I + 32 * weth9SymLongWC σ I = 256 + 64 * weth9SymLongWC σ I from by ring] at this))
        (by rw [hmaskAddr, ulit_toNat' _ (by omega), hawnorm,
          machineState_M_inBounds (show (256 + 64 * weth9SymLongWC σ I) + 32 ≤ 32 * (9 + 2 * weth9SymLongWC σ I) from by omega)])
        (by evm_ov),
      push1 ⟨1⟩, dup4, push1 ⟨32⟩, sub, push2 ⟨256⟩, exp, sub, not, and, dup2,
      raw mstore _ (weth9SymLong2FinalMem σ I) (UInt256.ofNat (9 + 2 * weth9SymLongWC σ I))
        (by decide +native) weth9MstoreCostSpec
        (by rw [hmaskAddr, hmaskVal]; exact hmemMask)
        (by rw [hmaskAddr, ulit_toNat' _ (by omega),
          machineState_M_inBounds (show (256 + 64 * weth9SymLongWC σ I) + 32 ≤ 32 * (9 + 2 * weth9SymLongWC σ I) from by omega)])
        (by evm_ov),
      push1 ⟨32⟩, add, swap2, pop,
      jumpdest, pop, swap3, pop, pop, pop, push1 ⟨64⟩,
      raw mload _ (weth9StringNewFp (weth9StringSlotWord σ I ⟨1⟩)) (UInt256.ofNat (9 + 2 * weth9SymLongWC σ I))
        (by decide +native) weth9MloadCostSpec
        (mloadWordValue_of_readWithPadding
          (by rw [weth9SymLong2FinalMem_size hpos, show (⟨64⟩ : UInt256).toNat = 64 from by decide]; omega)
          (wordMul32_not_ge_of_lt (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, ulit_toNat' _ (by omega)]; omega)
            (by rw [ulit_toNat' _ (by omega)]; omega))
          (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; exact weth9SymLong2FinalMem_read64 hpos hfit))
        (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, ulit_toNat' _ (by omega),
          machineState_M_inBounds (show (64 : Nat) + 32 ≤ 32 * (9 + 2 * weth9SymLongWC σ I) from by omega)]) (by evm_ov),
      dup1, swap2, sub, swap1,
      raw ret _ (weth9SymLongStringAbi σ I) (by decide +native) weth9ReturnCostSpec
        (by rw [hretlen]; exact weth9SymLong2FinalMem_readAbi hpos hfit) (by evm_ov)]

end Benchmarks.WETH9
