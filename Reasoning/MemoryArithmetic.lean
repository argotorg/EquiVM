import Reasoning.DynamicMemory
import Reasoning.HeapMemory
import Reasoning.SolcMemory
import Reasoning.BytecodePatching
import Reasoning.WordArithmetic
import Reasoning.ABIComposite

/-!
# Memory bounds and byte conversions

Shared byte-array conversion, word-copy, scratch-memory, memory-expansion, and gas-bound facts.
Every statement is independent of any concrete contract or bytecode.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Reach

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000

namespace Reasoning.Theory

theorem callOutputMem_zero (mem out : ByteArray) (off : UInt256) :
    callOutputMem mem out off ⟨0⟩ = mem := by
  unfold callOutputMem
  have hmin : min (⟨0⟩ : UInt256) (UInt256.ofNat out.size) = ⟨0⟩ := by
    have hle : (⟨0⟩ : UInt256) ≤ UInt256.ofNat out.size := by
      change (0 : Nat) ≤ _
      omega
    simp [min, hle]
  rw [hmin]
  exact byteArray_write_len_zero _ _ _ _

theorem callActiveWords_zero (aw inOff outOff : UInt256) :
    callActiveWords aw inOff ⟨0⟩ outOff ⟨0⟩ = aw := by
  exact u256_ofNat_toNat aw

theorem sparseCascade_read_below (mem : ByteArray) (writes : List (Nat × UInt256)) (read : Nat)
    (hin : read + 32 ≤ mem.size) (hbelow : ∀ w ∈ writes, read + 32 ≤ w.1) :
    (writeCascade mem writes).readWithPadding read 32 = mem.readWithPadding read 32 := by
  induction writes generalizing mem with
  | nil => rfl
  | cons w ws ih =>
    rw [writeCascade_cons]
    have hin' : read + 32 ≤ (writeWord mem w.1 w.2).size := by
      rw [writeWord_sparse_size]
      exact le_trans hin (Nat.le_max_left _ _)
    rw [ih (writeWord mem w.1 w.2) hin' (fun w hw ↦ hbelow w (List.mem_cons_of_mem _ hw))]
    exact writeWord_sparse_read_preserved mem w.1 read w.2
      (Or.inl ⟨hbelow w List.mem_cons_self, hin⟩)

theorem sparseCascade_read_word (mem : ByteArray) (off : Nat) (word : UInt256)
    (rest : List (Nat × UInt256)) (hlater : ∀ w ∈ rest, off + 32 ≤ w.1) :
    (writeCascade mem ((off, word) :: rest)).readWithPadding off 32 = word.toByteArray := by
  rw [writeCascade_cons, sparseCascade_read_below _ rest off
    (by rw [writeWord_sparse_size]; exact Nat.le_max_right _ _) hlater]
  exact writeWord_sparse_read_back _ _ _

theorem memoryPrefix_sparse_cascade (mem : ByteArray) (writes : List (Nat × UInt256)) (limit : Nat)
    (hdisj : ∀ write ∈ writes, limit ≤ write.1 ∨ write.1 + 32 ≤ 96) :
    MemoryPrefix mem (writeCascade mem writes) limit := by
  induction writes generalizing mem with
  | nil => exact .refl _ _
  | cons w ws ih =>
    exact (memoryPrefix_sparse_writeWord mem w.1 limit w.2 (hdisj w (by simp))).trans
      (ih _ (fun w hw ↦ hdisj w (List.mem_cons_of_mem _ hw)))

theorem returnReserve_load {mem aw ptr word} (hm : MemoryCursor mem aw ptr) (size : Nat)
    (hin : ptr.toNat + 32 ≤ mem.size)
    (hread : mem.readWithPadding ptr.toNat 32 = word.toByteArray) :
    loadedWord (returnReserveMem mem ptr size) ptr = word := by
  apply loadedWord_of_read (by rw [returnReserveMem_size hm size]; exact hin)
  rw [returnReserve_read_word hm size hin, hread]

/-- `MachineState.M` (Nat form): a memory touch of `sz` bytes at `off` inside the active window
(`off + sz ≤ a·32`) does not grow the active words. Needed to rewrite the *inner* `M` of a nested
post-`CALL` active-words expression `M (M a inOff inSize) outOff outSize`. -/
theorem machineState_M_eq_of_cover (a off sz : Nat) (h : off + sz ≤ a * 32) : MachineState.M a off
    sz = a := by
  rcases sz with _ | l
  · simp [MachineState.M]
  · show max a ((off + (l + 1) + 31) / 32) = a
    rw [max_eq_left]; omega

/-- Generalisation of the frozen `awInv32` to an arbitrary access size (`ofNat` form): reusable for
every call's post-`CALL` active-words invariance (`awInv32` only covers `sz = 32`; the calls copy
`68`/`196`/… bytes). -/
theorem activeWords_eq_of_cover (aw : UInt256) (off sz : Nat) (h : off + sz ≤ aw.toNat * 32) :
    UInt256.ofNat (MachineState.M aw.toNat off sz) = aw := by
  apply u256_inj
  rw [machineState_M_eq_of_cover aw.toNat off sz h]
  exact congrArg UInt256.toNat (u256_ofNat_toNat aw)

theorem machineState_M_32_lt_size (a : UInt256) (o : ℕ) (ho : o + 32 < UInt256.size) :
    MachineState.M a.toNat o 32 < UInt256.size := by
  simp only [MachineState.M]
  have ha : a.toNat < UInt256.size := a.val.isLt
  omega

theorem activeWords_expand32_collapse (a : UInt256) (o1 o2 : ℕ) (hle : o1 ≤ o2)
    (hb : MachineState.M a.toNat o1 32 < UInt256.size) :
    UInt256.ofNat (MachineState.M (UInt256.ofNat (MachineState.M a.toNat o1 32)).toNat o2 32)
      = UInt256.ofNat (MachineState.M a.toNat o2 32) := by
  rw [UInt256.toNat_ofNat_of_lt hb]
  congr 1
  simp only [MachineState.M]
  rw [Nat.max_assoc]
  congr 1
  exact Nat.max_eq_right (by omega)

theorem mstoreCost_eq_machineState_M {aw off : UInt256} :
    Cₘ (M aw off ⟨32⟩) - Cₘ aw =
      Cₘ (UInt256.ofNat (MachineState.M aw.toNat off.toNat 32)) - Cₘ aw := by
  rfl

theorem wordWrite_size_of_le (base : ByteArray) (w : UInt256) (off : Nat)
    (h : off + 32 ≤ base.size) : ((UInt256.toByteArray w).write 0 base off 32).size = base.size :=
      by
  rw [toByteArray_write32_size_of_le base w off base.size base.size rfl (by omega) (by omega)]

/-- `p`-relative clone of `fiveWordWrite128_size`: the 5-word event build (`[p, p+160)`) preserves size. -/
theorem fiveWordWrite_size (base : ByteArray) (p v1 v2 v3 v4 v5 : UInt256)
    (_hp96 : 96 ≤ p.toNat) (hbase : p.toNat + 160 ≤ base.size)
      (hpsz : p.toNat + 160 < UInt256.size) :
    ((UInt256.toByteArray v5).write 0
      ((UInt256.toByteArray v4).write 0 ((UInt256.toByteArray v3).write 0
      ((UInt256.toByteArray v2).write 0 ((UInt256.toByteArray v1).write 0 base p.toNat 32)
        (p + ⟨32⟩).toNat 32) (p + ⟨64⟩).toNat 32) (p + ⟨96⟩).toNat 32) (p + ⟨128⟩).toNat 32).size
      = base.size := by
  have f32 : (p + ⟨32⟩).toNat = p.toNat + 32 := by
    rw [uadd_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide, Nat.mod_eq_of_lt (by omega)]
  have f64 : (p + ⟨64⟩).toNat = p.toNat + 64 := by
    rw [uadd_toNat, show (⟨64⟩ : UInt256).toNat = 64 from by decide, Nat.mod_eq_of_lt (by omega)]
  have f96 : (p + ⟨96⟩).toNat = p.toNat + 96 := by
    rw [uadd_toNat, show (⟨96⟩ : UInt256).toNat = 96 from by decide, Nat.mod_eq_of_lt (by omega)]
  have f128 : (p + ⟨128⟩).toNat = p.toNat + 128 := by
    rw [uadd_toNat, show (⟨128⟩ : UInt256).toNat = 128 from by decide, Nat.mod_eq_of_lt (by omega)]
  rw [f32, f64, f96, f128]
  have s1 := wordWrite_size_of_le base v1 p.toNat (by omega)
  have s2 : ((UInt256.toByteArray v2).write 0 ((UInt256.toByteArray v1).write 0 base p.toNat 32)
      (p.toNat + 32) 32).size = base.size := by
        rw [wordWrite_size_of_le _ v2 (p.toNat + 32) (by rw [s1]; omega)]; exact s1
  have s3 : ((UInt256.toByteArray v3).write 0 ((UInt256.toByteArray v2).write 0
      ((UInt256.toByteArray v1).write 0 base p.toNat 32) (p.toNat + 32) 32) (p.toNat + 64) 32).size
        = base.size := by
          rw [wordWrite_size_of_le _ v3 (p.toNat + 64) (by rw [s2]; omega)]; exact s2
  have s4 : ((UInt256.toByteArray v4).write 0 ((UInt256.toByteArray v3).write 0
      ((UInt256.toByteArray v2).write 0 ((UInt256.toByteArray v1).write 0 base p.toNat 32)
        (p.toNat + 32) 32)
        (p.toNat + 64) 32) (p.toNat + 96) 32).size = base.size := by
    rw [wordWrite_size_of_le _ v4 (p.toNat + 96) (by rw [s3]; omega)]; exact s3
  rw [wordWrite_size_of_le _ v5 (p.toNat + 128) (by rw [s4]; omega)]; exact s4

theorem wordWrite_read64_of_ge96 (base : ByteArray) (w : UInt256) (off : Nat)
    (hoff : 96 ≤ off) (h : off + 32 ≤ base.size) :
    ((UInt256.toByteArray w).write 0 base off 32).readWithPadding 64 32 = base.readWithPadding 64
      32 :=
  write32_read_below_len (UInt256.toByteArray w) base off 64 32 (by rw [toByteArray_size])
    (by omega) (by omega) (by omega) (by omega) (by omega)

/-- `p`-relative clone of `fiveWordWrite128_read64`: the event build (`[p, p+160)`, `96 ≤ p`) leaves `@64`. -/
theorem fiveWordWrite_read64 (base : ByteArray) (p v1 v2 v3 v4 v5 : UInt256)
    (hp96 : 96 ≤ p.toNat) (hbase : p.toNat + 160 ≤ base.size) (hpsz : p.toNat + 160 < UInt256.size)
      :
    ((UInt256.toByteArray v5).write 0
      ((UInt256.toByteArray v4).write 0 ((UInt256.toByteArray v3).write 0
      ((UInt256.toByteArray v2).write 0 ((UInt256.toByteArray v1).write 0 base p.toNat 32)
        (p + ⟨32⟩).toNat 32) (p + ⟨64⟩).toNat 32) (p + ⟨96⟩).toNat 32) (p + ⟨128⟩).toNat
          32).readWithPadding 64 32
      = base.readWithPadding 64 32 := by
  have f32 : (p + ⟨32⟩).toNat = p.toNat + 32 := by
    rw [uadd_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide, Nat.mod_eq_of_lt (by omega)]
  have f64 : (p + ⟨64⟩).toNat = p.toNat + 64 := by
    rw [uadd_toNat, show (⟨64⟩ : UInt256).toNat = 64 from by decide, Nat.mod_eq_of_lt (by omega)]
  have f96 : (p + ⟨96⟩).toNat = p.toNat + 96 := by
    rw [uadd_toNat, show (⟨96⟩ : UInt256).toNat = 96 from by decide, Nat.mod_eq_of_lt (by omega)]
  have f128 : (p + ⟨128⟩).toNat = p.toNat + 128 := by
    rw [uadd_toNat, show (⟨128⟩ : UInt256).toNat = 128 from by decide, Nat.mod_eq_of_lt (by omega)]
  rw [f32, f64, f96, f128]
  have s1 := wordWrite_size_of_le base v1 p.toNat (by omega)
  have s2 : ((UInt256.toByteArray v2).write 0 ((UInt256.toByteArray v1).write 0 base p.toNat 32)
      (p.toNat + 32) 32).size = base.size := by
        rw [wordWrite_size_of_le _ v2 (p.toNat + 32) (by rw [s1]; omega)]; exact s1
  have s3 : ((UInt256.toByteArray v3).write 0 ((UInt256.toByteArray v2).write 0
      ((UInt256.toByteArray v1).write 0 base p.toNat 32) (p.toNat + 32) 32) (p.toNat + 64) 32).size
        = base.size := by
          rw [wordWrite_size_of_le _ v3 (p.toNat + 64) (by rw [s2]; omega)]; exact s2
  have s4 : ((UInt256.toByteArray v4).write 0 ((UInt256.toByteArray v3).write 0
      ((UInt256.toByteArray v2).write 0 ((UInt256.toByteArray v1).write 0 base p.toNat 32)
        (p.toNat + 32) 32)
        (p.toNat + 64) 32) (p.toNat + 96) 32).size = base.size := by
    rw [wordWrite_size_of_le _ v4 (p.toNat + 96) (by rw [s3]; omega)]; exact s3
  rw [wordWrite_read64_of_ge96 _ v5 (p.toNat + 128) (by omega) (by rw [s4]; omega),
    wordWrite_read64_of_ge96 _ v4 (p.toNat + 96) (by omega) (by rw [s3]; omega),
    wordWrite_read64_of_ge96 _ v3 (p.toNat + 64) (by omega) (by rw [s2]; omega),
    wordWrite_read64_of_ge96 _ v2 (p.toNat + 32) (by omega) (by rw [s1]; omega),
    wordWrite_read64_of_ge96 _ v1 p.toNat (by omega) (by omega)]

/-- The active-words after the kick `CALL` (`aw' = M (M aw p 164) p 32`) still cover `[0, p+164)`:
memory expansion is `max`-monotone, so the argument-region growth survives. -/
theorem activeWords_cover164_after_expand32 (aw p : UInt256) (hpsz : p.toNat + 164 < UInt256.size) :
    p.toNat + 164 ≤
      (UInt256.ofNat (MachineState.M (MachineState.M aw.toNat p.toNat 164) p.toNat 32)).toNat * 32
        := by
  have hinnerEq : MachineState.M aw.toNat p.toNat 164 = max aw.toNat ((p.toNat + 164 + 31) / 32) :=
    rfl
  have houterEq : MachineState.M (MachineState.M aw.toNat p.toNat 164) p.toNat 32 =
      max (MachineState.M aw.toNat p.toNat 164) ((p.toNat + 32 + 31) / 32) := rfl
  have hinner_ge : (p.toNat + 164 + 31) / 32 ≤ MachineState.M aw.toNat p.toNat 164 := by
    rw [hinnerEq]; exact le_max_right _ _
  have houter_ge : MachineState.M aw.toNat p.toNat 164 ≤
      MachineState.M (MachineState.M aw.toNat p.toNat 164) p.toNat 32 := by
    rw [houterEq]; exact le_max_left _ _
  have hlt : MachineState.M (MachineState.M aw.toNat p.toNat 164) p.toNat 32 < UInt256.size := by
    rw [houterEq, hinnerEq]
    have h1 : aw.toNat < UInt256.size := aw.val.isLt
    have h2 : (p.toNat + 164 + 31) / 32 < UInt256.size := by omega
    have h3 : (p.toNat + 32 + 31) / 32 < UInt256.size := by omega
    omega
  have hval : (UInt256.ofNat
    (MachineState.M (MachineState.M aw.toNat p.toNat 164) p.toNat 32)).toNat
      = MachineState.M (MachineState.M aw.toNat p.toNat 164) p.toNat 32 := ulit_toNat' _ hlt
  rw [hval]
  have hceil : p.toNat + 164 ≤ (p.toNat + 164 + 31) / 32 * 32 := by omega
  calc p.toNat + 164 ≤ (p.toNat + 164 + 31) / 32 * 32 := hceil
    _ ≤ MachineState.M (MachineState.M aw.toNat p.toNat 164) p.toNat 32 * 32 := by
        have := le_trans hinner_ge houter_ge; exact Nat.mul_le_mul_right 32 this

/-- The `min 32 |o|` return-copy length collapses to `32` once `32 ≤ |o|`. -/
theorem callWriteLen32_eq_of_size_ge (o : ByteArray) (ho32 : 32 ≤ o.size)
    (hout : o.size < UInt256.size) :
    (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat = 32 :=
  umin_ofNat_right_toNat_of_ge (c := 32) (n := o.size) (by decide) ho32 hout

theorem callWriteLen64_eq_of_size_ge (o : ByteArray) (hlo : 64 ≤ o.size)
    (hout : o.size < UInt256.size) :
    (min (⟨64⟩ : UInt256) (UInt256.ofNat o.size)).toNat = 64 :=
  umin_ofNat_right_toNat_of_ge (c := 64) (n := o.size) (by decide) hlo hout

theorem byteArray_toList_take32_length {o : ByteArray} {start : Nat} (h : start + 32 ≤ o.size) :
    ((o.toList.drop start).take 32).length = 32 := by
  have hlen : o.toList.length = o.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [List.length_take, List.length_drop, hlen]; omega

/-- **Return-data-copy span read.**  An EVM `STATICCALL`/`CALL` return copy is modeled as
    `o.write 0 base destAddr len` (copy `o[0,len)` into `base` at byte offset `destAddr`, extending
    `base` if it runs past the end).  A 32-byte read at an offset inside the copied region
    `[destAddr, destAddr+len)` returns the corresponding slice of `o`.

    (Hypothesis `destAddr ≤ base.size` added: without it the extending write uses `USize` gap
    arithmetic that can wrap, so the identity is not clean; `destAddr ≤ base.size` covers both the
    in-bounds and the memory-extending cases.) -/
theorem writeReturnCopy_read32 (o base : ByteArray) (destAddr len readAddr : ℕ)
    (hlen : len ≤ o.size)
    (hdest : destAddr ≤ base.size)
    (hlo : destAddr ≤ readAddr)
    (hhi : readAddr + 32 ≤ destAddr + len) :
    (o.write 0 base destAddr len).readWithPadding readAddr 32
      = o.extract (readAddr - destAddr) (readAddr - destAddr + 32) := by
  have hlne : len ≠ 0 := by omega
  have hPsz : (base.extract 0 destAddr).size = destAddr := by rw [ByteArray.size_extract]; omega
  have hMsz : (o.extract 0 len).size = len := by rw [ByteArray.size_extract]; omega
  have hPMsz : (base.extract 0 destAddr ++ o.extract 0 len).size = destAddr + len := by
    rw [ByteArray.size_append, hPsz, hMsz]
  -- The read lands inside the copied middle segment `o.extract 0 len`.
  have key : (base.extract 0 destAddr ++ o.extract 0 len).extract readAddr (readAddr + 32)
      = o.extract (readAddr - destAddr) (readAddr - destAddr + 32) := by
    rw [extract_append_right_window _ _ _ _ (by rw [hPsz]; omega), hPsz, extract_extract_BA,
      show 0 + (readAddr - destAddr) = readAddr - destAddr from by omega,
      show min (0 + (readAddr + 32 - destAddr)) len = readAddr - destAddr + 32 from by omega]
  by_cases hb : destAddr + len ≤ base.size
  · -- in-bounds splice: base[0,destAddr) ++ o[0,len) ++ base[destAddr+len, size)
    rw [write_eq_gen o base destAddr len hlne hlen hb]
    rw [readWithPadding_eq_extract _ readAddr
      (by rw [ByteArray.size_append, hPMsz, ByteArray.size_extract]; omega)]
    rw [extract_append_left _ _ _ _ (by rw [hPMsz]; omega)]
    exact key
  · -- extending splice: base[0,destAddr) ++ o[0,len)
    rw [write_eq_gen_extend o base destAddr len hlne hlen hdest (by omega)]
    rw [readWithPadding_eq_extract _ readAddr (by rw [hPMsz]; omega)]
    exact key

/-- **Word roundtrip.**  Reading 32 in-bounds bytes and big-endian decoding-then-re-encoding is the
    identity: the read equals `toByteArray` of its decoded word. -/
theorem readWithPadding_eq_toByteArray_ofNat (o : ByteArray) (readAddr : ℕ)
    (h : readAddr + 32 ≤ o.size) :
    o.readWithPadding readAddr 32 =
      UInt256.toByteArray
        (UInt256.ofNat (fromByteArrayBigEndian (o.extract readAddr (readAddr + 32)))) := by
  have hsize : (o.extract readAddr (readAddr + 32)).size = 32 := by
    rw [ByteArray.size_extract]; omega
  rw [readWithPadding_eq_extract o readAddr h]
  symm
  rw [← uInt256OfByteArray_eq (o.extract readAddr (readAddr + 32))]
  rw [← word_toBytesBE_toByteArray_eq_toByteArray
    (uInt256OfByteArray (o.extract readAddr (readAddr + 32)))]
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [List.toList_data_toByteArray]
  simpa [byteArray_toList_eq] using toBytesBE_uInt256OfByteArray_of_size hsize

/-- `REVERT` memory-expansion cost is `0` when the reverted region `[off, off+len)` is already within
    active-words (`M aw off len = aw`). Mirrors `mloadCost0`/`memoryCost_zero_of_M_eq'`. -/
theorem memoryCost_zero_of_M_eq {aw off len : UInt256}
    (hM : UInt256.ofNat (MachineState.M aw.toNat off.toNat len.toNat) = aw) :
    Cₘ (M aw off len) - Cₘ aw = 0 := by
  simp [M, hM]

theorem awInv32 (aw : UInt256) {off : Nat}
    (h : off + 32 ≤ aw.toNat * 32) :
    UInt256.ofNat (MachineState.M aw.toNat off 32) = aw := by
  apply u256_inj
  have hM : MachineState.M aw.toNat off 32 = aw.toNat := by
    simp only [MachineState.M]; rw [max_eq_left]; omega
  rw [hM]; exact congrArg UInt256.toNat (u256_ofNat_toNat aw)

theorem catBiteAwMInv64 (aw : UInt256) {off : Nat}
    (h : off + 64 ≤ aw.toNat * 32) :
    UInt256.ofNat (MachineState.M aw.toNat off 64) = aw := by
  apply u256_inj
  have hM : MachineState.M aw.toNat off 64 = aw.toNat := by
    simp only [MachineState.M]; rw [max_eq_left]; omega
  rw [hM]; exact congrArg UInt256.toNat (u256_ofNat_toNat aw)

theorem memoryCost_zero_of_M_eq' {aw off sz : UInt256}
    (hM : UInt256.ofNat (MachineState.M aw.toNat off.toNat sz.toNat) = aw) :
    Cₘ (M aw off sz) - Cₘ aw = 0 := by
  simp [M, hM]

theorem mloadCost0 {aw off : UInt256}
    (hM : UInt256.ofNat (MachineState.M aw.toNat off.toNat 32) = aw) :
    Cₘ (M aw off ⟨32⟩) - Cₘ aw = 0 := by
  exact memoryExpansionCost_zero_of_aw_stable hM

theorem fiveWordWrite128_read64 (base : ByteArray) (v1 v2 v3 v4 v5 : UInt256)
    (hsz : 288 ≤ base.size) :
    ((UInt256.toByteArray v5).write 0
      ((UInt256.toByteArray v4).write 0 ((UInt256.toByteArray v3).write 0
      ((UInt256.toByteArray v2).write 0 ((UInt256.toByteArray v1).write 0 base 128 32) 160 32) 192
        32) 224 32) 256 32).readWithPadding 64 32
      = base.readWithPadding 64 32 := by
  have s1 : ((UInt256.toByteArray v1).write 0 base 128 32).size = base.size :=
    wordWrite_size_of_le base v1 128 (by omega)
  have s2 : ((UInt256.toByteArray v2).write 0 ((UInt256.toByteArray v1).write 0 base 128 32) 160
    32).size = base.size := by
    rw [wordWrite_size_of_le _ v2 160 (by omega)]; exact s1
  have s3 : ((UInt256.toByteArray v3).write 0
    ((UInt256.toByteArray v2).write 0 ((UInt256.toByteArray v1).write 0 base 128 32) 160 32) 192
      32).size = base.size := by
    rw [wordWrite_size_of_le _ v3 192 (by omega)]; exact s2
  have s4 : ((UInt256.toByteArray v4).write 0
    ((UInt256.toByteArray v3).write 0
      ((UInt256.toByteArray v2).write 0 ((UInt256.toByteArray v1).write 0 base 128 32) 160 32) 192
        32) 224 32).size = base.size := by
    rw [wordWrite_size_of_le _ v4 224 (by omega)]; exact s3
  rw [wordWrite_read64_of_ge96 _ v5 256 (by omega) (by omega),
    wordWrite_read64_of_ge96 _ v4 224 (by omega) (by omega),
    wordWrite_read64_of_ge96 _ v3 192 (by omega) (by omega),
      wordWrite_read64_of_ge96 _ v2 160 (by omega) (by omega),
    wordWrite_read64_of_ge96 _ v1 128 (by omega) (by omega)]

theorem awInv160 (aw : UInt256) {off : Nat} (h : off + 160 ≤ aw.toNat * 32) :
    UInt256.ofNat (MachineState.M aw.toNat off 160) = aw := by
  apply u256_inj
  have hM : MachineState.M aw.toNat off 160 = aw.toNat := by
    simp only [MachineState.M]; rw [max_eq_left]; omega
  rw [hM]; exact congrArg UInt256.toNat (u256_ofNat_toNat aw)

theorem fiveWordWrite128_size (base : ByteArray) (v1 v2 v3 v4 v5 : UInt256) (hsz : 288 ≤ base.size)
    :
    ((UInt256.toByteArray v5).write 0
      ((UInt256.toByteArray v4).write 0 ((UInt256.toByteArray v3).write 0
      ((UInt256.toByteArray v2).write 0 ((UInt256.toByteArray v1).write 0 base 128 32) 160 32) 192
        32) 224 32) 256 32).size = base.size := by
  have s1 := wordWrite_size_of_le base v1 128 (by omega)
  have s2 : ((UInt256.toByteArray v2).write 0 ((UInt256.toByteArray v1).write 0 base 128 32) 160
    32).size = base.size := by
    rw [wordWrite_size_of_le _ v2 160 (by rw [s1]; omega)]; exact s1
  have s3 : ((UInt256.toByteArray v3).write 0
    ((UInt256.toByteArray v2).write 0 ((UInt256.toByteArray v1).write 0 base 128 32) 160 32) 192
      32).size = base.size := by
    rw [wordWrite_size_of_le _ v3 192 (by rw [s2]; omega)]; exact s2
  have s4 : ((UInt256.toByteArray v4).write 0
    ((UInt256.toByteArray v3).write 0
      ((UInt256.toByteArray v2).write 0 ((UInt256.toByteArray v1).write 0 base 128 32) 160 32) 192
        32) 224 32).size = base.size := by
    rw [wordWrite_size_of_le _ v4 224 (by rw [s3]; omega)]; exact s3
  rw [wordWrite_size_of_le _ v5 256 (by rw [s4]; omega)]; exact s4

theorem zeroes32_size : (ByteArray.zeroes 32).size = 32 := by
  rw [ByteArray_zeroes_size]

/-- `twoWordHashMem` read of `[0,64)` = `key ++ slot`, for any base of size ≥ 64 (the size-96
    library lemma is too specific for the 164-byte post-call buffer). -/
theorem twoWordHashMem_read0_64_of_ge64' (key slot : UInt256) {base : ByteArray}
    (hb : 64 ≤ base.size) :
    (twoWordHashMem key slot base).readWithPadding 0 64 =
      UInt256.toByteArray key ++ UInt256.toByteArray slot := by
  have hinner : ((UInt256.toByteArray key).write 0 base 0 32).size = base.size := by
    rw [write32_eq (UInt256.toByteArray key) base 0 (by rw [toByteArray_size]) (by omega),
      ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
      ByteArray.size_extract, toByteArray_size]
    omega
  unfold twoWordHashMem wordAt32Mem wordAt0Mem
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [write32_eq _ _ 32 (by rw [toByteArray_size]) (by rw [hinner]; omega),
        ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
        ByteArray.size_extract, ByteArray.size_extract, hinner, toByteArray_size]; omega)]
  have hleft :
      ((UInt256.toByteArray slot).write 0 ((UInt256.toByteArray key).write 0 base 0 32) 32
        32).extract
        0 32 = UInt256.toByteArray key := by
    rw [← readWithPadding_eq_extract _ 0
        (by rw [write32_eq _ _ 32 (by rw [toByteArray_size]) (by rw [hinner]; omega),
          ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
          ByteArray.size_extract, ByteArray.size_extract, hinner, toByteArray_size]; omega),
      write32_read_below_len _ _ 32 0 32 (by rw [toByteArray_size]) (by rw [hinner]; omega)
        (by omega) (by rw [hinner]; omega) (by norm_num) (by norm_num),
      write32_read_prefix_len _ _ 0 32 (by rw [toByteArray_size]) (by omega) (by norm_num)
        (by norm_num) (by norm_num)]
    have h := @ByteArray.extract_zero_size (UInt256.toByteArray key)
    rwa [toByteArray_size] at h
  have hright :
      ((UInt256.toByteArray slot).write 0 ((UInt256.toByteArray key).write 0 base 0 32) 32
        32).extract
        32 64 = UInt256.toByteArray slot := by
    rw [← readWithPadding_eq_extract' _ 32 32 (by norm_num) (by norm_num)
        (by rw [write32_eq _ _ 32 (by rw [toByteArray_size]) (by rw [hinner]; omega),
          ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
          ByteArray.size_extract, ByteArray.size_extract, hinner, toByteArray_size]; omega),
      write32_read_prefix_len _ _ 32 32 (by rw [toByteArray_size]) (by rw [hinner]; omega)
        (by norm_num) (by norm_num) (by norm_num)]
    have h := @ByteArray.extract_zero_size (UInt256.toByteArray slot)
    rwa [toByteArray_size] at h
  rw [show ((UInt256.toByteArray slot).write 0 ((UInt256.toByteArray key).write 0 base 0 32) 32
    32).extract
      0 64 =
      ((UInt256.toByteArray slot).write 0 ((UInt256.toByteArray key).write 0 base 0 32) 32
        32).extract
        0 32 ++
      ((UInt256.toByteArray slot).write 0 ((UInt256.toByteArray key).write 0 base 0 32) 32
        32).extract
        32 64 by rw [ByteArray.extract_append_extract]; norm_num,
    hleft, hright]

theorem list_toByteArray_toList (xs : List UInt8) : xs.toByteArray.toList = xs := by
  rw [byteArray_toList_eq]
  simp

theorem byteArray_toList_toByteArray (b : ByteArray) : b.toList.toByteArray = b := by
  apply ByteArray.ext
  rw [List.data_toByteArray, byteArray_toList_eq]

theorem write0_eq_extract_from_of_base_le (src base : ByteArray)
    (srcAddr len : Nat) (hlen : len ≠ 0) (hsrc : srcAddr + len ≤ src.size)
    (hbase : base.size ≤ len) :
    src.write srcAddr base 0 len = src.extract srcAddr (srcAddr + len) := by
  apply ByteArray.ext
  rw [write0_data_from src base srcAddr len hlen hsrc]
  rw [show base.data.extract len base.data.size = (#[] : Array UInt8) from by
    apply Array.extract_eq_empty_of_le
    rw [show base.data.size = base.size from rfl]
    simpa using hbase]
  simp

theorem spliceBytes_toByteArray_eq_writeWord (mem : ByteArray) (off : Nat)
    (w : UInt256) (h : off + 32 ≤ mem.size) :
    spliceBytes? mem off (UInt256.toByteArray w) = some (writeWord mem off w) := by
  unfold spliceBytes? Reasoning.Theory.writeWord
  rw [toByteArray_size, if_pos h]
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by omega)]
  rw [toByteArray_extract_all]

theorem patchRuntime_wordWrites_eq_writeCascade
    (mem : ByteArray) (writes : List (Nat × UInt256))
    (hfit : ∀ p ∈ writes, p.1 + 32 ≤ mem.size) :
    patchRuntime mem (writes.map fun p => (p.1, UInt256.toByteArray p.2)) =
      some (writeCascade mem writes) := by
  induction writes generalizing mem with
  | nil => rfl
  | cons p rest ih =>
      rcases p with ⟨off, word⟩
      have hoff : off + 32 ≤ mem.size := hfit (off, word) (by simp)
      have hgap : off - mem.size < USize.size := by
        rw [Nat.sub_eq_zero_of_le (by omega)]
        exact lt_usize 0 (by norm_num)
      have hsize : (writeWord mem off word).size = mem.size := by
        rw [writeWord_size mem off word hgap]
        omega
      have hrest : ∀ p ∈ rest, p.1 + 32 ≤ (writeWord mem off word).size := by
        intro p hp
        rw [hsize]
        exact hfit p (by simp [hp])
      simp only [List.map_cons, patchRuntime, List.foldlM_cons,
        Option.bind_eq_bind, toByteArray_size, ↓reduceIte]
      rw [spliceBytes_toByteArray_eq_writeWord mem off word hoff]
      simpa [writeCascade] using ih (writeWord mem off word) hrest

theorem word_toBytesBE_array_eq_toByteArray (w : UInt256) :
    (ByteArray.mk (EVM.Word.toBytesBE w).toArray) = UInt256.toByteArray w := by
  rw [← word_toBytesBE_toByteArray_eq_toByteArray]
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [List.toList_data_toByteArray]

theorem byteArray_write_read_first_word_back (src base : ByteArray)
    (destAddr len : ℕ) (hlen : len ≠ 0) (hsrc : len ≤ src.size)
    (hword : 32 ≤ len) (hin : destAddr + len ≤ base.size) :
    (src.write 0 base destAddr len).readWithPadding destAddr 32 =
      src.extract 0 32 := by
  rw [write_eq_gen src base destAddr len hlen hsrc hin]
  have hprefix : (base.extract 0 destAddr).size = destAddr := by
    rw [ByteArray.size_extract]
    omega
  have hsrcPrefix : (src.extract 0 len).size = len := by
    rw [ByteArray.size_extract]
    omega
  have htail : (base.extract (destAddr + len) base.size).size = base.size - (destAddr + len) := by
    rw [ByteArray.size_extract]
    omega
  rw [readWithPadding_eq_extract _ destAddr (by
    rw [ByteArray.append_assoc, ByteArray.size_append, ByteArray.size_append, hprefix,
      hsrcPrefix, htail]
    omega)]
  rw [ByteArray.append_assoc]
  rw [extract_append_right_window (base.extract 0 destAddr)
    (src.extract 0 len ++ base.extract (destAddr + len) base.size)
    destAddr (destAddr + 32) (by rw [hprefix])]
  rw [show destAddr - (base.extract 0 destAddr).size = 0 by rw [hprefix]; omega]
  rw [show destAddr + 32 - (base.extract 0 destAddr).size = 32 by
    rw [hprefix]; omega]
  rw [extract_append_left (src.extract 0 len)
    (base.extract (destAddr + len) base.size) 0 32 (by rw [hsrcPrefix]; omega)]
  exact extract_prefix src len 0 32 hword

theorem byteArray_write_read_second_word_back (src base : ByteArray)
    (destAddr len : ℕ) (hlen : len ≠ 0) (hsrc : len ≤ src.size)
    (hword : 64 ≤ len) (hin : destAddr + len ≤ base.size) :
    (src.write 0 base destAddr len).readWithPadding (destAddr + 32) 32 =
      src.extract 32 64 := by
  rw [write_eq_gen src base destAddr len hlen hsrc hin]
  have hprefix : (base.extract 0 destAddr).size = destAddr := by
    rw [ByteArray.size_extract]
    omega
  have hsrcPrefix : (src.extract 0 len).size = len := by
    rw [ByteArray.size_extract]
    omega
  have htail : (base.extract (destAddr + len) base.size).size = base.size - (destAddr + len) := by
    rw [ByteArray.size_extract]
    omega
  rw [readWithPadding_eq_extract _ (destAddr + 32) (by
    rw [ByteArray.append_assoc, ByteArray.size_append, ByteArray.size_append, hprefix,
      hsrcPrefix, htail]
    omega)]
  rw [ByteArray.append_assoc]
  rw [extract_append_right_window (base.extract 0 destAddr)
    (src.extract 0 len ++ base.extract (destAddr + len) base.size)
    (destAddr + 32) (destAddr + 32 + 32) (by rw [hprefix]; omega)]
  rw [show destAddr + 32 - (base.extract 0 destAddr).size = 32 by
    rw [hprefix]; omega]
  rw [show destAddr + 32 + 32 - (base.extract 0 destAddr).size = 64 by
    rw [hprefix]; omega]
  rw [extract_append_left (src.extract 0 len)
    (base.extract (destAddr + len) base.size) 32 64 (by rw [hsrcPrefix]; omega)]
  exact extract_prefix src len 32 64 hword

theorem byteArray_write_extend_read_first_word_back (src base : ByteArray)
    (destAddr len : Nat) (hlen : len ≠ 0) (hsrc : len ≤ src.size)
    (hword : 32 ≤ len) (hdest : destAddr ≤ base.size)
    (hext : base.size < destAddr + len) :
    (src.write 0 base destAddr len).readWithPadding destAddr 32 =
      src.extract 0 32 := by
  rw [write_eq_gen_extend src base destAddr len hlen hsrc hdest hext]
  have hprefix : (base.extract 0 destAddr).size = destAddr := by
    rw [ByteArray.size_extract]
    omega
  have hsrcPrefix : (src.extract 0 len).size = len := by
    rw [ByteArray.size_extract]
    omega
  rw [readWithPadding_eq_extract _ destAddr (by
    rw [ByteArray.size_append, hprefix, hsrcPrefix]
    omega)]
  rw [extract_append_right_window (base.extract 0 destAddr) (src.extract 0 len)
    destAddr (destAddr + 32) (by rw [hprefix])]
  rw [show destAddr - (base.extract 0 destAddr).size = 0 by rw [hprefix]; omega]
  rw [show destAddr + 32 - (base.extract 0 destAddr).size = 32 by
    rw [hprefix]; omega]
  exact extract_prefix src len 0 32 hword

theorem errorStringMem0_size {mem : ByteArray} (hmem : mem.size = 192) :
    (solcErrorStringMem0 mem).size = 192 := by
  unfold solcErrorStringMem0
  exact toByteArray_write32_size_of_le mem solcErrorStringSelector 128
    192 192 hmem (by rw [hmem]; omega) (by decide)

theorem errorStringMem1_size {mem : ByteArray} (hmem : mem.size = 192) :
    (solcErrorStringMem1 mem).size = 192 := by
  unfold solcErrorStringMem1
  exact toByteArray_write32_size_of_le (solcErrorStringMem0 mem) ⟨32⟩ 132
    192 192 (errorStringMem0_size hmem)
      (by rw [errorStringMem0_size hmem]; omega) (by decide)

theorem errorStringMem2_size (len : UInt256) {mem : ByteArray}
    (hmem : mem.size = 192) : (solcErrorStringMem2 len mem).size = 196 := by
  unfold solcErrorStringMem2
  exact toByteArray_write32_size_of_le (solcErrorStringMem1 mem) len 164
    192 196 (errorStringMem1_size hmem)
      (by rw [errorStringMem1_size hmem]; omega) (by decide)

theorem errorStringMem3_size (len word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 192) : (solcErrorStringMem3 len word mem).size = 228 := by
  unfold solcErrorStringMem3
  exact toByteArray_write32_size_of_le (solcErrorStringMem2 len mem) word 196
    196 228 (errorStringMem2_size len hmem)
      (by rw [errorStringMem2_size len hmem]) (by decide)

theorem errorStringMem3_read64 (len word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 192)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (solcErrorStringMem3 len word mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold solcErrorStringMem3
  rw [toByteArray_write_read_below_of_gap word _ 196 64
      (by rw [errorStringMem2_size len hmem]; decide)
      (by decide)
      (by rw [errorStringMem2_size len hmem]; exact lt_usize _ (by omega))]
  unfold solcErrorStringMem2
  rw [toByteArray_write_read_below_of_gap len _ 164 64
      (by rw [errorStringMem1_size hmem]; omega) (by decide)
      (by rw [errorStringMem1_size hmem]; exact lt_usize _ (by omega))]
  unfold solcErrorStringMem1
  rw [toByteArray_write_read_below_of_gap (⟨32⟩ : UInt256) _ 132 64
      (by rw [errorStringMem0_size hmem]; omega) (by decide)
      (by rw [errorStringMem0_size hmem]; exact lt_usize _ (by omega))]
  unfold solcErrorStringMem0
  rw [toByteArray_write_read_below_of_gap solcErrorStringSelector _ 128 64
      (by rw [hmem]; omega) (by decide)
      (by rw [hmem]; exact lt_usize _ (by omega))]
  exact hread64

theorem errorStringMem3_mload64 (len word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 192)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (solcErrorStringMem3 len word mem).size then ⟨0⟩
     else UInt256.ofNat (fromByteArrayBigEndian
        ((solcErrorStringMem3 len word mem).readWithPadding 64 32))) = ⟨128⟩ :=
  mloadFreePtrValue (by rw [errorStringMem3_size len word hmem]; decide)
    (errorStringMem3_read64 len word hmem hread64)

theorem mk_toArray_eq (l : List UInt8) : (⟨l.toArray⟩ : ByteArray) = l.toByteArray := by
  rw [← List.data_toByteArray]

theorem natBytes_toByteArray (n : Nat) :
    (ABI.natBytes n).toByteArray = UInt256.toByteArray (UInt256.ofNat n) := by
  show (EVM.Word.toBytesBE (UInt256.ofNat n)).toByteArray = _
  exact word_toBytesBE_toByteArray_eq_toByteArray _

theorem uInt256_toByteArray_natBytes (w : UInt256) :
    UInt256.toByteArray w = ⟨(ABI.natBytes w.toNat).toArray⟩ := by
  symm
  rw [mk_toArray_eq, natBytes_toByteArray, u256_ofNat_toNat]

theorem m_return_mload64 (n : Nat) :
    MachineState.M (5 + n) 64 32 = 5 + n := by
  unfold MachineState.M
  simp only []
  omega

theorem m_return_storeOffset (n : Nat) :
    MachineState.M (5 + n) (160 + 32 * n) 32 = 6 + n := by
  unfold MachineState.M
  simp only []
  omega

theorem m_return_mload128_from6 (n : Nat) :
    MachineState.M (6 + n) 128 32 = 6 + n := by
  unfold MachineState.M
  simp only []
  omega

theorem m_return_storeLength (n : Nat) :
    MachineState.M (6 + n) (192 + 32 * n) 32 = 7 + n := by
  unfold MachineState.M
  simp only []
  omega

theorem m_return_mload128_from7 (n : Nat) :
    MachineState.M (7 + n) 128 32 = 7 + n := by
  unfold MachineState.M
  simp only []
  omega

theorem m_return_copy_mload (n k : Nat) :
    MachineState.M (7 + n + k) (160 + 32 * k) 32 = 7 + n + k := by
  unfold MachineState.M
  simp only []
  omega

theorem m_return_copy_mstore (n k : Nat) :
    MachineState.M (7 + n + k) (224 + 32 * n + 32 * k) 32 = 8 + n + k := by
  unfold MachineState.M
  simp only []
  omega

theorem zeroBytes_toByteArray (n : Nat) (hn : n ≤ 32) :
    (ABI.zeroBytes n).toByteArray =
      (UInt256.toByteArray ⟨0⟩).extract 0 n := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop,
    toByteArray_eq_toBytesBE]
  have hz : EVM.Word.toBytesBE (⟨0⟩ : UInt256) = List.replicate 32 0 := by
    decide +kernel
  rw [show ((EVM.Word.toBytesBE (⟨0⟩ : UInt256)).toArray).toList =
      EVM.Word.toBytesBE (⟨0⟩ : UInt256) by simp, hz]
  rw [List.toList_data_toByteArray]
  simp only [ABI.zeroBytes, Nat.sub_zero, List.drop_zero]
  change List.replicate n 0 = (List.replicate 32 0).take n
  rw [List.take_replicate, Nat.min_eq_left hn]

theorem zeroReturndataWrite_eq (out mem : ByteArray) :
    out.write 0 mem 128 (min (⟨0⟩ : UInt256) (UInt256.ofNat out.size)).toNat = mem := by
  have hmin :
      (min (⟨0⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 0 := by
    have hle : (⟨0⟩ : UInt256) ≤ UInt256.ofNat out.size := by
      show (0 : Nat) ≤ (UInt256.ofNat out.size).val.val
      exact Nat.zero_le _
    simp [min, hle]
  simp [hmin, byteArray_write_len_zero]

theorem vatMovePostCallAw_eq :
    UInt256.ofNat
      (MachineState.M (MachineState.M (UInt256.ofNat 9).toNat
        (⟨128⟩ : UInt256).toNat (⟨100⟩ : UInt256).toNat)
        (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) =
      UInt256.ofNat 9 := by
  decide

theorem write32_size_of_end_le (mem : ByteArray) (word : UInt256)
    (off : Nat) (hend : off + 32 ≤ mem.size) :
    ((UInt256.toByteArray word).write 0 mem off 32).size = mem.size := by
  exact toByteArray_write32_size_of_le mem word off mem.size mem.size rfl
    (by omega) (max_eq_left hend)

theorem mloadCostZero {aw off : UInt256}
    (hawOff : UInt256.ofNat (MachineState.M aw.toNat off.toNat 32) = aw) :
    Cₘ (M aw off ⟨32⟩) - Cₘ aw = 0 :=
  memoryExpansionCost_zero_of_aw_stable hawOff

theorem vatFluxPostCallAw_eq :
    UInt256.ofNat
      (MachineState.M (MachineState.M (UInt256.ofNat 9).toNat
        (⟨128⟩ : UInt256).toNat (⟨132⟩ : UInt256).toNat)
        (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) =
      UInt256.ofNat 9 := by
  decide

theorem bytesToWord_drop_take32_eq_extract (out : ByteArray) (start : Nat) :
    ABI.bytesToWord ((out.toList.drop start).take 32) =
      UInt256.ofNat (fromByteArrayBigEndian (out.extract start (start + 32))) := by
  unfold ABI.bytesToWord fromByteArrayBigEndian
  congr 1
  rw [byteArray_toList_eq (out.extract start (start + 32)), ByteArray.data_extract,
    Array.toList_extract, List.extract_eq_take_drop, byteArray_toList_eq]
  simp [byteArray_toList_eq]

theorem vatIlksPostCallWrite_size_gt64 {base : ByteArray} (out : ByteArray) (L : ℕ)
    (hbase : base.size = 164) (hLo : L ≤ out.size) :
    64 < (out.write 0 base 128 L).size := by
  rcases Nat.eq_zero_or_pos L with hzero | hpos
  · subst L
    rw [byteArray_write_len_zero, hbase]
    norm_num
  · by_cases hin : 128 + L ≤ base.size
    · rw [write_eq_gen out base 128 L (by omega) hLo hin, ByteArray.size_append,
        ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
        ByteArray.size_extract, hbase]
      omega
    · have hdest : 128 ≤ base.size := by
        rw [hbase]
        omega
      have hext : base.size < 128 + L := Nat.lt_of_not_ge hin
      rw [write_eq_gen_extend out base 128 L (by omega) hLo hdest hext,
        ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract, hbase]
      omega

theorem fileEventMem_size {mem : ByteArray} (data : UInt256)
    (hmem : mem.size = 96) :
    ((UInt256.toByteArray data).write 0 mem 128 32).size = 160 := by
  exact toByteArray_write32_size_of_ge mem data 128 96 160 hmem (by omega)
    (lt_usize _ (by decide)) (by omega)

theorem fileEventMem_read64 {mem : ByteArray} (data : UInt256)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    ((UInt256.toByteArray data).write 0 mem 128 32).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  have hgap : 128 - mem.size < USize.size := by
    rw [hmem]
    exact lt_usize _ (by decide)
  have hreadBound : 64 + 32 ≤ mem.size := by
    omega
  have hbelow : 64 + 32 ≤ 128 := by
    norm_num
  rw [toByteArray_write_read_below_of_gap data mem 128 64
    hreadBound hbelow hgap]
  exact hread64

theorem machineState_M_endWrite (aw : Nat) :
    MachineState.M aw (32 * aw) 32 = aw + 1 := by
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

theorem loadCureReturnWrite_size {base o : ByteArray} {L : ℕ}
    (hbase : base.size = 160) (hL : L ≤ 32) (hLo : L ≤ o.size) :
    (o.write 0 base 128 L).size = 160 := by
  rcases Nat.eq_zero_or_pos L with h | h
  · subst h
    rw [byteArray_write_len_zero]
    exact hbase
  · rw [write_eq_gen o base 128 L (by omega) hLo (by rw [hbase]; omega),
      ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, hbase]
    omega

theorem loadCureReturnWrite_read64 {base o : ByteArray} {L : ℕ}
    (hbase : base.size = 160)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hL : L ≤ 32) (hLo : L ≤ o.size) :
    (o.write 0 base 128 L).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  rcases Nat.eq_zero_or_pos L with h | h
  · subst h
    rw [byteArray_write_len_zero]
    exact hread64
  · rw [write_read_below_gen o base 128 L 64 (by omega) hLo
      (by rw [hbase]; omega) (by omega), hread64]

theorem loadCureReturnWrite_read128_32 {base o : ByteArray}
    (hbase : base.size = 160) (ho32 : 32 ≤ o.size) :
    (o.write 0 base 128 32).readWithPadding 128 32 = o.extract 0 32 :=
  write32_read_back o base 128 ho32 (by rw [hbase]; omega)

theorem byteArray_mk_toArray_eq_toByteArray (xs : List UInt8) :
    ByteArray.mk xs.toArray = xs.toByteArray := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  change xs.toArray.toList = xs.toByteArray.data.toList
  rw [show xs.toArray.toList = xs by simp]
  rw [List.toList_data_toByteArray]

theorem keccak_toList_length (bytes : ByteArray) : (KEC bytes).toList.length = 32 := by
  rw [byteArray_toList_eq, Array.length_toList]
  exact keccak_size bytes

theorem write_from_gap_eq (src base : ByteArray) (srcAddr destAddr len : Nat)
    (hlen : len ≠ 0) (hsrc : srcAddr + len ≤ src.size) (hge : base.size ≤ destAddr)
    (_hgap : destAddr - base.size < USize.size) :
    src.write srcAddr base destAddr len =
      base ++ ByteArray.zeroes (destAddr - base.size) ++
        src.extract srcAddr (srcAddr + len) := by
  apply ByteArray.ext
  unfold ByteArray.write
  rw [if_neg hlen, if_neg (show ¬ srcAddr ≥ src.size from by omega)]
  have hcopy : min len (src.size - srcAddr) = len := by omega
  have htail : min base.size (destAddr + len) - (destAddr + len) = 0 := by omega
  simp only [hcopy, htail, ByteArray.data_copySlice, ByteArray.data_append,
    ByteArray.data_extract]
  have hpz : (ByteArray.zeroes (destAddr - base.size)).data.size =
      destAddr - base.size := by
    rw [show (ByteArray.zeroes (destAddr - base.size)).data.size =
          (ByteArray.zeroes (destAddr - base.size)).size from rfl,
      ByteArray_zeroes_size]
  have hDsz :
      (base.data ++
        (ByteArray.zeroes (destAddr - base.size)).data).size =
        destAddr := by
    rw [Array.size_append, hpz, show base.data.size = base.size from rfl]
    omega
  rw [show (ByteArray.zeroes 0).data = (#[] : Array UInt8) from by
    rw [zeroes_zero (n := 0) (by rfl)]
    rfl]
  simp only [Array.append_empty, Nat.add_zero]
  rw [show min len (src.data.size - srcAddr) = len by
    have : src.data.size = src.size := rfl
    omega]
  rw [Array.extract_eq_self_of_le (by rw [hDsz])]
  rw [show (base.data ++
        (ByteArray.zeroes (destAddr - base.size)).data).extract
          (destAddr + len) = (#[] : Array UInt8) from by
    apply Array.extract_eq_empty_of_le
    rw [hDsz]
    omega]
  simp [Array.append_assoc]

theorem pokePeekPostCallWrite_size_gt64 (out base : ByteArray) (L : Nat)
    (hbase : base.size = 160) (hLo : L ≤ out.size) :
    64 < (out.write 0 base 128 L).size := by
  rcases Nat.eq_zero_or_pos L with hzero | hpos
  · subst L
    rw [byteArray_write_len_zero, hbase]
    norm_num
  · by_cases hin : 128 + L ≤ base.size
    · rw [write_eq_gen out base 128 L (by omega) hLo hin, ByteArray.size_append,
        ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
        ByteArray.size_extract, hbase]
      omega
    · have hdest : 128 ≤ base.size := by
        rw [hbase]
        omega
      have hext : base.size < 128 + L := Nat.lt_of_not_ge hin
      rw [write_eq_gen_extend out base 128 L (by omega) hLo hdest hext,
        ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract, hbase]
      omega

theorem endCage_byteArray_extract_empty_of_le (b : ByteArray) {i j : ℕ} (h : j ≤ i) :
    b.extract i j = ByteArray.empty := by
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_empty_of_le (le_trans (Nat.min_le_left j b.data.size) h)

theorem endCageIlkSpotIlksWriteLen_eq {out : ByteArray}
    (hout : out.size < UInt256.size) :
    (min (⟨64⟩ : UInt256) (UInt256.ofNat out.size)).toNat = min 64 out.size := by
  by_cases hle : 64 ≤ out.size
  · rw [Nat.min_eq_left hle]
    exact umin_ofNat_right_toNat_of_ge (c := 64) (n := out.size) (by decide) hle hout
  · have hlt : out.size < 64 := by omega
    rw [Nat.min_eq_right (by omega : out.size ≤ 64)]
    exact umin_ofNat_right_toNat_of_lt (c := 64) (n := out.size) (by decide) hlt hout

theorem endCageIlkNoArgWriteLen_eq {out : ByteArray}
    (hout : out.size < UInt256.size) :
    (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat = min 32 out.size := by
  by_cases hle : 32 ≤ out.size
  · rw [Nat.min_eq_left hle]
    exact umin_ofNat_right_toNat_of_ge (c := 32) (n := out.size) (by decide) hle hout
  · have hlt : out.size < 32 := by omega
    rw [Nat.min_eq_right (by omega : out.size ≤ 32)]
    exact umin_ofNat_right_toNat_of_lt (c := 32) (n := out.size) (by decide) hlt hout

theorem endCageIlk_bytesToWord_drop_take32_eq_extract (out : ByteArray) (start : ℕ) :
    ABI.bytesToWord ((out.toList.drop start).take 32) =
      UInt256.ofNat (fromByteArrayBigEndian (out.extract start (start + 32))) := by
  unfold ABI.bytesToWord fromByteArrayBigEndian
  congr 1
  rw [byteArray_toList_eq (out.extract start (start + 32)), ByteArray.data_extract,
    Array.toList_extract, List.extract_eq_take_drop, byteArray_toList_eq]
  rw [byteArray_toList_eq]
  simp

theorem write128Min160_size_gt64 (base out : ByteArray) (hbaseSize : base.size = 164) :
    64 < (out.write 0 base 128 (min 160 out.size)).size := by
  by_cases hlen0 : min 160 out.size = 0
  · rw [hlen0, byteArray_write_len_zero, hbaseSize]
    omega
  · by_cases hext : base.size < 128 + min 160 out.size
    · rw [write_eq_gen_extend out base 128 (min 160 out.size) hlen0
        (Nat.min_le_right _ _) (by omega) hext]
      have hprefix : (base.extract 0 128).size = 128 := by
        rw [ByteArray.size_extract, hbaseSize]
        omega
      have hsrc : (out.extract 0 (min 160 out.size)).size = min 160 out.size := by
        rw [ByteArray.size_extract]
        omega
      rw [ByteArray.size_append, hprefix, hsrc]
      have hleout : min 160 out.size ≤ out.size := Nat.min_le_right _ _
      omega
    · have hin : 128 + min 160 out.size ≤ base.size := by
        omega
      rw [write_eq_gen out base 128 (min 160 out.size) hlen0
        (Nat.min_le_right _ _) hin]
      have hprefix : (base.extract 0 128).size = 128 := by
        rw [ByteArray.size_extract, hbaseSize]
        omega
      have hsrc : (out.extract 0 (min 160 out.size)).size = min 160 out.size := by
        rw [ByteArray.size_extract]
        omega
      have htail :
          (base.extract (128 + min 160 out.size) base.size).size =
            164 - (128 + min 160 out.size) := by
        rw [ByteArray.size_extract, hbaseSize]
        omega
      rw [ByteArray.size_append, ByteArray.size_append, hprefix, hsrc, htail]
      have hleout : min 160 out.size ≤ out.size := Nat.min_le_right _ _
      omega

theorem write32_read_above_from (src base : ByteArray) (srcAddr destAddr readAddr : ℕ)
    (hsrc : srcAddr + 32 ≤ src.size) (hinwrite : destAddr + 32 ≤ base.size)
    (habove : destAddr + 32 ≤ readAddr) (hin : readAddr + 32 ≤ base.size) :
    (src.write srcAddr base destAddr 32).readWithPadding readAddr 32 =
      base.readWithPadding readAddr 32 := by
  have hbsz : (base.extract 0 destAddr).size = destAddr := by
    rw [ByteArray.size_extract]
    omega
  have hsz32 : (src.extract srcAddr (srcAddr + 32)).size = 32 := by
    rw [ByteArray.size_extract]
    omega
  have hcsz : (base.extract (destAddr + 32) base.size).size =
      base.size - (destAddr + 32) := by
    rw [ByteArray.size_extract]
    omega
  have habsz :
      (base.extract 0 destAddr ++ src.extract srcAddr (srcAddr + 32)).size =
        destAddr + 32 := by
    rw [ByteArray.size_append, hbsz, hsz32]
  rw [write_eq_gen_from src base srcAddr destAddr 32 (by decide) hsrc hinwrite,
    readWithPadding_eq_extract _ readAddr
      (by rw [ByteArray.size_append, habsz, hcsz]; omega),
    readWithPadding_eq_extract _ readAddr (by omega),
    extract_append_right_window _ _ _ _ (by rw [habsz]; omega), habsz,
    extract_extract_BA,
    show destAddr + 32 + (readAddr - (destAddr + 32)) = readAddr from by omega,
    show min (destAddr + 32 + (readAddr + 32 - (destAddr + 32))) base.size =
      readAddr + 32 from by omega]

theorem byteArray_write_size_ge_base
    (src base : ByteArray) (srcOff destOff len : Nat) :
    base.size ≤ (src.write srcOff base destOff len).size := by
  unfold ByteArray.write
  split
  · simp
  · split
    · change base.data.size ≤
        (ByteArray.copySlice (ByteArray.zeroes (min len (base.size - destOff))) 0 base
          (min destOff base.size) (min len (base.size - destOff)) true).data.size
      rw [ByteArray.data_copySlice]
      simp [Array.size_append, Array.size_extract]
      omega
    · change base.data.size ≤
        (ByteArray.copySlice
          (src ++ ByteArray.zeroes
            (min base.size (destOff + len) - (destOff + min len (src.size - srcOff))))
          srcOff (base ++ ByteArray.zeroes (destOff - base.size)) destOff
          (min len (src.size - srcOff) +
            (min base.size (destOff + len) - (destOff + min len (src.size - srcOff))))
          true).data.size
      rw [ByteArray.data_copySlice]
      simp [Array.size_append, Array.size_extract]
      omega

theorem toByteArray_uInt256OfByteArray_of_size_gemJoin {arr : ByteArray}
    (hsize : arr.size = 32) :
    UInt256.toByteArray (uInt256OfByteArray arr) = arr := by
  rw [← word_toBytesBE_toByteArray_eq_toByteArray (uInt256OfByteArray arr),
    toBytesBE_uInt256OfByteArray_of_size hsize, byteArray_toList_toByteArray]

theorem gemJoinCtorDecimalsReturnWrite_read64 {base out : ByteArray} (L : ℕ)
    (hbase : base.size = 256)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨224⟩)
    (hL : L ≤ 32) (hLo : L ≤ out.size) :
    (out.write 0 base 224 L).readWithPadding 64 32 = UInt256.toByteArray ⟨224⟩ := by
  rcases Nat.eq_zero_or_pos L with h | h
  · subst h
    rw [byteArray_write_len_zero]
    exact hread64
  · rw [write_read_below_gen out base 224 L 64 (by omega) hLo
      (by rw [hbase]; omega) (by omega), hread64]

theorem gemJoinCtorDecimalsReturnWrite_size {base out : ByteArray} (L : ℕ)
    (hbase : base.size = 256) (hL : L ≤ 32) (hLo : L ≤ out.size) :
    (out.write 0 base 224 L).size = 256 := by
  rcases Nat.eq_zero_or_pos L with h | h
  · subst h
    rw [byteArray_write_len_zero]
    exact hbase
  · rw [write_eq_gen out base 224 L (by omega) hLo (by rw [hbase]; omega),
      ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, hbase]
    omega

theorem gemJoinCtorDecimalsReturnWrite_read224_32 {base out : ByteArray}
    (hbase : base.size = 256) (ho32 : 32 ≤ out.size) :
    (out.write 0 base 224 32).readWithPadding 224 32 =
      out.extract 0 32 :=
  write32_read_back out base 224 ho32 (by rw [hbase]; omega)

theorem joinTransferFromReturnWrite_size {base out : ByteArray} (L : ℕ)
    (hbase : base.size = 228) (hL : L ≤ 32) (hLo : L ≤ out.size) :
    (out.write 0 base 128 L).size = 228 := by
  rcases Nat.eq_zero_or_pos L with h | h
  · subst h
    rw [byteArray_write_len_zero]
    exact hbase
  · rw [write_eq_gen out base 128 L (by omega) hLo (by rw [hbase]; omega),
      ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, hbase]
    omega

theorem joinTransferFromReturnWrite_read64 {base out : ByteArray} (L : ℕ)
    (hbase : base.size = 228)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hL : L ≤ 32) (hLo : L ≤ out.size) :
    (out.write 0 base 128 L).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  rcases Nat.eq_zero_or_pos L with h | h
  · subst h
    rw [byteArray_write_len_zero]
    exact hread64
  · rw [write_read_below_gen out base 128 L 64 (by omega) hLo
      (by rw [hbase]; omega) (by omega), hread64]

theorem joinTransferFromReturnWrite_read128_32 {base out : ByteArray}
    (hbase : base.size = 228) (ho32 : 32 ≤ out.size) :
    (out.write 0 base 128 32).readWithPadding 128 32 =
      out.extract 0 32 :=
  write32_read_back out base 128 ho32 (by rw [hbase]; omega)

theorem write32_read_above_from' (src base : ByteArray) (srcAddr destAddr readAddr : ℕ)
    (hsrc : srcAddr + 32 ≤ src.size) (hlo : destAddr ≤ base.size)
    (habove : destAddr + 32 ≤ readAddr) (hin : readAddr + 32 ≤ base.size) :
    (src.write srcAddr base destAddr 32).readWithPadding readAddr 32 =
      base.readWithPadding readAddr 32 := by
  have hbsz : (base.extract 0 destAddr).size = destAddr := by
    rw [ByteArray.size_extract]
    omega
  have hsrcsz : (src.extract srcAddr (srcAddr + 32)).size = 32 := by
    rw [ByteArray.size_extract]
    omega
  have hcsz : (base.extract (destAddr + 32) base.size).size =
      base.size - (destAddr + 32) := by
    rw [ByteArray.size_extract]
    omega
  have habsz :
      (base.extract 0 destAddr ++ src.extract srcAddr (srcAddr + 32)).size =
        destAddr + 32 := by
    rw [ByteArray.size_append, hbsz, hsrcsz]
  rw [write_eq_gen_from src base srcAddr destAddr 32 (by decide) hsrc (by omega),
      readWithPadding_eq_extract _ readAddr
        (by rw [ByteArray.size_append, habsz, hcsz]; omega),
      readWithPadding_eq_extract _ readAddr (by omega),
      extract_append_right_window _ _ _ _ (by rw [habsz]; omega), habsz,
      extract_extract_BA,
      show destAddr + 32 + (readAddr - (destAddr + 32)) = readAddr from by omega,
      show min (destAddr + 32 + (readAddr + 32 - (destAddr + 32))) base.size =
          readAddr + 32 from by omega]

theorem returnWrite_size_164 {base : ByteArray} (o : ByteArray) (L : ℕ)
    (hbase : base.size = 164) (hL : L ≤ 32) (hLo : L ≤ o.size) :
    (o.write 0 base 128 L).size = 164 := by
  rcases Nat.eq_zero_or_pos L with h | h
  · subst h
    rw [byteArray_write_len_zero]
    exact hbase
  · rw [write_eq_gen o base 128 L (by omega) hLo (by rw [hbase]; omega),
      ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, hbase]
    omega

theorem returnWrite_read64 {base : ByteArray} (o : ByteArray) (L : ℕ)
    (hbase : base.size = 164)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hL : L ≤ 32) (hLo : L ≤ o.size) :
    (o.write 0 base 128 L).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  rcases Nat.eq_zero_or_pos L with h | h
  · subst h
    rw [byteArray_write_len_zero]
    exact hread64
  · rw [write_read_below_gen o base 128 L 64 (by omega) hLo (by rw [hbase]; omega)
      (by omega), hread64]

theorem returnWrite_read128_32 {base : ByteArray} (o : ByteArray)
    (hbase : base.size = 164) (ho32 : 32 ≤ o.size) :
    (o.write 0 base 128 32).readWithPadding 128 32 = o.extract 0 32 :=
  write32_read_back o base 128 ho32 (by rw [hbase]; omega)

theorem awM0_eq (aw : UInt256) (h : 1 ≤ aw.toNat) :
    UInt256.ofNat (MachineState.M aw.toNat 0 32) = aw := by
  apply u256_inj
  have hM : MachineState.M aw.toNat 0 32 = aw.toNat := by
    simp only [MachineState.M]; change max aw.toNat 1 = aw.toNat; exact max_eq_left h
  rw [hM]; exact congrArg UInt256.toNat (u256_ofNat_toNat aw)

theorem awMemPtr_eq (aw : UInt256) (memPtr : Nat)
    (h : memPtr + 32 ≤ aw.toNat * 32) :
    UInt256.ofNat (MachineState.M aw.toNat memPtr 32) = aw := by
  apply u256_inj
  have hM : MachineState.M aw.toNat memPtr 32 = aw.toNat := by
    simp only [MachineState.M]
    rw [max_eq_left]
    omega
  rw [hM]; exact congrArg UInt256.toNat (u256_ofNat_toNat aw)

theorem byteArray_extract0_toList (b : ByteArray) (r : ℕ) :
    (b.extract 0 r).toList = b.toList.take r := by
  rw [byteArray_toList_eq, byteArray_toList_eq, ByteArray.data_extract, Array.toList_extract]; simp

theorem bytesBE_extract_high (w : UInt256) (r : ℕ) (hr : r ≤ 32) :
    fromBytesBigEndian ((w.toByteArray.extract 0 r).toList) = w.toNat / 2 ^ (8 * (32 - r)) := by
  have hbs : (w.toByteArray).toList = EVM.Word.toBytesBE w := by
    rw [toByteArray_eq_toBytesBE]; simp [byteArray_toList_eq]
  have hlen : (EVM.Word.toBytesBE w).length = 32 := by
    rw [← hbs, byteArray_toList_eq, Array.length_toList]; exact toByteArray_size w
  rw [byteArray_extract0_toList, hbs]
  have hdroplen : ((EVM.Word.toBytesBE w).drop r).length = 32 - r := by
    rw [List.length_drop, hlen]
  have key := fromBytesBigEndian_append_div ((EVM.Word.toBytesBE w).take r)
    ((EVM.Word.toBytesBE w).drop r)
  rw [List.take_append_drop, hdroplen] at key
  rw [← key, fromBytesBE_word]

/-- **Tail-mask reconciliation (the crux).**  The runtime's masked last data word `~(2^(8·(32-r))-1) &
    w` — clearing the low `8·(32-r)` bytes — equals the ABI's `w`-prefix `extract 0 r` zero-padded to a
    full word.  Shared by the short case (`r = len`) and the long final word (`r = len mod 32`). -/
theorem tailMask_toByteArray (w L : UInt256) (hr : 0 < L.toNat) (hr31 : L.toNat ≤ 31) :
    UInt256.toByteArray (UInt256.land (UInt256.lnot (UInt256.sub
        (UInt256.exp ⟨256⟩ (UInt256.sub ⟨32⟩ L)) ⟨1⟩)) w) =
      ⟨((w.toByteArray.extract 0 L.toNat).toList ++ List.replicate (32 - L.toNat) 0).toArray⟩ := by
  have hr32 : L.toNat ≤ 32 := by omega
  have h32 : (⟨32⟩ : UInt256).toNat = 32 := by decide
  have h1 : (⟨1⟩ : UInt256).toNat = 1 := by decide
  have hwlt : w.toNat < 2 ^ 256 := by
    change w.val.val < 2 ^ 256; simpa [UInt256.size] using w.val.isLt
  have hsubeq : UInt256.sub ⟨32⟩ L = UInt256.ofNat (32 - L.toNat) := by
    apply u256_inj
    rw [usub_toNat (by rw [h32]; exact hr32), h32,
      ulit_toNat' _ (by rw [show UInt256.size = 2 ^ 256 from by decide]; omega)]
  have hexp : (UInt256.exp ⟨256⟩ (UInt256.sub ⟨32⟩ L)).toNat = 2 ^ (8 * (32 - L.toNat)) := by
    rw [hsubeq, exp256_toNat (32 - L.toNat) (by omega),
      show (256 : ℕ) = 2 ^ 8 from by norm_num, ← Nat.pow_mul]
  have h2mpos : 1 ≤ 2 ^ (8 * (32 - L.toNat)) := Nat.one_le_two_pow
  have h2mle : 2 ^ (8 * (32 - L.toNat)) ≤ 2 ^ 256 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hX : (UInt256.sub (UInt256.exp ⟨256⟩ (UInt256.sub ⟨32⟩ L)) ⟨1⟩).toNat
      = 2 ^ (8 * (32 - L.toNat)) - 1 := by
    rw [usub_toNat (by rw [h1, hexp]; exact h2mpos), hexp, h1]
  have hlnotX : (UInt256.lnot (UInt256.sub (UInt256.exp ⟨256⟩ (UInt256.sub ⟨32⟩ L)) ⟨1⟩)).toNat
      = 2 ^ 256 - 2 ^ (8 * (32 - L.toNat)) := by
    rw [lnot_toNat_gen, hX]; omega
  have hlnotXeq : UInt256.lnot (UInt256.sub (UInt256.exp ⟨256⟩ (UInt256.sub ⟨32⟩ L)) ⟨1⟩)
      = UInt256.ofNat (2 ^ 256 - 2 ^ (8 * (32 - L.toNat))) := by
    apply u256_inj
    rw [hlnotX, ulit_toNat' _ (by rw [show UInt256.size = 2 ^ 256 from by decide]; omega)]
  have hmask : (UInt256.land (UInt256.lnot (UInt256.sub
        (UInt256.exp ⟨256⟩ (UInt256.sub ⟨32⟩ L)) ⟨1⟩)) w).toNat
      = w.toNat / 2 ^ (8 * (32 - L.toNat)) * 2 ^ (8 * (32 - L.toNat)) := by
    rw [hlnotXeq]
    exact u256_land_high_mask_toNat w (8 * (32 - L.toNat)) (by omega)
  have hextlen : (w.toByteArray.extract 0 L.toNat).toList.length = L.toNat := by
    rw [byteArray_extract0_toList, List.length_take, byteArray_toList_eq, Array.length_toList]
    have hsz : (w.toByteArray).data.size = 32 := toByteArray_size w
    omega
  have hlist : EVM.Word.toBytesBE (UInt256.land (UInt256.lnot (UInt256.sub
        (UInt256.exp ⟨256⟩ (UInt256.sub ⟨32⟩ L)) ⟨1⟩)) w)
      = (w.toByteArray.extract 0 L.toNat).toList ++ List.replicate (32 - L.toNat) 0 := by
    apply fromBytesBigEndian_inj_of_length
    · rw [word_toBytesBE_length_32, List.length_append, hextlen, List.length_replicate]; omega
    · rw [fromBytesBE_word, hmask, fromBytesBigEndian_append_zeros,
        bytesBE_extract_high w L.toNat hr32]
  rw [toByteArray_eq_toBytesBE, hlist]

theorem natBytes_toByteArray' (n : ℕ) :
    (ABI.natBytes n).toByteArray = UInt256.toByteArray (UInt256.ofNat n) := by
  show (EVM.Word.toBytesBE (UInt256.ofNat n)).toByteArray = _
  exact word_toBytesBE_toByteArray_eq_toByteArray _

theorem bytearray_append_list_eq (X : ByteArray) (Y : List UInt8) :
    X ++ Y.toByteArray = ⟨(X.toList ++ Y).toArray⟩ := by
  rw [mk_toArray_eq, List.toByteArray_append, byteArray_toList_toByteArray]

/-- A low read `[read, read+32)` is unchanged by a later word write at `off ≥ read+32`. -/
theorem writeWord_read_preserved_below_of_read {mem : ByteArray} {off read : Nat} {word w : UInt256}
    (hbase : mem.readWithPadding read 32 = UInt256.toByteArray w)
    (hsz : read + 32 ≤ mem.size) (_hoff : mem.size ≤ off) (hgap : off - mem.size < USize.size)
    (hro : read + 32 ≤ off) :
    (writeWord mem off word).readWithPadding read 32 = UInt256.toByteArray w := by
  rw [writeWord_read_preserved mem off read word hgap (Or.inl ⟨hro, hsz⟩)]; exact hbase

theorem nestedHashMem_size (baseSlot owner : UInt256) (ee : ExecutionEnv) (mem : ByteArray)
    (h : mem.size = 96) : (solcNestedMappingCallerHashMem baseSlot owner ee mem).size = 96 := by
  unfold solcNestedMappingCallerHashMem
  exact twoWordHashMem_size_96 _ _ (twoWordHashMem_size_96 owner baseSlot h)

theorem nestedHashMem_read64 (baseSlot owner : UInt256) (ee : ExecutionEnv) (mem : ByteArray)
    (hsize : mem.size = 96) (hr : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (solcNestedMappingCallerHashMem baseSlot owner ee mem).readWithPadding 64 32
      = UInt256.toByteArray ⟨128⟩ := by
  unfold solcNestedMappingCallerHashMem
  exact twoWordHashMem_read64 _ _ (twoWordHashMem_size_96 owner baseSlot hsize)
    (twoWordHashMem_read64 owner baseSlot hsize hr)

/-- The big-endian value of a 32-byte ABI `natBytes` word is the number itself. -/
theorem fromByteArrayBigEndian_natBytes (n : ℕ) (hn : n < UInt256.size) :
    fromByteArrayBigEndian ((ABI.natBytes n).toByteArray) = n := by
  unfold ABI.natBytes
  rw [word_toBytesBE_toByteArray_eq_toByteArray, fromByteArrayBigEndian_toByteArray]
  exact UInt256.toNat_ofNat_of_lt hn

theorem natBytes_toByteArray_size (n : ℕ) : (ABI.natBytes n).toByteArray.size = 32 := by
  unfold ABI.natBytes; exact word_toBytesBE_toByteArray_size _

/-- Reading the first 32-byte word of `natBytes m ‖ rest` returns `natBytes m`. -/
theorem natBytes_read0 (m : ℕ) (rest : List UInt8) :
    ((ABI.natBytes m ++ rest).toByteArray).readWithPadding 0 32 = (ABI.natBytes m).toByteArray := by
  have hm := natBytes_toByteArray_size m
  rw [List.toByteArray_append,
      readWithPadding_eq_extract _ _ (by rw [ByteArray.size_append, hm]; omega),
      extract_append_left _ _ _ _ (by rw [hm])]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (le_of_eq hm)

/-- Reading the second 32-byte word of `natBytes a ‖ natBytes b ‖ rest` returns `natBytes b`. -/
theorem natBytes_read1 (a b : ℕ) (rest : List UInt8) :
    ((ABI.natBytes a ++ (ABI.natBytes b ++ rest)).toByteArray).readWithPadding 32 32
      = (ABI.natBytes b).toByteArray := by
  have ha := natBytes_toByteArray_size a
  have hb := natBytes_toByteArray_size b
  rw [List.toByteArray_append, List.toByteArray_append,
      readWithPadding_eq_extract _ _
        (by rw [ByteArray.size_append, ByteArray.size_append, ha, hb]; omega),
      extract_append_right_window _ _ _ _ (le_of_eq ha), ha,
      show (32 - 32 : ℕ) = 0 from rfl, show (32 + 32 - 32 : ℕ) = 32 from rfl,
      extract_append_left _ _ _ _ (by rw [hb])]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (le_of_eq hb)

/-- `argBytes.size = 0x40 + 0x20·n` for the `bytes32[]` deployment shape. -/
theorem abiArrayWords_size (n : ℕ) (elemBytes : List UInt8) (argBytes : ByteArray)
    (hstruct : argBytes = (ABI.natBytes 32 ++ (ABI.natBytes n ++ elemBytes)).toByteArray)
    (helems : elemBytes.length = 32 * n) :
    argBytes.size = 64 + 32 * n := by
  rw [hstruct, List.toByteArray_append, ByteArray.size_append, List.toByteArray_append,
    ByteArray.size_append, natBytes_toByteArray_size, natBytes_toByteArray_size,
    List.size_toByteArray, helems]
  omega

/-- Active-words is **stable** for the copy loop's source `MLOAD`: reading element `i` at `0xc0+0x20·i`
    stays within the `7+n+i` active words. -/
theorem m_copy_stable (n i : ℕ) :
    MachineState.M (7 + n + i) (192 + 32 * i) 32 = 7 + n + i := by
  unfold MachineState.M; simp only []; omega

/-- Active-words **grows by one word** for the copy loop's destination `MSTORE`: writing at
    `fp+0x20+0x20·i = (7+n+i)·0x20` (the current end) bumps the count to `8+n+i`. -/
theorem m_copy_grow (n i : ℕ) :
    MachineState.M (7 + n + i) (224 + 32 * n + 32 * i) 32 = 8 + n + i := by
  unfold MachineState.M; simp only []; omega

/-- A 32-byte in-bounds memory read round-trips through `uInt256OfByteArray`: the bytes the copy loop
    re-stores (`MLOAD`'s `ofNat ∘ fromBE`, then `MSTORE`'s `toByteArray`) are exactly the source bytes. -/
theorem read32_roundtrip (mem : ByteArray) (addr : ℕ) (h : addr + 32 ≤ mem.size) :
    mem.readWithPadding addr 32
      = UInt256.toByteArray (uInt256OfByteArray (mem.readWithPadding addr 32)) := by
  have hsz : (mem.readWithPadding addr 32).size = 32 := by
    rw [readWithPadding_eq_extract mem addr h, ByteArray.size_extract]; omega
  rw [← word_toBytesBE_toByteArray_eq_toByteArray,
    toBytesBE_uInt256OfByteArray_of_size hsz]
  apply ByteArray.ext
  apply Array.ext'
  rw [byteArray_toList_eq] at *
  rw [List.toList_data_toByteArray]

theorem write0_size_ge_32 (src base : ByteArray) (srcAddr : ℕ)
    (hsrc : srcAddr + 32 ≤ src.size) :
    32 ≤ (src.write srcAddr base 0 32).size := by
  show 32 ≤ (src.write srcAddr base 0 32).data.size
  rw [write0_data_from src base srcAddr 32 (by decide) hsrc, Array.size_append]
  have hpart : (src.data.extract srcAddr (srcAddr + 32)).size = 32 := by
    rw [Array.size_extract]
    have : src.data.size = src.size := rfl
    omega
  omega

theorem reveal_aw_call_empty (aw fp : UInt256) :
    UInt256.ofNat
      (MachineState.M (MachineState.M aw.toNat fp.toNat (⟨0⟩ : UInt256).toNat)
        fp.toNat (⟨0⟩ : UInt256).toNat) = aw := by
  simpa [MachineState.M] using (u256_ofNat_toNat aw)

theorem readNat_drop4_eq_calldataWord {I : ExecutionEnv} {headOff : Nat}
    (h : 4 + headOff + 32 ≤ I.calldata.size) :
    readNat? (List.drop 4 I.calldata.toList) headOff =
      some (calldataWord I.calldata (4 + headOff)).toNat := by
  unfold readNat? readWord? readBytes?
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hslice :
      (List.take 32 (List.drop headOff (List.drop 4 I.calldata.toList))).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]
    omega
  rw [if_pos hslice]
  rw [calldataWord]
  rw [List.drop_drop]
  rw [← decode_word_at_eq_any I.calldata (4 + headOff) h]
  rfl

theorem readNat_drop4_array_len_eq {I : ExecutionEnv} {off len : UInt256}
    (hoff : off.toNat ≤ solcMaxU64)
    (hbound : 4 + off.toNat + 32 ≤ I.calldata.size)
    (hlenWord :
      uInt256OfByteArray (I.calldata.readBytes (((⟨4⟩ : UInt256) + off).toNat) 32) =
        len) :
    readNat? (List.drop 4 I.calldata.toList) off.toNat = some len.toNat := by
  have hread :=
    readNat_drop4_eq_calldataWord (I := I) (headOff := off.toNat)
      (by simpa [Nat.add_assoc] using hbound)
  have hstart : ((⟨4⟩ : UInt256) + off).toNat = 4 + off.toNat :=
    add4_word_toNat off hoff
  have hword : calldataWord I.calldata (4 + off.toNat) = len := by
    unfold calldataWord
    rw [← hstart]
    exact hlenWord
  rw [hread, hword]

theorem revealCalldataLoad_of_readNat {I : ExecutionEnv} {headOff : Nat}
    {addr value : UInt256}
    (hread : readNat? (List.drop 4 I.calldata.toList) headOff = some value.toNat)
    (haddr : addr.toNat = 4 + headOff) :
    uInt256OfByteArray (I.calldata.readBytes addr.toNat 32) = value := by
  have hword := readNat?_calldataWord_eq (I := I) (headOff := headOff) hread
  have hcalldata : calldataWord I.calldata (4 + headOff) = value := by
    rw [hword, u256_ofNat_toNat]
  unfold calldataWord at hcalldata
  rw [haddr]
  exact hcalldata

theorem reveal_aw_mstore0_of_ge3 {aw : UInt256} (haw : 3 ≤ aw.toNat) :
    UInt256.ofNat (MachineState.M aw.toNat 0 32) = aw := by
  apply u256_inj
  simp [MachineState.M]
  rw [UInt256.toNat_ofNat_of_lt]
  · omega
  · exact lt_of_le_of_lt (by omega : max aw.toNat 1 ≤ aw.toNat) aw.val.isLt

theorem reveal_aw_mstore32_of_ge3 {aw : UInt256} (haw : 3 ≤ aw.toNat) :
    UInt256.ofNat (MachineState.M aw.toNat 32 32) = aw := by
  apply u256_inj
  simp [MachineState.M]
  rw [UInt256.toNat_ofNat_of_lt]
  · omega
  · exact lt_of_le_of_lt (by omega : max aw.toNat 2 ≤ aw.toNat) aw.val.isLt

theorem reveal_aw_mstore4_of_ge3 {aw : UInt256} (haw : 3 ≤ aw.toNat) :
    UInt256.ofNat (MachineState.M aw.toNat 4 32) = aw := by
  apply u256_inj
  simp [MachineState.M]
  rw [UInt256.toNat_ofNat_of_lt]
  · omega
  · exact lt_of_le_of_lt (by omega : max aw.toNat 2 ≤ aw.toNat) aw.val.isLt

theorem reveal_aw_keccak64_of_ge3 {aw : UInt256} (haw : 3 ≤ aw.toNat) :
    UInt256.ofNat (MachineState.M aw.toNat 0 64) = aw := by
  apply u256_inj
  simp [MachineState.M]
  rw [UInt256.toNat_ofNat_of_lt]
  · omega
  · exact lt_of_le_of_lt (by omega : max aw.toNat 2 ≤ aw.toNat) aw.val.isLt

theorem reveal_aw_mload64_of_ge3 {aw : UInt256} (haw : 3 ≤ aw.toNat) :
    UInt256.ofNat (MachineState.M aw.toNat 64 32) = aw := by
  apply u256_inj
  simp [MachineState.M]
  rw [UInt256.toNat_ofNat_of_lt]
  · omega
  · exact lt_of_le_of_lt (by omega : max aw.toNat 3 ≤ aw.toNat) aw.val.isLt

theorem reveal_aw_M_ge3 {aw off len : UInt256} (haw : 3 ≤ aw.toNat) :
    3 ≤ (UInt256.ofNat (MachineState.M aw.toNat off.toNat len.toNat)).toNat := by
  unfold MachineState.M
  split
  · have h : UInt256.ofNat aw.toNat = aw := u256_ofNat_toNat aw
    rw [h]
    exact haw
  · have hterm : (off.toNat + len.toNat + 31) / 32 < UInt256.size := by
      apply Nat.div_lt_of_lt_mul
      have hoff : off.toNat < 2 ^ 256 := by
        change off.val.val < 2 ^ 256
        exact off.val.isLt
      have hlen : len.toNat < 2 ^ 256 := by
        change len.val.val < 2 ^ 256
        exact len.val.isLt
      change off.toNat + len.toNat + 31 < 32 * 2 ^ 256
      omega
    have hmax : max aw.toNat ((off.toNat + len.toNat + 31) / 32) < UInt256.size :=
      max_lt aw.val.isLt hterm
    rw [UInt256.toNat_ofNat_of_lt hmax]
    exact le_trans haw (Nat.le_max_left _ _)

theorem reveal_aw_M_small {aw off len : UInt256}
    (hawSmall : aw.toNat * 32 < UInt256.size)
    (hbound : off.toNat + len.toNat + 31 < UInt256.size) :
    (UInt256.ofNat (MachineState.M aw.toNat off.toNat len.toNat)).toNat * 32 <
      UInt256.size := by
  unfold MachineState.M
  split
  · have h : UInt256.ofNat aw.toNat = aw := u256_ofNat_toNat aw
    rw [h]
    exact hawSmall
  · let n := off.toNat + len.toNat + 31
    have hdivMul : (n / 32) * 32 ≤ n := Nat.div_mul_le_self n 32
    have htermSmall : (n / 32) * 32 < UInt256.size := by
      exact lt_of_le_of_lt hdivMul (by simpa [n] using hbound)
    have hmaxSmall : max aw.toNat (n / 32) * 32 < UInt256.size := by
      rw [Nat.max_def]
      split <;> omega
    have hmaxLt : max aw.toNat (n / 32) < UInt256.size := by
      omega
    rw [UInt256.toNat_ofNat_of_lt hmaxLt]
    simpa [n] using hmaxSmall

theorem not_mload_oob_after_M32 {aw off : UInt256}
    (hsmall :
      (UInt256.ofNat (MachineState.M aw.toNat off.toNat 32)).toNat * 32 <
        UInt256.size) :
    ¬ (off ≥ (UInt256.ofNat (MachineState.M aw.toNat off.toNat 32)) * ⟨32⟩) := by
  intro h
  let aw' := UInt256.ofNat (MachineState.M aw.toNat off.toNat 32)
  have hmul : (aw' * (⟨32⟩ : UInt256)).toNat = aw'.toNat * 32 := by
    rw [u256_mul_op_toNat]
    exact Nat.mod_eq_of_lt (by simpa [aw'] using hsmall)
  have hceil : off.toNat < ((off.toNat + 32 + 31) / 32) * 32 := by
    omega
  have htermDivLt : ((off.toNat + 32 + 31) / 32) < UInt256.size := by
    apply Nat.div_lt_of_lt_mul
    have hoff : off.toNat < 2 ^ 256 := by
      change off.val.val < 2 ^ 256
      exact off.val.isLt
    change off.toNat + 32 + 31 < 32 * 2 ^ 256
    omega
  have htermLt : max aw.toNat ((off.toNat + 32 + 31) / 32) < UInt256.size :=
    max_lt aw.val.isLt htermDivLt
  have hcover : off.toNat < aw'.toNat * 32 := by
    dsimp [aw']
    simp [MachineState.M, UInt256.toNat_ofNat_of_lt htermLt]
    exact lt_of_lt_of_le hceil (Nat.mul_le_mul_right 32 (Nat.le_max_right _ _))
  change off.toNat ≥ (aw' * ⟨32⟩ : UInt256).toNat at h
  rw [hmul] at h
  omega

theorem twoWordWrite_read0_64_any (mem : ByteArray) (key slot : UInt256) :
    (((UInt256.toByteArray slot).write 0
      ((UInt256.toByteArray key).write 0 mem 0 32) 32 32).readWithPadding 0 64) =
      UInt256.toByteArray key ++ UInt256.toByteArray slot := by
  let mem1 := (UInt256.toByteArray key).write 0 mem 0 32
  have hmem1size : 32 ≤ mem1.size := by
    dsimp [mem1]
    rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by omega)]
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, toByteArray_size]
    omega
  have hslotExtract : (UInt256.toByteArray slot).extract 0 32 = UInt256.toByteArray slot := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_self_of_le (by
      change (UInt256.toByteArray slot).size ≤ 32
      rw [toByteArray_size])
  have hkeyExtract : (UInt256.toByteArray key).extract 0 32 = UInt256.toByteArray key := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_self_of_le (by
      change (UInt256.toByteArray key).size ≤ 32
      rw [toByteArray_size])
  have hmem1extract : mem1.extract 0 32 = UInt256.toByteArray key := by
    have hmem1read : mem1.readWithPadding 0 32 = UInt256.toByteArray key := by
      dsimp [mem1]
      rw [write0_read_back_gen _ _ 32 (by decide) (by rw [toByteArray_size])
        (by norm_num)]
      exact hkeyExtract
    rw [← readWithPadding_eq_extract mem1 0 hmem1size]
    exact hmem1read
  rw [show ((UInt256.toByteArray slot).write 0
      ((UInt256.toByteArray key).write 0 mem 0 32) 32 32) =
        (UInt256.toByteArray slot).write 0 mem1 32 32 by rfl]
  rw [readWithPadding_eq_extract' _ 0 64 (by omega) (by norm_num) (by
    rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by omega)]
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, toByteArray_size]
    omega)]
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by omega)]
  let A := mem1.extract 0 32
  let B := (UInt256.toByteArray slot).extract 0 32
  let C := mem1.extract (32 + 32) mem1.size
  have hAsize : A.size = 32 := by
    dsimp [A]
    rw [ByteArray.size_extract]
    omega
  have hBsize : B.size = 32 := by
    dsimp [B]
    rw [ByteArray.size_extract, toByteArray_size]
    omega
  have hABsize : (A ++ B).size = 64 := by
    rw [ByteArray.size_append, hAsize, hBsize]
  change (A ++ B ++ C).extract 0 (0 + 64) =
    UInt256.toByteArray key ++ UInt256.toByteArray slot
  rw [show 0 + 64 = 64 by omega]
  rw [extract_append_left (A ++ B) C 0 64 (by rw [hABsize])]
  rw [← hABsize, byteArray_extract_self]
  dsimp [A, B]
  rw [hmem1extract, hslotExtract]

theorem readWithPadding_split_32_1_32 (mem : ByteArray) (base : Nat)
    (h : base + 65 ≤ mem.size) :
    mem.readWithPadding base 65 =
      mem.readWithPadding base 32 ++ mem.readWithPadding (base + 32) 1 ++
        mem.readWithPadding (base + 33) 32 := by
  rw [readWithPadding_eq_extract' mem base 65 (by norm_num) (by norm_num) h]
  rw [readWithPadding_eq_extract' mem base 32 (by norm_num) (by norm_num) (by omega)]
  rw [readWithPadding_eq_extract' mem (base + 32) 1 (by norm_num) (by norm_num) (by omega)]
  rw [readWithPadding_eq_extract' mem (base + 33) 32 (by norm_num) (by norm_num) (by omega)]
  rw [show base + 65 = base + 32 + 33 by omega]
  rw [show base + 33 = base + 32 + 1 by omega]
  have hsplit1 :
      mem.extract base (base + 65) =
        mem.extract base (base + 32) ++ mem.extract (base + 32) (base + 65) := by
    symm
    rw [ByteArray.extract_append_extract]
    congr <;> omega
  have hsplit2 :
      mem.extract (base + 32) (base + 65) =
        mem.extract (base + 32) (base + 33) ++ mem.extract (base + 33) (base + 65) := by
    symm
    rw [ByteArray.extract_append_extract]
    congr <;> omega
  rw [hsplit1, hsplit2]
  rw [show base + 32 + 1 = base + 33 by omega]
  rw [show base + 32 + 33 = base + 65 by omega]
  rw [ByteArray.append_assoc]

theorem mload_of_read {mem : ByteArray} {fp packedLen : UInt256}
    (hmem : fp.toNat < mem.size)
    (hread : mem.readWithPadding fp.toNat 32 = UInt256.toByteArray packedLen) :
    (if fp.toNat ≥ mem.size then ⟨0⟩
     else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding fp.toNat 32))) =
      packedLen :=
  mloadWordValue_of_readWithPadding hmem hread

theorem toByteArray_extract0_32 (w : UInt256) :
    (UInt256.toByteArray w).extract 0 32 = UInt256.toByteArray w := by
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray w).size ≤ 32
    rw [toByteArray_size])

theorem scratchMem_mload64 {base : ByteArray}
    (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ base.size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian (base.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [hbase]; decide) hread64

theorem withdrawReturnDataActiveWords_M_mul32_lt (o : ByteArray)
    (hosz : o.size < 2 ^ 255) :
    MachineState.M (UInt256.ofNat 5).toNat 160 o.size * 32 < UInt256.size := by
  rw [show (UInt256.ofNat 5).toNat = 5 from by decide]
  unfold MachineState.M
  split
  · norm_num [UInt256.size]
  · by_cases hle : 5 ≤ (160 + o.size + 31) / 32
    · rw [Nat.max_eq_right hle]
      have hdiv : ((160 + o.size + 31) / 32) * 32 ≤ 160 + o.size + 31 :=
        Nat.div_mul_le_self _ _
      have hcap : 2 ^ 255 + 191 < UInt256.size := by norm_num [UInt256.size]
      omega
    · rw [Nat.max_eq_left (Nat.le_of_not_ge hle)]
      norm_num [UInt256.size]

theorem withdrawReturnDataHugeCopyMemCost_gt_g (g : Sat256) (o : ByteArray)
    (hhi : 2 ^ 255 ≤ o.size) (hlo : o.size < UInt256.size) :
    g.toNat <
      Cₘ (UInt256.ofNat (MachineState.M (UInt256.ofNat 5).toNat 160 o.size)) -
        Cₘ (UInt256.ofNat 5) := by
  let M := MachineState.M (UInt256.ofNat 5).toNat 160 o.size
  have hMge : 2 ^ 250 ≤ M := by
    simp only [M]
    rw [show (UInt256.ofNat 5).toNat = 5 from by decide]
    unfold MachineState.M
    split
    · omega
    · apply le_trans ?_ (Nat.le_max_right _ _)
      rw [Nat.le_div_iff_mul_le (by norm_num)]
      norm_num
      omega
  have hMlt : M < UInt256.size := by
    simp only [M]
    rw [show (UInt256.ofNat 5).toNat = 5 from by decide]
    unfold MachineState.M
    split
    · norm_num [UInt256.size]
    · apply max_lt
      · norm_num [UInt256.size]
      · rw [Nat.div_lt_iff_lt_mul (by norm_num)]
        norm_num [UInt256.size] at hlo ⊢
        omega
  have hdivLower : 2 ^ 491 ≤ M * M / 512 := by
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    have hMM : (2 ^ 250) * (2 ^ 250) ≤ M * M := Nat.mul_le_mul hMge hMge
    have hpow : (2 ^ 491) * 512 = (2 ^ 250) * (2 ^ 250) := by decide
    rwa [hpow]
  have hbig :
      UInt256.size + Cₘ (UInt256.ofNat 5) <
        Cₘ (UInt256.ofNat M) := by
    rw [show Cₘ (UInt256.ofNat 5) = 15 from by
      decide]
    rw [Cₘ, UInt256.toNat_ofNat_of_lt hMlt]
    simp only [GasConstants.Gmemory, Cₘ.QuadraticCeofficient]
    have hpow : UInt256.size + 15 < 2 ^ 491 := by decide
    omega
  have hg : g.toNat < UInt256.size := g.isLt
  have hcost :
      UInt256.size <
        Cₘ (UInt256.ofNat M) - Cₘ (UInt256.ofNat 5) := by
    omega
  simpa [M] using lt_trans hg hcost

theorem writeWord_size_ge_mem {mem : ByteArray} {off : Nat} {word : UInt256}
    (hin : off ≤ mem.size) :
    mem.size ≤ (word.toByteArray.write 0 mem off 32).size := by
  rw [write32_eq (UInt256.toByteArray word) mem off
      (by rw [toByteArray_size]) hin]
  have hhead : (mem.extract 0 off).size = off := by
    rw [ByteArray.size_extract]
    omega
  have hword : ((UInt256.toByteArray word).extract 0 32).size = 32 := by
    rw [ByteArray.size_extract, toByteArray_size]
    omega
  by_cases htailIn : off + 32 ≤ mem.size
  · have htail :
        (mem.extract (off + 32) mem.size).size =
          mem.size - (off + 32) := by
      rw [ByteArray.size_extract]
      omega
    rw [ByteArray.size_append, ByteArray.size_append, hhead, hword, htail]
    omega
  · have htail : (mem.extract (off + 32) mem.size).size = 0 := by
      rw [ByteArray.size_extract]
      omega
    rw [ByteArray.size_append, ByteArray.size_append, hhead, hword, htail]
    omega

theorem writeWord_size_gt64_of_mem {mem : ByteArray} {off : Nat} {word : UInt256}
    (hmem : 64 < mem.size) (hin : off ≤ mem.size) :
    64 < (word.toByteArray.write 0 mem off 32).size :=
  lt_of_lt_of_le hmem (writeWord_size_ge_mem (mem := mem) (off := off) (word := word) hin)

theorem currentLengthReturnWrite_preserves_read64 {mem : ByteArray} {len freePtr : UInt256}
    (hptr : 96 ≤ freePtr.toNat) (hin : freePtr.toNat ≤ mem.size)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray freePtr) :
    (len.toByteArray.write 0 mem freePtr.toNat 32).readWithPadding 64 32 =
      UInt256.toByteArray freePtr := by
  rw [write32_read_below (UInt256.toByteArray len) mem freePtr.toNat 64
    (by rw [toByteArray_size]) hin (by
      rw [show 64 + 32 = 96 from rfl]
      exact hptr)]
  exact hread

theorem currentLengthReturnWrite_readBack {mem : ByteArray} {len freePtr : UInt256}
    (hin : freePtr.toNat ≤ mem.size) :
    (len.toByteArray.write 0 mem freePtr.toNat 32).readWithPadding freePtr.toNat 32 =
      UInt256.toByteArray len := by
  rw [write32_read_back (UInt256.toByteArray len) mem freePtr.toNat
    (by rw [toByteArray_size]) hin]
  rw [toByteArray_extract_all]

theorem currentLengthReturnWrite_preserves_read64_zero {mem : ByteArray} {len freePtr : UInt256}
    (hptr : 96 ≤ freePtr.toNat) (hin : freePtr.toNat ≤ mem.size)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray freePtr) :
    (len.toByteArray.write 0 mem (freePtr + ⟨0⟩).toNat 32).readWithPadding 64 32 =
      UInt256.toByteArray freePtr := by
  simpa [setAddZero_toNat] using
    currentLengthReturnWrite_preserves_read64
      (mem := mem) (len := len) (freePtr := freePtr) hptr hin hread

theorem currentLengthReturnWrite_retBytes {mem : ByteArray} {len freePtr : UInt256}
    (hin : freePtr.toNat ≤ mem.size)
    (hretLen : (UInt256.sub (freePtr + ⟨32⟩) freePtr).toNat = 32) :
    (len.toByteArray.write 0 mem (freePtr + ⟨0⟩).toNat 32).readWithPadding
        freePtr.toNat (UInt256.sub (freePtr + ⟨32⟩) freePtr).toNat =
      UInt256.toByteArray len := by
  rw [hretLen]
  simpa [setAddZero_toNat] using
    currentLengthReturnWrite_readBack (mem := mem) (len := len) (freePtr := freePtr) hin

theorem currentLength_mload64_of_read64 {mem : ByteArray} {freePtr : UInt256}
    (hmem : 64 < mem.size)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray freePtr) :
    (if (⟨64⟩ : UInt256).toNat ≥ mem.size then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      freePtr := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (v := freePtr)
    (by simpa using hmem)
    (by simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hread)

theorem machineState_M_32_lt_u256_size {s f : ℕ}
    (hs : s < UInt256.size) (hf : f < UInt256.size) :
    MachineState.M s f 32 < UInt256.size := by
  simp only [MachineState.M]
  apply max_lt hs
  apply Nat.div_lt_of_lt_mul
  have hsize : 64 ≤ UInt256.size := by
    norm_num [UInt256.size]
  nlinarith

theorem machineState_M_mul32_lt_of_bounds {s f l : ℕ}
    (hs : s * 32 < UInt256.size)
    (hfl : f + l + 31 < UInt256.size) :
    MachineState.M s f l * 32 < UInt256.size := by
  by_cases hl : l = 0
  · simp [MachineState.M, hl, hs]
  · simp only [MachineState.M]
    let c := (f + l + 31) / 32
    have hceil : ((f + l + 31) / 32) * 32 ≤ f + l + 31 :=
      Nat.div_mul_le_self (f + l + 31) 32
    have hc : c * 32 < UInt256.size := by
      exact lt_of_le_of_lt hceil hfl
    by_cases hsc : s ≤ c
    · rw [max_eq_right hsc]
      exact hc
    · have hcs : c ≤ s := Nat.le_of_not_ge hsc
      rw [max_eq_left hcs]
      exact hs

theorem machineState_M_word_mul32_lt_of_bounds {aw off len : UInt256}
    (haw : aw.toNat * 32 < UInt256.size)
    (hoff : off.toNat + len.toNat + 31 < UInt256.size) :
    (UInt256.ofNat (MachineState.M aw.toNat off.toNat len.toNat)).toNat * 32 <
      UInt256.size := by
  have hM := machineState_M_mul32_lt_of_bounds
    (s := aw.toNat) (f := off.toNat) (l := len.toNat) haw hoff
  have hMSize : MachineState.M aw.toNat off.toNat len.toNat < UInt256.size := by
    have hle : MachineState.M aw.toNat off.toNat len.toNat ≤
        MachineState.M aw.toNat off.toNat len.toNat * 32 := by
      simpa using Nat.mul_le_mul_left
        (MachineState.M aw.toNat off.toNat len.toNat) (by decide : 1 ≤ 32)
    exact lt_of_le_of_lt hle hM
  rw [ulit_toNat' _ hMSize]
  exact hM

theorem machineState_M_ge_left {s f l : Nat} : s ≤ MachineState.M s f l := by
  by_cases hl : l = 0
  · simp [MachineState.M, hl]
  · simp [MachineState.M]

theorem machineState_M_word_ge_aw {aw off len : UInt256}
    (hMSize : MachineState.M aw.toNat off.toNat len.toNat < UInt256.size) :
    aw.toNat ≤ (UInt256.ofNat (MachineState.M aw.toNat off.toNat len.toNat)).toNat := by
  rw [ulit_toNat' _ hMSize]
  exact machineState_M_ge_left

theorem activeWordsMload64_eq_self {aw : UInt256} (hge : 3 ≤ aw.toNat) :
    UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32) = aw := by
  apply u256_inj
  have hM : MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32 = aw.toNat := by
    simp only [MachineState.M]
    have hceil : ((⟨64⟩ : UInt256).toNat + 32 + 31) / 32 = 3 := by
      decide
    rw [hceil]
    exact max_eq_left hge
  rw [hM]
  exact congrArg UInt256.toNat (u256_ofNat_toNat aw)

theorem activeWordsMload128_eq_self {aw : UInt256} (hge : 5 ≤ aw.toNat) :
    UInt256.ofNat (MachineState.M aw.toNat (⟨128⟩ : UInt256).toNat 32) = aw := by
  apply u256_inj
  have hM : MachineState.M aw.toNat (⟨128⟩ : UInt256).toNat 32 = aw.toNat := by
    simp only [MachineState.M]
    change max aw.toNat 5 = aw.toNat
    exact max_eq_left hge
  rw [hM]
  exact congrArg UInt256.toNat (u256_ofNat_toNat aw)

theorem activeWordsMstore0_eq_self {aw : UInt256} (hge : 1 ≤ aw.toNat) :
    UInt256.ofNat (MachineState.M aw.toNat 0 32) = aw := by
  apply u256_inj
  have hM : MachineState.M aw.toNat 0 32 = aw.toNat := by
    simp only [MachineState.M]
    change max aw.toNat 1 = aw.toNat
    exact max_eq_left hge
  rw [hM]
  exact congrArg UInt256.toNat (u256_ofNat_toNat aw)

theorem stringStoreLite_write_len_zero (src base : ByteArray) (sa da : Nat) :
    src.write sa base da 0 = base := by
  simp [ByteArray.write]

theorem byteArray_eq_of_toList_eq {a b : ByteArray} (h : a.toList = b.toList) : a = b := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [← byteArray_toList_eq a, ← byteArray_toList_eq b]
  exact h

theorem activeWordsMstore4_eq_self {aw : UInt256} (hge : 2 ≤ aw.toNat) :
    UInt256.ofNat (MachineState.M aw.toNat 4 32) = aw := by
  apply u256_inj
  have hM : MachineState.M aw.toNat 4 32 = aw.toNat := by
    simp only [MachineState.M]
    change max aw.toNat 2 = aw.toNat
    exact max_eq_left hge
  rw [hM]
  exact congrArg UInt256.toNat (u256_ofNat_toNat aw)

theorem activeWordsRevert0_36_eq_self {aw : UInt256} (hge : 2 ≤ aw.toNat) :
    UInt256.ofNat (MachineState.M aw.toNat 0 36) = aw := by
  apply u256_inj
  have hM : MachineState.M aw.toNat 0 36 = aw.toNat := by
    simp only [MachineState.M]
    change max aw.toNat 2 = aw.toNat
    exact max_eq_left hge
  rw [hM]
  exact congrArg UInt256.toNat (u256_ofNat_toNat aw)

theorem byteArray_extract_toList (bytes : ByteArray) (start stop : Nat) :
    (bytes.extract start stop).toList =
      (bytes.toList.drop start).take (stop - start) := by
  rw [byteArray_toList_eq (bytes.extract start stop)]
  rw [ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop]
  rw [← byteArray_toList_eq bytes]

theorem byteArray_extract_toList_length_of_le {bytes : ByteArray} {start stop : Nat}
    (hle : stop ≤ bytes.size) :
    (bytes.extract start stop).toList.length = stop - start := by
  rw [byteArray_extract_toList]
  rw [List.length_take, List.length_drop]
  have hlen : bytes.toList.length = bytes.size := by
    rw [byteArray_toList_eq bytes, Array.length_toList]
    rw [ByteArray.size_data]
  rw [hlen]
  omega

theorem readWithPadding_tail32_toList (b : ByteArray) {addr : Nat}
    (hsize32 : 32 ≤ b.size) (haddr : addr < b.size) (htail : b.size < addr + 32) :
    (b.readWithPadding addr 32).toList =
      b.toList.drop addr ++ List.replicate (32 - (b.toList.drop addr).length) 0 := by
  unfold ByteArray.readWithPadding ByteArray.readWithoutPadding
  rw [if_neg (by norm_num : ¬ ((32 : Nat) ≥ 2 ^ 64))]
  rw [if_neg (by omega : ¬ addr ≥ b.size)]
  rw [show min 32 b.size = 32 by omega]
  change
    (b.extract addr (addr + 32) ++
        ByteArray.zeroes (32 - (b.extract addr (addr + 32)).size)).toList =
      b.toList.drop addr ++ List.replicate (32 - (b.toList.drop addr).length) 0
  rw [byteArray_toList_eq (_ ++ _), ByteArray.data_append, Array.toList_append]
  rw [ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop]
  rw [← byteArray_toList_eq b]
  have hdropLen : (b.toList.drop addr).length = b.size - addr := by
    rw [List.length_drop]
    rw [byteArray_toList_eq b, Array.length_toList, ByteArray.size_data]
  have htake : (b.toList.drop addr).take (addr + 32 - addr) = b.toList.drop addr := by
    rw [show addr + 32 - addr = 32 by omega]
    exact List.take_of_length_le (by rw [hdropLen]; omega)
  rw [htake]
  have hreadSize : (b.extract addr (addr + 32)).size = b.size - addr := by
    rw [ByteArray.size_extract]
    omega
  rw [hreadSize, byteArray_zeroes_toList]
  have pad_toNat : b.size - addr = (List.drop addr b.toList).length := by omega
  rw [pad_toNat]

@[simp] theorem wordBytesBEArray_size (w : UInt256) :
    ({ data := (EVM.Word.toBytesBE w).toArray } : ByteArray).size = 32 := by
  simpa using word_toBytesBE_toByteArray_size w

theorem writeCascade_extract_preserved_len
    (mem : ByteArray) (writes : List (Nat × UInt256)) (read len : Nat)
    (hwin : WindowDisjointFromWrites mem.size read len writes)
    (hpos : 0 < len) (hlen64 : len < 2 ^ 64)
    (hout : read + len ≤ (writeCascade mem writes).size)
    (hin : read + len ≤ mem.size) :
    (writeCascade mem writes).extract read (read + len) =
      mem.extract read (read + len) := by
  rw [← readWithPadding_eq_extract' (writeCascade mem writes) read len hpos hlen64 hout]
  rw [← readWithPadding_eq_extract' mem read len hpos hlen64 hin]
  exact writeCascade_read_preserved_len mem writes read len hwin hpos hlen64

theorem get?_eq_of_extract_one' (a b : ByteArray) (i : Nat) (ha : i < a.size) (hb : i < b.size)
    (h : a.extract i (i + 1) = b.extract i (i + 1)) :
    a.get? i = b.get? i := by
  unfold ByteArray.get?
  simp only [dif_pos ha, dif_pos hb]
  have h0 : (a.extract i (i + 1)).get? 0 = (b.extract i (i + 1)).get? 0 := by rw [h]
  unfold ByteArray.get? at h0
  have hsa : 0 < (a.extract i (i + 1)).size := by rw [ByteArray.size_extract]; omega
  have hsb : 0 < (b.extract i (i + 1)).size := by rw [ByteArray.size_extract]; omega
  simp only [dif_pos hsa, dif_pos hsb] at h0
  have hla : (a.extract i (i + 1)).get 0 hsa = a.get i ha := by
    change (a.extract i (i + 1))[0] = a[i]
    simpa using ByteArray.get_extract (a := a) (start := i) (stop := i + 1) (i := 0) hsa
  have hlb : (b.extract i (i + 1)).get 0 hsb = b.get i hb := by
    change (b.extract i (i + 1))[0] = b[i]
    simpa using ByteArray.get_extract (a := b) (start := i) (stop := i + 1) (i := 0) hsb
  rw [hla, hlb] at h0
  exact h0

theorem decode_eq_of_get?_arg_eq (a b : ByteArray) (pc : UInt256)
    (hget : a.get? pc.toNat = b.get? pc.toNat)
    (harg : ∀ byte instr,
      b.get? pc.toNat = some byte → parseInstr byte = some instr →
      a.extract' (pc.toNat + 1) (pc.toNat + 1 + argOnNBytesOfInstr instr) =
        b.extract' (pc.toNat + 1) (pc.toNat + 1 + argOnNBytesOfInstr instr)) :
    decode a pc = decode b pc := by
  unfold decode
  rw [hget]
  cases hb : b.get? pc.toNat with
  | none => rfl
  | some byte =>
      cases hi : parseInstr byte with
      | none => simp [hi]
      | some instr =>
          simp [hi]
          by_cases hn : argOnNBytesOfInstr instr = 0
          · simp [hn]
          · simp [hn]
            rw [harg byte instr hb hi]

theorem uInt256OfByteArray_toByteArray (w : UInt256) :
    uInt256OfByteArray (UInt256.toByteArray w) = w := by
  rw [uInt256OfByteArray_eq]
  rw [fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]

theorem write_from_gap_eq' (src base : ByteArray) (srcAddr destAddr len : Nat)
    (hlen : len ≠ 0) (hsrc : srcAddr + len ≤ src.size)
    (hge : base.size ≤ destAddr) (hgap : destAddr - base.size < USize.size) :
    src.write srcAddr base destAddr len =
      base ++ ByteArray.zeroes (destAddr - base.size) ++
        src.extract srcAddr (srcAddr + len) := by
  apply ByteArray.ext
  unfold ByteArray.write
  rw [if_neg hlen, if_neg (show ¬ srcAddr ≥ src.size from by omega)]
  have hcopy : min len (src.size - srcAddr) = len := by omega
  have htail : min base.size (destAddr + len) - (destAddr + len) = 0 := by omega
  simp only [hcopy, htail, ByteArray.data_copySlice, ByteArray.data_append,
    ByteArray.data_extract, show (destAddr - base.size) =
      destAddr - base.size from rfl]
  have hpz : (ByteArray.zeroes (destAddr - base.size)).data.size =
      destAddr - base.size := by
    rw [show (ByteArray.zeroes (destAddr - base.size)).data.size =
          (ByteArray.zeroes (destAddr - base.size)).size from rfl,
      ByteArray_zeroes_size]
  have hDsz : (base.data ++
        (ByteArray.zeroes (destAddr - base.size)).data).size =
      destAddr := by
    rw [Array.size_append, hpz, show base.data.size = base.size from rfl]
    omega
  rw [show (ByteArray.zeroes 0).data = (#[] : Array UInt8) from by
    rw [zeroes_zero (n := (0)) (by rfl)]
    rfl]
  simp only [Array.append_empty, Nat.add_zero]
  rw [show min len (src.data.size - srcAddr) = len by
    have : src.data.size = src.size := rfl
    omega]
  rw [Array.extract_eq_self_of_le (by rw [hDsz])]
  rw [show (base.data ++
        (ByteArray.zeroes (destAddr - base.size)).data).extract
          (destAddr + len) = (#[] : Array UInt8) from by
    apply Array.extract_eq_empty_of_le
    rw [hDsz]
    omega]
  simp [Array.append_assoc]

theorem balanceOfThisStaticcallWriteLen_of_size_ge (o : ByteArray)
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size) :
    (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat = 32 := by
  simpa using
    umin_ofNat_right_toNat_of_ge (c := 32) (n := o.size) (by decide) hlo hhi

theorem balanceOfThisStaticcallWriteLen_of_size_lt (o : ByteArray)
    (hshort : o.size < 32) (hhi : o.size < UInt256.size) :
    (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat = o.size := by
  simpa using
    umin_ofNat_right_toNat_of_lt (c := 32) (n := o.size) (by decide) hshort hhi

theorem balanceDynamicReturnWriteLen (out : ByteArray) (hout : out.size < UInt256.size) :
    (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat = min 32 out.size := by
  by_cases hlo : 32 ≤ out.size
  · rw [balanceOfThisStaticcallWriteLen_of_size_ge out hlo hout, Nat.min_eq_left hlo]
  · rw [balanceOfThisStaticcallWriteLen_of_size_lt out (by omega) hout, Nat.min_eq_right (by omega)]

theorem fromByteArrayBigEndian_readWithPadding0_32_lt (o : ByteArray) :
    fromByteArrayBigEndian (o.readWithPadding 0 32) < UInt256.size := by
  unfold fromByteArrayBigEndian fromBytesBigEndian
  have h := EVM.fromBytes'_le (bs := (o.readWithPadding 0 32).toList.reverse)
  rw [List.length_reverse] at h
  have hlen : (o.readWithPadding 0 32).toList.length = 32 := by
    rw [byteArray_toList_eq, Array.length_toList]
    change (o.readWithPadding 0 32).size = 32
    unfold ByteArray.readWithPadding
    rw [if_neg (by norm_num : ¬ (32 ≥ 2 ^ 64))]
    rw [ByteArray.size_append, ByteArray_zeroes_size]
    have hreadLe : (o.readWithoutPadding 0 32).size ≤ 32 := by
      unfold ByteArray.readWithoutPadding
      by_cases h : 0 ≥ o.size
      · rw [if_pos h]
        simp
      · rw [if_neg h]
        rw [ByteArray.size_extract]
        omega
    omega
  rw [hlen] at h
  simpa [UInt256.size] using h

theorem permitRuntimeEcrecoverStaticcallWriteLen_of_size_ge (o : ByteArray)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat = 32 := by
  exact umin_ofNat_right_toNat_of_ge (c := 32) (n := o.size) (by decide) ho32 hoSize

theorem permitRuntimeEcrecoverStaticcallWriteLen_of_size_lt (o : ByteArray)
    (hshort : o.size < 32) (hoSize : o.size < UInt256.size) :
    (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat = o.size := by
  simpa using
    umin_ofNat_right_toNat_of_lt (c := 32) (n := o.size) (by decide) hshort hoSize

theorem empty_readWithPadding32_eq_zeroWord :
    ByteArray.empty.readWithPadding 0 32 = UInt256.toByteArray (⟨0⟩ : UInt256) := by
  decide +kernel

theorem byteArray_readWithPadding0_short_eq_extract_zero_tail (o : ByteArray)
    (hzero : o.size ≠ 0) (hshort : o.size < 32) :
    o.readWithPadding 0 32 =
      o.extract 0 o.size ++ (UInt256.toByteArray (⟨0⟩ : UInt256)).extract o.size 32 := by
  symm
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [show (o.readWithPadding 0 32).data.toList = (o.readWithPadding 0 32).toList by
    rw [← byteArray_toList_eq]]
  rw [readWithPadding_zero_toList_of_size_lt32 o hzero hshort]
  rw [ByteArray.toList_data_append]
  rw [show (o.extract 0 o.size).data.toList = o.data.toList by
    rw [← byteArray_toList_eq, byteArray_extract_self, byteArray_toList_eq]]
  rw [byteArray_toList_eq]
  rw [zero_toByteArray_eq_zeroes32]
  rw [ByteArray.data_extract, Array.toList_extract, byteArray_zeroes_toList]
  rw [List.extract_eq_take_drop, List.drop_replicate, List.take_replicate]
  congr 1
  rw [min_self]

theorem safeTransferReturnDataActiveWords_M_mul32_lt (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    MachineState.M (UInt256.ofNat 13).toNat 324 out.size * 32 < UInt256.size := by
  rw [show (UInt256.ofNat 13).toNat = 13 from by decide]
  unfold MachineState.M
  split
  · norm_num [UInt256.size]
  · by_cases hle : 13 ≤ (324 + out.size + 31) / 32
    · rw [Nat.max_eq_right hle]
      have hdiv : ((324 + out.size + 31) / 32) * 32 ≤ 324 + out.size + 31 :=
        Nat.div_mul_le_self _ _
      have hcap : 2 ^ 255 + 355 < UInt256.size := by norm_num [UInt256.size]
      omega
    · rw [Nat.max_eq_left (Nat.le_of_not_ge hle)]
      norm_num [UInt256.size]

theorem safeTransferReturnDataHugeCopyMemCost_gt_g
    (g : Sat256) (out : ByteArray)
    (hhi : 2 ^ 255 ≤ out.size) (hlo : out.size < UInt256.size) :
    g.toNat <
      Cₘ (UInt256.ofNat (MachineState.M (UInt256.ofNat 13).toNat 324 out.size)) -
        Cₘ (UInt256.ofNat 13) := by
  let M := MachineState.M (UInt256.ofNat 13).toNat 324 out.size
  have hMge : 2 ^ 250 ≤ M := by
    simp only [M]
    rw [show (UInt256.ofNat 13).toNat = 13 from by decide]
    unfold MachineState.M
    split
    · omega
    · apply le_trans ?_ (Nat.le_max_right _ _)
      rw [Nat.le_div_iff_mul_le (by norm_num)]
      norm_num
      omega
  have hMlt : M < UInt256.size := by
    simp only [M]
    rw [show (UInt256.ofNat 13).toNat = 13 from by decide]
    unfold MachineState.M
    split
    · norm_num [UInt256.size]
    · apply max_lt
      · norm_num [UInt256.size]
      · rw [Nat.div_lt_iff_lt_mul (by norm_num)]
        norm_num [UInt256.size] at hlo ⊢
        omega
  have hdivLower : 2 ^ 491 ≤ M * M / 512 := by
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    have hMM : (2 ^ 250) * (2 ^ 250) ≤ M * M := Nat.mul_le_mul hMge hMge
    have hpow : (2 ^ 491) * 512 = (2 ^ 250) * (2 ^ 250) := by decide
    rwa [hpow]
  have hbig :
      UInt256.size + Cₘ (UInt256.ofNat 13) <
        Cₘ (UInt256.ofNat M) := by
    rw [show Cₘ (UInt256.ofNat 13) = 39 from by decide]
    rw [Cₘ, UInt256.toNat_ofNat_of_lt hMlt]
    simp only [GasConstants.Gmemory, Cₘ.QuadraticCeofficient]
    have hpow : UInt256.size + 39 < 2 ^ 491 := by decide
    omega
  have hg : g.toNat < UInt256.size := g.isLt
  have hcost :
      UInt256.size <
        Cₘ (UInt256.ofNat M) - Cₘ (UInt256.ofNat 13) := by
    omega
  simpa [M] using lt_trans hg hcost

theorem uInt256_mload64_same_of_toNat_ge13 (aw : UInt256) (haw : 13 ≤ aw.toNat) :
    UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32) = aw := by
  have hM : MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32 = aw.toNat := by
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
    simp [MachineState.M]
    omega
  rw [hM]
  exact u256_ofNat_toNat aw

theorem writeCascade_size_of_eq
    (base : ByteArray) (writes : List (Nat × UInt256)) (baseSize finalSize : Nat)
    (hbase : base.size = baseSize) (hgaps : WriteGapsOk base.size writes)
    (hwritesSize : writeCascadeSize baseSize writes = finalSize) :
    (writeCascade base writes).size = finalSize := by
  rw [writeCascade_size base writes hgaps, hbase]
  exact hwritesSize

theorem wordWrite_read_boundary4
    (mem : ByteArray) (leftWord rightWord : UInt256) (writeOff : Nat)
    (hlo : 4 ≤ writeOff) (hmem : mem.size = writeOff)
    (hleft :
      mem.readWithPadding (writeOff - 4) 4 =
        (UInt256.toByteArray leftWord).extract 28 32) :
    ((UInt256.toByteArray rightWord).write 0 mem writeOff 32).readWithPadding
        (writeOff - 4) 32 =
      (UInt256.toByteArray leftWord).extract 28 32 ++
        (UInt256.toByteArray rightWord).extract 0 28 := by
  let out := (UInt256.toByteArray rightWord).write 0 mem writeOff 32
  have hsize : out.size = writeOff + 32 := by
    dsimp [out]
    exact toByteArray_write32_size_of_ge mem rightWord writeOff writeOff
      (writeOff + 32) hmem (by omega)
      (by rw [Nat.sub_self]; exact lt_usize 0 (by norm_num)) rfl
  have hleftExtract :
      out.extract (writeOff - 4) writeOff =
        (UInt256.toByteArray leftWord).extract 28 32 := by
    rw [show out.extract (writeOff - 4) writeOff =
        out.extract (writeOff - 4) ((writeOff - 4) + 4) by
      rw [show (writeOff - 4) + 4 = writeOff by omega]]
    rw [← readWithPadding_eq_extract' out (writeOff - 4) 4 (by norm_num) (by norm_num)
      (by rw [hsize]; omega)]
    dsimp [out]
    rw [write32_read_below_len _ _ writeOff (writeOff - 4) 4 (by rw [toByteArray_size])
      (by rw [hmem]) (by omega) (by rw [hmem]; omega) (by norm_num) (by norm_num)]
    exact hleft
  have hrightExtract :
      out.extract writeOff (writeOff + 28) =
        (UInt256.toByteArray rightWord).extract 0 28 := by
    rw [← readWithPadding_eq_extract' out writeOff 28 (by norm_num) (by norm_num)
      (by rw [hsize]; omega)]
    dsimp [out]
    exact toByteArray_write_read_window_of_gap rightWord mem writeOff 0 28
      (by norm_num) (by norm_num) (by norm_num)
      (by rw [hmem, Nat.sub_self]; exact lt_usize 0 (by norm_num))
  rw [readWithPadding_eq_extract' out (writeOff - 4) 32 (by norm_num) (by norm_num)
    (by rw [hsize]; omega)]
  rw [show (writeOff - 4) + 32 = writeOff + 28 by omega]
  rw [show out.extract (writeOff - 4) (writeOff + 28) =
      out.extract (writeOff - 4) writeOff ++ out.extract writeOff (writeOff + 28) by
    rw [ByteArray.extract_append_extract]
    congr <;> omega]
  rw [hleftExtract, hrightExtract]

theorem fromBytesBigEndian_append (a b : List UInt8) :
    fromBytesBigEndian (a ++ b) =
      fromBytesBigEndian a * 2 ^ (8 * b.length) + fromBytesBigEndian b := by
  unfold fromBytesBigEndian Function.comp
  rw [List.reverse_append, fromBytes'_append, List.length_reverse]
  ring

theorem fromByteArrayBigEndian_append (a b : ByteArray) :
    fromByteArrayBigEndian (a ++ b) =
      fromByteArrayBigEndian a * 2 ^ (8 * b.size) + fromByteArrayBigEndian b := by
  simp [fromByteArrayBigEndian, byteArray_toList_eq, fromBytesBigEndian_append]

theorem toByteArray_extract4_32_toList (w : UInt256) :
    ((UInt256.toByteArray w).extract 4 32).toList =
      (UInt256.toByteArray w).toList.drop 4 := by
  rw [byteArray_toList_eq, byteArray_toList_eq]
  rw [ByteArray.data_extract, Array.toList_extract]
  rw [List.extract_eq_take_drop]
  have hlen : (UInt256.toByteArray w).data.toList.length = 32 := by
    rw [← byteArray_toList_eq]
    have hs := toByteArray_size w
    simpa [byteArray_toList_eq] using congrArg (fun n => n) hs
  rw [List.take_of_length_le]
  rw [List.length_drop, hlen]

theorem fromBytesBigEndian_bound (xs : List UInt8) :
    fromBytesBigEndian xs < 2 ^ (8 * xs.length) := by
  unfold fromBytesBigEndian Function.comp
  simpa [List.length_reverse] using (fromBytes'_le (bs := xs.reverse))

theorem fromByteArrayBigEndian_toByteArray_extract4_32 (w : UInt256) :
    fromByteArrayBigEndian ((UInt256.toByteArray w).extract 4 32) =
      w.toNat % 2 ^ 224 := by
  let xs := (UInt256.toByteArray w).toList
  have hxsLen : xs.length = 32 := by
    dsimp [xs]
    simpa [byteArray_toList_eq] using toByteArray_size w
  have htailLen : (xs.drop 4).length = 28 := by
    rw [List.length_drop, hxsLen]
  have htailBound : fromBytesBigEndian (xs.drop 4) < 2 ^ 224 := by
    have hb := fromBytesBigEndian_bound (xs.drop 4)
    rw [htailLen] at hb
    simpa using hb
  have hfull : fromBytesBigEndian xs = w.toNat := by
    dsimp [xs]
    simpa [fromByteArrayBigEndian] using fromByteArrayBigEndian_toByteArray w
  have hsplit :
      fromBytesBigEndian xs =
        fromBytesBigEndian (xs.take 4) * 2 ^ 224 + fromBytesBigEndian (xs.drop 4) := by
    calc
      fromBytesBigEndian xs = fromBytesBigEndian (xs.take 4 ++ xs.drop 4) := by
        exact congrArg fromBytesBigEndian (List.take_append_drop 4 xs).symm
      _ = fromBytesBigEndian (xs.take 4) * 2 ^ 224 + fromBytesBigEndian (xs.drop 4) := by
        rw [fromBytesBigEndian_append, htailLen]
  have hfull' :
      w.toNat =
        fromBytesBigEndian (xs.take 4) * 2 ^ 224 + fromBytesBigEndian (xs.drop 4) := by
    rw [← hfull, hsplit]
  unfold fromByteArrayBigEndian
  rw [toByteArray_extract4_32_toList]
  dsimp [xs] at htailLen htailBound hfull' ⊢
  rw [hfull']
  change fromBytesBigEndian (List.drop 4 (UInt256.toByteArray w).toList) =
    (fromBytesBigEndian (List.take 4 (UInt256.toByteArray w).toList) * 2 ^ 224 +
      fromBytesBigEndian (List.drop 4 (UInt256.toByteArray w).toList)) % 2 ^ 224
  rw [show fromBytesBigEndian (List.take 4 (UInt256.toByteArray w).toList) * 2 ^ 224 +
        fromBytesBigEndian (List.drop 4 (UInt256.toByteArray w).toList) =
      fromBytesBigEndian (List.drop 4 (UInt256.toByteArray w).toList) +
        2 ^ 224 * fromBytesBigEndian (List.take 4 (UInt256.toByteArray w).toList) by ring]
  rw [Nat.add_mul_mod_self_left]
  exact (Nat.mod_eq_of_lt htailBound).symm

theorem toByteArray_extract0_4_toList (w : UInt256) :
    ((UInt256.toByteArray w).extract 0 4).toList =
      (UInt256.toByteArray w).toList.take 4 := by
  rw [byteArray_toList_eq, byteArray_toList_eq]
  rw [ByteArray.data_extract, Array.toList_extract]
  rw [List.extract_eq_take_drop, List.drop_zero]

theorem fromByteArrayBigEndian_toByteArray_extract0_4 (w : UInt256) :
    fromByteArrayBigEndian ((UInt256.toByteArray w).extract 0 4) =
      w.toNat / 2 ^ 224 := by
  let xs := (UInt256.toByteArray w).toList
  have hxsLen : xs.length = 32 := by
    dsimp [xs]
    simpa [byteArray_toList_eq] using toByteArray_size w
  have htailLen : (xs.drop 4).length = 28 := by
    rw [List.length_drop, hxsLen]
  have hfull : fromBytesBigEndian xs = w.toNat := by
    dsimp [xs]
    simpa [fromByteArrayBigEndian] using fromByteArrayBigEndian_toByteArray w
  have hdiv : fromBytesBigEndian xs / 2 ^ 224 = fromBytesBigEndian (xs.take 4) := by
    conv_lhs => rw [← List.take_append_drop 4 xs]
    rw [show (224 : ℕ) = 8 * (xs.drop 4).length by rw [htailLen],
      fromBytesBigEndian_append_div]
  unfold fromByteArrayBigEndian
  rw [toByteArray_extract0_4_toList]
  dsimp [xs] at hfull hdiv ⊢
  rw [← hdiv, hfull]

theorem secondBalanceStaticcallWriteLen_of_size_ge (out : ByteArray)
    (hlo : 32 ≤ out.size) (hhi : out.size < UInt256.size) :
    (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 32 := by
  simpa using
    umin_ofNat_right_toNat_of_ge (c := 32) (n := out.size) (by decide) hlo hhi

theorem secondBalanceStaticcallWriteLen_of_size_lt (out : ByteArray)
    (hshort : out.size < 32) (hhi : out.size < UInt256.size) :
    (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat = out.size := by
  simpa using
    umin_ofNat_right_toNat_of_lt (c := 32) (n := out.size) (by decide) hshort hhi

theorem byteArray_zeroes_size_le (n : Nat) :
    (ByteArray.zeroes n).size ≤ n :=
  (ByteArray_zeroes_size n).le

theorem byteArray_copySlice_size_le
    (source destination : ByteArray) (sourceOffset destinationOffset length : Nat) :
    (source.copySlice sourceOffset destination destinationOffset length).size ≤
      max destination.size (destinationOffset + length) := by
  rw [ByteArray.copySlice_eq_append, ByteArray.size_append, ByteArray.size_append,
    ByteArray.size_extract, ByteArray.size_extract, ByteArray.size_extract]
  rw [show source.data.size = source.size from rfl,
    show destination.data.size = destination.size from rfl]
  omega

theorem byteArray_write_size_le
    (source destination : ByteArray) (sourceOffset destinationOffset length : Nat) :
    (source.write sourceOffset destination destinationOffset length).size ≤
      max destination.size (destinationOffset + length) := by
  unfold ByteArray.write
  by_cases hlen : length = 0
  · simp [hlen]
  · simp [hlen]
    by_cases hsrc : sourceOffset ≥ source.size
    · simp [hsrc]
      have hcopy := byteArray_copySlice_size_le
        (ByteArray.zeroes
          (min length (destination.size - destinationOffset)))
        destination 0 (min destinationOffset destination.size)
        (min length (destination.size - destinationOffset))
      have hbound :
          max destination.size
              (min destinationOffset destination.size +
                min length (destination.size - destinationOffset)) ≤
            max destination.size (destinationOffset + length) := by
        omega
      exact le_max_iff.mp (le_trans hcopy hbound)
    · simp [hsrc]
      have hpad :
          (ByteArray.zeroes
              (destinationOffset - destination.size)).size ≤
            destinationOffset - destination.size :=
        byteArray_zeroes_size_le _
      have hdest :
          (destination ++ ByteArray.zeroes
              (destinationOffset - destination.size)).size ≤
            max destination.size (destinationOffset + length) := by
        rw [ByteArray.size_append]
        omega
      have hcopy := byteArray_copySlice_size_le
        (source ++ ByteArray.zeroes
          (min destination.size (destinationOffset + length) -
            (destinationOffset + min length (source.size - sourceOffset))))
        (destination ++ ByteArray.zeroes
          (destinationOffset - destination.size))
        sourceOffset destinationOffset
        (min length (source.size - sourceOffset) +
          (min destination.size (destinationOffset + length) -
            (destinationOffset + min length (source.size - sourceOffset))))
      have hwriteEnd :
          destinationOffset +
              (min length (source.size - sourceOffset) +
                (min destination.size (destinationOffset + length) -
                  (destinationOffset + min length (source.size - sourceOffset)))) ≤
            max destination.size (destinationOffset + length) := by
        omega
      exact le_max_iff.mp (le_trans hcopy (max_le hdest hwriteEnd))

theorem machineState_M_same_of_cover_len (s f l : Nat) (hcover : f + l ≤ s * 32) :
    MachineState.M s f l = s := by
  unfold MachineState.M
  cases l with
  | zero => rfl
  | succ l =>
      change max s ((f + (l + 1) + 31) / 32) = s
      rw [Nat.max_eq_left]
      have hdivlt : (f + (l + 1) + 31) / 32 < s + 1 := by
        rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 32)]
        omega
      omega

theorem secondSafeTransferReturnDataActiveWords_M_mul32_lt (out : ByteArray)
    (houtSize : out.size < 2 ^ 255) :
    MachineState.M (UInt256.ofNat 18).toNat 488 out.size * 32 < UInt256.size := by
  rw [show (UInt256.ofNat 18).toNat = 18 from by decide]
  unfold MachineState.M
  split
  · norm_num [UInt256.size]
  · by_cases hle : 18 ≤ (488 + out.size + 31) / 32
    · rw [Nat.max_eq_right hle]
      have hdiv : ((488 + out.size + 31) / 32) * 32 ≤ 488 + out.size + 31 :=
        Nat.div_mul_le_self _ _
      have hcap : 2 ^ 255 + 519 < UInt256.size := by norm_num [UInt256.size]
      omega
    · rw [Nat.max_eq_left (Nat.le_of_not_ge hle)]
      norm_num [UInt256.size]

theorem secondSafeTransferReturnDataHugeCopyMemCost_gt_g (g : Sat256) (out : ByteArray)
    (hhi : 2 ^ 255 ≤ out.size) (hlo : out.size < UInt256.size) :
    g.toNat <
      Cₘ (UInt256.ofNat (MachineState.M (UInt256.ofNat 18).toNat 488 out.size)) -
        Cₘ (UInt256.ofNat 18) := by
  let M := MachineState.M (UInt256.ofNat 18).toNat 488 out.size
  have hMge : 2 ^ 250 ≤ M := by
    simp only [M]
    rw [show (UInt256.ofNat 18).toNat = 18 from by decide]
    unfold MachineState.M
    split
    · omega
    · apply le_trans ?_ (Nat.le_max_right _ _)
      rw [Nat.le_div_iff_mul_le (by norm_num)]
      norm_num
      omega
  have hMlt : M < UInt256.size := by
    simp only [M]
    rw [show (UInt256.ofNat 18).toNat = 18 from by decide]
    unfold MachineState.M
    split
    · norm_num [UInt256.size]
    · apply max_lt
      · norm_num [UInt256.size]
      · rw [Nat.div_lt_iff_lt_mul (by norm_num)]
        norm_num [UInt256.size] at hlo ⊢
        omega
  have hdivLower : 2 ^ 491 ≤ M * M / 512 := by
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    have hMM : (2 ^ 250) * (2 ^ 250) ≤ M * M := Nat.mul_le_mul hMge hMge
    have hpow : (2 ^ 491) * 512 = (2 ^ 250) * (2 ^ 250) := by decide
    rwa [hpow]
  have hbig :
      UInt256.size + Cₘ (UInt256.ofNat 18) <
        Cₘ (UInt256.ofNat M) := by
    rw [show Cₘ (UInt256.ofNat 18) = 54 from by decide]
    rw [Cₘ, UInt256.toNat_ofNat_of_lt hMlt]
    simp only [GasConstants.Gmemory, Cₘ.QuadraticCeofficient]
    have hpow : UInt256.size + 54 < 2 ^ 491 := by decide
    omega
  have hg : g.toNat < UInt256.size := g.isLt
  have hcost :
      UInt256.size <
        Cₘ (UInt256.ofNat M) - Cₘ (UInt256.ofNat 18) := by
    omega
  simpa [M] using lt_trans hg hcost

theorem returnWrite_size_gt64_of_size196 (out base : ByteArray) (L : Nat)
    (hbase : base.size = 196) (hLo : L ≤ out.size) :
    64 < (out.write 0 base 128 L).size := by
  rcases Nat.eq_zero_or_pos L with hzero | hpos
  · subst L
    rw [byteArray_write_len_zero, hbase]
    norm_num
  · by_cases hin : 128 + L ≤ base.size
    · rw [write_eq_gen out base 128 L (by omega) hLo hin, ByteArray.size_append,
        ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
        ByteArray.size_extract, hbase]
      omega
    · have hdest : 128 ≤ base.size := by
        rw [hbase]
        omega
      have hext : base.size < 128 + L := Nat.lt_of_not_ge hin
      rw [write_eq_gen_extend out base 128 L (by omega) hLo hdest hext,
        ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract, hbase]
      omega

end Reasoning.Theory
