import Examples.Ripemd160.HashRuntime

/-!
# RIPEMD-160 runtime/model bridge

Memory invariants connecting the bytecode-level cursors in `HashRuntime` to the pure compression
model in `HashModel`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Ripemd160

/-- A cursor contains `value` as a complete EVM word at `addr`, and that word is inside the
active-memory range used by `runtimeMloadValue`. -/
def RuntimeWordAt (c : RuntimeMemCursor) (addr value : UInt256) : Prop :=
  c.mem.readWithPadding addr.toNat 32 = value.toByteArray ∧
  addr.toNat + 32 ≤ c.mem.size ∧
  ¬ addr ≥ c.aw * ⟨32⟩

def RuntimeCursorSmall (c : RuntimeMemCursor) : Prop :=
  c.aw.toNat < 2 ^ 64 ∧ c.mem.size < 2 ^ 64

theorem RuntimeWordAt.load {c : RuntimeMemCursor} {addr value : UInt256}
    (h : RuntimeWordAt c addr value) :
    runtimeMloadValue c.mem c.aw addr = value := by
  rcases h with ⟨hread, hmem, haw⟩
  exact mloadWordValue_of_readWithPadding (by omega) haw hread

/-- `BYTE 0` of an in-bounds runtime load is the first byte at the load address. -/
theorem runtimeMloadByte0_of_readByte {c : RuntimeMemCursor} {addr : UInt256} {byte : UInt8}
    (hmem : addr.toNat < c.mem.size)
    (haw : ¬ addr ≥ c.aw * ⟨32⟩)
    (hread : c.mem.readWithPadding addr.toNat 1 = ⟨#[byte]⟩) :
    UInt256.byteAt ⟨0⟩ (runtimeMloadValue c.mem c.aw addr) =
      UInt256.ofNat byte.toNat := by
  unfold runtimeMloadValue
  rw [if_neg (not_or.mpr ⟨by omega, haw⟩)]
  rw [← uInt256OfByteArray_eq]
  apply byteAt_zero_uInt256OfByteArray
  · exact readWithPadding_size_eq _ _ 32 (by decide)
  · rw [readWithPadding32_extract_one _ _ hmem]
    exact hread

theorem mul32_toNat_of_lt_pow64 {x : UInt256} (hx : x.toNat < 2 ^ 64) :
    (x * ⟨32⟩).toNat = 32 * x.toNat := by
  rw [umul_toNat]
  · rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
    omega
  · rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide,
      show UInt256.size = 2 ^ 256 from by decide]
    omega

theorem runtimeMstoreAw_lt_pow64 {aw addr : UInt256}
    (haw : aw.toNat < 2 ^ 64) (haddr : addr.toNat + 63 < 32 * (2 ^ 64)) :
    (runtimeMstoreAw aw addr).toNat < 2 ^ 64 := by
  unfold runtimeMstoreAw
  have hm : MachineState.M aw.toNat addr.toNat 32 < 2 ^ 64 := by
    simp only [MachineState.M, OfNat.ofNat]
    rw [max_lt_iff]
    refine ⟨haw, ?_⟩
    rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 32)]
    omega
  rw [ulit_toNat' _ (lt_trans hm (by
    rw [show UInt256.size = 2 ^ 256 from by decide]
    norm_num))]
  exact hm

theorem runtimeMstoreAw_covers_end {aw addr : UInt256}
    (haw : aw.toNat < 2 ^ 64) (haddr : addr.toNat + 63 < 32 * (2 ^ 64)) :
    addr.toNat + 32 ≤ 32 * (runtimeMstoreAw aw addr).toNat := by
  have hM : (runtimeMstoreAw aw addr).toNat =
      MachineState.M aw.toNat addr.toNat 32 := by
    unfold runtimeMstoreAw
    rw [ulit_toNat' _ (machineM_lt_uint256 aw addr.toNat 32 (by
      rw [show UInt256.size = 2 ^ 256 from by decide]
      omega))]
  rw [hM]
  have hceil : addr.toNat + 32 ≤ 32 * ((addr.toNat + 32 + 31) / 32) := by
    have hmod := Nat.mod_lt (addr.toNat + 63) (by decide : 0 < 32)
    have hdecomp := Nat.mod_add_div (addr.toNat + 63) 32
    omega
  exact le_trans hceil (Nat.mul_le_mul_left 32 (by simp [MachineState.M]))

theorem runtimeMstoreAw_covers {aw addr : UInt256}
    (haw : aw.toNat < 2 ^ 64) (haddr : addr.toNat + 63 < 32 * (2 ^ 64)) :
    ¬ addr ≥ runtimeMstoreAw aw addr * ⟨32⟩ := by
  intro h
  have hout := runtimeMstoreAw_lt_pow64 haw haddr
  have hmul := mul32_toNat_of_lt_pow64 hout
  change (runtimeMstoreAw aw addr * ⟨32⟩).toNat ≤ addr.toNat at h
  rw [hmul] at h
  have hM : (runtimeMstoreAw aw addr).toNat =
      MachineState.M aw.toNat addr.toNat 32 := by
    unfold runtimeMstoreAw
    rw [ulit_toNat' _ (machineM_lt_uint256 aw addr.toNat 32 (by
      rw [show UInt256.size = 2 ^ 256 from by decide]
      omega))]
  rw [hM] at h
  have hceil : addr.toNat < 32 * ((addr.toNat + 32 + 31) / 32) := by
    have hmod := Nat.mod_lt (addr.toNat + 63) (by decide : 0 < 32)
    have hdecomp := Nat.mod_add_div (addr.toNat + 63) 32
    omega
  have hmax :
      (addr.toNat + 32 + 31) / 32 ≤ MachineState.M aw.toNat addr.toNat 32 := by
    simp [MachineState.M]
  have hstrict : addr.toNat < 32 * MachineState.M aw.toNat addr.toNat 32 :=
    lt_of_lt_of_le hceil (Nat.mul_le_mul_left 32 hmax)
  omega

theorem runtimeMstoreAw_preserves_cover {aw addr read : UInt256}
    (haw : aw.toNat < 2 ^ 64) (haddr : addr.toNat + 63 < 32 * (2 ^ 64))
    (hread : ¬ read ≥ aw * ⟨32⟩) :
    ¬ read ≥ runtimeMstoreAw aw addr * ⟨32⟩ := by
  intro hnew
  have hout := runtimeMstoreAw_lt_pow64 haw haddr
  have hge : aw.toNat ≤ (runtimeMstoreAw aw addr).toNat := by
    unfold runtimeMstoreAw
    apply machineM_ofNat_ge
    rw [show UInt256.size = 2 ^ 256 from by decide]
    omega
  apply hread
  change (aw * ⟨32⟩).toNat ≤ read.toNat
  change (runtimeMstoreAw aw addr * ⟨32⟩).toNat ≤ read.toNat at hnew
  rw [mul32_toNat_of_lt_pow64 haw]
  rw [mul32_toNat_of_lt_pow64 hout] at hnew
  omega

/-- A word store establishes the corresponding word invariant. -/
theorem runtimeStoreCursor_word_self (c : RuntimeMemCursor) (addr value : UInt256)
    (haw : c.aw.toNat < 2 ^ 64)
    (haddr : addr.toNat + 63 < 32 * (2 ^ 64))
    (hgap : addr.toNat - c.mem.size < USize.size) :
    RuntimeWordAt (runtimeStoreCursor c addr value) addr value := by
  refine ⟨?_, ?_, ?_⟩
  · exact toByteArray_write_read_back_of_gap value c.mem addr.toNat hgap
  · have hs := toByteArray_write_size_ge_off_add32 value c.mem addr.toNat hgap
    simpa [runtimeStoreCursor, runtimeMstoreMem] using hs
  · exact runtimeMstoreAw_covers haw haddr

theorem runtimeMstoreMem_size_ge (mem : ByteArray) (addr value : UInt256)
    (hgap : addr.toNat - mem.size < USize.size) :
    mem.size ≤ (runtimeMstoreMem mem addr value).size := by
  by_cases hoff : addr.toNat ≤ mem.size
  · have hs := toByteArray_write32_size_of_le mem value addr.toNat mem.size
      (max mem.size (addr.toNat + 32)) rfl hoff rfl
    simp only [runtimeMstoreMem, hs]
    exact Nat.le_max_left _ _
  · have hge : mem.size ≤ addr.toNat := by omega
    have hs := toByteArray_write32_size_of_ge mem value addr.toNat mem.size
      (addr.toNat + 32) rfl hge hgap rfl
    simp only [runtimeMstoreMem, hs]
    omega

theorem runtimeMstoreMem_size_lt_pow64 {mem : ByteArray} {addr value : UInt256}
    (hmem : mem.size < 2 ^ 64) (haddr : addr.toNat + 32 < 2 ^ 64) :
    (runtimeMstoreMem mem addr value).size < 2 ^ 64 := by
  have hgap : addr.toNat - mem.size < USize.size := by
    rw [show USize.size = 2 ^ 64 from by native_decide]
    omega
  by_cases hoff : addr.toNat ≤ mem.size
  · have hs := toByteArray_write32_size_of_le mem value addr.toNat mem.size
      (max mem.size (addr.toNat + 32)) rfl hoff rfl
    simp only [runtimeMstoreMem, hs]
    exact max_lt hmem haddr
  · have hge : mem.size ≤ addr.toNat := by omega
    have hs := toByteArray_write32_size_of_ge mem value addr.toNat mem.size
      (addr.toNat + 32) rfl hge hgap rfl
    simpa [runtimeMstoreMem, hs] using haddr

theorem RuntimeCursorSmall.store {c : RuntimeMemCursor} {addr value : UInt256}
    (hc : RuntimeCursorSmall c) (haddr : addr.toNat + 63 < 2 ^ 64) :
    RuntimeCursorSmall (runtimeStoreCursor c addr value) := by
  rcases hc with ⟨haw, hmem⟩
  constructor
  · exact runtimeMstoreAw_lt_pow64 haw (by omega)
  · exact runtimeMstoreMem_size_lt_pow64 hmem (by omega)

theorem RuntimeCursorSmall.storeWord {c : RuntimeMemCursor} {addr value : UInt256}
    (hc : RuntimeCursorSmall c) (haddr : addr.toNat + 63 < 2 ^ 64) :
    RuntimeWordAt (runtimeStoreCursor c addr value) addr value := by
  apply runtimeStoreCursor_word_self c addr value hc.1 (by omega)
  rw [show USize.size = 2 ^ 64 from by native_decide]
  omega

/-- A later word store strictly above an established word preserves it. -/
theorem RuntimeWordAt.storeAbove {c : RuntimeMemCursor} {read value addr stored : UInt256}
    (hword : RuntimeWordAt c read value)
    (haw : c.aw.toNat < 2 ^ 64)
    (haddr : addr.toNat + 63 < 32 * (2 ^ 64))
    (hbelow : read.toNat + 32 ≤ addr.toNat)
    (hgap : addr.toNat - c.mem.size < USize.size) :
    RuntimeWordAt (runtimeStoreCursor c addr stored) read value := by
  rcases hword with ⟨hread, hmem, hcover⟩
  refine ⟨?_, ?_, runtimeMstoreAw_preserves_cover haw haddr hcover⟩
  · simpa [runtimeStoreCursor, runtimeMstoreMem] using
      toByteArray_write_read_below_of_gap stored c.mem addr.toNat read.toNat
        hmem hbelow hgap |>.trans hread
  · have hs := toByteArray_write_size_ge_off_add32 stored c.mem addr.toNat hgap
    simp only [runtimeStoreCursor, runtimeMstoreMem]
    have hold : c.mem.size ≤
        ((UInt256.toByteArray stored).write 0 c.mem addr.toNat 32).size := by
      simpa [runtimeMstoreMem] using runtimeMstoreMem_size_ge c.mem addr stored hgap
    omega

theorem RuntimeWordAt.storeAboveSmall {c : RuntimeMemCursor}
    {read value addr stored : UInt256}
    (hword : RuntimeWordAt c read value) (hc : RuntimeCursorSmall c)
    (haddr : addr.toNat + 63 < 2 ^ 64)
    (hbelow : read.toNat + 32 ≤ addr.toNat) :
    RuntimeWordAt (runtimeStoreCursor c addr stored) read value := by
  apply hword.storeAbove hc.1 (by omega) hbelow
  rw [show USize.size = 2 ^ 64 from by native_decide]
  omega

/-- A later in-bounds word store strictly below an established word preserves it. -/
theorem RuntimeWordAt.storeBelow {c : RuntimeMemCursor} {read value addr stored : UInt256}
    (hword : RuntimeWordAt c read value)
    (haw : c.aw.toNat < 2 ^ 64)
    (haddr : addr.toNat + 63 < 32 * (2 ^ 64))
    (habove : addr.toNat + 32 ≤ read.toNat) :
    RuntimeWordAt (runtimeStoreCursor c addr stored) read value := by
  rcases hword with ⟨hread, hmem, hcover⟩
  have hoff : addr.toNat ≤ c.mem.size := by omega
  refine ⟨?_, ?_, runtimeMstoreAw_preserves_cover haw haddr hcover⟩
  · simpa [runtimeStoreCursor, runtimeMstoreMem] using
      (write32_read_above (UInt256.toByteArray stored) c.mem addr.toNat read.toNat
        (by rw [toByteArray_size]) hoff habove hmem).trans hread
  · have hs := toByteArray_write32_size_of_le c.mem stored addr.toNat c.mem.size
      c.mem.size rfl hoff (by omega)
    simpa [runtimeStoreCursor, runtimeMstoreMem, hs] using hmem

theorem RuntimeWordAt.storeBelowSmall {c : RuntimeMemCursor}
    {read value addr stored : UInt256}
    (hword : RuntimeWordAt c read value) (hc : RuntimeCursorSmall c)
    (haddr : addr.toNat + 63 < 2 ^ 64)
    (habove : addr.toNat + 32 ≤ read.toNat) :
    RuntimeWordAt (runtimeStoreCursor c addr stored) read value :=
  hword.storeBelow hc.1 (by omega) habove

theorem uadd_ofNat_toNat {x : UInt256} (n : Nat)
    (hn : n < UInt256.size) (hbound : x.toNat + n < UInt256.size) :
    (x + UInt256.ofNat n).toNat = x.toNat + n := by
  rw [uadd_toNat, ulit_toNat' n hn,
    show UInt256.size = 2 ^ 256 from by decide, Nat.mod_eq_of_lt]
  simpa [UInt256.size] using hbound

structure RuntimeLineState where
  a : UInt256
  b : UInt256
  c : UInt256
  d : UInt256
  e : UInt256
deriving DecidableEq, Repr

def RuntimeLineAt (cursor : RuntimeMemCursor) (base : UInt256)
    (s : RuntimeLineState) : Prop :=
  RuntimeWordAt cursor base s.a ∧
  RuntimeWordAt cursor (base + ⟨32⟩) s.b ∧
  RuntimeWordAt cursor (base + ⟨64⟩) s.c ∧
  RuntimeWordAt cursor (base + ⟨96⟩) s.d ∧
  RuntimeWordAt cursor (base + ⟨128⟩) s.e

def runtimeInitLineCursor (cursor : RuntimeMemCursor) (base : UInt256)
    (s : RuntimeLineState) : RuntimeMemCursor :=
  let cursor := runtimeStoreCursor cursor base s.a
  let cursor := runtimeStoreCursor cursor (base + ⟨32⟩) s.b
  let cursor := runtimeStoreCursor cursor (base + ⟨64⟩) s.c
  let cursor := runtimeStoreCursor cursor (base + ⟨96⟩) s.d
  runtimeStoreCursor cursor (base + ⟨128⟩) s.e

theorem runtimeInitLineCursor_small {cursor : RuntimeMemCursor} {base : UInt256}
    {s : RuntimeLineState} (hc : RuntimeCursorSmall cursor)
    (hbase : base.toNat + 191 < 2 ^ 64) :
    RuntimeCursorSmall (runtimeInitLineCursor cursor base s) := by
  have h32 : (base + ⟨32⟩).toNat = base.toNat + 32 :=
    uadd_ofNat_toNat 32 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]
      omega)
  have h64 : (base + ⟨64⟩).toNat = base.toNat + 64 :=
    uadd_ofNat_toNat 64 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]
      omega)
  have h96 : (base + ⟨96⟩).toNat = base.toNat + 96 :=
    uadd_ofNat_toNat 96 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]
      omega)
  have h128 : (base + ⟨128⟩).toNat = base.toNat + 128 :=
    uadd_ofNat_toNat 128 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]
      omega)
  simp only [runtimeInitLineCursor]
  exact ((((hc.store (by omega)).store (by rw [h32]; omega)).store
    (by rw [h64]; omega)).store (by rw [h96]; omega)).store (by rw [h128]; omega)

theorem runtimeInitLineCursor_line {cursor : RuntimeMemCursor} {base : UInt256}
    {s : RuntimeLineState} (hc : RuntimeCursorSmall cursor)
    (hbase : base.toNat + 191 < 2 ^ 64) :
    RuntimeLineAt (runtimeInitLineCursor cursor base s) base s := by
  let c1 := runtimeStoreCursor cursor base s.a
  let c2 := runtimeStoreCursor c1 (base + ⟨32⟩) s.b
  let c3 := runtimeStoreCursor c2 (base + ⟨64⟩) s.c
  let c4 := runtimeStoreCursor c3 (base + ⟨96⟩) s.d
  let c5 := runtimeStoreCursor c4 (base + ⟨128⟩) s.e
  have h32 : (base + ⟨32⟩).toNat = base.toNat + 32 :=
    uadd_ofNat_toNat 32 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]
      omega)
  have h64 : (base + ⟨64⟩).toNat = base.toNat + 64 :=
    uadd_ofNat_toNat 64 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]
      omega)
  have h96 : (base + ⟨96⟩).toNat = base.toNat + 96 :=
    uadd_ofNat_toNat 96 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]
      omega)
  have h128 : (base + ⟨128⟩).toNat = base.toNat + 128 :=
    uadd_ofNat_toNat 128 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]
      omega)
  have hs1 : RuntimeCursorSmall c1 := hc.store (by omega)
  have hs2 : RuntimeCursorSmall c2 := hs1.store (by rw [h32]; omega)
  have hs3 : RuntimeCursorSmall c3 := hs2.store (by rw [h64]; omega)
  have hs4 : RuntimeCursorSmall c4 := hs3.store (by rw [h96]; omega)
  have ha1 : RuntimeWordAt c1 base s.a := hc.storeWord (by omega)
  have ha2 : RuntimeWordAt c2 base s.a :=
    ha1.storeAboveSmall hs1 (by rw [h32]; omega) (by omega)
  have ha3 : RuntimeWordAt c3 base s.a :=
    ha2.storeAboveSmall hs2 (by rw [h64]; omega) (by rw [h64]; omega)
  have ha4 : RuntimeWordAt c4 base s.a :=
    ha3.storeAboveSmall hs3 (by rw [h96]; omega) (by rw [h96]; omega)
  have ha5 : RuntimeWordAt c5 base s.a :=
    ha4.storeAboveSmall hs4 (by rw [h128]; omega) (by rw [h128]; omega)
  have hb2 : RuntimeWordAt c2 (base + ⟨32⟩) s.b :=
    hs1.storeWord (by rw [h32]; omega)
  have hb3 : RuntimeWordAt c3 (base + ⟨32⟩) s.b :=
    hb2.storeAboveSmall hs2 (by rw [h64]; omega) (by omega)
  have hb4 : RuntimeWordAt c4 (base + ⟨32⟩) s.b :=
    hb3.storeAboveSmall hs3 (by rw [h96]; omega) (by rw [h32, h96]; omega)
  have hb5 : RuntimeWordAt c5 (base + ⟨32⟩) s.b :=
    hb4.storeAboveSmall hs4 (by rw [h128]; omega) (by rw [h32, h128]; omega)
  have hc3 : RuntimeWordAt c3 (base + ⟨64⟩) s.c :=
    hs2.storeWord (by rw [h64]; omega)
  have hc4 : RuntimeWordAt c4 (base + ⟨64⟩) s.c :=
    hc3.storeAboveSmall hs3 (by rw [h96]; omega) (by omega)
  have hc5 : RuntimeWordAt c5 (base + ⟨64⟩) s.c :=
    hc4.storeAboveSmall hs4 (by rw [h128]; omega) (by rw [h64, h128]; omega)
  have hd4 : RuntimeWordAt c4 (base + ⟨96⟩) s.d :=
    hs3.storeWord (by rw [h96]; omega)
  have hd5 : RuntimeWordAt c5 (base + ⟨96⟩) s.d :=
    hd4.storeAboveSmall hs4 (by rw [h128]; omega) (by omega)
  have he5 : RuntimeWordAt c5 (base + ⟨128⟩) s.e :=
    hs4.storeWord (by rw [h128]; omega)
  simpa [RuntimeLineAt, runtimeInitLineCursor, c1, c2, c3, c4, c5] using
    And.intro ha5 (And.intro hb5 (And.intro hc5 (And.intro hd5 he5)))

theorem RuntimeWordAt.runtimeInitLineCursor_below {cursor : RuntimeMemCursor}
    {read value base : UInt256} {s : RuntimeLineState}
    (hword : RuntimeWordAt cursor read value) (hc : RuntimeCursorSmall cursor)
    (hbase : base.toNat + 191 < 2 ^ 64)
    (hbelow : read.toNat + 32 ≤ base.toNat) :
    RuntimeWordAt (runtimeInitLineCursor cursor base s) read value := by
  let c1 := runtimeStoreCursor cursor base s.a
  let c2 := runtimeStoreCursor c1 (base + ⟨32⟩) s.b
  let c3 := runtimeStoreCursor c2 (base + ⟨64⟩) s.c
  let c4 := runtimeStoreCursor c3 (base + ⟨96⟩) s.d
  let c5 := runtimeStoreCursor c4 (base + ⟨128⟩) s.e
  have h32 : (base + ⟨32⟩).toNat = base.toNat + 32 :=
    uadd_ofNat_toNat 32 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  have h64 : (base + ⟨64⟩).toNat = base.toNat + 64 :=
    uadd_ofNat_toNat 64 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  have h96 : (base + ⟨96⟩).toNat = base.toNat + 96 :=
    uadd_ofNat_toNat 96 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  have h128 : (base + ⟨128⟩).toNat = base.toNat + 128 :=
    uadd_ofNat_toNat 128 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  have hw1 := hword.storeAboveSmall hc (stored := s.a) (by omega) hbelow
  have hs1 : RuntimeCursorSmall c1 := hc.store (by omega)
  have hw2 := hw1.storeAboveSmall hs1 (stored := s.b)
    (by rw [h32]; omega) (by rw [h32]; omega)
  have hs2 : RuntimeCursorSmall c2 := hs1.store (by rw [h32]; omega)
  have hw3 := hw2.storeAboveSmall hs2 (stored := s.c)
    (by rw [h64]; omega) (by rw [h64]; omega)
  have hs3 : RuntimeCursorSmall c3 := hs2.store (by rw [h64]; omega)
  have hw4 := hw3.storeAboveSmall hs3 (stored := s.d)
    (by rw [h96]; omega) (by rw [h96]; omega)
  have hs4 : RuntimeCursorSmall c4 := hs3.store (by rw [h96]; omega)
  have hw5 := hw4.storeAboveSmall hs4 (stored := s.e)
    (by rw [h128]; omega) (by rw [h128]; omega)
  change RuntimeWordAt c5 read value
  exact hw5

theorem runtimeInitLineCursor_cover {cursor : RuntimeMemCursor} {base : UInt256}
    {s : RuntimeLineState} (hc : RuntimeCursorSmall cursor)
    (hbase : base.toNat + 191 < 2 ^ 64) :
    base.toNat + 160 ≤ 32 * (runtimeInitLineCursor cursor base s).aw.toNat := by
  let c1 := runtimeStoreCursor cursor base s.a
  let c2 := runtimeStoreCursor c1 (base + ⟨32⟩) s.b
  let c3 := runtimeStoreCursor c2 (base + ⟨64⟩) s.c
  let c4 := runtimeStoreCursor c3 (base + ⟨96⟩) s.d
  have h32 : (base + ⟨32⟩).toNat = base.toNat + 32 :=
    uadd_ofNat_toNat 32 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  have h64 : (base + ⟨64⟩).toNat = base.toNat + 64 :=
    uadd_ofNat_toNat 64 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  have h96 : (base + ⟨96⟩).toNat = base.toNat + 96 :=
    uadd_ofNat_toNat 96 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  have h128 : (base + ⟨128⟩).toNat = base.toNat + 128 :=
    uadd_ofNat_toNat 128 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  have hs1 : RuntimeCursorSmall c1 := hc.store (by omega)
  have hs2 : RuntimeCursorSmall c2 := hs1.store (by rw [h32]; omega)
  have hs3 : RuntimeCursorSmall c3 := hs2.store (by rw [h64]; omega)
  have hs4 : RuntimeCursorSmall c4 := hs3.store (by rw [h96]; omega)
  change base.toNat + 160 ≤
    32 * (runtimeMstoreAw c4.aw (base + ⟨128⟩)).toNat
  calc
    base.toNat + 160 = (base + ⟨128⟩).toNat + 32 := by rw [h128]
    _ ≤ 32 * (runtimeMstoreAw c4.aw (base + ⟨128⟩)).toNat :=
      runtimeMstoreAw_covers_end hs4.1 (by rw [h128]; omega)

def runtimeLoadCursor (cursor : RuntimeMemCursor) (addr : UInt256) : RuntimeMemCursor :=
  { mem := cursor.mem, aw := runtimeMloadAw cursor.aw addr }

theorem runtimeMloadAw_eq_mstoreAw (aw addr : UInt256) :
    runtimeMloadAw aw addr = runtimeMstoreAw aw addr := rfl

theorem runtimeMloadAw_eq_of_covers_wide {aw addr : UInt256}
    (haw : aw.toNat < 2 ^ 64) (haddr : addr.toNat + 63 < 32 * UInt256.size)
    (hcover : addr.toNat + 32 ≤ 32 * aw.toNat) :
    runtimeMloadAw aw addr = aw := by
  apply u256_inj
  unfold runtimeMloadAw
  rw [ulit_toNat' _ (machineM_lt_uint256 aw addr.toNat 32 haddr)]
  simp only [MachineState.M, OfNat.ofNat]
  rw [max_eq_left]
  rw [Nat.div_le_iff_le_mul (by decide : 0 < 32)]
  calc
    addr.toNat + 32 + 31 ≤ 32 * aw.toNat + 31 := Nat.add_le_add_right hcover 31
    _ = aw.toNat * 32 + 32 - 1 := by omega

theorem runtimeMloadAw_eq_of_covers {aw addr : UInt256}
    (haw : aw.toNat < 2 ^ 64) (haddr : addr.toNat + 63 < 2 ^ 64)
    (hcover : addr.toNat + 32 ≤ 32 * aw.toNat) :
    runtimeMloadAw aw addr = aw := by
  apply runtimeMloadAw_eq_of_covers_wide haw _ hcover
  rw [show UInt256.size = 2 ^ 256 from by decide]
  omega

theorem RuntimeCursorSmall.load {cursor : RuntimeMemCursor} {addr : UInt256}
    (hc : RuntimeCursorSmall cursor) (haddr : addr.toNat + 63 < 2 ^ 64) :
    RuntimeCursorSmall (runtimeLoadCursor cursor addr) := by
  exact ⟨by simpa [runtimeLoadCursor, runtimeMloadAw_eq_mstoreAw] using
      runtimeMstoreAw_lt_pow64 hc.1 (by omega), by simpa [runtimeLoadCursor] using hc.2⟩

theorem RuntimeWordAt.afterLoad {cursor : RuntimeMemCursor} {read value addr : UInt256}
    (hword : RuntimeWordAt cursor read value) (hc : RuntimeCursorSmall cursor)
    (haddr : addr.toNat + 63 < 2 ^ 64) :
    RuntimeWordAt (runtimeLoadCursor cursor addr) read value := by
  rcases hword with ⟨hread, hmem, hcover⟩
  exact ⟨by simpa [runtimeLoadCursor] using hread,
    by simpa [runtimeLoadCursor] using hmem,
    by simpa [runtimeLoadCursor, runtimeMloadAw_eq_mstoreAw] using
      runtimeMstoreAw_preserves_cover hc.1 (by omega) hcover⟩

def runtimeRoundReadCursor (cursor : RuntimeMemCursor)
    (lineBase messageBase row round : UInt256) : RuntimeMemCursor :=
  let cursor := runtimeLoadCursor cursor lineBase
  let cursor := runtimeLoadCursor cursor (lineBase + ⟨32⟩)
  let cursor := runtimeLoadCursor cursor (lineBase + ⟨64⟩)
  let cursor := runtimeLoadCursor cursor (lineBase + ⟨96⟩)
  let cursor := runtimeLoadCursor cursor (lineBase + ⟨128⟩)
  runtimeLoadCursor cursor (runtimeRoundMessageAddr messageBase row round)

theorem runtimeRoundReadCursor_mem (cursor : RuntimeMemCursor)
    (lineBase messageBase row round : UInt256) :
    (runtimeRoundReadCursor cursor lineBase messageBase row round).mem = cursor.mem := rfl

theorem runtimeRoundReadCursor_aw (cursor : RuntimeMemCursor)
    (lineBase messageBase row round : UInt256) :
    (runtimeRoundReadCursor cursor lineBase messageBase row round).aw =
      runtimeRoundAwX cursor lineBase messageBase row round := rfl

theorem runtimeRoundReadCursor_small {cursor : RuntimeMemCursor}
    {lineBase messageBase row round : UInt256}
    (hc : RuntimeCursorSmall cursor) (hbase : lineBase.toNat + 191 < 2 ^ 64)
    (hmsg : (runtimeRoundMessageAddr messageBase row round).toNat + 63 < 2 ^ 64) :
    RuntimeCursorSmall (runtimeRoundReadCursor cursor lineBase messageBase row round) := by
  have h32 : (lineBase + ⟨32⟩).toNat = lineBase.toNat + 32 :=
    uadd_ofNat_toNat 32 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  have h64 : (lineBase + ⟨64⟩).toNat = lineBase.toNat + 64 :=
    uadd_ofNat_toNat 64 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  have h96 : (lineBase + ⟨96⟩).toNat = lineBase.toNat + 96 :=
    uadd_ofNat_toNat 96 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  have h128 : (lineBase + ⟨128⟩).toNat = lineBase.toNat + 128 :=
    uadd_ofNat_toNat 128 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  simp only [runtimeRoundReadCursor]
  exact (((((hc.load (by omega)).load (by rw [h32]; omega)).load
    (by rw [h64]; omega)).load (by rw [h96]; omega)).load
    (by rw [h128]; omega)).load hmsg

theorem runtimeRound_values {cursor : RuntimeMemCursor}
    {lineBase messageBase row round x : UInt256} {s : RuntimeLineState}
    (hline : RuntimeLineAt cursor lineBase s)
    (hx : RuntimeWordAt cursor (runtimeRoundMessageAddr messageBase row round) x)
    (hc : RuntimeCursorSmall cursor) (hbase : lineBase.toNat + 191 < 2 ^ 64)
    (hmsg : (runtimeRoundMessageAddr messageBase row round).toNat + 63 < 2 ^ 64)
    (hlineCover : lineBase.toNat + 160 ≤ 32 * cursor.aw.toNat)
    (hmsgCover : (runtimeRoundMessageAddr messageBase row round).toNat + 32 ≤
      32 * cursor.aw.toNat) :
    runtimeRoundA cursor lineBase = s.a ∧
    runtimeRoundB cursor lineBase = s.b ∧
    runtimeRoundC cursor lineBase = s.c ∧
    runtimeRoundD cursor lineBase = s.d ∧
    runtimeRoundE cursor lineBase = s.e ∧
    runtimeRoundX cursor lineBase messageBase row round = x := by
  rcases hline with ⟨ha, hb, hcword, hd, he⟩
  have h32 : (lineBase + ⟨32⟩).toNat = lineBase.toNat + 32 :=
    uadd_ofNat_toNat 32 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  have h64 : (lineBase + ⟨64⟩).toNat = lineBase.toNat + 64 :=
    uadd_ofNat_toNat 64 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  have h96 : (lineBase + ⟨96⟩).toNat = lineBase.toNat + 96 :=
    uadd_ofNat_toNat 96 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  have h128 : (lineBase + ⟨128⟩).toNat = lineBase.toNat + 128 :=
    uadd_ofNat_toNat 128 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  have hawA : runtimeRoundAwA cursor lineBase = cursor.aw :=
    runtimeMloadAw_eq_of_covers hc.1 (by omega) (by omega)
  have hawB : runtimeRoundAwB cursor lineBase = cursor.aw := by
    simp only [runtimeRoundAwB, hawA]
    exact runtimeMloadAw_eq_of_covers hc.1 (by rw [h32]; omega) (by rw [h32]; omega)
  have hawC : runtimeRoundAwC cursor lineBase = cursor.aw := by
    simp only [runtimeRoundAwC, hawB]
    exact runtimeMloadAw_eq_of_covers hc.1 (by rw [h64]; omega) (by rw [h64]; omega)
  have hawD : runtimeRoundAwD cursor lineBase = cursor.aw := by
    simp only [runtimeRoundAwD, hawC]
    exact runtimeMloadAw_eq_of_covers hc.1 (by rw [h96]; omega) (by rw [h96]; omega)
  have hawE : runtimeRoundAwE cursor lineBase = cursor.aw := by
    simp only [runtimeRoundAwE, hawD]
    exact runtimeMloadAw_eq_of_covers hc.1 (by rw [h128]; omega) (by rw [h128]; omega)
  have hawX : runtimeRoundAwX cursor lineBase messageBase row round = cursor.aw := by
    simp only [runtimeRoundAwX, hawE]
    exact runtimeMloadAw_eq_of_covers hc.1 hmsg hmsgCover
  refine ⟨ha.load, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [runtimeRoundB, hawA] using hb.load
  · simpa [runtimeRoundC, hawB] using hcword.load
  · simpa [runtimeRoundD, hawC] using hd.load
  · simpa [runtimeRoundE, hawD] using he.load
  · simpa [runtimeRoundX, hawE] using hx.load

def runtimePureRoundNext (s : RuntimeLineState) (x round row rotationRow boolF constant : UInt256) :
    UInt256 :=
  UInt256.land mask32Word
    (runtimeRol32
      (UInt256.land mask32Word
        (UInt256.land mask32Word boolF + s.a + x + constant))
      (runtimeRowEntry rotationRow round) + s.e)

def runtimePureRound (s : RuntimeLineState) (x round row rotationRow boolF constant : UInt256) :
    RuntimeLineState :=
  { a := s.e
    b := runtimePureRoundNext s x round row rotationRow boolF constant
    c := s.b
    d := runtimeRol32 s.c ⟨10⟩
    e := s.d }

theorem runtimeRoundNext_eq_pure {cursor : RuntimeMemCursor}
    {lineBase messageBase round row rotationRow boolF constant x : UInt256}
    {s : RuntimeLineState}
    (hline : RuntimeLineAt cursor lineBase s)
    (hx : RuntimeWordAt cursor (runtimeRoundMessageAddr messageBase row round) x)
    (hc : RuntimeCursorSmall cursor) (hbase : lineBase.toNat + 191 < 2 ^ 64)
    (hmsg : (runtimeRoundMessageAddr messageBase row round).toNat + 63 < 2 ^ 64)
    (hlineCover : lineBase.toNat + 160 ≤ 32 * cursor.aw.toNat)
    (hmsgCover : (runtimeRoundMessageAddr messageBase row round).toNat + 32 ≤
      32 * cursor.aw.toNat) :
    runtimeRoundNext cursor lineBase messageBase round row rotationRow boolF constant =
      runtimePureRoundNext s x round row rotationRow boolF constant := by
  rcases runtimeRound_values hline hx hc hbase hmsg hlineCover hmsgCover with
    ⟨ha, _, _, _, he, hxv⟩
  simp [runtimeRoundNext, runtimeRoundSum, runtimePureRoundNext, ha, he, hxv]

theorem runtimeRoundCursor_small {cursor : RuntimeMemCursor}
    {lineBase messageBase round row rotationRow boolF constant x : UInt256}
    {s : RuntimeLineState}
    (hline : RuntimeLineAt cursor lineBase s)
    (hx : RuntimeWordAt cursor (runtimeRoundMessageAddr messageBase row round) x)
    (hc : RuntimeCursorSmall cursor) (hbase : lineBase.toNat + 191 < 2 ^ 64)
    (hmsg : (runtimeRoundMessageAddr messageBase row round).toNat + 63 < 2 ^ 64)
    (hlineCover : lineBase.toNat + 160 ≤ 32 * cursor.aw.toNat)
    (hmsgCover : (runtimeRoundMessageAddr messageBase row round).toNat + 32 ≤
      32 * cursor.aw.toNat) :
    RuntimeCursorSmall
      (runtimeRoundCursor cursor lineBase messageBase round row rotationRow boolF constant) := by
  have hreads := runtimeRoundReadCursor_small hc hbase hmsg
  have h32 : (lineBase + ⟨32⟩).toNat = lineBase.toNat + 32 :=
    uadd_ofNat_toNat 32 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  have h64 : (lineBase + ⟨64⟩).toNat = lineBase.toNat + 64 :=
    uadd_ofNat_toNat 64 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  have h96 : (lineBase + ⟨96⟩).toNat = lineBase.toNat + 96 :=
    uadd_ofNat_toNat 96 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  have h128 : (lineBase + ⟨128⟩).toNat = lineBase.toNat + 128 :=
    uadd_ofNat_toNat 128 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  let c0 : RuntimeMemCursor :=
    { mem := cursor.mem, aw := runtimeRoundAwX cursor lineBase messageBase row round }
  let c1 := runtimeStoreCursor c0 lineBase (runtimeRoundE cursor lineBase)
  let c2 := runtimeStoreCursor c1 (lineBase + ⟨128⟩) (runtimeRoundD cursor lineBase)
  let c3 := runtimeStoreCursor c2 (lineBase + ⟨96⟩)
    (runtimeRol32 (runtimeRoundC cursor lineBase) ⟨10⟩)
  let c4 := runtimeStoreCursor c3 (lineBase + ⟨64⟩) (runtimeRoundB cursor lineBase)
  let c5 := runtimeStoreCursor c4 (lineBase + ⟨32⟩)
    (runtimeRoundNext cursor lineBase messageBase round row rotationRow boolF constant)
  have hc0 : RuntimeCursorSmall c0 := by
    simpa [c0, runtimeRoundReadCursor_mem, runtimeRoundReadCursor_aw] using hreads
  have hs1 : RuntimeCursorSmall c1 := hc0.store (by omega)
  have hs2 : RuntimeCursorSmall c2 := hs1.store (by rw [h128]; omega)
  have hs3 : RuntimeCursorSmall c3 := hs2.store
    (by rw [h96]; omega)
  have hs4 : RuntimeCursorSmall c4 := hs3.store (by rw [h64]; omega)
  have hs5 : RuntimeCursorSmall c5 := hs4.store (by rw [h32]; omega)
  change RuntimeCursorSmall c5
  exact hs5

theorem runtimeRoundCursor_line {cursor : RuntimeMemCursor}
    {lineBase messageBase round row rotationRow boolF constant x : UInt256}
    {s : RuntimeLineState}
    (hline : RuntimeLineAt cursor lineBase s)
    (hx : RuntimeWordAt cursor (runtimeRoundMessageAddr messageBase row round) x)
    (hc : RuntimeCursorSmall cursor) (hbase : lineBase.toNat + 191 < 2 ^ 64)
    (hmsg : (runtimeRoundMessageAddr messageBase row round).toNat + 63 < 2 ^ 64)
    (hlineCover : lineBase.toNat + 160 ≤ 32 * cursor.aw.toNat)
    (hmsgCover : (runtimeRoundMessageAddr messageBase row round).toNat + 32 ≤
      32 * cursor.aw.toNat) :
    RuntimeLineAt
      (runtimeRoundCursor cursor lineBase messageBase round row rotationRow boolF constant)
      lineBase (runtimePureRound s x round row rotationRow boolF constant) := by
  rcases runtimeRound_values hline hx hc hbase hmsg hlineCover hmsgCover with
    ⟨ha, hb, hcv, hd, he, hxv⟩
  have hnext := runtimeRoundNext_eq_pure
    (rotationRow := rotationRow) (boolF := boolF) (constant := constant)
    hline hx hc hbase hmsg hlineCover hmsgCover
  have hreads := runtimeRoundReadCursor_small hc hbase hmsg
  have h32 : (lineBase + ⟨32⟩).toNat = lineBase.toNat + 32 :=
    uadd_ofNat_toNat 32 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  have h64 : (lineBase + ⟨64⟩).toNat = lineBase.toNat + 64 :=
    uadd_ofNat_toNat 64 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  have h96 : (lineBase + ⟨96⟩).toNat = lineBase.toNat + 96 :=
    uadd_ofNat_toNat 96 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  have h128 : (lineBase + ⟨128⟩).toNat = lineBase.toNat + 128 :=
    uadd_ofNat_toNat 128 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  let c0 : RuntimeMemCursor :=
    { mem := cursor.mem, aw := runtimeRoundAwX cursor lineBase messageBase row round }
  let c1 := runtimeStoreCursor c0 lineBase s.e
  let c2 := runtimeStoreCursor c1 (lineBase + ⟨128⟩) s.d
  let c3 := runtimeStoreCursor c2 (lineBase + ⟨96⟩) (runtimeRol32 s.c ⟨10⟩)
  let c4 := runtimeStoreCursor c3 (lineBase + ⟨64⟩) s.b
  let c5 := runtimeStoreCursor c4 (lineBase + ⟨32⟩)
    (runtimePureRoundNext s x round row rotationRow boolF constant)
  have hc0 : RuntimeCursorSmall c0 := by
    simpa [c0, runtimeRoundReadCursor_mem, runtimeRoundReadCursor_aw] using hreads
  have hs1 : RuntimeCursorSmall c1 := hc0.store (by omega)
  have hs2 : RuntimeCursorSmall c2 := hs1.store (by rw [h128]; omega)
  have hs3 : RuntimeCursorSmall c3 := hs2.store (by rw [h96]; omega)
  have hs4 : RuntimeCursorSmall c4 := hs3.store (by rw [h64]; omega)
  have ha1 : RuntimeWordAt c1 lineBase s.e := hc0.storeWord (by omega)
  have ha2 := ha1.storeAboveSmall hs1 (stored := s.d)
    (by rw [h128]; omega) (by omega)
  have ha3 := ha2.storeAboveSmall hs2 (stored := runtimeRol32 s.c ⟨10⟩)
    (by rw [h96]; omega) (by omega)
  have ha4 := ha3.storeAboveSmall hs3 (stored := s.b)
    (by rw [h64]; omega) (by omega)
  have ha5 := ha4.storeAboveSmall hs4
    (stored := runtimePureRoundNext s x round row rotationRow boolF constant)
    (by rw [h32]; omega) (by omega)
  have he2 : RuntimeWordAt c2 (lineBase + ⟨128⟩) s.d :=
    hs1.storeWord (by rw [h128]; omega)
  have he3 := he2.storeBelowSmall hs2 (stored := runtimeRol32 s.c ⟨10⟩)
    (by rw [h96]; omega) (by omega)
  have he4 := he3.storeBelowSmall hs3 (stored := s.b)
    (by rw [h64]; omega) (by omega)
  have he5 := he4.storeBelowSmall hs4
    (stored := runtimePureRoundNext s x round row rotationRow boolF constant)
    (by rw [h32]; omega) (by omega)
  have hd3 : RuntimeWordAt c3 (lineBase + ⟨96⟩) (runtimeRol32 s.c ⟨10⟩) :=
    hs2.storeWord (by rw [h96]; omega)
  have hd4 := hd3.storeBelowSmall hs3 (stored := s.b)
    (by rw [h64]; omega) (by omega)
  have hd5 := hd4.storeBelowSmall hs4
    (stored := runtimePureRoundNext s x round row rotationRow boolF constant)
    (by rw [h32]; omega) (by omega)
  have hc4 : RuntimeWordAt c4 (lineBase + ⟨64⟩) s.b :=
    hs3.storeWord (by rw [h64]; omega)
  have hc5 := hc4.storeBelowSmall hs4
    (stored := runtimePureRoundNext s x round row rotationRow boolF constant)
    (by rw [h32]; omega) (by omega)
  have hb5 : RuntimeWordAt c5 (lineBase + ⟨32⟩)
      (runtimePureRoundNext s x round row rotationRow boolF constant) :=
    hs4.storeWord (by rw [h32]; omega)
  have hout :
      runtimeRoundCursor cursor lineBase messageBase round row rotationRow boolF constant = c5 := by
    simp [runtimeRoundCursor, c0, c1, c2, c3, c4, c5, ha, hb, hcv, hd, he, hxv, hnext]
  rw [hout]
  exact ⟨ha5, hb5, hc5, hd5, he5⟩

theorem runtimeRowEntry_lt_sixteen (row round : UInt256) :
    (runtimeRowEntry row round).toNat < 16 := by
  unfold runtimeRowEntry
  rw [uland_toNat]
  have hle := nat_land_le_right
    (UInt256.shiftRight row (⟨60⟩ - UInt256.shiftLeft (UInt256.land round ⟨15⟩) ⟨2⟩)).toNat
    15
  exact lt_of_le_of_lt hle (by omega)

theorem ushl5_toNat_of_lt16 {x : UInt256} (hx : x.toNat < 16) :
    (UInt256.shiftLeft x ⟨5⟩).toNat = 32 * x.toNat := by
  calc
    (UInt256.shiftLeft x ⟨5⟩).toNat =
        (UInt256.shiftLeft (UInt256.ofNat x.toNat) ⟨5⟩).toNat := by
          rw [u256_ofNat_toNat]
    _ = 32 * x.toNat := ushl5_ofNat_toNat x.toNat (by omega)

def runtimeMessageAddress (messageBase : UInt256) (i : Fin 16) : UInt256 :=
  messageBase + UInt256.ofNat (32 * i.val)

def RuntimeMessageAt (cursor : RuntimeMemCursor) (messageBase : UInt256)
    (X : Fin 16 → UInt256) : Prop :=
  ∀ i, RuntimeWordAt cursor (runtimeMessageAddress messageBase i) (X i)

theorem runtimeRoundMessageAddr_eq {messageBase row round : UInt256}
    (hbase : messageBase.toNat + 512 < UInt256.size) :
    runtimeRoundMessageAddr messageBase row round =
      runtimeMessageAddress messageBase
        ⟨(runtimeRowEntry row round).toNat, runtimeRowEntry_lt_sixteen row round⟩ := by
  apply u256_inj
  unfold runtimeRoundMessageAddr runtimeMessageAddress
  have hentry := runtimeRowEntry_lt_sixteen row round
  have hshift : 32 * (runtimeRowEntry row round).toNat < UInt256.size := by
    rw [show UInt256.size = 2 ^ 256 from by decide]
    omega
  have hsum : messageBase.toNat + 32 * (runtimeRowEntry row round).toNat <
      UInt256.size := by
    omega
  rw [uadd_toNat, uadd_toNat, ushl5_toNat_of_lt16 (runtimeRowEntry_lt_sixteen row round)]
  rw [ulit_toNat' _ hshift, Nat.mod_eq_of_lt hsum]

theorem RuntimeMessageAt.selected {cursor : RuntimeMemCursor} {messageBase : UInt256}
    {X : Fin 16 → UInt256} {row round : UInt256}
    (hX : RuntimeMessageAt cursor messageBase X)
    (hbase : messageBase.toNat + 512 < UInt256.size) :
    RuntimeWordAt cursor (runtimeRoundMessageAddr messageBase row round)
      (X ⟨(runtimeRowEntry row round).toNat, runtimeRowEntry_lt_sixteen row round⟩) := by
  rw [runtimeRoundMessageAddr_eq hbase]
  exact hX _

theorem runtimeMessageAddress_toNat {messageBase : UInt256} (i : Fin 16)
    (hbase : messageBase.toNat + 512 < UInt256.size) :
    (runtimeMessageAddress messageBase i).toNat = messageBase.toNat + 32 * i.val := by
  unfold runtimeMessageAddress
  rw [uadd_toNat, ulit_toNat' (32 * i.val) (by
    rw [show UInt256.size = 2 ^ 256 from by decide]
    omega), Nat.mod_eq_of_lt]
  omega

theorem runtimeRoundMessageAddr_toNat {messageBase row round : UInt256}
    (hbase : messageBase.toNat + 512 < UInt256.size) :
    (runtimeRoundMessageAddr messageBase row round).toNat =
      messageBase.toNat + 32 * (runtimeRowEntry row round).toNat := by
  rw [runtimeRoundMessageAddr_eq hbase, runtimeMessageAddress_toNat _ hbase]

theorem runtimeRoundPreludeCursor_eq {cursor : RuntimeMemCursor} {messageBase : UInt256}
    (hc : RuntimeCursorSmall cursor)
    (hbase : messageBase.toNat + 672 < 2 ^ 64)
    (hcover : messageBase.toNat + 640 ≤ 32 * cursor.aw.toNat) :
    runtimeRoundPreludeCursor cursor messageBase = cursor := by
  have h544 : (messageBase + ⟨544⟩).toNat = messageBase.toNat + 544 :=
    uadd_ofNat_toNat 544 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  have h576 : (messageBase + ⟨576⟩).toNat = messageBase.toNat + 576 :=
    uadd_ofNat_toNat 576 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  have h608 : (messageBase + ⟨608⟩).toNat = messageBase.toNat + 608 :=
    uadd_ofNat_toNat 608 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  have hB := runtimeMloadAw_eq_of_covers hc.1 (addr := messageBase + ⟨544⟩)
    (by rw [h544]; omega) (by rw [h544]; omega)
  have hC := runtimeMloadAw_eq_of_covers hc.1 (addr := messageBase + ⟨576⟩)
    (by rw [h576]; omega) (by rw [h576]; omega)
  have hD := runtimeMloadAw_eq_of_covers hc.1 (addr := messageBase + ⟨608⟩)
    (by rw [h608]; omega) (by rw [h608]; omega)
  cases cursor
  simp [runtimeRoundPreludeCursor, hB, hC, hD]

theorem runtimeRightPreludeCursor_eq {cursor : RuntimeMemCursor} {messageBase : UInt256}
    (hc : RuntimeCursorSmall cursor)
    (hbase : messageBase.toNat + 832 < 2 ^ 64)
    (hcover : messageBase.toNat + 800 ≤ 32 * cursor.aw.toNat) :
    runtimeRightPreludeCursor cursor messageBase = cursor := by
  have h704 : (messageBase + ⟨704⟩).toNat = messageBase.toNat + 704 :=
    uadd_ofNat_toNat 704 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  have h736 : (messageBase + ⟨736⟩).toNat = messageBase.toNat + 736 :=
    uadd_ofNat_toNat 736 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  have h768 : (messageBase + ⟨768⟩).toNat = messageBase.toNat + 768 :=
    uadd_ofNat_toNat 768 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  have hB := runtimeMloadAw_eq_of_covers hc.1 (addr := messageBase + ⟨704⟩)
    (by rw [h704]; omega) (by rw [h704]; omega)
  have hC := runtimeMloadAw_eq_of_covers hc.1 (addr := messageBase + ⟨736⟩)
    (by rw [h736]; omega) (by rw [h736]; omega)
  have hD := runtimeMloadAw_eq_of_covers hc.1 (addr := messageBase + ⟨768⟩)
    (by rw [h768]; omega) (by rw [h768]; omega)
  cases cursor
  simp [runtimeRightPreludeCursor, hB, hC, hD]

def runtimePureLeftRound (X : Fin 16 → UInt256) (group round : Nat)
    (s : RuntimeLineState) : RuntimeLineState :=
  runtimePureRound s
    (X ⟨(runtimeRowEntry (leftWordRowWord group) (UInt256.ofNat round)).toNat,
      runtimeRowEntry_lt_sixteen _ _⟩)
    (UInt256.ofNat round) (leftWordRowWord group) (leftRotationRowWord group)
    (runtimeLeftF group s.b s.c s.d) (leftConstantWord group)

def runtimePureRightRound (X : Fin 16 → UInt256) (group round : Nat)
    (s : RuntimeLineState) : RuntimeLineState :=
  runtimePureRound s
    (X ⟨(runtimeRowEntry (rightWordRowWord group) (UInt256.ofNat round)).toNat,
      runtimeRowEntry_lt_sixteen _ _⟩)
    (UInt256.ofNat round) (rightWordRowWord group) (rightRotationRowWord group)
    (runtimeRightF group s.b s.c s.d) (rightConstantWord group)

theorem runtimeLeftRoundCursor_line {cursor : RuntimeMemCursor} {messageBase : UInt256}
    {X : Fin 16 → UInt256} {s : RuntimeLineState} {group round : Nat}
    (hX : RuntimeMessageAt cursor messageBase X)
    (hline : RuntimeLineAt cursor (messageBase + ⟨512⟩) s)
    (hc : RuntimeCursorSmall cursor)
    (hbase : messageBase.toNat + 863 < 2 ^ 64)
    (hcover : messageBase.toNat + 672 ≤ 32 * cursor.aw.toNat) :
    RuntimeLineAt (runtimeLeftRoundCursor cursor messageBase group round)
      (messageBase + ⟨512⟩) (runtimePureLeftRound X group round s) := by
  have h512 : (messageBase + ⟨512⟩).toNat = messageBase.toNat + 512 :=
    uadd_ofNat_toNat 512 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  have hpre := runtimeRoundPreludeCursor_eq (messageBase := messageBase) hc
    (by omega) (by omega)
  have h544 : (messageBase + ⟨544⟩).toNat = messageBase.toNat + 544 :=
    uadd_ofNat_toNat 544 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  have h576 : (messageBase + ⟨576⟩).toNat = messageBase.toNat + 576 :=
    uadd_ofNat_toNat 576 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  have h608 : (messageBase + ⟨608⟩).toNat = messageBase.toNat + 608 :=
    uadd_ofNat_toNat 608 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  have hadd544 : messageBase + ⟨512⟩ + ⟨32⟩ = messageBase + ⟨544⟩ := by
    rw [u256_add_assoc]
    rw [show (⟨512⟩ : UInt256) + ⟨32⟩ = ⟨544⟩ by native_decide]
  have hadd576 : messageBase + ⟨512⟩ + ⟨64⟩ = messageBase + ⟨576⟩ := by
    rw [u256_add_assoc]
    rw [show (⟨512⟩ : UInt256) + ⟨64⟩ = ⟨576⟩ by native_decide]
  have hadd608 : messageBase + ⟨512⟩ + ⟨96⟩ = messageBase + ⟨608⟩ := by
    rw [u256_add_assoc]
    rw [show (⟨512⟩ : UInt256) + ⟨96⟩ = ⟨608⟩ by native_decide]
  have haw544 := runtimeMloadAw_eq_of_covers hc.1
    (addr := messageBase + ⟨544⟩) (by rw [h544]; omega) (by rw [h544]; omega)
  have haw576 := runtimeMloadAw_eq_of_covers hc.1
    (addr := messageBase + ⟨576⟩) (by rw [h576]; omega) (by rw [h576]; omega)
  have hB : runtimePreludeB cursor messageBase = s.b := by
    rw [runtimePreludeB, ← hadd544]
    exact hline.2.1.load
  have hC : runtimePreludeC cursor messageBase = s.c := by
    rw [runtimePreludeC, haw544, ← hadd576]
    exact hline.2.2.1.load
  have hD : runtimePreludeD cursor messageBase = s.d := by
    rw [runtimePreludeD, haw544, haw576, ← hadd608]
    exact hline.2.2.2.1.load
  have huint : messageBase.toNat + 512 < UInt256.size := by
    rw [show UInt256.size = 2 ^ 256 from by decide]
    omega
  have hx := hX.selected (row := leftWordRowWord group)
    (round := UInt256.ofNat round) huint
  have hmsg : (runtimeRoundMessageAddr messageBase (leftWordRowWord group)
      (UInt256.ofNat round)).toNat + 63 < 2 ^ 64 := by
    rw [runtimeRoundMessageAddr_toNat huint]
    have := runtimeRowEntry_lt_sixteen (leftWordRowWord group) (UInt256.ofNat round)
    omega
  have hresult := runtimeRoundCursor_line
    (rotationRow := leftRotationRowWord group)
    (boolF := runtimeLeftF group s.b s.c s.d)
    (constant := leftConstantWord group) hline hx hc (by rw [h512]; omega) hmsg
    (by rw [h512]; omega)
    (by rw [runtimeRoundMessageAddr_toNat huint];
        have := runtimeRowEntry_lt_sixteen (leftWordRowWord group) (UInt256.ofNat round); omega)
  unfold runtimeLeftRoundCursor
  rw [hpre, hB, hC, hD]
  exact hresult

theorem runtimeRoundAwX_eq {cursor : RuntimeMemCursor}
    {lineBase messageBase row round : UInt256}
    (hc : RuntimeCursorSmall cursor)
    (hlineBase : lineBase.toNat + 191 < 2 ^ 64)
    (hmsg : (runtimeRoundMessageAddr messageBase row round).toNat + 63 < 2 ^ 64)
    (hlineCover : lineBase.toNat + 160 ≤ 32 * cursor.aw.toNat)
    (hmsgCover : (runtimeRoundMessageAddr messageBase row round).toNat + 32 ≤
      32 * cursor.aw.toNat) :
    runtimeRoundAwX cursor lineBase messageBase row round = cursor.aw := by
  have h32 : (lineBase + ⟨32⟩).toNat = lineBase.toNat + 32 :=
    uadd_ofNat_toNat 32 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  have h64 : (lineBase + ⟨64⟩).toNat = lineBase.toNat + 64 :=
    uadd_ofNat_toNat 64 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  have h96 : (lineBase + ⟨96⟩).toNat = lineBase.toNat + 96 :=
    uadd_ofNat_toNat 96 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  have h128 : (lineBase + ⟨128⟩).toNat = lineBase.toNat + 128 :=
    uadd_ofNat_toNat 128 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  have hA := runtimeMloadAw_eq_of_covers hc.1 (addr := lineBase)
    (by omega) (by omega)
  have hB := runtimeMloadAw_eq_of_covers hc.1 (addr := lineBase + ⟨32⟩)
    (by rw [h32]; omega) (by rw [h32]; omega)
  have hC := runtimeMloadAw_eq_of_covers hc.1 (addr := lineBase + ⟨64⟩)
    (by rw [h64]; omega) (by rw [h64]; omega)
  have hD := runtimeMloadAw_eq_of_covers hc.1 (addr := lineBase + ⟨96⟩)
    (by rw [h96]; omega) (by rw [h96]; omega)
  have hE := runtimeMloadAw_eq_of_covers hc.1 (addr := lineBase + ⟨128⟩)
    (by rw [h128]; omega) (by rw [h128]; omega)
  have hX := runtimeMloadAw_eq_of_covers hc.1
    (addr := runtimeRoundMessageAddr messageBase row round) hmsg hmsgCover
  simp [runtimeRoundAwX, runtimeRoundAwE, runtimeRoundAwD, runtimeRoundAwC,
    runtimeRoundAwB, runtimeRoundAwA, hA, hB, hC, hD, hE, hX]

theorem runtimeRoundCursor_aw_eq {cursor : RuntimeMemCursor}
    {lineBase messageBase row round rotationRow boolF constant : UInt256}
    (hc : RuntimeCursorSmall cursor)
    (hlineBase : lineBase.toNat + 191 < 2 ^ 64)
    (hmsg : (runtimeRoundMessageAddr messageBase row round).toNat + 63 < 2 ^ 64)
    (hlineCover : lineBase.toNat + 160 ≤ 32 * cursor.aw.toNat)
    (hmsgCover : (runtimeRoundMessageAddr messageBase row round).toNat + 32 ≤
      32 * cursor.aw.toNat) :
    (runtimeRoundCursor cursor lineBase messageBase round row rotationRow boolF constant).aw =
      cursor.aw := by
  have hawX := runtimeRoundAwX_eq hc hlineBase hmsg hlineCover hmsgCover
  have h32 : (lineBase + ⟨32⟩).toNat = lineBase.toNat + 32 :=
    uadd_ofNat_toNat 32 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  have h64 : (lineBase + ⟨64⟩).toNat = lineBase.toNat + 64 :=
    uadd_ofNat_toNat 64 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  have h96 : (lineBase + ⟨96⟩).toNat = lineBase.toNat + 96 :=
    uadd_ofNat_toNat 96 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  have h128 : (lineBase + ⟨128⟩).toNat = lineBase.toNat + 128 :=
    uadd_ofNat_toNat 128 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  have hs0 := runtimeMloadAw_eq_of_covers hc.1 (addr := lineBase)
    (by omega) (by omega)
  have hs128 := runtimeMloadAw_eq_of_covers hc.1 (addr := lineBase + ⟨128⟩)
    (by rw [h128]; omega) (by rw [h128]; omega)
  have hs96 := runtimeMloadAw_eq_of_covers hc.1 (addr := lineBase + ⟨96⟩)
    (by rw [h96]; omega) (by rw [h96]; omega)
  have hs64 := runtimeMloadAw_eq_of_covers hc.1 (addr := lineBase + ⟨64⟩)
    (by rw [h64]; omega) (by rw [h64]; omega)
  have hs32 := runtimeMloadAw_eq_of_covers hc.1 (addr := lineBase + ⟨32⟩)
    (by rw [h32]; omega) (by rw [h32]; omega)
  have hs0' : runtimeMstoreAw cursor.aw lineBase = cursor.aw := by
    simpa only [runtimeMloadAw_eq_mstoreAw] using hs0
  have hs128' : runtimeMstoreAw cursor.aw (lineBase + ⟨128⟩) = cursor.aw := by
    simpa only [runtimeMloadAw_eq_mstoreAw] using hs128
  have hs96' : runtimeMstoreAw cursor.aw (lineBase + ⟨96⟩) = cursor.aw := by
    simpa only [runtimeMloadAw_eq_mstoreAw] using hs96
  have hs64' : runtimeMstoreAw cursor.aw (lineBase + ⟨64⟩) = cursor.aw := by
    simpa only [runtimeMloadAw_eq_mstoreAw] using hs64
  have hs32' : runtimeMstoreAw cursor.aw (lineBase + ⟨32⟩) = cursor.aw := by
    simpa only [runtimeMloadAw_eq_mstoreAw] using hs32
  simp [runtimeRoundCursor, runtimeStoreCursor, hawX, hs0', hs128', hs96', hs64', hs32']

theorem RuntimeWordAt.runtimeRoundCursor_below {cursor : RuntimeMemCursor}
    {read value lineBase messageBase row round rotationRow boolF constant : UInt256}
    (hword : RuntimeWordAt cursor read value)
    (hc : RuntimeCursorSmall cursor)
    (hlineBase : lineBase.toNat + 191 < 2 ^ 64)
    (hmsg : (runtimeRoundMessageAddr messageBase row round).toNat + 63 < 2 ^ 64)
    (hlineCover : lineBase.toNat + 160 ≤ 32 * cursor.aw.toNat)
    (hmsgCover : (runtimeRoundMessageAddr messageBase row round).toNat + 32 ≤
      32 * cursor.aw.toNat)
    (hbelow : read.toNat + 32 ≤ lineBase.toNat) :
    RuntimeWordAt
      (runtimeRoundCursor cursor lineBase messageBase round row rotationRow boolF constant)
      read value := by
  have hawX := runtimeRoundAwX_eq hc hlineBase hmsg hlineCover hmsgCover
  let c0 : RuntimeMemCursor :=
    { mem := cursor.mem, aw := runtimeRoundAwX cursor lineBase messageBase row round }
  let c1 := runtimeStoreCursor c0 lineBase (runtimeRoundE cursor lineBase)
  let c2 := runtimeStoreCursor c1 (lineBase + ⟨128⟩) (runtimeRoundD cursor lineBase)
  let c3 := runtimeStoreCursor c2 (lineBase + ⟨96⟩)
    (runtimeRol32 (runtimeRoundC cursor lineBase) ⟨10⟩)
  let c4 := runtimeStoreCursor c3 (lineBase + ⟨64⟩) (runtimeRoundB cursor lineBase)
  let c5 := runtimeStoreCursor c4 (lineBase + ⟨32⟩)
    (runtimeRoundNext cursor lineBase messageBase round row rotationRow boolF constant)
  have hc0 : c0 = cursor := by cases cursor; simp [c0, hawX]
  have hs0 : RuntimeCursorSmall c0 := by rw [hc0]; exact hc
  have h32 : (lineBase + ⟨32⟩).toNat = lineBase.toNat + 32 :=
    uadd_ofNat_toNat 32 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  have h64 : (lineBase + ⟨64⟩).toNat = lineBase.toNat + 64 :=
    uadd_ofNat_toNat 64 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  have h96 : (lineBase + ⟨96⟩).toNat = lineBase.toNat + 96 :=
    uadd_ofNat_toNat 96 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  have h128 : (lineBase + ⟨128⟩).toNat = lineBase.toNat + 128 :=
    uadd_ofNat_toNat 128 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  have hw0 : RuntimeWordAt c0 read value := by rw [hc0]; exact hword
  have hw1 := hw0.storeAboveSmall hs0 (stored := runtimeRoundE cursor lineBase)
    (by omega) hbelow
  have hs1 : RuntimeCursorSmall c1 := hs0.store (by omega)
  have hw2 := hw1.storeAboveSmall hs1 (stored := runtimeRoundD cursor lineBase)
    (by rw [h128]; omega)
    (by rw [h128]; omega)
  have hs2 : RuntimeCursorSmall c2 := hs1.store (by rw [h128]; omega)
  have hw3 := hw2.storeAboveSmall hs2
    (stored := runtimeRol32 (runtimeRoundC cursor lineBase) ⟨10⟩)
    (by rw [h96]; omega)
    (by rw [h96]; omega)
  have hs3 : RuntimeCursorSmall c3 := hs2.store (by rw [h96]; omega)
  have hw4 := hw3.storeAboveSmall hs3 (stored := runtimeRoundB cursor lineBase)
    (by rw [h64]; omega)
    (by rw [h64]; omega)
  have hs4 : RuntimeCursorSmall c4 := hs3.store (by rw [h64]; omega)
  have hw5 := hw4.storeAboveSmall hs4
    (stored := runtimeRoundNext cursor lineBase messageBase round row rotationRow boolF constant)
    (by rw [h32]; omega)
    (by rw [h32]; omega)
  change RuntimeWordAt c5 read value
  exact hw5

structure RuntimeLeftInvariant (cursor : RuntimeMemCursor) (messageBase : UInt256)
    (X : Fin 16 → UInt256) (s : RuntimeLineState) : Prop where
  small : RuntimeCursorSmall cursor
  message : RuntimeMessageAt cursor messageBase X
  line : RuntimeLineAt cursor (messageBase + ⟨512⟩) s
  cover : messageBase.toNat + 672 ≤ 32 * cursor.aw.toNat

theorem RuntimeLeftInvariant.round {cursor : RuntimeMemCursor} {messageBase : UInt256}
    {X : Fin 16 → UInt256} {s : RuntimeLineState} {group round : Nat}
    (hinv : RuntimeLeftInvariant cursor messageBase X s)
    (hbase : messageBase.toNat + 863 < 2 ^ 64) :
    RuntimeLeftInvariant (runtimeLeftRoundCursor cursor messageBase group round)
      messageBase X (runtimePureLeftRound X group round s) := by
  rcases hinv with ⟨hc, hX, hline, hcover⟩
  have hpre := runtimeRoundPreludeCursor_eq (messageBase := messageBase) hc
    (by omega) (by omega)
  have h512 : (messageBase + ⟨512⟩).toNat = messageBase.toNat + 512 :=
    uadd_ofNat_toNat 512 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  have huint : messageBase.toNat + 512 < UInt256.size := by
    rw [show UInt256.size = 2 ^ 256 from by decide]
    omega
  let row := leftWordRowWord group
  let r := UInt256.ofNat round
  have hx := hX.selected (row := row) (round := r) huint
  have hmsg : (runtimeRoundMessageAddr messageBase row r).toNat + 63 < 2 ^ 64 := by
    rw [runtimeRoundMessageAddr_toNat huint]
    have := runtimeRowEntry_lt_sixteen row r
    omega
  have hmsgCover : (runtimeRoundMessageAddr messageBase row r).toNat + 32 ≤
      32 * cursor.aw.toNat := by
    rw [runtimeRoundMessageAddr_toNat huint]
    have := runtimeRowEntry_lt_sixteen row r
    omega
  have hlineCover : (messageBase + ⟨512⟩).toNat + 160 ≤
      32 * cursor.aw.toNat := by rw [h512]; omega
  have hsmall : RuntimeCursorSmall
      (runtimeLeftRoundCursor cursor messageBase group round) := by
    unfold runtimeLeftRoundCursor
    rw [hpre]
    exact runtimeRoundCursor_small hline hx hc (by rw [h512]; omega) hmsg
      hlineCover hmsgCover
  have haw : (runtimeLeftRoundCursor cursor messageBase group round).aw = cursor.aw := by
    unfold runtimeLeftRoundCursor
    rw [hpre]
    exact runtimeRoundCursor_aw_eq hc (by rw [h512]; omega) hmsg
      hlineCover hmsgCover
  refine ⟨hsmall, ?_, runtimeLeftRoundCursor_line hX hline hc hbase hcover, ?_⟩
  · intro i
    unfold runtimeLeftRoundCursor
    rw [hpre]
    apply (hX i).runtimeRoundCursor_below hc (by rw [h512]; omega) hmsg
      hlineCover hmsgCover
    rw [runtimeMessageAddress_toNat i huint, h512]
    omega
  · rw [haw]
    exact hcover

def runtimePureLeftGroup (X : Fin 16 → UInt256) (group : Nat) :
    Nat → RuntimeLineState → RuntimeLineState
  | 0, s => s
  | round + 1, s => runtimePureLeftRound X group round
      (runtimePureLeftGroup X group round s)

def runtimePureLeftLine (X : Fin 16 → UInt256) :
    Nat → RuntimeLineState → RuntimeLineState
  | 0, s => s
  | group + 1, s => runtimePureLeftGroup X group 16
      (runtimePureLeftLine X group s)

theorem runtimeLeftGroupCursor_invariant {initial : RuntimeMemCursor}
    {messageBase : UInt256} {X : Fin 16 → UInt256} {s : RuntimeLineState}
    {group rounds : Nat}
    (hinv : RuntimeLeftInvariant initial messageBase X s)
    (hbase : messageBase.toNat + 863 < 2 ^ 64) :
    RuntimeLeftInvariant (runtimeLeftGroupCursor initial messageBase group rounds)
      messageBase X (runtimePureLeftGroup X group rounds s) := by
  induction rounds with
  | zero => simpa [runtimeLeftGroupCursor, runtimePureLeftGroup] using hinv
  | succ round ih =>
      simpa [runtimeLeftGroupCursor, runtimePureLeftGroup] using ih.round hbase

theorem runtimeLeftLineCursor_invariant {initial : RuntimeMemCursor}
    {messageBase : UInt256} {X : Fin 16 → UInt256} {s : RuntimeLineState}
    {groups : Nat}
    (hinv : RuntimeLeftInvariant initial messageBase X s)
    (hbase : messageBase.toNat + 863 < 2 ^ 64) :
    RuntimeLeftInvariant (runtimeLeftLineCursor initial messageBase groups)
      messageBase X (runtimePureLeftLine X groups s) := by
  induction groups with
  | zero => simpa [runtimeLeftLineCursor, runtimePureLeftLine] using hinv
  | succ group ih =>
      have hg := runtimeLeftGroupCursor_invariant (group := group) (rounds := 16)
        ih hbase
      simpa [runtimeLeftLineCursor, runtimePureLeftLine] using hg

theorem runtimeRightRoundCursor_line {cursor : RuntimeMemCursor} {messageBase : UInt256}
    {X : Fin 16 → UInt256} {s : RuntimeLineState} {group round : Nat}
    (hX : RuntimeMessageAt cursor messageBase X)
    (hline : RuntimeLineAt cursor (messageBase + ⟨672⟩) s)
    (hc : RuntimeCursorSmall cursor)
    (hbase : messageBase.toNat + 863 < 2 ^ 64)
    (hcover : messageBase.toNat + 832 ≤ 32 * cursor.aw.toNat) :
    RuntimeLineAt (runtimeRightRoundCursor cursor messageBase group round)
      (messageBase + ⟨672⟩) (runtimePureRightRound X group round s) := by
  have h672 : (messageBase + ⟨672⟩).toNat = messageBase.toNat + 672 :=
    uadd_ofNat_toNat 672 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  have hpre := runtimeRightPreludeCursor_eq (messageBase := messageBase) hc
    (by omega) (by omega)
  have h704 : (messageBase + ⟨704⟩).toNat = messageBase.toNat + 704 :=
    uadd_ofNat_toNat 704 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  have h736 : (messageBase + ⟨736⟩).toNat = messageBase.toNat + 736 :=
    uadd_ofNat_toNat 736 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  have h768 : (messageBase + ⟨768⟩).toNat = messageBase.toNat + 768 :=
    uadd_ofNat_toNat 768 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  have hadd704 : messageBase + ⟨672⟩ + ⟨32⟩ = messageBase + ⟨704⟩ := by
    rw [u256_add_assoc]
    rw [show (⟨672⟩ : UInt256) + ⟨32⟩ = ⟨704⟩ by native_decide]
  have hadd736 : messageBase + ⟨672⟩ + ⟨64⟩ = messageBase + ⟨736⟩ := by
    rw [u256_add_assoc]
    rw [show (⟨672⟩ : UInt256) + ⟨64⟩ = ⟨736⟩ by native_decide]
  have hadd768 : messageBase + ⟨672⟩ + ⟨96⟩ = messageBase + ⟨768⟩ := by
    rw [u256_add_assoc]
    rw [show (⟨672⟩ : UInt256) + ⟨96⟩ = ⟨768⟩ by native_decide]
  have haw704 := runtimeMloadAw_eq_of_covers hc.1
    (addr := messageBase + ⟨704⟩) (by rw [h704]; omega) (by rw [h704]; omega)
  have haw736 := runtimeMloadAw_eq_of_covers hc.1
    (addr := messageBase + ⟨736⟩) (by rw [h736]; omega) (by rw [h736]; omega)
  have hB : runtimeRightPreludeB cursor messageBase = s.b := by
    rw [runtimeRightPreludeB, ← hadd704]
    exact hline.2.1.load
  have hC : runtimeRightPreludeC cursor messageBase = s.c := by
    rw [runtimeRightPreludeC, haw704, ← hadd736]
    exact hline.2.2.1.load
  have hD : runtimeRightPreludeD cursor messageBase = s.d := by
    rw [runtimeRightPreludeD, haw704, haw736, ← hadd768]
    exact hline.2.2.2.1.load
  have huint : messageBase.toNat + 512 < UInt256.size := by
    rw [show UInt256.size = 2 ^ 256 from by decide]
    omega
  have hx := hX.selected (row := rightWordRowWord group)
    (round := UInt256.ofNat round) huint
  have hmsg : (runtimeRoundMessageAddr messageBase (rightWordRowWord group)
      (UInt256.ofNat round)).toNat + 63 < 2 ^ 64 := by
    rw [runtimeRoundMessageAddr_toNat huint]
    have := runtimeRowEntry_lt_sixteen (rightWordRowWord group) (UInt256.ofNat round)
    omega
  have hresult := runtimeRoundCursor_line
    (rotationRow := rightRotationRowWord group)
    (boolF := runtimeRightF group s.b s.c s.d)
    (constant := rightConstantWord group) hline hx hc (by rw [h672]; omega) hmsg
    (by rw [h672]; omega)
    (by rw [runtimeRoundMessageAddr_toNat huint];
        have := runtimeRowEntry_lt_sixteen (rightWordRowWord group) (UInt256.ofNat round); omega)
  unfold runtimeRightRoundCursor
  rw [hpre, hB, hC, hD]
  exact hresult

structure RuntimeRightInvariant (cursor : RuntimeMemCursor) (messageBase : UInt256)
    (X : Fin 16 → UInt256) (left right : RuntimeLineState) : Prop where
  small : RuntimeCursorSmall cursor
  message : RuntimeMessageAt cursor messageBase X
  leftLine : RuntimeLineAt cursor (messageBase + ⟨512⟩) left
  rightLine : RuntimeLineAt cursor (messageBase + ⟨672⟩) right
  cover : messageBase.toNat + 832 ≤ 32 * cursor.aw.toNat

theorem RuntimeRightInvariant.round {cursor : RuntimeMemCursor} {messageBase : UInt256}
    {X : Fin 16 → UInt256} {left right : RuntimeLineState} {group round : Nat}
    (hinv : RuntimeRightInvariant cursor messageBase X left right)
    (hbase : messageBase.toNat + 863 < 2 ^ 64) :
    RuntimeRightInvariant (runtimeRightRoundCursor cursor messageBase group round)
      messageBase X left (runtimePureRightRound X group round right) := by
  rcases hinv with ⟨hc, hX, hleft, hright, hcover⟩
  have hpre := runtimeRightPreludeCursor_eq (messageBase := messageBase) hc
    (by omega) (by omega)
  have h512 : (messageBase + ⟨512⟩).toNat = messageBase.toNat + 512 :=
    uadd_ofNat_toNat 512 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  have h672 : (messageBase + ⟨672⟩).toNat = messageBase.toNat + 672 :=
    uadd_ofNat_toNat 672 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  have huint : messageBase.toNat + 512 < UInt256.size := by
    rw [show UInt256.size = 2 ^ 256 from by decide]
    omega
  let row := rightWordRowWord group
  let r := UInt256.ofNat round
  have hx := hX.selected (row := row) (round := r) huint
  have hmsg : (runtimeRoundMessageAddr messageBase row r).toNat + 63 < 2 ^ 64 := by
    rw [runtimeRoundMessageAddr_toNat huint]
    have := runtimeRowEntry_lt_sixteen row r
    omega
  have hmsgCover : (runtimeRoundMessageAddr messageBase row r).toNat + 32 ≤
      32 * cursor.aw.toNat := by
    rw [runtimeRoundMessageAddr_toNat huint]
    have := runtimeRowEntry_lt_sixteen row r
    omega
  have hlineCover : (messageBase + ⟨672⟩).toNat + 160 ≤
      32 * cursor.aw.toNat := by rw [h672]; omega
  have hsmall : RuntimeCursorSmall
      (runtimeRightRoundCursor cursor messageBase group round) := by
    unfold runtimeRightRoundCursor
    rw [hpre]
    exact runtimeRoundCursor_small hright hx hc (by rw [h672]; omega) hmsg
      hlineCover hmsgCover
  have haw : (runtimeRightRoundCursor cursor messageBase group round).aw = cursor.aw := by
    unfold runtimeRightRoundCursor
    rw [hpre]
    exact runtimeRoundCursor_aw_eq hc (by rw [h672]; omega) hmsg
      hlineCover hmsgCover
  have preserve {addr value : UInt256} (hw : RuntimeWordAt cursor addr value)
      (hbelow : addr.toNat + 32 ≤ (messageBase + ⟨672⟩).toNat) :
      RuntimeWordAt (runtimeRightRoundCursor cursor messageBase group round) addr value := by
    unfold runtimeRightRoundCursor
    rw [hpre]
    exact hw.runtimeRoundCursor_below hc (by rw [h672]; omega) hmsg
      hlineCover hmsgCover hbelow
  have h32 : (messageBase + ⟨512⟩ + ⟨32⟩).toNat = messageBase.toNat + 544 := by
    rw [u256_add_assoc, show (⟨512⟩ : UInt256) + ⟨32⟩ = ⟨544⟩ by native_decide]
    exact uadd_ofNat_toNat 544 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  have h64 : (messageBase + ⟨512⟩ + ⟨64⟩).toNat = messageBase.toNat + 576 := by
    rw [u256_add_assoc, show (⟨512⟩ : UInt256) + ⟨64⟩ = ⟨576⟩ by native_decide]
    exact uadd_ofNat_toNat 576 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  have h96 : (messageBase + ⟨512⟩ + ⟨96⟩).toNat = messageBase.toNat + 608 := by
    rw [u256_add_assoc, show (⟨512⟩ : UInt256) + ⟨96⟩ = ⟨608⟩ by native_decide]
    exact uadd_ofNat_toNat 608 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  have h128 : (messageBase + ⟨512⟩ + ⟨128⟩).toNat = messageBase.toNat + 640 := by
    rw [u256_add_assoc, show (⟨512⟩ : UInt256) + ⟨128⟩ = ⟨640⟩ by native_decide]
    exact uadd_ofNat_toNat 640 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  refine ⟨hsmall, ?_, ?_, runtimeRightRoundCursor_line hX hright hc hbase hcover, ?_⟩
  · intro i
    apply preserve (hX i)
    rw [runtimeMessageAddress_toNat i huint, h672]
    omega
  · exact ⟨preserve hleft.1 (by rw [h512, h672]; omega),
      preserve hleft.2.1 (by rw [h32, h672]; omega),
      preserve hleft.2.2.1 (by rw [h64, h672]; omega),
      preserve hleft.2.2.2.1 (by rw [h96, h672]; omega),
      preserve hleft.2.2.2.2 (by rw [h128, h672])⟩
  · rw [haw]
    exact hcover

def runtimePureRightGroup (X : Fin 16 → UInt256) (group : Nat) :
    Nat → RuntimeLineState → RuntimeLineState
  | 0, s => s
  | round + 1, s => runtimePureRightRound X group round
      (runtimePureRightGroup X group round s)

def runtimePureRightLine (X : Fin 16 → UInt256) :
    Nat → RuntimeLineState → RuntimeLineState
  | 0, s => s
  | group + 1, s => runtimePureRightGroup X group 16
      (runtimePureRightLine X group s)

theorem runtimeRightGroupCursor_invariant {initial : RuntimeMemCursor}
    {messageBase : UInt256} {X : Fin 16 → UInt256}
    {left right : RuntimeLineState} {group rounds : Nat}
    (hinv : RuntimeRightInvariant initial messageBase X left right)
    (hbase : messageBase.toNat + 863 < 2 ^ 64) :
    RuntimeRightInvariant (runtimeRightGroupCursor initial messageBase group rounds)
      messageBase X left (runtimePureRightGroup X group rounds right) := by
  induction rounds with
  | zero => simpa [runtimeRightGroupCursor, runtimePureRightGroup] using hinv
  | succ round ih =>
      simpa [runtimeRightGroupCursor, runtimePureRightGroup] using ih.round hbase

theorem runtimeRightLineCursor_invariant {initial : RuntimeMemCursor}
    {messageBase : UInt256} {X : Fin 16 → UInt256}
    {left right : RuntimeLineState} {groups : Nat}
    (hinv : RuntimeRightInvariant initial messageBase X left right)
    (hbase : messageBase.toNat + 863 < 2 ^ 64) :
    RuntimeRightInvariant (runtimeRightLineCursor initial messageBase groups)
      messageBase X left (runtimePureRightLine X groups right) := by
  induction groups with
  | zero => simpa [runtimeRightLineCursor, runtimePureRightLine] using hinv
  | succ group ih =>
      have hg := runtimeRightGroupCursor_invariant (group := group) (rounds := 16)
        ih hbase
      simpa [runtimeRightLineCursor, runtimePureRightLine] using hg

def runtimeLineOfChain (h : RuntimeChain) : RuntimeLineState :=
  { a := h.h0, b := h.h1, c := h.h2, d := h.h3, e := h.h4 }

theorem hashLeftInitCursor_eq (I : ExecutionEnv) (h : RuntimeChain)
    (cursor : RuntimeMemCursor) :
    hashLeftInitCursor I h cursor =
      runtimeInitLineCursor cursor (hashScratchPtr I + ⟨512⟩) (runtimeLineOfChain h) := by
  simp [hashLeftInitCursor, runtimeInitLineCursor, runtimeLineOfChain, u256_add_assoc,
    show (⟨512⟩ : UInt256) + ⟨32⟩ = ⟨544⟩ by native_decide,
    show (⟨512⟩ : UInt256) + ⟨64⟩ = ⟨576⟩ by native_decide,
    show (⟨512⟩ : UInt256) + ⟨96⟩ = ⟨608⟩ by native_decide,
    show (⟨512⟩ : UInt256) + ⟨128⟩ = ⟨640⟩ by native_decide]

theorem hashRightInitCursor_eq (I : ExecutionEnv) (h : RuntimeChain)
    (cursor : RuntimeMemCursor) :
    hashRightInitCursor I h cursor =
      runtimeInitLineCursor cursor (hashScratchPtr I + ⟨672⟩) (runtimeLineOfChain h) := by
  simp [hashRightInitCursor, runtimeInitLineCursor, runtimeLineOfChain, u256_add_assoc,
    show (⟨672⟩ : UInt256) + ⟨32⟩ = ⟨704⟩ by native_decide,
    show (⟨672⟩ : UInt256) + ⟨64⟩ = ⟨736⟩ by native_decide,
    show (⟨672⟩ : UInt256) + ⟨96⟩ = ⟨768⟩ by native_decide,
    show (⟨672⟩ : UInt256) + ⟨128⟩ = ⟨800⟩ by native_decide]

theorem RuntimeMessageAt.initLeft {cursor : RuntimeMemCursor} {messageBase : UInt256}
    {X : Fin 16 → UInt256} {h : RuntimeChain}
    (hX : RuntimeMessageAt cursor messageBase X)
    (hc : RuntimeCursorSmall cursor)
    (hbase : messageBase.toNat + 863 < 2 ^ 64) :
    RuntimeLeftInvariant
      (runtimeInitLineCursor cursor (messageBase + ⟨512⟩) (runtimeLineOfChain h))
      messageBase X (runtimeLineOfChain h) := by
  have h512 : (messageBase + ⟨512⟩).toNat = messageBase.toNat + 512 :=
    uadd_ofNat_toNat 512 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  have huint : messageBase.toNat + 512 < UInt256.size := by
    rw [show UInt256.size = 2 ^ 256 from by decide]
    omega
  have hlineBase : (messageBase + ⟨512⟩).toNat + 191 < 2 ^ 64 := by
    rw [h512]
    omega
  refine ⟨runtimeInitLineCursor_small hc hlineBase, ?_,
    runtimeInitLineCursor_line hc hlineBase, ?_⟩
  · intro i
    apply (hX i).runtimeInitLineCursor_below hc hlineBase
    rw [runtimeMessageAddress_toNat i huint, h512]
    omega
  · have hcov := runtimeInitLineCursor_cover
      (s := runtimeLineOfChain h) hc hlineBase
    rw [h512] at hcov
    exact hcov

theorem RuntimeLeftInvariant.initRight {cursor : RuntimeMemCursor}
    {messageBase : UInt256} {X : Fin 16 → UInt256}
    {left : RuntimeLineState} {h : RuntimeChain}
    (hinv : RuntimeLeftInvariant cursor messageBase X left)
    (hbase : messageBase.toNat + 863 < 2 ^ 64) :
    RuntimeRightInvariant
      (runtimeInitLineCursor cursor (messageBase + ⟨672⟩) (runtimeLineOfChain h))
      messageBase X left (runtimeLineOfChain h) := by
  rcases hinv with ⟨hc, hX, hleft, _⟩
  have h512 : (messageBase + ⟨512⟩).toNat = messageBase.toNat + 512 :=
    uadd_ofNat_toNat 512 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  have h672 : (messageBase + ⟨672⟩).toNat = messageBase.toNat + 672 :=
    uadd_ofNat_toNat 672 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  have huint : messageBase.toNat + 512 < UInt256.size := by
    rw [show UInt256.size = 2 ^ 256 from by decide]
    omega
  have hlineBase : (messageBase + ⟨672⟩).toNat + 191 < 2 ^ 64 := by
    rw [h672]
    omega
  have preserve {addr value : UInt256} (hw : RuntimeWordAt cursor addr value)
      (hbelow : addr.toNat + 32 ≤ (messageBase + ⟨672⟩).toNat) :
      RuntimeWordAt
        (runtimeInitLineCursor cursor (messageBase + ⟨672⟩) (runtimeLineOfChain h))
        addr value :=
    hw.runtimeInitLineCursor_below hc hlineBase hbelow
  have h32 : (messageBase + ⟨512⟩ + ⟨32⟩).toNat = messageBase.toNat + 544 := by
    rw [u256_add_assoc, show (⟨512⟩ : UInt256) + ⟨32⟩ = ⟨544⟩ by native_decide]
    exact uadd_ofNat_toNat 544 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  have h64 : (messageBase + ⟨512⟩ + ⟨64⟩).toNat = messageBase.toNat + 576 := by
    rw [u256_add_assoc, show (⟨512⟩ : UInt256) + ⟨64⟩ = ⟨576⟩ by native_decide]
    exact uadd_ofNat_toNat 576 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  have h96 : (messageBase + ⟨512⟩ + ⟨96⟩).toNat = messageBase.toNat + 608 := by
    rw [u256_add_assoc, show (⟨512⟩ : UInt256) + ⟨96⟩ = ⟨608⟩ by native_decide]
    exact uadd_ofNat_toNat 608 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  have h128 : (messageBase + ⟨512⟩ + ⟨128⟩).toNat = messageBase.toNat + 640 := by
    rw [u256_add_assoc, show (⟨512⟩ : UInt256) + ⟨128⟩ = ⟨640⟩ by native_decide]
    exact uadd_ofNat_toNat 640 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  refine ⟨runtimeInitLineCursor_small hc hlineBase, ?_, ?_,
    runtimeInitLineCursor_line hc hlineBase, ?_⟩
  · intro i
    apply preserve (hX i)
    rw [runtimeMessageAddress_toNat i huint, h672]
    omega
  · exact ⟨preserve hleft.1 (by rw [h512, h672]; omega),
      preserve hleft.2.1 (by rw [h32, h672]; omega),
      preserve hleft.2.2.1 (by rw [h64, h672]; omega),
      preserve hleft.2.2.2.1 (by rw [h96, h672]; omega),
      preserve hleft.2.2.2.2 (by rw [h128, h672])⟩
  · have hcov := runtimeInitLineCursor_cover
      (s := runtimeLineOfChain h) hc hlineBase
    rw [h672] at hcov
    exact hcov

theorem hashParseScratchAddress_eq (I : ExecutionEnv) {i : Nat} (hi : i < 16) :
    hashParseScratchAddress I (UInt256.ofNat i) =
      runtimeMessageAddress (hashScratchPtr I) ⟨i, hi⟩ := by
  apply u256_inj
  unfold hashParseScratchAddress runtimeMessageAddress
  have hiSize : i < UInt256.size := by
    rw [show UInt256.size = 2 ^ 256 from by decide]
    omega
  have hshift : (UInt256.shiftLeft (UInt256.ofNat i) ⟨5⟩).toNat = 32 * i :=
    ushl5_ofNat_toNat i (by omega)
  have hnat : (UInt256.ofNat (32 * i)).toNat = 32 * i :=
    ulit_toNat' _ (by
      rw [show UInt256.size = 2 ^ 256 from by decide]
      omega)
  rw [uadd_toNat, uadd_toNat, hshift, hnat]

def hashParseReadCursor (cursor : RuntimeMemCursor) (addr : UInt256) : RuntimeMemCursor :=
  let cursor := runtimeLoadCursor cursor (addr + ⟨3⟩)
  let cursor := runtimeLoadCursor cursor (addr + ⟨2⟩)
  let cursor := runtimeLoadCursor cursor (addr + ⟨1⟩)
  runtimeLoadCursor cursor addr

theorem hashParseReadCursor_small {cursor : RuntimeMemCursor} {addr : UInt256}
    (hc : RuntimeCursorSmall cursor) (haddr : addr.toNat + 66 < 2 ^ 64) :
    RuntimeCursorSmall (hashParseReadCursor cursor addr) := by
  have h1 : (addr + ⟨1⟩).toNat = addr.toNat + 1 :=
    uadd_ofNat_toNat 1 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  have h2 : (addr + ⟨2⟩).toNat = addr.toNat + 2 :=
    uadd_ofNat_toNat 2 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  have h3 : (addr + ⟨3⟩).toNat = addr.toNat + 3 :=
    uadd_ofNat_toNat 3 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  simp only [hashParseReadCursor]
  exact (((hc.load (by rw [h3]; omega)).load (by rw [h2]; omega)).load
    (by rw [h1]; omega)).load (by omega)

theorem hashParseStep_eq_store (I : ExecutionEnv) (blk i : UInt256)
    (cursor : RuntimeMemCursor) :
    hashParseStep I blk i cursor =
      runtimeStoreCursor (hashParseReadCursor cursor (hashParseAddress I blk i))
        (hashParseScratchAddress I i)
        (hashParseWord cursor (hashParseAddress I blk i)) := by
  rfl

theorem hashParseStep_small {I : ExecutionEnv} {blk i : UInt256}
    {cursor : RuntimeMemCursor}
    (hc : RuntimeCursorSmall cursor)
    (hread : (hashParseAddress I blk i).toNat + 66 < 2 ^ 64)
    (hwrite : (hashParseScratchAddress I i).toNat + 63 < 2 ^ 64) :
    RuntimeCursorSmall (hashParseStep I blk i cursor) := by
  rw [hashParseStep_eq_store]
  exact (hashParseReadCursor_small hc hread).store hwrite

theorem RuntimeWordAt.afterParseReads {cursor : RuntimeMemCursor} {read value addr : UInt256}
    (hword : RuntimeWordAt cursor read value) (hc : RuntimeCursorSmall cursor)
    (haddr : addr.toNat + 66 < 2 ^ 64) :
    RuntimeWordAt (hashParseReadCursor cursor addr) read value := by
  have h1 : (addr + ⟨1⟩).toNat = addr.toNat + 1 :=
    uadd_ofNat_toNat 1 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  have h2 : (addr + ⟨2⟩).toNat = addr.toNat + 2 :=
    uadd_ofNat_toNat 2 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  have h3 : (addr + ⟨3⟩).toNat = addr.toNat + 3 :=
    uadd_ofNat_toNat 3 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  let c1 := runtimeLoadCursor cursor (addr + ⟨3⟩)
  let c2 := runtimeLoadCursor c1 (addr + ⟨2⟩)
  let c3 := runtimeLoadCursor c2 (addr + ⟨1⟩)
  have hw1 := hword.afterLoad hc (by rw [h3]; omega)
  have hc1 := hc.load (by rw [h3]; omega)
  have hw2 := hw1.afterLoad hc1 (by rw [h2]; omega)
  have hc2 := hc1.load (by rw [h2]; omega)
  have hw3 := hw2.afterLoad hc2 (by rw [h1]; omega)
  have hc3 := hc2.load (by rw [h1]; omega)
  have hw4 := hw3.afterLoad hc3 (addr := addr) (by omega)
  change RuntimeWordAt (runtimeLoadCursor c3 addr) read value
  exact hw4

theorem hashParseStep_word_self {I : ExecutionEnv} {blk i : UInt256}
    {cursor : RuntimeMemCursor}
    (hc : RuntimeCursorSmall cursor)
    (hread : (hashParseAddress I blk i).toNat + 66 < 2 ^ 64)
    (hwrite : (hashParseScratchAddress I i).toNat + 63 < 2 ^ 64) :
    RuntimeWordAt (hashParseStep I blk i cursor) (hashParseScratchAddress I i)
      (hashParseWord cursor (hashParseAddress I blk i)) := by
  rw [hashParseStep_eq_store]
  exact (hashParseReadCursor_small hc hread).storeWord hwrite

theorem RuntimeWordAt.hashParseStep_before {I : ExecutionEnv} {blk i : UInt256}
    {cursor : RuntimeMemCursor} {read value : UInt256}
    (hword : RuntimeWordAt cursor read value)
    (hc : RuntimeCursorSmall cursor)
    (hread : (hashParseAddress I blk i).toNat + 66 < 2 ^ 64)
    (hwrite : (hashParseScratchAddress I i).toNat + 63 < 2 ^ 64)
    (hbelow : read.toNat + 32 ≤ (hashParseScratchAddress I i).toNat) :
    RuntimeWordAt (hashParseStep I blk i cursor) read value := by
  rw [hashParseStep_eq_store]
  exact (hword.afterParseReads hc hread).storeAboveSmall
    (hashParseReadCursor_small hc hread) hwrite hbelow

def runtimeParsedWords (I : ExecutionEnv) (blk : UInt256)
    (initial : RuntimeMemCursor) (i : Fin 16) : UInt256 :=
  hashParseWord (hashParseCursor I blk initial i.val)
    (hashParseAddress I blk (UInt256.ofNat i.val))

/-- Parser load addresses are the corresponding byte offsets in the padded message. -/
theorem hashParseAddress_toNat (I : ExecutionEnv) {block i : Nat}
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize)
    (hblock : block < Model.paddedLength I.calldata.size / 64)
    (hi : i < 16) :
    (hashParseAddress I (UInt256.ofNat block) (UInt256.ofNat i)).toNat =
      (hashPadPtr I).toNat + block * 64 + i * 4 := by
  have hb256 : block < UInt256.size := by
    rw [show UInt256.size = 2 ^ 256 from by decide]
    have hp := (hashPaddedLength_bounds I.calldata.size).2
    unfold maxFallbackCalldataSize at hsmall
    omega
  have hi256 : i < UInt256.size := lt_trans hi (by decide)
  have hshb :
      (UInt256.shiftLeft (UInt256.ofNat block) (⟨6⟩ : UInt256)).toNat =
        block * 64 := by
    rw [show (⟨6⟩ : UInt256) = UInt256.ofNat 6 from rfl,
      ushl_ofNat_toNat _ 6 (by decide), ulit_toNat' block hb256]
    simp only [Nat.shiftLeft_eq, pow_succ, pow_zero]
    rw [Nat.mod_eq_of_lt]
    · omega
    · rw [show UInt256.size = 2 ^ 256 from by decide]
      have hp := (hashPaddedLength_bounds I.calldata.size).2
      have hmul : block * 64 < Model.paddedLength I.calldata.size := by omega
      unfold maxFallbackCalldataSize at hsmall
      omega
  have hshi :
      (UInt256.shiftLeft (UInt256.ofNat i) (⟨2⟩ : UInt256)).toNat = i * 4 := by
    rw [show (⟨2⟩ : UInt256) = UInt256.ofNat 2 from rfl,
      ushl_ofNat_toNat _ 2 (by decide), ulit_toNat' i hi256]
    simp only [Nat.shiftLeft_eq, pow_succ, pow_zero]
    rw [Nat.mod_eq_of_lt]
    · omega
    · rw [show UInt256.size = 2 ^ 256 from by decide]
      omega
  unfold hashParseAddress
  rw [uadd_toNat, uadd_toNat, hshb, hshi,
    show UInt256.size = 2 ^ 256 from by decide]
  have hp := (hashPaddedLength_bounds I.calldata.size).2
  have hmul : block * 64 < Model.paddedLength I.calldata.size := by omega
  have hsum1 : (hashPadPtr I).toNat + block * 64 < 2 ^ 256 := by
    rw [hashPadPtr_toNat I hsmall]
    unfold maxFallbackCalldataSize at hsmall
    omega
  rw [Nat.mod_eq_of_lt hsum1]
  have hsum2 : (hashPadPtr I).toNat + block * 64 + i * 4 < 2 ^ 256 := by
    rw [hashPadPtr_toNat I hsmall]
    unfold maxFallbackCalldataSize at hsmall
    omega
  rw [Nat.mod_eq_of_lt hsum2]

def RuntimeMessagePrefix (cursor : RuntimeMemCursor) (messageBase : UInt256)
    (X : Fin 16 → UInt256) (n : Nat) : Prop :=
  ∀ i, i.val < n → RuntimeWordAt cursor (runtimeMessageAddress messageBase i) (X i)

theorem hashParseCursor_invariant {I : ExecutionEnv} {blk : UInt256}
    {initial : RuntimeMemCursor} {n : Nat}
    (hc : RuntimeCursorSmall initial)
    (hn : n ≤ 16)
    (hbase : (hashScratchPtr I).toNat + 575 < 2 ^ 64)
    (hread : ∀ i, i < n →
      (hashParseAddress I blk (UInt256.ofNat i)).toNat + 66 < 2 ^ 64) :
    RuntimeCursorSmall (hashParseCursor I blk initial n) ∧
    RuntimeMessagePrefix (hashParseCursor I blk initial n) (hashScratchPtr I)
      (runtimeParsedWords I blk initial) n := by
  induction n with
  | zero =>
      exact ⟨by simpa [hashParseCursor] using hc, by simp [RuntimeMessagePrefix]⟩
  | succ n ih =>
      have hn16 : n < 16 := by omega
      have hprev := ih (by omega) (fun i hi => hread i (by omega))
      let c := hashParseCursor I blk initial n
      let iword := UInt256.ofNat n
      have hrd : (hashParseAddress I blk iword).toNat + 66 < 2 ^ 64 :=
        hread n (by omega)
      have hdst := hashParseScratchAddress_eq I hn16
      have huint : (hashScratchPtr I).toNat + 512 < UInt256.size := by
        rw [show UInt256.size = 2 ^ 256 from by decide]
        omega
      have hdstNat : (hashParseScratchAddress I iword).toNat =
          (hashScratchPtr I).toNat + 32 * n := by
        rw [hdst, runtimeMessageAddress_toNat ⟨n, hn16⟩ huint]
      have hwr : (hashParseScratchAddress I iword).toNat + 63 < 2 ^ 64 := by
        rw [hdstNat]
        omega
      constructor
      · simpa [hashParseCursor, c, iword] using
          hashParseStep_small hprev.1 hrd hwr
      · intro j hj
        by_cases heq : j.val = n
        · have hjeq : j = ⟨n, hn16⟩ := Fin.ext heq
          subst j
          rw [hashParseCursor, ← hdst]
          simpa [runtimeParsedWords, c, iword] using
            hashParseStep_word_self hprev.1 hrd hwr
        · have hjn : j.val < n := by omega
          have hold := hprev.2 j hjn
          rw [hashParseCursor]
          apply hold.hashParseStep_before hprev.1 hrd hwr
          rw [runtimeMessageAddress_toNat j huint, hdstNat]
          omega

theorem hashParseCursor_message {I : ExecutionEnv} {blk : UInt256}
    {initial : RuntimeMemCursor}
    (hc : RuntimeCursorSmall initial)
    (hbase : (hashScratchPtr I).toNat + 575 < 2 ^ 64)
    (hread : ∀ i, i < 16 →
      (hashParseAddress I blk (UInt256.ofNat i)).toNat + 66 < 2 ^ 64) :
    RuntimeCursorSmall (hashParseCursor I blk initial 16) ∧
    RuntimeMessageAt (hashParseCursor I blk initial 16) (hashScratchPtr I)
      (runtimeParsedWords I blk initial) := by
  have h := hashParseCursor_invariant hc (n := 16) (by omega) hbase hread
  exact ⟨h.1, fun i => h.2 i i.isLt⟩

end Ripemd160
