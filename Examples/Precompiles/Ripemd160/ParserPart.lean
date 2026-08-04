import Examples.Precompiles.Ripemd160.HashBridge

/-!
# RIPEMD-160 padded-message parser bridge

This module connects the byte-oriented parser in the optimized runtime with the pure padded
message model.  Its frontier invariant deliberately tracks only memory that the parser has
actually written; it therefore remains valid across the allocator's full accepted calldata range.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Ripemd160

theorem runtimeMstoreAw_toNat_ge (aw addr : UInt256)
    (hbound : addr.toNat + 63 < 32 * UInt256.size) :
    aw.toNat ≤ (runtimeMstoreAw aw addr).toNat := by
  unfold runtimeMstoreAw
  exact machineM_ofNat_ge aw addr.toNat 32 hbound

theorem runtimeMloadAw_toNat_ge (aw addr : UInt256)
    (hbound : addr.toNat + 63 < 32 * UInt256.size) :
    aw.toNat ≤ (runtimeMloadAw aw addr).toNat := by
  simpa [runtimeMloadAw_eq_mstoreAw] using runtimeMstoreAw_toNat_ge aw addr hbound

/-- The parser has retained the padded message and written the first `n` scratch words. -/
structure RuntimePaddedCursor (I : ExecutionEnv) (c : RuntimeMemCursor) (n : Nat) : Prop where
  awSmall : c.aw.toNat < 2 ^ 64
  activeCover : (hashScratchPtr I).toNat ≤ 32 * c.aw.toNat
  frontier : (hashScratchPtr I).toNat + 32 * n ≤ c.mem.size
  read : ∀ p, p < Model.paddedLength I.calldata.size →
    c.mem.readWithPadding ((hashPadPtr I).toNat + p) 1 =
      ⟨#[UInt8.ofNat (Model.paddedByte I.calldata p)]⟩

theorem RuntimePaddedCursor.initial (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    RuntimePaddedCursor I
      { mem := hashScratchMem I, aw := hashPaddedMessageAw I } 0 := by
  constructor
  · exact hashPaddedMessageAw_lt_pow64 I hsmall
  · change (hashNewFreePtr I).toNat ≤ 32 * (hashPaddedMessageAw I).toNat
    rw [hashNewFreePtr_toNat I hsmall]
    exact hashPaddedMessageAw_covers_message I hsmall
  · simp only [Nat.mul_zero, Nat.add_zero]
    change (hashNewFreePtr I).toNat ≤ (hashScratchMem I).size
    rw [hashNewFreePtr_toNat I hsmall]
    exact hashScratchMem_covers_message I hsmall
  · exact fun p hp => hashScratchMem_read_padded_byte I hsmall hp

theorem hashParseStep_awSmall {I : ExecutionEnv} {blk i : UInt256}
    {c : RuntimeMemCursor} (hc : c.aw.toNat < 2 ^ 64)
    (hread : (hashParseAddress I blk i).toNat + 66 < 32 * (2 ^ 64))
    (hwrite : (hashParseScratchAddress I i).toNat + 63 < 32 * (2 ^ 64)) :
    (hashParseStep I blk i c).aw.toNat < 2 ^ 64 := by
  let addr := hashParseAddress I blk i
  change addr.toNat + 66 < 32 * (2 ^ 64) at hread
  have h3 : (addr + (⟨3⟩ : UInt256)).toNat + 63 < 32 * (2 ^ 64) := by
    rw [show (⟨3⟩ : UInt256) = UInt256.ofNat 3 from rfl,
      uadd_ofNat_toNat 3 (by decide) (by
        rw [show UInt256.size = 2 ^ 256 from by decide]
        omega)]
    omega
  have h2 : (addr + (⟨2⟩ : UInt256)).toNat + 63 < 32 * (2 ^ 64) := by
    rw [show (⟨2⟩ : UInt256) = UInt256.ofNat 2 from rfl,
      uadd_ofNat_toNat 2 (by decide) (by
        rw [show UInt256.size = 2 ^ 256 from by decide]
        omega)]
    omega
  have h1 : (addr + (⟨1⟩ : UInt256)).toNat + 63 < 32 * (2 ^ 64) := by
    rw [show (⟨1⟩ : UInt256) = UInt256.ofNat 1 from rfl,
      uadd_ofNat_toNat 1 (by decide) (by
        rw [show UInt256.size = 2 ^ 256 from by decide]
        omega)]
    omega
  have ha3 : (hashParseAw3 c addr).toNat < 2 ^ 64 :=
    runtimeMstoreAw_lt_pow64 hc h3
  have ha2 : (hashParseAw2 c addr).toNat < 2 ^ 64 :=
    runtimeMstoreAw_lt_pow64 ha3 h2
  have ha1 : (hashParseAw1 c addr).toNat < 2 ^ 64 :=
    runtimeMstoreAw_lt_pow64 ha2 h1
  have ha0 : (hashParseAw0 c addr).toNat < 2 ^ 64 :=
    runtimeMstoreAw_lt_pow64 ha1 (by omega)
  change (runtimeMstoreAw
    (hashParseAw0 c (hashParseAddress I blk i))
    (hashParseScratchAddress I i)).toNat < 2 ^ 64
  change (runtimeMstoreAw (hashParseAw0 c addr)
    (hashParseScratchAddress I i)).toNat < 2 ^ 64
  exact runtimeMstoreAw_lt_pow64 ha0 hwrite

theorem hashParseStep_awGe {I : ExecutionEnv} {blk i : UInt256}
    {c : RuntimeMemCursor}
    (hread : (hashParseAddress I blk i).toNat + 66 < UInt256.size)
    (hwrite : (hashParseScratchAddress I i).toNat + 63 < UInt256.size) :
    c.aw.toNat ≤ (hashParseStep I blk i c).aw.toNat := by
  let addr := hashParseAddress I blk i
  change addr.toNat + 66 < UInt256.size at hread
  have h3 : (addr + (⟨3⟩ : UInt256)).toNat + 63 < 32 * UInt256.size := by
    rw [show (⟨3⟩ : UInt256) = UInt256.ofNat 3 from rfl,
      uadd_ofNat_toNat 3 (by decide) (by omega)]
    omega
  have h2 : (addr + (⟨2⟩ : UInt256)).toNat + 63 < 32 * UInt256.size := by
    rw [show (⟨2⟩ : UInt256) = UInt256.ofNat 2 from rfl,
      uadd_ofNat_toNat 2 (by decide) (by omega)]
    omega
  have h1 : (addr + (⟨1⟩ : UInt256)).toNat + 63 < 32 * UInt256.size := by
    rw [show (⟨1⟩ : UInt256) = UInt256.ofNat 1 from rfl,
      uadd_ofNat_toNat 1 (by decide) (by omega)]
    omega
  have ha3 := runtimeMloadAw_toNat_ge c.aw (addr + (⟨3⟩ : UInt256)) h3
  have ha2 := runtimeMloadAw_toNat_ge (hashParseAw3 c addr)
    (addr + (⟨2⟩ : UInt256)) h2
  have ha1 := runtimeMloadAw_toNat_ge (hashParseAw2 c addr)
    (addr + (⟨1⟩ : UInt256)) h1
  have ha0 := runtimeMloadAw_toNat_ge (hashParseAw1 c addr) addr (by omega)
  have hs := runtimeMstoreAw_toNat_ge (hashParseAw0 c addr)
    (hashParseScratchAddress I i) (by omega)
  have ha3' : c.aw.toNat ≤ (hashParseAw3 c addr).toNat := by
    simpa [hashParseAw3] using ha3
  have ha2' : (hashParseAw3 c addr).toNat ≤ (hashParseAw2 c addr).toNat := by
    simpa [hashParseAw2] using ha2
  have ha1' : (hashParseAw2 c addr).toNat ≤ (hashParseAw1 c addr).toNat := by
    simpa [hashParseAw1] using ha1
  have ha0' : (hashParseAw1 c addr).toNat ≤ (hashParseAw0 c addr).toNat := by
    simpa [hashParseAw0] using ha0
  change c.aw.toNat ≤
    (runtimeMstoreAw (hashParseAw0 c (hashParseAddress I blk i))
      (hashParseScratchAddress I i)).toNat
  change c.aw.toNat ≤
    (runtimeMstoreAw (hashParseAw0 c addr) (hashParseScratchAddress I i)).toNat
  exact le_trans ha3' (le_trans ha2' (le_trans ha1' (le_trans ha0' hs)))

theorem RuntimePaddedCursor.step {I : ExecutionEnv} {blk : UInt256}
    {c : RuntimeMemCursor} {n : Nat} (hc : RuntimePaddedCursor I c n)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize)
    (hn : n < 16)
    (hread : (hashParseAddress I blk (UInt256.ofNat n)).toNat + 66 <
      32 * (2 ^ 64))
    (hwrite : (hashParseScratchAddress I (UInt256.ofNat n)).toNat + 63 <
      32 * (2 ^ 64)) :
    RuntimePaddedCursor I
      (hashParseStep I blk (UInt256.ofNat n) c) (n + 1) := by
  have hdst := hashParseScratchAddress_eq I hn
  have huint : (hashScratchPtr I).toNat + 512 < UInt256.size := by
    change (hashNewFreePtr I).toNat + 512 < UInt256.size
    rw [hashNewFreePtr_toNat I hsmall, hashPadPtr_toNat I hsmall,
      show UInt256.size = 2 ^ 256 from by decide]
    have hp := (hashPaddedLength_bounds I.calldata.size).2
    unfold maxFallbackCalldataSize at hsmall
    omega
  have hdstNat : (hashParseScratchAddress I (UInt256.ofNat n)).toNat =
      (hashScratchPtr I).toNat + 32 * n := by
    rw [hdst, runtimeMessageAddress_toNat (Fin.mk n hn) huint]
  constructor
  · exact hashParseStep_awSmall hc.awSmall hread hwrite
  · have hge := hashParseStep_awGe (c := c) (I := I) (blk := blk)
      (i := UInt256.ofNat n) (by
        rw [show UInt256.size = 2 ^ 256 from by decide]
        omega) (by
        rw [show UInt256.size = 2 ^ 256 from by decide]
        omega)
    exact le_trans hc.activeCover (Nat.mul_le_mul_left 32 hge)
  · have hgap :
        (hashParseScratchAddress I (UInt256.ofNat n)).toNat - c.mem.size <
          USize.size := by
      rw [hdstNat]
      have hle := hc.frontier
      rw [Nat.sub_eq_zero_of_le hle]
      native_decide
    have hs := toByteArray_write_size_ge_off_add32
      (hashParseWord c (hashParseAddress I blk (UInt256.ofNat n))) c.mem
      (hashParseScratchAddress I (UInt256.ofNat n)).toNat hgap
    rw [hdstNat] at hs
    change (hashScratchPtr I).toNat + 32 * (n + 1) ≤
      (runtimeMstoreMem c.mem
        (hashParseScratchAddress I (UInt256.ofNat n))
        (hashParseWord c
          (hashParseAddress I blk (UInt256.ofNat n)))).size
    unfold runtimeMstoreMem
    rw [hdstNat]
    omega
  · intro p hp
    have hpos : (hashPadPtr I).toNat + p + 1 ≤ c.mem.size := by
      have hpbase : (hashPadPtr I).toNat + p + 1 ≤
          (hashScratchPtr I).toNat := by
        have hptr : (hashScratchPtr I).toNat =
            (hashPadPtr I).toNat + Model.paddedLength I.calldata.size :=
          hashNewFreePtr_toNat I hsmall
        rw [hptr]
        omega
      exact le_trans hpbase (le_trans (by omega : (hashScratchPtr I).toNat ≤
        (hashScratchPtr I).toNat + 32 * n) hc.frontier)
    have hbelow : (hashPadPtr I).toNat + p + 1 ≤
        (hashParseScratchAddress I (UInt256.ofNat n)).toNat := by
      rw [hdstNat]
      have hptr : (hashScratchPtr I).toNat =
          (hashPadPtr I).toNat + Model.paddedLength I.calldata.size :=
        hashNewFreePtr_toNat I hsmall
      rw [hptr]
      omega
    have hgap :
        (hashParseScratchAddress I (UInt256.ofNat n)).toNat - c.mem.size <
          USize.size := by
      rw [hdstNat]
      have hle := hc.frontier
      rw [Nat.sub_eq_zero_of_le hle]
      native_decide
    change ((UInt256.toByteArray
      (hashParseWord c (hashParseAddress I blk (UInt256.ofNat n)))).write
        0 c.mem (hashParseScratchAddress I (UInt256.ofNat n)).toNat 32).readWithPadding
          ((hashPadPtr I).toNat + p) 1 =
      ⟨#[UInt8.ofNat (Model.paddedByte I.calldata p)]⟩
    rw [toByteArray_write_read_below_len_of_gap _ _ _ _ _ hpos hbelow
      (by decide) (by decide) hgap]
    exact hc.read p hp

theorem RuntimePaddedCursor.afterLoad {I : ExecutionEnv} {c : RuntimeMemCursor}
    {n : Nat} (hc : RuntimePaddedCursor I c n) {addr : UInt256}
    (haddr : addr.toNat + 63 < 32 * (2 ^ 64)) :
    RuntimePaddedCursor I (runtimeLoadCursor c addr) n := by
  constructor
  · simpa [runtimeLoadCursor, runtimeMloadAw_eq_mstoreAw] using
      runtimeMstoreAw_lt_pow64 hc.awSmall haddr
  · have hge := runtimeMloadAw_toNat_ge c.aw addr (by
      rw [show UInt256.size = 2 ^ 256 from by decide]
      omega)
    exact le_trans hc.activeCover (Nat.mul_le_mul_left 32 hge)
  · simpa [runtimeLoadCursor] using hc.frontier
  · simpa [runtimeLoadCursor] using hc.read

theorem RuntimePaddedCursor.loadPaddedByte {I : ExecutionEnv} {c : RuntimeMemCursor}
    {n p : Nat} (hc : RuntimePaddedCursor I c n)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize)
    {addr : UInt256}
    (haddr : addr.toNat = (hashPadPtr I).toNat + p)
    (hp : p < Model.paddedLength I.calldata.size) :
    UInt256.byteAt ⟨0⟩ (runtimeMloadValue c.mem c.aw addr) =
      UInt256.ofNat (Model.paddedByte I.calldata p) := by
  have hptr : (hashScratchPtr I).toNat =
      (hashPadPtr I).toNat + Model.paddedLength I.calldata.size :=
    hashNewFreePtr_toNat I hsmall
  have haddrScratch : addr.toNat < (hashScratchPtr I).toNat := by
    rw [haddr, hptr]
    omega
  have hmem : addr.toNat < c.mem.size := by
    exact lt_of_lt_of_le haddrScratch
      (le_trans (by omega : (hashScratchPtr I).toNat ≤
        (hashScratchPtr I).toNat + 32 * n) hc.frontier)
  have haw : ¬ addr ≥ c.aw * ⟨32⟩ := by
    intro h
    change (c.aw * ⟨32⟩).toNat ≤ addr.toNat at h
    rw [mul32_toNat_of_lt_pow64 hc.awSmall] at h
    have hcover := hc.activeCover
    omega
  have hread : c.mem.readWithPadding addr.toNat 1 =
      ⟨#[UInt8.ofNat (Model.paddedByte I.calldata p)]⟩ := by
    rw [haddr]
    exact hc.read p hp
  have hload := runtimeMloadByte0_of_readByte hmem haw hread
  rw [UInt8.toNat_ofNat', show 2 ^ 8 = 256 by norm_num,
    Nat.mod_eq_of_lt (Model.paddedByte_lt I.calldata p)] at hload
  exact hload

theorem hashParseByteAddress_toNat (I : ExecutionEnv) {block i q : Nat}
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize)
    (hblock : block < Model.paddedLength I.calldata.size / 64)
    (hi : i < 16) (hq : q < 4) :
    (hashParseAddress I (UInt256.ofNat block) (UInt256.ofNat i) +
        UInt256.ofNat q).toNat =
      (hashPadPtr I).toNat + block * 64 + i * 4 + q := by
  rw [uadd_ofNat_toNat q (lt_trans hq (by decide))]
  · rw [hashParseAddress_toNat I hsmall hblock hi]
  · rw [hashParseAddress_toNat I hsmall hblock hi,
      hashPadPtr_toNat I hsmall, show UInt256.size = 2 ^ 256 from by decide]
    have hp := (hashPaddedLength_bounds I.calldata.size).2
    have hb : block * 64 < Model.paddedLength I.calldata.size := by omega
    unfold maxFallbackCalldataSize at hsmall
    omega

theorem hashParseWord_bytes {I : ExecutionEnv} {c : RuntimeMemCursor}
    {n block i : Nat} (hc : RuntimePaddedCursor I c n)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize)
    (hblock : block < Model.paddedLength I.calldata.size / 64)
    (hi : i < 16) :
    let p := block * 64 + i * 4
    UInt256.byteAt ⟨0⟩
        (hashParseV3 c
          (hashParseAddress I (UInt256.ofNat block) (UInt256.ofNat i))) =
        UInt256.ofNat (Model.paddedByte I.calldata (p + 3)) ∧
      UInt256.byteAt ⟨0⟩
        (hashParseV2 c
          (hashParseAddress I (UInt256.ofNat block) (UInt256.ofNat i))) =
        UInt256.ofNat (Model.paddedByte I.calldata (p + 2)) ∧
      UInt256.byteAt ⟨0⟩
        (hashParseV1 c
          (hashParseAddress I (UInt256.ofNat block) (UInt256.ofNat i))) =
        UInt256.ofNat (Model.paddedByte I.calldata (p + 1)) ∧
      UInt256.byteAt ⟨0⟩
        (hashParseV0 c
          (hashParseAddress I (UInt256.ofNat block) (UInt256.ofNat i))) =
        UInt256.ofNat (Model.paddedByte I.calldata p) := by
  dsimp only
  let addr := hashParseAddress I (UInt256.ofNat block) (UInt256.ofNat i)
  let p := block * 64 + i * 4
  have hp3 : p + 3 < Model.paddedLength I.calldata.size := by
    have hb : block * 64 < Model.paddedLength I.calldata.size := by omega
    have hmod := hashPaddedLength_mod I.calldata.size
    omega
  have haddr0 : addr.toNat = (hashPadPtr I).toNat + p := by
    dsimp only [addr, p]
    rw [hashParseAddress_toNat I hsmall hblock hi]
    omega
  have haddr1 : (addr + ⟨1⟩).toNat = (hashPadPtr I).toNat + (p + 1) := by
    rw [show (⟨1⟩ : UInt256) = UInt256.ofNat 1 from rfl]
    have h := hashParseByteAddress_toNat I hsmall hblock hi (by decide : 1 < 4)
    dsimp only [addr, p]
    omega
  have haddr2 : (addr + ⟨2⟩).toNat = (hashPadPtr I).toNat + (p + 2) := by
    rw [show (⟨2⟩ : UInt256) = UInt256.ofNat 2 from rfl]
    have h := hashParseByteAddress_toNat I hsmall hblock hi (by decide : 2 < 4)
    dsimp only [addr, p]
    omega
  have haddr3 : (addr + ⟨3⟩).toNat = (hashPadPtr I).toNat + (p + 3) := by
    rw [show (⟨3⟩ : UInt256) = UInt256.ofNat 3 from rfl]
    have h := hashParseByteAddress_toNat I hsmall hblock hi (by decide : 3 < 4)
    dsimp only [addr, p]
    omega
  have hbound (q : Nat) (hq : q < 4) :
      (addr + UInt256.ofNat q).toNat + 63 < 32 * (2 ^ 64) := by
    rw [hashParseByteAddress_toNat I hsmall hblock hi hq,
      hashPadPtr_toNat I hsmall]
    have hp := (hashPaddedLength_bounds I.calldata.size).2
    have hb : block * 64 < Model.paddedLength I.calldata.size := by omega
    unfold maxFallbackCalldataSize at hsmall
    omega
  let c3 := runtimeLoadCursor c (addr + ⟨3⟩)
  let c2 := runtimeLoadCursor c3 (addr + ⟨2⟩)
  let c1 := runtimeLoadCursor c2 (addr + ⟨1⟩)
  have hc3 : RuntimePaddedCursor I c3 n :=
    hc.afterLoad (by simpa [c3] using hbound 3 (by decide))
  have hc2 : RuntimePaddedCursor I c2 n :=
    hc3.afterLoad (by simpa [c2] using hbound 2 (by decide))
  have hc1 : RuntimePaddedCursor I c1 n :=
    hc2.afterLoad (by simpa [c1] using hbound 1 (by decide))
  have hb3 := hc.loadPaddedByte hsmall haddr3 hp3
  have hb2 := hc3.loadPaddedByte hsmall haddr2 (by omega)
  have hb1 := hc2.loadPaddedByte hsmall haddr1 (by omega)
  have hb0 := hc1.loadPaddedByte hsmall haddr0 (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [addr, hashParseV3] using hb3
  · simpa [addr, c3, runtimeLoadCursor, hashParseV2, hashParseAw3] using hb2
  · simpa [addr, c3, c2, runtimeLoadCursor, hashParseV1,
      hashParseAw3, hashParseAw2] using hb1
  · simpa [addr, c3, c2, c1, runtimeLoadCursor, hashParseV0,
      hashParseAw3, hashParseAw2, hashParseAw1] using hb0


end Ripemd160
