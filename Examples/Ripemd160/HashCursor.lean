import Examples.Ripemd160.HashRunPure

/-!
# RIPEMD-160 scratch cursor preservation

The EVM stores active memory as a count of 32-byte words. Consequently a valid byte address may
exceed `2^64` while the active-word count remains below `2^64`. These lemmas retain the padded
message using scratch-relative bounds instead of the older byte-address-small invariant.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Ripemd160

theorem hashScratchPtr_add_wide (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    (hashScratchPtr I).toNat + 895 < 32 * (2 ^ 64) := by
  change (hashNewFreePtr I).toNat + 895 < 32 * (2 ^ 64)
  rw [hashNewFreePtr_toNat I hsmall, hashPadPtr_toNat I hsmall]
  have hp := (hashPaddedLength_bounds I.calldata.size).2
  unfold maxFallbackCalldataSize at hsmall
  omega

theorem hashScratchPtr_add_uint (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    (hashScratchPtr I).toNat + 895 < UInt256.size := by
  have hwide := hashScratchPtr_add_wide I hsmall
  rw [show UInt256.size = 2 ^ 256 from by decide]
  norm_num at hwide ⊢
  omega

theorem hashScratchAdd_toNat (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize)
    {offset : Nat} (hoffset : offset ≤ 895) :
    (hashScratchPtr I + UInt256.ofNat offset).toNat =
      (hashScratchPtr I).toNat + offset := by
  exact uadd_ofNat_toNat offset (by
    rw [show UInt256.size = 2 ^ 256 from by decide]
    omega) (lt_of_le_of_lt (Nat.add_le_add_left hoffset _) (hashScratchPtr_add_uint I hsmall))

theorem RuntimePaddedCursor.weaken {I : ExecutionEnv} {c : RuntimeMemCursor}
    {m n : Nat} (hc : RuntimePaddedCursor I c n) (hmn : m ≤ n) :
    RuntimePaddedCursor I c m := by
  exact ⟨hc.awSmall, hc.activeCover, le_trans (by omega) hc.frontier, hc.read⟩

theorem RuntimePaddedCursor.storeAboveScratch {I : ExecutionEnv}
    {c : RuntimeMemCursor} {n offset : Nat} {addr value : UInt256}
    (hc : RuntimePaddedCursor I c n)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize)
    (hoffset : offset ≤ 832)
    (haddr : addr.toNat = (hashScratchPtr I).toNat + offset) :
    RuntimePaddedCursor I (runtimeStoreCursor c addr value) n := by
  have hwide := hashScratchPtr_add_wide I hsmall
  have haddrWide : addr.toNat + 63 < 32 * (2 ^ 64) := by omega
  have hgap : addr.toNat - c.mem.size < USize.size := by
    have hcover : (hashScratchPtr I).toNat ≤ c.mem.size :=
      le_trans (by omega) hc.frontier
    rw [show USize.size = 2 ^ 64 from by native_decide]
    omega
  constructor
  · simpa [runtimeStoreCursor] using
      runtimeMstoreAw_lt_pow64 hc.awSmall haddrWide
  · have hge : c.aw.toNat ≤ (runtimeMstoreAw c.aw addr).toNat := by
      unfold runtimeMstoreAw
      apply machineM_ofNat_ge
      rw [show UInt256.size = 2 ^ 256 from by decide]
      omega
    exact le_trans hc.activeCover (Nat.mul_le_mul_left 32 hge)
  · have hsize := runtimeMstoreMem_size_ge c.mem addr value hgap
    simpa [runtimeStoreCursor] using le_trans hc.frontier hsize
  · intro p hp
    have hpbase : (hashPadPtr I).toNat + p + 1 ≤ (hashScratchPtr I).toNat := by
      have hptr : (hashScratchPtr I).toNat =
          (hashPadPtr I).toNat + Model.paddedLength I.calldata.size :=
        hashNewFreePtr_toNat I hsmall
      rw [hptr]
      omega
    have hpos : (hashPadPtr I).toNat + p + 1 ≤ c.mem.size :=
      le_trans hpbase (le_trans (by omega) hc.frontier)
    have hbelow : (hashPadPtr I).toNat + p + 1 ≤ addr.toNat := by
      rw [haddr]
      omega
    change ((UInt256.toByteArray value).write 0 c.mem addr.toNat 32).readWithPadding
        ((hashPadPtr I).toNat + p) 1 =
      ⟨#[UInt8.ofNat (Model.paddedByte I.calldata p)]⟩
    rw [toByteArray_write_read_below_len_of_gap _ _ _ _ _ hpos hbelow
      (by decide) (by decide) hgap]
    exact hc.read p hp

theorem RuntimePaddedCursor.loadScratch {I : ExecutionEnv}
    {c : RuntimeMemCursor} {n offset : Nat} {addr : UInt256}
    (hc : RuntimePaddedCursor I c n)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize)
    (hoffset : offset ≤ 832)
    (haddr : addr.toNat = (hashScratchPtr I).toNat + offset) :
    RuntimePaddedCursor I (runtimeLoadCursor c addr) n := by
  apply hc.afterLoad
  have hwide := hashScratchPtr_add_wide I hsmall
  omega

theorem RuntimeWordAt.afterLoadWide {cursor : RuntimeMemCursor}
    {read value addr : UInt256}
    (hword : RuntimeWordAt cursor read value)
    (haw : cursor.aw.toNat < 2 ^ 64)
    (haddr : addr.toNat + 63 < 32 * (2 ^ 64)) :
    RuntimeWordAt (runtimeLoadCursor cursor addr) read value := by
  rcases hword with ⟨hread, hmem, hcover⟩
  exact ⟨by simpa [runtimeLoadCursor] using hread,
    by simpa [runtimeLoadCursor] using hmem,
    by simpa [runtimeLoadCursor, runtimeMloadAw_eq_mstoreAw] using
      runtimeMstoreAw_preserves_cover haw haddr hcover⟩

theorem RuntimePaddedCursor.storeWordAboveScratch {I : ExecutionEnv}
    {c : RuntimeMemCursor} {n offset : Nat} {addr value : UInt256}
    (hc : RuntimePaddedCursor I c n)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize)
    (hoffset : offset ≤ 832)
    (haddr : addr.toNat = (hashScratchPtr I).toNat + offset) :
    RuntimeWordAt (runtimeStoreCursor c addr value) addr value := by
  have hwide := hashScratchPtr_add_wide I hsmall
  apply runtimeStoreCursor_word_self c addr value hc.awSmall (by omega)
  have hcover : (hashScratchPtr I).toNat ≤ c.mem.size :=
    le_trans (by omega) hc.frontier
  rw [show USize.size = 2 ^ 64 from by native_decide]
  omega

theorem RuntimeWordAt.storeAboveScratch {I : ExecutionEnv}
    {c : RuntimeMemCursor} {n offset : Nat} {read value addr stored : UInt256}
    (hword : RuntimeWordAt c read value)
    (hc : RuntimePaddedCursor I c n)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize)
    (hoffset : offset ≤ 832)
    (haddr : addr.toNat = (hashScratchPtr I).toNat + offset)
    (hbelow : read.toNat + 32 ≤ addr.toNat) :
    RuntimeWordAt (runtimeStoreCursor c addr stored) read value := by
  have hwide := hashScratchPtr_add_wide I hsmall
  apply hword.storeAbove hc.awSmall (by omega) hbelow
  have hcover : (hashScratchPtr I).toNat ≤ c.mem.size :=
    le_trans (by omega) hc.frontier
  rw [show USize.size = 2 ^ 64 from by native_decide]
  omega

theorem RuntimeWordAt.storeBelowScratch {I : ExecutionEnv}
    {c : RuntimeMemCursor} {n offset : Nat} {read value addr stored : UInt256}
    (hword : RuntimeWordAt c read value)
    (hc : RuntimePaddedCursor I c n)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize)
    (hoffset : offset ≤ 832)
    (haddr : addr.toNat = (hashScratchPtr I).toNat + offset)
    (habove : addr.toNat + 32 ≤ read.toNat) :
    RuntimeWordAt (runtimeStoreCursor c addr stored) read value := by
  have hwide := hashScratchPtr_add_wide I hsmall
  exact hword.storeBelow hc.awSmall (by omega) habove

theorem runtimeRoundReadCursor_padded {I : ExecutionEnv}
    {c : RuntimeMemCursor} {n lineOffset : Nat}
    {lineBase row round : UInt256}
    (hc : RuntimePaddedCursor I c n)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize)
    (hline : lineBase.toNat = (hashScratchPtr I).toNat + lineOffset)
    (hoffset : lineOffset + 191 ≤ 895) :
    RuntimePaddedCursor I
      (runtimeRoundReadCursor c lineBase (hashScratchPtr I) row round) n := by
  have addNat (offset : Nat) (hoff : lineOffset + offset ≤ 895) :
      (lineBase + UInt256.ofNat offset).toNat =
        (hashScratchPtr I).toNat + (lineOffset + offset) := by
    rw [uadd_ofNat_toNat offset (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega) (by
        rw [hline]
        have hu := hashScratchPtr_add_uint I hsmall
        omega)]
    omega
  have hmessageBase : (hashScratchPtr I).toNat + 512 < UInt256.size :=
    lt_of_le_of_lt (Nat.add_le_add_left (by omega : 512 ≤ 895) _)
      (hashScratchPtr_add_uint I hsmall)
  have hmsg :
      (runtimeRoundMessageAddr (hashScratchPtr I) row round).toNat =
        (hashScratchPtr I).toNat + 32 * (runtimeRowEntry row round).toNat :=
    runtimeRoundMessageAddr_toNat hmessageBase
  simp only [runtimeRoundReadCursor]
  exact (((((hc.loadScratch hsmall (by omega) hline).loadScratch hsmall
    (by omega) (addNat 32 (by omega))).loadScratch hsmall
    (by omega) (addNat 64 (by omega))).loadScratch hsmall
    (by omega) (addNat 96 (by omega))).loadScratch hsmall
    (by omega) (addNat 128 (by omega))).loadScratch hsmall
    (by have hr := runtimeRowEntry_lt_sixteen row round; omega) hmsg

theorem runtimeRoundCursor_padded {I : ExecutionEnv}
    {c : RuntimeMemCursor} {n lineOffset : Nat}
    {lineBase round row rotationRow boolF constant : UInt256}
    (hc : RuntimePaddedCursor I c n)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize)
    (hline : lineBase.toNat = (hashScratchPtr I).toNat + lineOffset)
    (hoffset : lineOffset + 191 ≤ 895) :
    RuntimePaddedCursor I
      (runtimeRoundCursor c lineBase (hashScratchPtr I)
        round row rotationRow boolF constant) n := by
  have addNat (offset : Nat) (hoff : lineOffset + offset ≤ 895) :
      (lineBase + UInt256.ofNat offset).toNat =
        (hashScratchPtr I).toNat + (lineOffset + offset) := by
    rw [uadd_ofNat_toNat offset (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega) (by
        rw [hline]
        have hu := hashScratchPtr_add_uint I hsmall
        omega)]
    omega
  have hreads := runtimeRoundReadCursor_padded hc hsmall hline hoffset
    (row := row) (round := round)
  let c0 : RuntimeMemCursor :=
    { mem := c.mem, aw := runtimeRoundAwX c lineBase (hashScratchPtr I) row round }
  let c1 := runtimeStoreCursor c0 lineBase (runtimeRoundE c lineBase)
  let c2 := runtimeStoreCursor c1 (lineBase + ⟨128⟩) (runtimeRoundD c lineBase)
  let c3 := runtimeStoreCursor c2 (lineBase + ⟨96⟩)
    (runtimeRol32 (runtimeRoundC c lineBase) ⟨10⟩)
  let c4 := runtimeStoreCursor c3 (lineBase + ⟨64⟩) (runtimeRoundB c lineBase)
  let c5 := runtimeStoreCursor c4 (lineBase + ⟨32⟩)
    (runtimeRoundNext c lineBase (hashScratchPtr I) round row rotationRow boolF constant)
  have hc0 : RuntimePaddedCursor I c0 n := by
    simpa [c0, runtimeRoundReadCursor_mem, runtimeRoundReadCursor_aw] using hreads
  have hc1 : RuntimePaddedCursor I c1 n :=
    hc0.storeAboveScratch hsmall (by omega) hline
  have hc2 : RuntimePaddedCursor I c2 n :=
    hc1.storeAboveScratch hsmall (by omega) (addNat 128 (by omega))
  have hc3 : RuntimePaddedCursor I c3 n :=
    hc2.storeAboveScratch hsmall (by omega) (addNat 96 (by omega))
  have hc4 : RuntimePaddedCursor I c4 n :=
    hc3.storeAboveScratch hsmall (by omega) (addNat 64 (by omega))
  have hc5 : RuntimePaddedCursor I c5 n :=
    hc4.storeAboveScratch hsmall (by omega) (addNat 32 (by omega))
  change RuntimePaddedCursor I c5 n
  exact hc5

theorem runtimeRoundPreludeCursor_eq_loads (c : RuntimeMemCursor) (messageBase : UInt256) :
    runtimeRoundPreludeCursor c messageBase =
      runtimeLoadCursor
        (runtimeLoadCursor (runtimeLoadCursor c (messageBase + ⟨544⟩))
          (messageBase + ⟨576⟩)) (messageBase + ⟨608⟩) := by
  rfl

theorem runtimeRightPreludeCursor_eq_loads (c : RuntimeMemCursor) (messageBase : UInt256) :
    runtimeRightPreludeCursor c messageBase =
      runtimeLoadCursor
        (runtimeLoadCursor (runtimeLoadCursor c (messageBase + ⟨704⟩))
          (messageBase + ⟨736⟩)) (messageBase + ⟨768⟩) := by
  rfl

end Ripemd160
