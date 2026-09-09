import Benchmarks.Auction.SettleAuctionTransferReturn

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Auction

theorem auctionMachineState_M_pos_offset_len_le_words_mul {s f l : ℕ} (hl : 0 < l) :
    f + l ≤ 32 * MachineState.M s f l := by
  unfold MachineState.M
  cases hcase : l with
  | zero =>
      omega
  | succ n =>
      simp
      have hceil : f + (n + 1) ≤ 32 * ((f + (n + 1) + 31) / 32) := by
        let a := f + (n + 1)
        have hdiv := Nat.div_add_mod (a + 31) 32
        have hmod : (a + 31) % 32 < 32 := Nat.mod_lt _ (by decide)
        omega
      exact le_trans hceil (Nat.mul_le_mul_left 32 (Nat.le_max_right _ _))

theorem auctionMachineState_M_inBounds {s f l : ℕ} (h : f + l ≤ 32 * s) :
    MachineState.M s f l = s := by
  rcases Nat.eq_zero_or_pos l with hl | hl
  · simp [MachineState.M, hl]
  · obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
    show max s ((f + (l' + 1) + 31) / 32) = s
    have hlt : (f + (l' + 1) + 31) / 32 < s + 1 := by
      rw [Nat.div_lt_iff_lt_mul (by norm_num)]
      omega
    omega

theorem auctionMachineState_M_word_bounds {s f : ℕ}
    (hs3 : 3 ≤ s) (hsMul : s * 32 < UInt256.size)
    (hf : f + 63 < UInt256.size) :
    let m := MachineState.M s f 32
    3 ≤ m ∧ m * 32 < UInt256.size ∧ f + 32 ≤ 32 * m ∧ m < UInt256.size := by
  let ceilW := (f + 32 + 31) / 32
  have hceilMulLt : ceilW * 32 < UInt256.size := by
    have hceilLe : ceilW * 32 ≤ f + 32 + 31 := Nat.div_mul_le_self _ _
    omega
  have hM : MachineState.M s f 32 = max s ceilW := by
    dsimp [MachineState.M, ceilW]
  dsimp only
  rw [hM]
  constructor
  · exact le_trans hs3 (Nat.le_max_left _ _)
  constructor
  · rw [Nat.mul_comm, mul_max, Nat.mul_comm 32 s, Nat.mul_comm 32 ceilW]
    exact max_lt hsMul hceilMulLt
  constructor
  · simpa [Nat.mul_comm] using
      auctionMachineState_M_pos_offset_len_le_words_mul (s := s) (f := f) (l := 32)
        (by omega)
  · have hpos : 0 < max s ceilW := by omega
    have hmul : max s ceilW * 32 < UInt256.size := by
      rw [Nat.mul_comm, mul_max, Nat.mul_comm 32 s, Nat.mul_comm 32 ceilW]
      exact max_lt hsMul hceilMulLt
    omega

def auctionSettleAuctionDynMload64 (mem : ByteArray) (aw : UInt256) : UInt256 :=
  if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
  else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))

def auctionSettleAuctionDynMload64Aw (aw : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)

def auctionSettleAuctionDynDepositMem (mem : ByteArray) (aw : UInt256) : ByteArray :=
  (UInt256.toByteArray auctionSettleAuctionDepositSelectorShifted).write 0 mem
    (auctionSettleAuctionDynMload64 mem aw).toNat 32

def auctionSettleAuctionDynDepositAw (mem : ByteArray) (aw : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M (auctionSettleAuctionDynMload64Aw aw).toNat
    (auctionSettleAuctionDynMload64 mem aw).toNat 32)

def auctionSettleAuctionDynDepositAwAfterMload64 (mem : ByteArray) (aw : UInt256) :
    UInt256 :=
  UInt256.ofNat (MachineState.M (auctionSettleAuctionDynDepositAw mem aw).toNat
    (⟨64⟩ : UInt256).toNat 32)

def auctionSettleAuctionDynDepositCallAw (mem : ByteArray) (aw : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M
    (MachineState.M (auctionSettleAuctionDynDepositAwAfterMload64 mem aw).toNat
      (auctionSettleAuctionDynMload64 mem aw).toNat 4)
    (auctionSettleAuctionDynMload64 mem aw).toNat 0)

def auctionSettleAuctionDynTransferSelMem (mem : ByteArray) (freePtr : UInt256) :
    ByteArray :=
  (UInt256.toByteArray auctionSettleAuctionTransferSelectorShifted).write 0 mem
    freePtr.toNat 32

def auctionSettleAuctionDynTransferArgMem
    (mem : ByteArray) (freePtr amount owner : UInt256) : ByteArray :=
  (UInt256.toByteArray (UInt256.land solcAddrMask owner)).write 0
    (auctionSettleAuctionDynTransferSelMem mem freePtr)
    (freePtr + (⟨4⟩ : UInt256)).toNat 32

def auctionSettleAuctionDynTransferMem
    (mem : ByteArray) (freePtr amount owner : UInt256) : ByteArray :=
  (UInt256.toByteArray amount).write 0
    (auctionSettleAuctionDynTransferArgMem mem freePtr amount owner)
    (freePtr + (⟨36⟩ : UInt256)).toNat 32

def auctionSettleAuctionDynTransferSelAw (aw freePtr : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M (auctionSettleAuctionDynMload64Aw aw).toNat
    freePtr.toNat 32)

def auctionSettleAuctionDynTransferArgAw (aw freePtr : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M (auctionSettleAuctionDynTransferSelAw aw freePtr).toNat
    (freePtr + (⟨4⟩ : UInt256)).toNat 32)

def auctionSettleAuctionDynTransferAw (aw freePtr : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M (auctionSettleAuctionDynTransferArgAw aw freePtr).toNat
    (freePtr + (⟨36⟩ : UInt256)).toNat 32)

def auctionSettleAuctionDynTransferAwAfterMload64 (aw freePtr : UInt256) :
    UInt256 :=
  UInt256.ofNat (MachineState.M (auctionSettleAuctionDynTransferAw aw freePtr).toNat
    (⟨64⟩ : UInt256).toNat 32)

def auctionSettleAuctionPayoutNonemptyOszWord (o : ByteArray) : UInt256 :=
  UInt256.ofNat o.size

def auctionSettleAuctionPayoutNonemptyRounded (o : ByteArray) : UInt256 :=
  UInt256.land (auctionSettleAuctionPayoutNonemptyOszWord o + ⟨63⟩) (UInt256.lnot ⟨31⟩)

def auctionSettleAuctionPayoutNonemptyNewFree (o : ByteArray) : UInt256 :=
  ⟨352⟩ + auctionSettleAuctionPayoutNonemptyRounded o

noncomputable def auctionSettleAuctionPayoutNonemptyMemFree
    (noun amount start finish bidder settled : UInt256) (o : ByteArray) : ByteArray :=
  (UInt256.toByteArray (auctionSettleAuctionPayoutNonemptyNewFree o)).write 0
    (auctionSettleAuctionPayoutLoopMem noun amount start finish bidder settled) 64 32

noncomputable def auctionSettleAuctionPayoutNonemptyMemLen
    (noun amount start finish bidder settled : UInt256) (o : ByteArray) : ByteArray :=
  (UInt256.toByteArray (auctionSettleAuctionPayoutNonemptyOszWord o)).write 0
    (auctionSettleAuctionPayoutNonemptyMemFree noun amount start finish bidder settled o) 352 32

noncomputable def auctionSettleAuctionPayoutNonemptyMemCopy
    (noun amount start finish bidder settled : UInt256) (o : ByteArray) : ByteArray :=
  o.write 0 (auctionSettleAuctionPayoutNonemptyMemLen noun amount start finish bidder settled o)
    384 (auctionSettleAuctionPayoutNonemptyOszWord o).toNat

def auctionSettleAuctionPayoutNonemptyAwCopy (o : ByteArray) : UInt256 :=
  UInt256.ofNat (MachineState.M (UInt256.ofNat 12).toNat 384
    (auctionSettleAuctionPayoutNonemptyOszWord o).toNat)

theorem auctionSettleAuctionDynMload64_of_readWithPadding_of_aw
    {mem : ByteArray} {aw val : UInt256}
    (hmem : 64 < mem.size)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray val)
    (haw3 : 3 ≤ aw.toNat) (hawMul : aw.toNat * 32 < UInt256.size) :
    auctionSettleAuctionDynMload64 mem aw = val := by
  unfold auctionSettleAuctionDynMload64
  apply mloadWordValue_of_readWithPadding
  · simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hmem
  · intro h
    have hmulNat : (aw * (⟨32⟩ : UInt256)).toNat = aw.toNat * 32 := by
      rw [umul_toNat]
      · rfl
      · simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using hawMul
    have hle : (aw * (⟨32⟩ : UInt256)).toNat ≤ 64 := by
      simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using h
    rw [hmulNat] at hle
    omega
  · simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hread

theorem auctionSettleAuctionPayoutNonemptyAwCopy_bounds {o : ByteArray}
    (hosmall : o.size < 2 ^ 138) :
    3 ≤ (auctionSettleAuctionPayoutNonemptyAwCopy o).toNat ∧
      (auctionSettleAuctionPayoutNonemptyAwCopy o).toNat * 32 < UInt256.size := by
  let len := (auctionSettleAuctionPayoutNonemptyOszWord o).toNat
  have hlen : len = o.size := by
    dsimp [len, auctionSettleAuctionPayoutNonemptyOszWord]
    exact UInt256.toNat_ofNat_of_lt (by
      norm_num [UInt256.size] at hosmall ⊢
      omega)
  let ceilW := (384 + len + 31) / 32
  have hceilLt : ceilW < UInt256.size := by
    have hceilLe : ceilW ≤ 384 + len + 31 := Nat.div_le_self _ _
    rw [hlen] at hceilLe
    norm_num [UInt256.size] at hosmall ⊢
    omega
  have hceilMulLt : ceilW * 32 < UInt256.size := by
    have hceilLe : ceilW * 32 ≤ 384 + len + 31 := Nat.div_mul_le_self _ _
    rw [hlen] at hceilLe
    norm_num [UInt256.size] at hosmall ⊢
    omega
  have hMlt : MachineState.M (UInt256.ofNat 12).toNat 384 len < UInt256.size := by
    dsimp [MachineState.M]
    rw [show (UInt256.ofNat 12).toNat = 12 by native_decide]
    cases hcase : len with
    | zero =>
      simp [hcase]
      norm_num [UInt256.size]
    | succ n =>
      simp [hcase]
      have hceilLt' : (384 + (n + 1) + 31) / 32 < UInt256.size := by
        have hceilLe : (384 + (n + 1) + 31) / 32 ≤ 384 + (n + 1) + 31 :=
          Nat.div_le_self _ _
        have hn : n + 1 = o.size := by
          simpa [hcase] using hlen
        rw [hn] at hceilLe
        norm_num [UInt256.size] at hosmall ⊢
        omega
      constructor
      · norm_num [UInt256.size]
      · exact hceilLt'
  have hawNat :
      (auctionSettleAuctionPayoutNonemptyAwCopy o).toNat =
        MachineState.M (UInt256.ofNat 12).toNat 384 len := by
    dsimp [auctionSettleAuctionPayoutNonemptyAwCopy, len]
    exact UInt256.toNat_ofNat_of_lt hMlt
  constructor
  · rw [hawNat]
    dsimp [MachineState.M]
    rw [show (UInt256.ofNat 12).toNat = 12 by native_decide]
    cases hcase : len with
    | zero =>
      simp [hcase]
    | succ n =>
      simp [hcase]
  · rw [hawNat]
    dsimp [MachineState.M]
    rw [show (UInt256.ofNat 12).toNat = 12 by native_decide]
    cases hcase : len with
    | zero =>
      simp [hcase]
      norm_num [UInt256.size]
    | succ n =>
      simp [hcase]
      rw [Nat.mul_comm, mul_max, Nat.mul_comm 32 12,
        Nat.mul_comm 32 ((384 + (n + 1) + 31) / 32)]
      have hceilMulLt' : ((384 + (n + 1) + 31) / 32) * 32 < UInt256.size := by
        have hceilLe :
            ((384 + (n + 1) + 31) / 32) * 32 ≤ 384 + (n + 1) + 31 :=
          Nat.div_mul_le_self _ _
        have hn : n + 1 = o.size := by
          simpa [hcase] using hlen
        rw [hn] at hceilLe
        norm_num [UInt256.size] at hosmall ⊢
        omega
      apply max_lt
      · norm_num [UInt256.size]
      · exact hceilMulLt'

theorem auctionSettleAuctionPayoutNonemptyMemCopy_size
    (noun amount start finish bidder settled : UInt256) {o : ByteArray}
    (hosmall : o.size < 2 ^ 138) (hne : o.size ≠ 0) :
    (auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled o).size =
      384 + o.size := by
  let memLoop := auctionSettleAuctionPayoutLoopMem noun amount start finish bidder settled
  let memFree := auctionSettleAuctionPayoutNonemptyMemFree noun amount start finish bidder settled o
  let memLen := auctionSettleAuctionPayoutNonemptyMemLen noun amount start finish bidder settled o
  let oszWord := auctionSettleAuctionPayoutNonemptyOszWord o
  have hmemFreeSize : memFree.size = 384 := by
    dsimp [memFree, auctionSettleAuctionPayoutNonemptyMemFree, memLoop]
    exact toByteArray_write32_size_of_le
      (auctionSettleAuctionPayoutLoopMem noun amount start finish bidder settled)
      (auctionSettleAuctionPayoutNonemptyNewFree o) 64 384 384
      (auctionSettleAuctionPayoutLoopMem_size noun amount start finish bidder settled)
      (by rw [auctionSettleAuctionPayoutLoopMem_size]; decide) (by decide)
  have hmemLenSize : memLen.size = 384 := by
    dsimp [memLen, auctionSettleAuctionPayoutNonemptyMemLen, memFree, oszWord]
    exact toByteArray_write32_size_of_le
      (auctionSettleAuctionPayoutNonemptyMemFree noun amount start finish bidder settled o)
      (auctionSettleAuctionPayoutNonemptyOszWord o) 352 384 384
      hmemFreeSize (by rw [hmemFreeSize]; decide) (by decide)
  have hoszNat : oszWord.toNat = o.size := by
    dsimp [oszWord, auctionSettleAuctionPayoutNonemptyOszWord]
    exact UInt256.toNat_ofNat_of_lt (by
      norm_num [UInt256.size] at hosmall ⊢
      omega)
  have hlenNe : oszWord.toNat ≠ 0 := by
    rw [hoszNat]
    exact hne
  have hsrc : 0 + oszWord.toNat ≤ o.size := by
    rw [hoszNat]
    omega
  have hsize : (o.write 0 memLen 384 oszWord.toNat).size = 384 + oszWord.toNat := by
    simpa [hmemLenSize] using write_end_size_from o memLen 0 oszWord.toNat hlenNe hsrc
  dsimp [auctionSettleAuctionPayoutNonemptyMemCopy, memLen, oszWord]
  rw [hsize, hoszNat]

theorem auctionSettleAuctionPayoutNonemptyMemCopy_read64
    (noun amount start finish bidder settled : UInt256) {o : ByteArray}
    (hosmall : o.size < 2 ^ 138) (hne : o.size ≠ 0) :
    (auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled o).readWithPadding
        64 32 =
      UInt256.toByteArray (auctionSettleAuctionPayoutNonemptyNewFree o) := by
  let memLoop := auctionSettleAuctionPayoutLoopMem noun amount start finish bidder settled
  let memFree := auctionSettleAuctionPayoutNonemptyMemFree noun amount start finish bidder settled o
  let memLen := auctionSettleAuctionPayoutNonemptyMemLen noun amount start finish bidder settled o
  let memCopy := auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled o
  let oszWord := auctionSettleAuctionPayoutNonemptyOszWord o
  let newFree := auctionSettleAuctionPayoutNonemptyNewFree o
  have hmemFreeSize : memFree.size = 384 := by
    dsimp [memFree, auctionSettleAuctionPayoutNonemptyMemFree, memLoop, newFree]
    exact toByteArray_write32_size_of_le
      (auctionSettleAuctionPayoutLoopMem noun amount start finish bidder settled)
      (auctionSettleAuctionPayoutNonemptyNewFree o) 64 384 384
      (auctionSettleAuctionPayoutLoopMem_size noun amount start finish bidder settled)
      (by rw [auctionSettleAuctionPayoutLoopMem_size]; decide) (by decide)
  have hreadFree : memFree.readWithPadding 64 32 = UInt256.toByteArray newFree := by
    dsimp [memFree, auctionSettleAuctionPayoutNonemptyMemFree, memLoop, newFree]
    exact toByteArray_write_read_back_of_gap
      (auctionSettleAuctionPayoutNonemptyNewFree o)
      (auctionSettleAuctionPayoutLoopMem noun amount start finish bidder settled) 64
      (by
        rw [auctionSettleAuctionPayoutLoopMem_size]
        native_decide)
  have hmemLenSize : memLen.size = 384 := by
    dsimp [memLen, auctionSettleAuctionPayoutNonemptyMemLen, memFree, oszWord]
    exact toByteArray_write32_size_of_le
      (auctionSettleAuctionPayoutNonemptyMemFree noun amount start finish bidder settled o)
      (auctionSettleAuctionPayoutNonemptyOszWord o) 352 384 384
      hmemFreeSize (by rw [hmemFreeSize]; decide) (by decide)
  have hreadLen : memLen.readWithPadding 64 32 = UInt256.toByteArray newFree := by
    have hpres := toByteArray_write_read_below_of_gap oszWord memFree 352 64
      (by rw [hmemFreeSize]; decide) (by decide)
      (by rw [hmemFreeSize]; native_decide)
    dsimp [memLen, auctionSettleAuctionPayoutNonemptyMemLen, memFree, oszWord]
    rw [hpres]
    exact hreadFree
  have hoszNat : oszWord.toNat = o.size := by
    dsimp [oszWord, auctionSettleAuctionPayoutNonemptyOszWord]
    exact UInt256.toNat_ofNat_of_lt (by
      norm_num [UInt256.size] at hosmall ⊢
      omega)
  have hlenNe : oszWord.toNat ≠ 0 := by
    rw [hoszNat]
    exact hne
  have hsrc : oszWord.toNat ≤ o.size := by
    rw [hoszNat]
  have hpres := write_read_below_gen_extend o memLen 384 oszWord.toNat 64
    hlenNe hsrc (by rw [hmemLenSize]) (by decide)
  dsimp [memCopy, auctionSettleAuctionPayoutNonemptyMemCopy, memLen, oszWord]
  rw [hpres]
  exact hreadLen

theorem auctionSettleAuctionPayoutNonemptyRounded_toNat_le {o : ByteArray}
    (hosmall : o.size < 2 ^ 138) :
    (auctionSettleAuctionPayoutNonemptyRounded o).toNat ≤ o.size + 63 := by
  have hoszLt : o.size < UInt256.size := by
    norm_num [UInt256.size] at hosmall ⊢
    omega
  have hsumLt : o.size + 63 < UInt256.size := by
    norm_num [UInt256.size] at hosmall ⊢
    omega
  dsimp [auctionSettleAuctionPayoutNonemptyRounded,
    auctionSettleAuctionPayoutNonemptyOszWord]
  rw [uland_toNat, lnot31_toNat, uadd_toNat, UInt256.toNat_ofNat_of_lt hoszLt,
    show ((⟨63⟩ : UInt256).toNat = 63) by decide, Nat.mod_eq_of_lt hsumLt]
  exact Nat.and_le_left

theorem auctionSettleAuctionPayoutNonemptyNewFree_toNat {o : ByteArray}
    (hosmall : o.size < 2 ^ 138) :
    (auctionSettleAuctionPayoutNonemptyNewFree o).toNat =
      352 + (auctionSettleAuctionPayoutNonemptyRounded o).toNat := by
  have hroundLe := auctionSettleAuctionPayoutNonemptyRounded_toNat_le (o := o) hosmall
  have hsumLt :
      352 + (auctionSettleAuctionPayoutNonemptyRounded o).toNat < UInt256.size := by
    norm_num [UInt256.size] at hosmall ⊢
    omega
  dsimp [auctionSettleAuctionPayoutNonemptyNewFree]
  rw [uadd_toNat, show ((⟨352⟩ : UInt256).toNat = 352) by decide,
    Nat.mod_eq_of_lt hsumLt]

theorem auctionSettleAuctionPayoutNonemptyNewFree_ge96 {o : ByteArray}
    (hosmall : o.size < 2 ^ 138) :
    96 ≤ (auctionSettleAuctionPayoutNonemptyNewFree o).toNat := by
  rw [auctionSettleAuctionPayoutNonemptyNewFree_toNat (o := o) hosmall]
  omega

theorem auctionSettleAuctionPayoutNonemptyNewFree_add63_lt {o : ByteArray}
    (hosmall : o.size < 2 ^ 138) :
    (auctionSettleAuctionPayoutNonemptyNewFree o).toNat + 63 < UInt256.size := by
  have hroundLe := auctionSettleAuctionPayoutNonemptyRounded_toNat_le (o := o) hosmall
  rw [auctionSettleAuctionPayoutNonemptyNewFree_toNat (o := o) hosmall]
  norm_num [UInt256.size] at hosmall ⊢
  omega

theorem auctionSettleAuctionPayoutNonemptyNewFree_add99_lt {o : ByteArray}
    (hosmall : o.size < 2 ^ 138) :
    (auctionSettleAuctionPayoutNonemptyNewFree o).toNat + 99 < UInt256.size := by
  have hroundLe := auctionSettleAuctionPayoutNonemptyRounded_toNat_le (o := o) hosmall
  rw [auctionSettleAuctionPayoutNonemptyNewFree_toNat (o := o) hosmall]
  norm_num [UInt256.size] at hosmall ⊢
  omega

theorem auctionSettleAuctionPayoutNonemptyNewFree_memCopy_gap
    (noun amount start finish bidder settled : UInt256) {o : ByteArray}
    (hosmall : o.size < 2 ^ 138) (hne : o.size ≠ 0) :
    (auctionSettleAuctionPayoutNonemptyNewFree o).toNat -
        (auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled o).size <
      USize.size := by
  have hroundLe := auctionSettleAuctionPayoutNonemptyRounded_toNat_le (o := o) hosmall
  have hmemSize :=
    auctionSettleAuctionPayoutNonemptyMemCopy_size
      noun amount start finish bidder settled hosmall hne
  rw [hmemSize, auctionSettleAuctionPayoutNonemptyNewFree_toNat (o := o) hosmall]
  have hU : 31 < USize.size := by native_decide
  omega

theorem u256_sub_lit4_add_cancel {ptr : UInt256}
    (hptr : ptr.toNat + 4 < UInt256.size) :
    UInt256.sub ((⟨4⟩ : UInt256) + ptr) ptr = ⟨4⟩ := by
  apply u256_inj
  have hsum : (((⟨4⟩ : UInt256) + ptr).toNat = ptr.toNat + 4) := by
    rw [uadd_toNat, show ((⟨4⟩ : UInt256).toNat = 4) by decide]
    rw [show 4 + ptr.toNat = ptr.toNat + 4 by omega]
    exact Nat.mod_eq_of_lt hptr
  rw [usub_toNat (a := ((⟨4⟩ : UInt256) + ptr)) (b := ptr) (by rw [hsum]; omega),
    hsum, show ((⟨4⟩ : UInt256).toNat = 4) by decide]
  omega

theorem u256_sub_lit68_add_cancel {ptr : UInt256}
    (hptr : ptr.toNat + 68 < UInt256.size) :
    UInt256.sub ((⟨68⟩ : UInt256) + ptr) ptr = ⟨68⟩ := by
  apply u256_inj
  have hsum : (((⟨68⟩ : UInt256) + ptr).toNat = ptr.toNat + 68) := by
    rw [uadd_toNat, show ((⟨68⟩ : UInt256).toNat = 68) by decide]
    rw [show 68 + ptr.toNat = ptr.toNat + 68 by omega]
    exact Nat.mod_eq_of_lt hptr
  rw [usub_toNat (a := ((⟨68⟩ : UInt256) + ptr)) (b := ptr) (by rw [hsum]; omega),
    hsum, show ((⟨68⟩ : UInt256).toNat = 68) by decide]
  omega

theorem u256_not_ge_mul32_of_cover {off aw : UInt256}
    (hawMul : aw.toNat * 32 < UInt256.size)
    (hcover : off.toNat + 32 ≤ 32 * aw.toNat) :
    ¬ off ≥ aw * ⟨32⟩ := by
  intro hge
  have hmulNat : (aw * (⟨32⟩ : UInt256)).toNat = aw.toNat * 32 := by
    rw [umul_toNat]
    · rfl
    · simpa [show (⟨32⟩ : UInt256).toNat = 32 by decide] using hawMul
  have hle : (aw * (⟨32⟩ : UInt256)).toNat ≤ off.toNat := hge
  rw [hmulNat] at hle
  omega

set_option maxHeartbeats 1000000 in
theorem auctionSettleAuctionTransferReturnLenRevertAt {cA gh bl σ σ₀ A I}
    {g : Sat256} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {base amount owner weth aw : UInt256} {mem o : ByteArray} {k C : ℕ}
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3518⟩
      [⟨1⟩, (⟨68⟩ : UInt256) + base, ⟨2835717307⟩, weth, amount, owner,
        ⟨4688⟩, ⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I]
      mem aw o acc k C)
    (hfp :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩
        then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      base)
    (hbad :
      UInt256.slt (UInt256.sub (base + UInt256.ofNat o.size) base) ⟨32⟩ = ⟨1⟩) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let osz := UInt256.ofNat o.size
  let rounded := UInt256.land (UInt256.add osz ⟨31⟩) (UInt256.lnot ⟨31⟩)
  let newFree := UInt256.add base rounded
  let aw64 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
  let memRet := (UInt256.toByteArray newFree).write 0 mem (⟨64⟩ : UInt256).toNat 32
  let awStore := UInt256.ofNat (MachineState.M aw64.toNat (⟨64⟩ : UInt256).toNat 32)
  have rd6062₀ := evm_run rd with [
    iszero, dup1, iszero, push2 ⟨3532⟩, jumpiT (by native_decide) (by jump_dest),
    jumpdest, pop, pop, pop, pop, push1 ⟨64⟩,
    raw mload (Cₘ aw64 - Cₘ aw) base aw64 (by native_decide)
      (fun _ haws hstks => auctionMloadCost_of_stack haws hstks (by rfl))
      hfp (by rfl) (by evm_ov),
    returndatasize, push1 ⟨31⟩, not, push1 ⟨31⟩, dup3, add, and, dup3, add,
    dup1, push1 ⟨64⟩,
    raw mstore (Cₘ awStore - Cₘ aw64) memRet awStore (by native_decide)
      (fun _ haws hstks => mstoreCost_of_stack haws hstks (by rfl))
      (by rfl) (by rfl) (by evm_ov),
    pop, dup2, add, swap1, push2 ⟨3568⟩, swap2, swap1, push2 ⟨6062⟩,
    jump (by jump_dest), jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt]
  have rd6069 := rd6062₀
  rw [hbad] at rd6069
  have rd6070₀ := evm_run rd6069 with [iszero]
  have rd6070 := rd6070₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by native_decide] at rd6070
  exact evm_run rd6070 with [
    push2 ⟨6078⟩, jumpiNT (by native_decide), push0, dup1,
    raw rev 0 (by native_decide) (fun s _ hstk => memExpRevert0 s hstk) (by evm_ov)]

theorem auctionSettleAuctionTransferReturnShortRevertAt {cA gh bl σ σ₀ A I}
    {g : Sat256} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {base amount owner weth aw : UInt256} {mem o : ByteArray} {k C : ℕ}
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3518⟩
      [⟨1⟩, (⟨68⟩ : UInt256) + base, ⟨2835717307⟩, weth, amount, owner,
        ⟨4688⟩, ⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I]
      mem aw o acc k C)
    (hshort : o.size < 32)
    (hbaseAdd : base.toNat + o.size < UInt256.size)
    (hfp :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩
        then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      base) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hbad :
      UInt256.slt (UInt256.sub (base + UInt256.ofNat o.size) base) ⟨32⟩ = ⟨1⟩ := by
    have hbase : base.toNat < UInt256.size := base.val.isLt
    have hbaseWord : UInt256.ofNat base.toNat = base := u256_ofNat_toNat base
    have hlenWord : UInt256.ofNat (32 * 1) = (⟨32⟩ : UInt256) := rfl
    have h :=
      solcReturnStaticLenCheckShort (base := base.toNat) (len := o.size) (words := 1)
        (by simpa using hshort) hbase hbaseAdd
        (by norm_num)
    simpa [hbaseWord, hlenWord] using h
  exact auctionSettleAuctionTransferReturnLenRevertAt rd hfp hbad

theorem auctionSettleAuctionTransferReturnHugeRevertAt {cA gh bl σ σ₀ A I}
    {g : Sat256} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {base amount owner weth aw : UInt256} {mem o : ByteArray} {k C : ℕ}
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3518⟩
      [⟨1⟩, (⟨68⟩ : UInt256) + base, ⟨2835717307⟩, weth, amount, owner,
        ⟨4688⟩, ⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I]
      mem aw o acc k C)
    (hhuge : (2 : Nat) ^ 255 ≤ o.size)
    (hosz : o.size < UInt256.size)
    (hfp :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩
        then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      base) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hbad :
      UInt256.slt (UInt256.sub (base + UInt256.ofNat o.size) base) ⟨32⟩ = ⟨1⟩ := by
    have hbase : base.toNat < UInt256.size := base.val.isLt
    have hbaseWord : UInt256.ofNat base.toNat = base := u256_ofNat_toNat base
    have hlenWord : UInt256.ofNat (32 * 1) = (⟨32⟩ : UInt256) := rfl
    have h :=
      solcReturnStaticLenCheckHuge (base := base.toNat) (len := o.size) (words := 1)
        hhuge hosz hbase (by norm_num)
    simpa [hbaseWord, hlenWord] using h
  exact auctionSettleAuctionTransferReturnLenRevertAt rd hfp hbad

set_option maxHeartbeats 1000000 in
theorem auctionSettleAuctionTransferReturnBoolToEventAt {cA gh bl σ σ₀ A I}
    {g : Sat256} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {base amount owner weth retWord aw : UInt256} {mem o : ByteArray} {k C : ℕ}
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3518⟩
      [⟨1⟩, (⟨68⟩ : UInt256) + base, ⟨2835717307⟩, weth, amount, owner,
        ⟨4688⟩, ⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I]
      mem aw o acc k C)
    (ho32 : 32 ≤ o.size)
    (hohi : o.size < 2 ^ 255)
    (hbaseAdd : base.toNat + o.size < UInt256.size)
    (hfp :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩
        then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      base)
    (hword :
      let osz := UInt256.ofNat o.size
      let rounded := UInt256.land (UInt256.add osz ⟨31⟩) (UInt256.lnot ⟨31⟩)
      let newFree := UInt256.add base rounded
      let aw64 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
      let memRet := (UInt256.toByteArray newFree).write 0 mem (⟨64⟩ : UInt256).toNat 32
      let awStore := UInt256.ofNat (MachineState.M aw64.toNat (⟨64⟩ : UInt256).toNat 32)
      (if base.toNat ≥ memRet.size ∨ base ≥ awStore * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (memRet.readWithPadding base.toNat 32))) =
      retWord)
    (hcanon : retWord = ⟨0⟩ ∨ retWord = ⟨1⟩) :
    ∃ mem' aw' k' C',
      RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4688⟩
        [⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I] mem' aw' o acc k' C' := by
  let osz := UInt256.ofNat o.size
  let rounded := UInt256.land (UInt256.add osz ⟨31⟩) (UInt256.lnot ⟨31⟩)
  let newFree := UInt256.add base rounded
  let aw64 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
  let memRet := (UInt256.toByteArray newFree).write 0 mem (⟨64⟩ : UInt256).toNat 32
  let awStore := UInt256.ofNat (MachineState.M aw64.toNat (⟨64⟩ : UInt256).toNat 32)
  let awLoad := UInt256.ofNat (MachineState.M awStore.toNat base.toNat 32)
  have hlenOk :
      UInt256.slt (UInt256.sub (base + osz) base) ⟨32⟩ = ⟨0⟩ := by
    have hbase : base.toNat < UInt256.size := base.val.isLt
    have hbaseWord : UInt256.ofNat base.toNat = base := u256_ofNat_toNat base
    have hlenWord : UInt256.ofNat (32 * 1) = (⟨32⟩ : UInt256) := rfl
    have h :=
      solcReturnStaticLenCheckOk (base := base.toNat) (len := o.size) (words := 1)
        (by simpa using ho32) hohi hbase hbaseAdd
    simpa [osz, hbaseWord, hlenWord] using h
  have hcondCanon :
      UInt256.eq (UInt256.isZero (UInt256.isZero retWord)) retWord = ⟨1⟩ := by
    rcases hcanon with rfl | rfl <;> native_decide
  have hcondCanon' :
      UInt256.eq retWord (UInt256.isZero (UInt256.isZero retWord)) = ⟨1⟩ := by
    rcases hcanon with rfl | rfl <;> native_decide
  have rd6062₀ := evm_run rd with [
    iszero, dup1, iszero, push2 ⟨3532⟩, jumpiT (by native_decide) (by jump_dest),
    jumpdest, pop, pop, pop, pop, push1 ⟨64⟩,
    raw mload (Cₘ aw64 - Cₘ aw) base aw64 (by native_decide)
      (fun _ haws hstks => auctionMloadCost_of_stack haws hstks (by rfl))
      hfp (by rfl) (by evm_ov),
    returndatasize, push1 ⟨31⟩, not, push1 ⟨31⟩, dup3, add, and, dup3, add,
    dup1, push1 ⟨64⟩,
    raw mstore (Cₘ awStore - Cₘ aw64) memRet awStore (by native_decide)
      (fun _ haws hstks => mstoreCost_of_stack haws hstks (by rfl))
      (by rfl) (by rfl) (by evm_ov),
    pop, dup2, add, swap1, push2 ⟨3568⟩, swap2, swap1, push2 ⟨6062⟩,
    jump (by jump_dest), jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt]
  have rd6069 := rd6062₀
  rw [hlenOk] at rd6069
  have rd5350₀ := evm_run rd6069 with [
    iszero, push2 ⟨6078⟩, jumpiT (by native_decide) (by jump_dest), jumpdest, dup2,
    raw mload (Cₘ awLoad - Cₘ awStore) retWord awLoad (by native_decide)
      (fun _ haws hstks => auctionMloadCost_of_stack haws hstks (by rfl))
      (by simpa [osz, rounded, newFree, aw64, memRet, awStore] using hword)
      (by rfl) (by evm_ov),
    dup1, iszero, iszero, dup2, eq]
  have rd5350 := rd5350₀
  rw [hcondCanon'] at rd5350
  have rd3568 := evm_run rd5350 with [
    push2 ⟨5350⟩, jumpiT (by native_decide) (by jump_dest), jumpdest, swap4, swap3,
    pop, pop, pop, jump (by jump_dest), jumpdest, pop]
  exact ⟨_, _, _, _, evm_run rd3568 with [jumpdest, pop, pop, jump (by jump_dest)]⟩

set_option maxHeartbeats 1000000 in
theorem auctionSettleAuctionTransferReturnNoncanonRevertAt {cA gh bl σ σ₀ A I}
    {g : Sat256} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {base amount owner weth retWord aw : UInt256} {mem o : ByteArray} {k C : ℕ}
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3518⟩
      [⟨1⟩, (⟨68⟩ : UInt256) + base, ⟨2835717307⟩, weth, amount, owner,
        ⟨4688⟩, ⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I]
      mem aw o acc k C)
    (ho32 : 32 ≤ o.size)
    (hohi : o.size < 2 ^ 255)
    (hbaseAdd : base.toNat + o.size < UInt256.size)
    (hfp :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩
        then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      base)
    (hword :
      let osz := UInt256.ofNat o.size
      let rounded := UInt256.land (UInt256.add osz ⟨31⟩) (UInt256.lnot ⟨31⟩)
      let newFree := UInt256.add base rounded
      let aw64 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
      let memRet := (UInt256.toByteArray newFree).write 0 mem (⟨64⟩ : UInt256).toNat 32
      let awStore := UInt256.ofNat (MachineState.M aw64.toNat (⟨64⟩ : UInt256).toNat 32)
      (if base.toNat ≥ memRet.size ∨ base ≥ awStore * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (memRet.readWithPadding base.toNat 32))) =
      retWord)
    (hnz : retWord ≠ ⟨0⟩) (hno : retWord ≠ ⟨1⟩) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let osz := UInt256.ofNat o.size
  let rounded := UInt256.land (UInt256.add osz ⟨31⟩) (UInt256.lnot ⟨31⟩)
  let newFree := UInt256.add base rounded
  let aw64 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
  let memRet := (UInt256.toByteArray newFree).write 0 mem (⟨64⟩ : UInt256).toNat 32
  let awStore := UInt256.ofNat (MachineState.M aw64.toNat (⟨64⟩ : UInt256).toNat 32)
  let awLoad := UInt256.ofNat (MachineState.M awStore.toNat base.toNat 32)
  have hlenOk :
      UInt256.slt (UInt256.sub (base + osz) base) ⟨32⟩ = ⟨0⟩ := by
    have hbase : base.toNat < UInt256.size := base.val.isLt
    have hbaseWord : UInt256.ofNat base.toNat = base := u256_ofNat_toNat base
    have hlenWord : UInt256.ofNat (32 * 1) = (⟨32⟩ : UInt256) := rfl
    have h :=
      solcReturnStaticLenCheckOk (base := base.toNat) (len := o.size) (words := 1)
        (by simpa using ho32) hohi hbase hbaseAdd
    simpa [osz, hbaseWord, hlenWord] using h
  have hcondCanon :
      UInt256.eq retWord (UInt256.isZero (UInt256.isZero retWord)) = ⟨0⟩ :=
    auctionTransferReturnBoolNoncanonEqZero hnz hno
  have rd6062₀ := evm_run rd with [
    iszero, dup1, iszero, push2 ⟨3532⟩, jumpiT (by native_decide) (by jump_dest),
    jumpdest, pop, pop, pop, pop, push1 ⟨64⟩,
    raw mload (Cₘ aw64 - Cₘ aw) base aw64 (by native_decide)
      (fun _ haws hstks => auctionMloadCost_of_stack haws hstks (by rfl))
      hfp (by rfl) (by evm_ov),
    returndatasize, push1 ⟨31⟩, not, push1 ⟨31⟩, dup3, add, and, dup3, add,
    dup1, push1 ⟨64⟩,
    raw mstore (Cₘ awStore - Cₘ aw64) memRet awStore (by native_decide)
      (fun _ haws hstks => mstoreCost_of_stack haws hstks (by rfl))
      (by rfl) (by rfl) (by evm_ov),
    pop, dup2, add, swap1, push2 ⟨3568⟩, swap2, swap1, push2 ⟨6062⟩,
    jump (by jump_dest), jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt]
  have rd6069 := rd6062₀
  rw [hlenOk] at rd6069
  have rd5350₀ := evm_run rd6069 with [
    iszero, push2 ⟨6078⟩, jumpiT (by native_decide) (by jump_dest), jumpdest, dup2,
    raw mload (Cₘ awLoad - Cₘ awStore) retWord awLoad (by native_decide)
      (fun _ haws hstks => auctionMloadCost_of_stack haws hstks (by rfl))
      (by simpa [osz, rounded, newFree, aw64, memRet, awStore] using hword)
      (by rfl) (by evm_ov),
    dup1, iszero, iszero, dup2, eq]
  have rd5350 := rd5350₀
  rw [hcondCanon] at rd5350
  exact evm_run rd5350 with [
    push2 ⟨5350⟩, jumpiNT (by native_decide), push0, dup1,
    raw rev 0 (by native_decide) (fun s _ hstk => memExpRevert0 s hstk) (by evm_ov)]

theorem auctionSettleAuctionDynMload64Aw_eq_of_bounds {aw : UInt256}
    (haw3 : 3 ≤ aw.toNat) :
    auctionSettleAuctionDynMload64Aw aw = aw := by
  apply u256_inj
  have hM : MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32 = aw.toNat := by
    rw [show ((⟨64⟩ : UInt256).toNat = 64) by decide]
    change max aw.toNat ((64 + 32 + 31) / 32) = aw.toNat
    rw [show ((64 + 32 + 31) / 32 = 3) by native_decide]
    exact max_eq_left haw3
  dsimp [auctionSettleAuctionDynMload64Aw]
  rw [UInt256.toNat_ofNat_of_lt (by rw [hM]; exact aw.val.isLt), hM]

theorem auctionSettleAuctionDynDepositAw_bounds_of_mload
    {mem : ByteArray} {aw ptr : UInt256}
    (hload : auctionSettleAuctionDynMload64 mem aw = ptr)
    (haw3 : 3 ≤ aw.toNat) (hawMul : aw.toNat * 32 < UInt256.size)
    (hptr : ptr.toNat + 63 < UInt256.size) :
    3 ≤ (auctionSettleAuctionDynDepositAw mem aw).toNat ∧
      (auctionSettleAuctionDynDepositAw mem aw).toNat * 32 < UInt256.size := by
  have hawFreeEq := auctionSettleAuctionDynMload64Aw_eq_of_bounds (aw := aw) haw3
  let ceilW := (ptr.toNat + 32 + 31) / 32
  have hceilLt : ceilW < UInt256.size := by
    have hceilLe : ceilW ≤ ptr.toNat + 32 + 31 := Nat.div_le_self _ _
    norm_num [ceilW] at hptr ⊢
    omega
  have hceilMulLt : ceilW * 32 < UInt256.size := by
    have hceilLe : ceilW * 32 ≤ ptr.toNat + 32 + 31 := Nat.div_mul_le_self _ _
    norm_num [ceilW] at hptr ⊢
    omega
  have hMlt : MachineState.M aw.toNat ptr.toNat 32 < UInt256.size := by
    dsimp [MachineState.M]
    change max aw.toNat ((ptr.toNat + 32 + 31) / 32) < UInt256.size
    apply max_lt
    · exact aw.val.isLt
    · exact hceilLt
  have hawNat :
      (auctionSettleAuctionDynDepositAw mem aw).toNat =
        MachineState.M aw.toNat ptr.toNat 32 := by
    dsimp [auctionSettleAuctionDynDepositAw]
    rw [hload, hawFreeEq]
    exact UInt256.toNat_ofNat_of_lt hMlt
  constructor
  · rw [hawNat]
    dsimp [MachineState.M]
    change 3 ≤ max aw.toNat ((ptr.toNat + 32 + 31) / 32)
    exact le_trans haw3 (Nat.le_max_left _ _)
  · rw [hawNat]
    dsimp [MachineState.M]
    change max aw.toNat ((ptr.toNat + 32 + 31) / 32) * 32 < UInt256.size
    rw [Nat.mul_comm, mul_max, Nat.mul_comm 32 aw.toNat,
      Nat.mul_comm 32 ((ptr.toNat + 32 + 31) / 32)]
    apply max_lt
    · exact hawMul
    · exact hceilMulLt

theorem auctionSettleAuctionDynDepositAw_cover_of_mload
    {mem : ByteArray} {aw ptr : UInt256}
    (hload : auctionSettleAuctionDynMload64 mem aw = ptr)
    (haw3 : 3 ≤ aw.toNat) (hptr : ptr.toNat + 63 < UInt256.size) :
    ptr.toNat + 32 ≤ 32 * (auctionSettleAuctionDynDepositAw mem aw).toNat := by
  have hawFreeEq := auctionSettleAuctionDynMload64Aw_eq_of_bounds (aw := aw) haw3
  let ceilW := (ptr.toNat + 32 + 31) / 32
  have hceilLt : ceilW < UInt256.size := by
    have hceilLe : ceilW ≤ ptr.toNat + 32 + 31 := Nat.div_le_self _ _
    norm_num [ceilW] at hptr ⊢
    omega
  have hMlt : MachineState.M aw.toNat ptr.toNat 32 < UInt256.size := by
    dsimp [MachineState.M]
    change max aw.toNat ((ptr.toNat + 32 + 31) / 32) < UInt256.size
    apply max_lt
    · exact aw.val.isLt
    · exact hceilLt
  have hawNat :
      (auctionSettleAuctionDynDepositAw mem aw).toNat =
        MachineState.M aw.toNat ptr.toNat 32 := by
    dsimp [auctionSettleAuctionDynDepositAw]
    rw [hload, hawFreeEq]
    exact UInt256.toNat_ofNat_of_lt hMlt
  rw [hawNat]
  simpa [Nat.mul_comm] using
    auctionMachineState_M_pos_offset_len_le_words_mul (s := aw.toNat)
      (f := ptr.toNat) (l := 32) (by omega)

theorem auctionSettleAuctionDynDepositCallAw_eq_afterMload64_of_mload
    {mem : ByteArray} {aw ptr : UInt256}
    (hload : auctionSettleAuctionDynMload64 mem aw = ptr)
    (haw3 : 3 ≤ aw.toNat) (hawMul : aw.toNat * 32 < UInt256.size)
    (hptr : ptr.toNat + 63 < UInt256.size) :
    auctionSettleAuctionDynDepositCallAw mem aw =
      auctionSettleAuctionDynDepositAwAfterMload64 mem aw := by
  have hawDeposit :=
    auctionSettleAuctionDynDepositAw_bounds_of_mload
      (mem := mem) (aw := aw) (ptr := ptr) hload haw3 hawMul hptr
  have hcover :=
    auctionSettleAuctionDynDepositAw_cover_of_mload
      (mem := mem) (aw := aw) (ptr := ptr) hload haw3 hptr
  have hawAfterEq :
      auctionSettleAuctionDynDepositAwAfterMload64 mem aw =
        auctionSettleAuctionDynDepositAw mem aw := by
    simpa [auctionSettleAuctionDynDepositAwAfterMload64,
      auctionSettleAuctionDynMload64Aw] using
      auctionSettleAuctionDynMload64Aw_eq_of_bounds
        (aw := auctionSettleAuctionDynDepositAw mem aw) hawDeposit.1
  have hcoverAfter :
      ptr.toNat + 4 ≤
        32 * (auctionSettleAuctionDynDepositAwAfterMload64 mem aw).toNat := by
    rw [hawAfterEq]
    omega
  have hM4 :
      MachineState.M (auctionSettleAuctionDynDepositAwAfterMload64 mem aw).toNat
          ptr.toNat 4 =
        (auctionSettleAuctionDynDepositAwAfterMload64 mem aw).toNat := by
    exact auctionMachineState_M_inBounds hcoverAfter
  have hM0 :
      MachineState.M
          (MachineState.M (auctionSettleAuctionDynDepositAwAfterMload64 mem aw).toNat
            ptr.toNat 4)
          ptr.toNat 0 =
        (auctionSettleAuctionDynDepositAwAfterMload64 mem aw).toNat := by
    rw [hM4]
    simp [MachineState.M]
  unfold auctionSettleAuctionDynDepositCallAw
  rw [hload, hM0]
  exact u256_ofNat_toNat _

theorem auctionSettleAuctionDynTransferAw_bounds
    {aw freePtr : UInt256}
    (haw3 : 3 ≤ aw.toNat) (hawMul : aw.toNat * 32 < UInt256.size)
    (hptr : freePtr.toNat + 99 < UInt256.size) :
    3 ≤ (auctionSettleAuctionDynTransferAw aw freePtr).toNat ∧
      (auctionSettleAuctionDynTransferAw aw freePtr).toNat * 32 < UInt256.size := by
  have hawFreeEq := auctionSettleAuctionDynMload64Aw_eq_of_bounds (aw := aw) haw3
  have hptr4 : (freePtr + (⟨4⟩ : UInt256)).toNat = freePtr.toNat + 4 := by
    rw [uadd_toNat, show ((⟨4⟩ : UInt256).toNat = 4) by decide]
    rw [show freePtr.toNat + 4 = 4 + freePtr.toNat by omega]
    exact Nat.mod_eq_of_lt (by omega)
  have hptr36 : (freePtr + (⟨36⟩ : UInt256)).toNat = freePtr.toNat + 36 := by
    rw [uadd_toNat, show ((⟨36⟩ : UInt256).toNat = 36) by decide]
    rw [show freePtr.toNat + 36 = 36 + freePtr.toNat by omega]
    exact Nat.mod_eq_of_lt (by omega)
  have hselWord :=
    auctionMachineState_M_word_bounds (s := aw.toNat) (f := freePtr.toNat)
      haw3 hawMul (by omega)
  have hselNat :
      (auctionSettleAuctionDynTransferSelAw aw freePtr).toNat =
        MachineState.M aw.toNat freePtr.toNat 32 := by
    dsimp [auctionSettleAuctionDynTransferSelAw]
    rw [hawFreeEq]
    exact UInt256.toNat_ofNat_of_lt hselWord.2.2.2
  have hselBounds :
      3 ≤ (auctionSettleAuctionDynTransferSelAw aw freePtr).toNat ∧
        (auctionSettleAuctionDynTransferSelAw aw freePtr).toNat * 32 <
          UInt256.size := by
    constructor
    · rw [hselNat]
      exact hselWord.1
    · rw [hselNat]
      exact hselWord.2.1
  have hargWord :=
    auctionMachineState_M_word_bounds
      (s := (auctionSettleAuctionDynTransferSelAw aw freePtr).toNat)
      (f := freePtr.toNat + 4)
      hselBounds.1 hselBounds.2 (by omega)
  have hargNat :
      (auctionSettleAuctionDynTransferArgAw aw freePtr).toNat =
        MachineState.M (auctionSettleAuctionDynTransferSelAw aw freePtr).toNat
          (freePtr.toNat + 4) 32 := by
    dsimp [auctionSettleAuctionDynTransferArgAw]
    rw [hptr4]
    exact UInt256.toNat_ofNat_of_lt hargWord.2.2.2
  have hargBounds :
      3 ≤ (auctionSettleAuctionDynTransferArgAw aw freePtr).toNat ∧
        (auctionSettleAuctionDynTransferArgAw aw freePtr).toNat * 32 <
          UInt256.size := by
    constructor
    · rw [hargNat]
      exact hargWord.1
    · rw [hargNat]
      exact hargWord.2.1
  have htransferWord :=
    auctionMachineState_M_word_bounds
      (s := (auctionSettleAuctionDynTransferArgAw aw freePtr).toNat)
      (f := freePtr.toNat + 36)
      hargBounds.1 hargBounds.2 (by omega)
  have htransferNat :
      (auctionSettleAuctionDynTransferAw aw freePtr).toNat =
        MachineState.M (auctionSettleAuctionDynTransferArgAw aw freePtr).toNat
          (freePtr.toNat + 36) 32 := by
    dsimp [auctionSettleAuctionDynTransferAw]
    rw [hptr36]
    exact UInt256.toNat_ofNat_of_lt htransferWord.2.2.2
  constructor
  · rw [htransferNat]
    exact htransferWord.1
  · rw [htransferNat]
    exact htransferWord.2.1

end Auction
