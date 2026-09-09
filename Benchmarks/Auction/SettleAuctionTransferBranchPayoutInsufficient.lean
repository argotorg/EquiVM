import Benchmarks.Auction.SettleAuctionTransferBranchDepth

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Auction

theorem transferBranchPayoutLoopDynMload64Aw14
    (noun amount start finish bidder settled : UInt256) :
    auctionSettleAuctionDynMload64
        (auctionSettleAuctionPayoutLoopMem noun amount start finish bidder settled)
        (UInt256.ofNat 14) =
      ⟨352⟩ := by
  unfold auctionSettleAuctionDynMload64
  apply mloadWordValue_of_readWithPadding
  · rw [auctionSettleAuctionPayoutLoopMem_size]
    decide
  · decide
  · unfold auctionSettleAuctionPayoutLoopMem
    rw [toByteArray_write_read_below_of_gap (⟨0⟩ : UInt256)
      (auctionSettleAuctionPayoutFreeMem noun amount start finish bidder settled)
      352 (⟨64⟩ : UInt256).toNat
      (by rw [auctionSettleAuctionPayoutFreeMem_size]; decide) (by decide)
      (by rw [auctionSettleAuctionPayoutFreeMem_size]; native_decide)]
    unfold auctionSettleAuctionPayoutFreeMem
    exact toByteArray_write_read_back_of_gap (⟨352⟩ : UInt256)
      (auctionSettleAuctionPayoutZeroLenMem noun amount start finish bidder settled) 64
      (by rw [auctionSettleAuctionPayoutZeroLenMem_size]; native_decide)

theorem transferBranchWethDepositDynMload64Aw14
    (noun amount start finish bidder settled : UInt256) :
    auctionSettleAuctionDynMload64
        (auctionSettleAuctionWethDepositMem noun amount start finish bidder settled)
        (UInt256.ofNat 14) =
      ⟨352⟩ := by
  unfold auctionSettleAuctionDynMload64
  apply mloadWordValue_of_readWithPadding
  · rw [auctionSettleAuctionWethDepositMem_size]
    decide
  · decide
  · unfold auctionSettleAuctionWethDepositMem
    rw [toByteArray_write_read_below_len_of_gap auctionSettleAuctionDepositSelectorShifted
      (auctionSettleAuctionPayoutLoopMem noun amount start finish bidder settled)
      352 (⟨64⟩ : UInt256).toNat 32
      (by rw [auctionSettleAuctionPayoutLoopMem_size]; decide)
      (by decide) (by decide) (by decide)
      (by rw [auctionSettleAuctionPayoutLoopMem_size]; native_decide)]
    unfold auctionSettleAuctionPayoutLoopMem
    rw [toByteArray_write_read_below_of_gap (⟨0⟩ : UInt256)
      (auctionSettleAuctionPayoutFreeMem noun amount start finish bidder settled)
      352 (⟨64⟩ : UInt256).toNat
      (by rw [auctionSettleAuctionPayoutFreeMem_size]; decide) (by decide)
      (by rw [auctionSettleAuctionPayoutFreeMem_size]; native_decide)]
    unfold auctionSettleAuctionPayoutFreeMem
    exact toByteArray_write_read_back_of_gap (⟨352⟩ : UInt256)
      (auctionSettleAuctionPayoutZeroLenMem noun amount start finish bidder settled) 64
      (by rw [auctionSettleAuctionPayoutZeroLenMem_size]; native_decide)

theorem transferBranchDynDepositMemLoopAw14
    (noun amount start finish bidder settled : UInt256) :
    auctionSettleAuctionDynDepositMem
        (auctionSettleAuctionPayoutLoopMem noun amount start finish bidder settled)
        (UInt256.ofNat 14) =
      auctionSettleAuctionWethDepositMem noun amount start finish bidder settled := by
  unfold auctionSettleAuctionDynDepositMem auctionSettleAuctionWethDepositMem
  rw [transferBranchPayoutLoopDynMload64Aw14 noun amount start finish bidder settled]
  rw [show (⟨352⟩ : UInt256).toNat = 352 by native_decide]

theorem transferBranchDynDepositAwLoopAw14
    (noun amount start finish bidder settled : UInt256) :
    auctionSettleAuctionDynDepositAw
        (auctionSettleAuctionPayoutLoopMem noun amount start finish bidder settled)
        (UInt256.ofNat 14) =
      UInt256.ofNat 14 := by
  unfold auctionSettleAuctionDynDepositAw
  rw [transferBranchPayoutLoopDynMload64Aw14 noun amount start finish bidder settled]
  native_decide

theorem transferBranchDynDepositAwAfterMload64LoopAw14
    (noun amount start finish bidder settled : UInt256) :
    auctionSettleAuctionDynDepositAwAfterMload64
        (auctionSettleAuctionPayoutLoopMem noun amount start finish bidder settled)
        (UInt256.ofNat 14) =
      UInt256.ofNat 14 := by
  unfold auctionSettleAuctionDynDepositAwAfterMload64
  rw [transferBranchDynDepositAwLoopAw14 noun amount start finish bidder settled]
  native_decide

theorem transferBranchPayoutLoopDynDepositFreeStableAw14
    (noun amount start finish bidder settled : UInt256) :
    auctionSettleAuctionDynMload64
        (auctionSettleAuctionDynDepositMem
          (auctionSettleAuctionPayoutLoopMem noun amount start finish bidder settled)
          (UInt256.ofNat 14))
        (auctionSettleAuctionDynDepositAw
          (auctionSettleAuctionPayoutLoopMem noun amount start finish bidder settled)
          (UInt256.ofNat 14)) =
      auctionSettleAuctionDynMload64
        (auctionSettleAuctionPayoutLoopMem noun amount start finish bidder settled)
        (UInt256.ofNat 14) := by
  rw [transferBranchDynDepositMemLoopAw14 noun amount start finish bidder settled]
  rw [transferBranchDynDepositAwLoopAw14 noun amount start finish bidder settled]
  rw [transferBranchWethDepositDynMload64Aw14 noun amount start finish bidder settled]
  rw [transferBranchPayoutLoopDynMload64Aw14 noun amount start finish bidder settled]

theorem transferBranchPayoutLoopDynDepositLenAw14
    (noun amount start finish bidder settled : UInt256) :
    UInt256.sub
        (⟨4⟩ +
          auctionSettleAuctionDynMload64
            (auctionSettleAuctionPayoutLoopMem noun amount start finish bidder settled)
            (UInt256.ofNat 14))
        (auctionSettleAuctionDynMload64
          (auctionSettleAuctionPayoutLoopMem noun amount start finish bidder settled)
          (UInt256.ofNat 14)) =
      ⟨4⟩ := by
  rw [transferBranchPayoutLoopDynMload64Aw14 noun amount start finish bidder settled]
  native_decide

theorem transferBranchTransferFromPayoutLoopDynMload64Aw14
    (noun amount start finish bidder settled caller : UInt256) :
    auctionSettleAuctionDynMload64
        (auctionSettleAuctionTransferFromPayoutLoopMem
          noun amount start finish bidder settled caller)
        (UInt256.ofNat 14) =
      ⟨352⟩ := by
  simpa [auctionSettleAuctionDynMload64] using
    auctionSettleAuctionTransferFromPayoutLoopMem_mload64
      noun amount start finish bidder settled caller

theorem transferBranchTransferFromPayoutLoopDynDepositAwAw14
    (noun amount start finish bidder settled caller : UInt256) :
    auctionSettleAuctionDynDepositAw
        (auctionSettleAuctionTransferFromPayoutLoopMem
          noun amount start finish bidder settled caller)
        (UInt256.ofNat 14) =
      UInt256.ofNat 14 := by
  unfold auctionSettleAuctionDynDepositAw auctionSettleAuctionDynMload64Aw
  rw [transferBranchTransferFromPayoutLoopDynMload64Aw14
    noun amount start finish bidder settled caller]
  native_decide

theorem transferBranchTransferFromPayoutLoopDynDepositFreeStableAw14
    (noun amount start finish bidder settled caller : UInt256) :
    auctionSettleAuctionDynMload64
        (auctionSettleAuctionDynDepositMem
          (auctionSettleAuctionTransferFromPayoutLoopMem
            noun amount start finish bidder settled caller)
          (UInt256.ofNat 14))
        (auctionSettleAuctionDynDepositAw
          (auctionSettleAuctionTransferFromPayoutLoopMem
            noun amount start finish bidder settled caller)
          (UInt256.ofNat 14)) =
      auctionSettleAuctionDynMload64
        (auctionSettleAuctionTransferFromPayoutLoopMem
          noun amount start finish bidder settled caller)
        (UInt256.ofNat 14) := by
  let memLoop :=
    auctionSettleAuctionTransferFromPayoutLoopMem
      noun amount start finish bidder settled caller
  have hbase :
      auctionSettleAuctionDynMload64 memLoop (UInt256.ofNat 14) = ⟨352⟩ := by
    simpa [memLoop] using
      transferBranchTransferFromPayoutLoopDynMload64Aw14
        noun amount start finish bidder settled caller
  have haw :
      auctionSettleAuctionDynDepositAw memLoop (UInt256.ofNat 14) =
        UInt256.ofNat 14 := by
    simpa [memLoop] using
      transferBranchTransferFromPayoutLoopDynDepositAwAw14
        noun amount start finish bidder settled caller
  have hread :
      (auctionSettleAuctionDynDepositMem memLoop (UInt256.ofNat 14)).readWithPadding
          (⟨64⟩ : UInt256).toNat 32 =
        memLoop.readWithPadding (⟨64⟩ : UInt256).toNat 32 := by
    dsimp [auctionSettleAuctionDynDepositMem]
    rw [hbase]
    exact write32_read_below
      (UInt256.toByteArray auctionSettleAuctionDepositSelectorShifted) memLoop
      352 (⟨64⟩ : UInt256).toNat
      (by rw [toByteArray_size])
      (by
        rw [auctionSettleAuctionTransferFromPayoutLoopMem_size]
        omega)
      (by native_decide)
  rw [hbase]
  unfold auctionSettleAuctionDynMload64
  rw [haw]
  have hsize :
      (auctionSettleAuctionDynDepositMem memLoop (UInt256.ofNat 14)).size = 420 := by
    dsimp [auctionSettleAuctionDynDepositMem]
    rw [hbase]
    exact toByteArray_write32_size_of_le memLoop
      auctionSettleAuctionDepositSelectorShifted 352 420 420
      (auctionSettleAuctionTransferFromPayoutLoopMem_size
        noun amount start finish bidder settled caller)
      (by
        rw [auctionSettleAuctionTransferFromPayoutLoopMem_size]
        omega)
      (by decide)
  rw [hsize]
  rw [if_neg (by
    show ¬((⟨64⟩ : UInt256).toNat ≥ 420 ∨
      (⟨64⟩ : UInt256) ≥ UInt256.ofNat 14 * ⟨32⟩)
    native_decide)]
  rw [hread]
  have hbaseRead :
      UInt256.ofNat
          (fromByteArrayBigEndian
            (memLoop.readWithPadding (⟨64⟩ : UInt256).toNat 32)) =
        ⟨352⟩ := by
    simpa [auctionSettleAuctionDynMload64, memLoop,
      auctionSettleAuctionTransferFromPayoutLoopMem_size] using
      auctionSettleAuctionTransferFromPayoutLoopMem_mload64
        noun amount start finish bidder settled caller
  exact hbaseRead

theorem transferBranchTransferFromPayoutLoopDynDepositLenAw14
    (noun amount start finish bidder settled caller : UInt256) :
    UInt256.sub
        (⟨4⟩ +
          auctionSettleAuctionDynMload64
            (auctionSettleAuctionTransferFromPayoutLoopMem
              noun amount start finish bidder settled caller)
            (UInt256.ofNat 14))
        (auctionSettleAuctionDynMload64
          (auctionSettleAuctionTransferFromPayoutLoopMem
            noun amount start finish bidder settled caller)
          (UInt256.ofNat 14)) =
      ⟨4⟩ := by
  rw [transferBranchTransferFromPayoutLoopDynMload64Aw14
    noun amount start finish bidder settled caller]
  native_decide

theorem transferBranchTransferFromPayoutLoopDynDepositGapAw14
    (noun amount start finish bidder settled caller : UInt256) :
    (auctionSettleAuctionDynMload64
        (auctionSettleAuctionTransferFromPayoutLoopMem
          noun amount start finish bidder settled caller)
        (UInt256.ofNat 14)).toNat -
      (auctionSettleAuctionTransferFromPayoutLoopMem
        noun amount start finish bidder settled caller).size <
    USize.size := by
  rw [transferBranchTransferFromPayoutLoopDynMload64Aw14]
  rw [auctionSettleAuctionTransferFromPayoutLoopMem_size]
  native_decide

theorem transferBranchTransferFromPayoutLoopDynDepositCallAwAw14
    (noun amount start finish bidder settled caller : UInt256) :
    auctionSettleAuctionDynDepositCallAw
        (auctionSettleAuctionTransferFromPayoutLoopMem
          noun amount start finish bidder settled caller)
        (UInt256.ofNat 14) =
      UInt256.ofNat 14 := by
  unfold auctionSettleAuctionDynDepositCallAw auctionSettleAuctionDynDepositAwAfterMload64
  rw [transferBranchTransferFromPayoutLoopDynMload64Aw14]
  rw [transferBranchTransferFromPayoutLoopDynDepositAwAw14]
  native_decide

theorem transferBranchTransferFromPayoutLoopDynDepositCallFreeStableAw14
    (noun amount start finish bidder settled caller : UInt256) :
    auctionSettleAuctionDynMload64
        (auctionSettleAuctionDynDepositMem
          (auctionSettleAuctionTransferFromPayoutLoopMem
            noun amount start finish bidder settled caller)
          (UInt256.ofNat 14))
        (auctionSettleAuctionDynDepositCallAw
          (auctionSettleAuctionTransferFromPayoutLoopMem
            noun amount start finish bidder settled caller)
          (UInt256.ofNat 14)) =
      auctionSettleAuctionDynMload64
        (auctionSettleAuctionTransferFromPayoutLoopMem
          noun amount start finish bidder settled caller)
        (UInt256.ofNat 14) := by
  rw [transferBranchTransferFromPayoutLoopDynDepositCallAwAw14]
  simpa [transferBranchTransferFromPayoutLoopDynDepositAwAw14]
    using transferBranchTransferFromPayoutLoopDynDepositFreeStableAw14
      noun amount start finish bidder settled caller

noncomputable def auctionSettleAuctionTransferFromPayoutNonemptyMemFree
    (noun amount start finish bidder settled caller : UInt256) (o : ByteArray) :
    ByteArray :=
  (UInt256.toByteArray (auctionSettleAuctionPayoutNonemptyNewFree o)).write 0
    (auctionSettleAuctionTransferFromPayoutLoopMem noun amount start finish bidder
      settled caller) 64 32

noncomputable def auctionSettleAuctionTransferFromPayoutNonemptyMemLen
    (noun amount start finish bidder settled caller : UInt256) (o : ByteArray) :
    ByteArray :=
  (UInt256.toByteArray (auctionSettleAuctionPayoutNonemptyOszWord o)).write 0
    (auctionSettleAuctionTransferFromPayoutNonemptyMemFree noun amount start finish
      bidder settled caller o) 352 32

noncomputable def auctionSettleAuctionTransferFromPayoutNonemptyMemCopy
    (noun amount start finish bidder settled caller : UInt256) (o : ByteArray) :
    ByteArray :=
  o.write 0
    (auctionSettleAuctionTransferFromPayoutNonemptyMemLen noun amount start finish
      bidder settled caller o) 384 (auctionSettleAuctionPayoutNonemptyOszWord o).toNat

def auctionSettleAuctionTransferFromPayoutNonemptyAwCopy (o : ByteArray) :
    UInt256 :=
  UInt256.ofNat
    (MachineState.M (UInt256.ofNat 14).toNat 384
      (auctionSettleAuctionPayoutNonemptyOszWord o).toNat)

theorem auctionSettleAuctionTransferFromPayoutNonemptyAwCopy_bounds {o : ByteArray}
    (hosmall : o.size < 2 ^ 138) :
    3 ≤ (auctionSettleAuctionTransferFromPayoutNonemptyAwCopy o).toNat ∧
      (auctionSettleAuctionTransferFromPayoutNonemptyAwCopy o).toNat * 32 <
        UInt256.size := by
  let len := (auctionSettleAuctionPayoutNonemptyOszWord o).toNat
  have hlen : len = o.size := by
    dsimp [len, auctionSettleAuctionPayoutNonemptyOszWord]
    exact UInt256.toNat_ofNat_of_lt (by
      norm_num [UInt256.size] at hosmall ⊢
      omega)
  have hMlt : MachineState.M (UInt256.ofNat 14).toNat 384 len < UInt256.size := by
    dsimp [MachineState.M]
    rw [show (UInt256.ofNat 14).toNat = 14 by native_decide]
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
      (auctionSettleAuctionTransferFromPayoutNonemptyAwCopy o).toNat =
        MachineState.M (UInt256.ofNat 14).toNat 384 len := by
    dsimp [auctionSettleAuctionTransferFromPayoutNonemptyAwCopy, len]
    exact UInt256.toNat_ofNat_of_lt hMlt
  constructor
  · rw [hawNat]
    dsimp [MachineState.M]
    rw [show (UInt256.ofNat 14).toNat = 14 by native_decide]
    cases hcase : len with
    | zero =>
      simp [hcase]
    | succ n =>
      simp [hcase]
  · rw [hawNat]
    dsimp [MachineState.M]
    rw [show (UInt256.ofNat 14).toNat = 14 by native_decide]
    cases hcase : len with
    | zero =>
      simp [hcase]
      norm_num [UInt256.size]
    | succ n =>
      simp [hcase]
      rw [Nat.mul_comm, mul_max, Nat.mul_comm 32 14,
        Nat.mul_comm 32 ((384 + (n + 1) + 31) / 32)]
      have hceilMulLt' : ((384 + (n + 1) + 31) / 32) * 32 <
          UInt256.size := by
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

theorem auctionSettleAuctionTransferFromPayoutNonemptyMemCopy_mload64
    (noun amount start finish bidder settled caller : UInt256) {o : ByteArray}
    (hosmall : o.size < 2 ^ 138) (hne : o.size ≠ 0) :
    auctionSettleAuctionDynMload64
        (auctionSettleAuctionTransferFromPayoutNonemptyMemCopy noun amount start
          finish bidder settled caller o)
        (auctionSettleAuctionTransferFromPayoutNonemptyAwCopy o) =
      auctionSettleAuctionPayoutNonemptyNewFree o := by
  let memLoop :=
    auctionSettleAuctionTransferFromPayoutLoopMem noun amount start finish bidder
      settled caller
  let memFree :=
    auctionSettleAuctionTransferFromPayoutNonemptyMemFree noun amount start finish
      bidder settled caller o
  let memLen :=
    auctionSettleAuctionTransferFromPayoutNonemptyMemLen noun amount start finish
      bidder settled caller o
  let memCopy :=
    auctionSettleAuctionTransferFromPayoutNonemptyMemCopy noun amount start finish
      bidder settled caller o
  let oszWord := auctionSettleAuctionPayoutNonemptyOszWord o
  let newFree := auctionSettleAuctionPayoutNonemptyNewFree o
  have hmemLoopSize : memLoop.size = 420 := by
    simpa [memLoop] using
      auctionSettleAuctionTransferFromPayoutLoopMem_size noun amount start finish
        bidder settled caller
  have hmemFreeSize : memFree.size = 420 := by
    dsimp [memFree, auctionSettleAuctionTransferFromPayoutNonemptyMemFree,
      memLoop, newFree]
    exact toByteArray_write32_size_of_le
      (auctionSettleAuctionTransferFromPayoutLoopMem noun amount start finish bidder
        settled caller)
      (auctionSettleAuctionPayoutNonemptyNewFree o) 64 420 420
      (auctionSettleAuctionTransferFromPayoutLoopMem_size noun amount start finish
        bidder settled caller)
      (by rw [auctionSettleAuctionTransferFromPayoutLoopMem_size]; decide)
      (by decide)
  have hreadFree : memFree.readWithPadding 64 32 = UInt256.toByteArray newFree := by
    dsimp [memFree, auctionSettleAuctionTransferFromPayoutNonemptyMemFree,
      memLoop, newFree]
    exact toByteArray_write_read_back_of_gap
      (auctionSettleAuctionPayoutNonemptyNewFree o)
      (auctionSettleAuctionTransferFromPayoutLoopMem noun amount start finish bidder
        settled caller) 64
      (by
        rw [auctionSettleAuctionTransferFromPayoutLoopMem_size]
        native_decide)
  have hmemLenSize : memLen.size = 420 := by
    dsimp [memLen, auctionSettleAuctionTransferFromPayoutNonemptyMemLen, memFree,
      oszWord]
    exact toByteArray_write32_size_of_le
      (auctionSettleAuctionTransferFromPayoutNonemptyMemFree noun amount start
        finish bidder settled caller o)
      (auctionSettleAuctionPayoutNonemptyOszWord o) 352 420 420
      hmemFreeSize (by rw [hmemFreeSize]; decide) (by decide)
  have hreadLen : memLen.readWithPadding 64 32 = UInt256.toByteArray newFree := by
    have hpres := toByteArray_write_read_below_of_gap oszWord memFree 352 64
      (by rw [hmemFreeSize]; decide) (by decide)
      (by rw [hmemFreeSize]; native_decide)
    dsimp [memLen, auctionSettleAuctionTransferFromPayoutNonemptyMemLen, memFree,
      oszWord]
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
  have hsrc0 : 0 + oszWord.toNat ≤ o.size := by
    simpa using hsrc
  have hreadCopy : memCopy.readWithPadding 64 32 = UInt256.toByteArray newFree := by
    have hpres := write_read_below_gen_extend o memLen 384 oszWord.toNat 64
      hlenNe hsrc (by rw [hmemLenSize]; decide) (by decide)
    dsimp [memCopy, auctionSettleAuctionTransferFromPayoutNonemptyMemCopy, memLen,
      oszWord]
    rw [hpres]
    exact hreadLen
  have hmemCopySize : 64 < memCopy.size := by
    by_cases hin : 384 + oszWord.toNat ≤ memLen.size
    · have hwrite := write_eq_gen o memLen 384 oszWord.toNat hlenNe hsrc hin
      change 64 < (o.write 0 memLen 384 oszWord.toNat).size
      rw [hwrite, ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
        ByteArray.size_extract, ByteArray.size_extract]
      rw [hmemLenSize]
      omega
    · have hext : memLen.size < 384 + oszWord.toNat := Nat.lt_of_not_ge hin
      have hdest : 384 ≤ memLen.size := by
        rw [hmemLenSize]
        omega
      have hwrite := write_eq_gen_extend o memLen 384 oszWord.toNat hlenNe hsrc hdest hext
      change 64 < (o.write 0 memLen 384 oszWord.toNat).size
      rw [hwrite, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract]
      omega
  have haw := auctionSettleAuctionTransferFromPayoutNonemptyAwCopy_bounds
    (o := o) hosmall
  exact auctionSettleAuctionDynMload64_of_readWithPadding_of_aw hmemCopySize
    hreadCopy haw.1 haw.2

theorem auctionSettleAuctionTransferFromPayoutNonemptyMemCopy_size_ge
    (noun amount start finish bidder settled caller : UInt256) {o : ByteArray}
    (hosmall : o.size < 2 ^ 138) (hne : o.size ≠ 0) :
    384 + o.size ≤
      (auctionSettleAuctionTransferFromPayoutNonemptyMemCopy noun amount start
        finish bidder settled caller o).size := by
  let memLoop :=
    auctionSettleAuctionTransferFromPayoutLoopMem noun amount start finish bidder
      settled caller
  let memFree :=
    auctionSettleAuctionTransferFromPayoutNonemptyMemFree noun amount start finish
      bidder settled caller o
  let memLen :=
    auctionSettleAuctionTransferFromPayoutNonemptyMemLen noun amount start finish
      bidder settled caller o
  let oszWord := auctionSettleAuctionPayoutNonemptyOszWord o
  have hmemLoopSize : memLoop.size = 420 := by
    simpa [memLoop] using
      auctionSettleAuctionTransferFromPayoutLoopMem_size noun amount start finish
        bidder settled caller
  have hmemFreeSize : memFree.size = 420 := by
    dsimp [memFree, auctionSettleAuctionTransferFromPayoutNonemptyMemFree,
      memLoop]
    exact toByteArray_write32_size_of_le
      (auctionSettleAuctionTransferFromPayoutLoopMem noun amount start finish bidder
        settled caller)
      (auctionSettleAuctionPayoutNonemptyNewFree o) 64 420 420
      (auctionSettleAuctionTransferFromPayoutLoopMem_size noun amount start finish
        bidder settled caller)
      (by rw [auctionSettleAuctionTransferFromPayoutLoopMem_size]; decide)
      (by decide)
  have hmemLenSize : memLen.size = 420 := by
    dsimp [memLen, auctionSettleAuctionTransferFromPayoutNonemptyMemLen, memFree,
      oszWord]
    exact toByteArray_write32_size_of_le
      (auctionSettleAuctionTransferFromPayoutNonemptyMemFree noun amount start
        finish bidder settled caller o)
      (auctionSettleAuctionPayoutNonemptyOszWord o) 352 420 420
      hmemFreeSize (by rw [hmemFreeSize]; decide) (by decide)
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
  dsimp [auctionSettleAuctionTransferFromPayoutNonemptyMemCopy, memLen, oszWord]
  by_cases hin : 384 + oszWord.toNat ≤ memLen.size
  · have hwrite := write_eq_gen o memLen 384 oszWord.toNat hlenNe hsrc hin
    rw [hwrite, ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract]
    rw [hoszNat]
    omega
  · have hext : memLen.size < 384 + oszWord.toNat := Nat.lt_of_not_ge hin
    have hdest : 384 ≤ memLen.size := by
      rw [hmemLenSize]
      omega
    have hwrite := write_eq_gen_extend o memLen 384 oszWord.toNat hlenNe hsrc hdest hext
    rw [hwrite, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract]
    rw [hoszNat]
    omega

theorem auctionSettleAuctionTransferFromPayoutNonemptyMemCopy_read64
    (noun amount start finish bidder settled caller : UInt256) {o : ByteArray}
    (hosmall : o.size < 2 ^ 138) (hne : o.size ≠ 0) :
    (auctionSettleAuctionTransferFromPayoutNonemptyMemCopy noun amount start
        finish bidder settled caller o).readWithPadding 64 32 =
      UInt256.toByteArray (auctionSettleAuctionPayoutNonemptyNewFree o) := by
  let memLoop :=
    auctionSettleAuctionTransferFromPayoutLoopMem noun amount start finish bidder
      settled caller
  let memFree :=
    auctionSettleAuctionTransferFromPayoutNonemptyMemFree noun amount start finish
      bidder settled caller o
  let memLen :=
    auctionSettleAuctionTransferFromPayoutNonemptyMemLen noun amount start finish
      bidder settled caller o
  let memCopy :=
    auctionSettleAuctionTransferFromPayoutNonemptyMemCopy noun amount start finish
      bidder settled caller o
  let oszWord := auctionSettleAuctionPayoutNonemptyOszWord o
  let newFree := auctionSettleAuctionPayoutNonemptyNewFree o
  have hmemFreeSize : memFree.size = 420 := by
    dsimp [memFree, auctionSettleAuctionTransferFromPayoutNonemptyMemFree,
      memLoop, newFree]
    exact toByteArray_write32_size_of_le
      (auctionSettleAuctionTransferFromPayoutLoopMem noun amount start finish bidder
        settled caller)
      (auctionSettleAuctionPayoutNonemptyNewFree o) 64 420 420
      (auctionSettleAuctionTransferFromPayoutLoopMem_size noun amount start finish
        bidder settled caller)
      (by rw [auctionSettleAuctionTransferFromPayoutLoopMem_size]; decide)
      (by decide)
  have hreadFree : memFree.readWithPadding 64 32 = UInt256.toByteArray newFree := by
    dsimp [memFree, auctionSettleAuctionTransferFromPayoutNonemptyMemFree,
      memLoop, newFree]
    exact toByteArray_write_read_back_of_gap
      (auctionSettleAuctionPayoutNonemptyNewFree o)
      (auctionSettleAuctionTransferFromPayoutLoopMem noun amount start finish bidder
        settled caller) 64
      (by
        rw [auctionSettleAuctionTransferFromPayoutLoopMem_size]
        native_decide)
  have hmemLenSize : memLen.size = 420 := by
    dsimp [memLen, auctionSettleAuctionTransferFromPayoutNonemptyMemLen, memFree,
      oszWord]
    exact toByteArray_write32_size_of_le
      (auctionSettleAuctionTransferFromPayoutNonemptyMemFree noun amount start
        finish bidder settled caller o)
      (auctionSettleAuctionPayoutNonemptyOszWord o) 352 420 420
      hmemFreeSize (by rw [hmemFreeSize]; decide) (by decide)
  have hreadLen : memLen.readWithPadding 64 32 = UInt256.toByteArray newFree := by
    have hpres := toByteArray_write_read_below_of_gap oszWord memFree 352 64
      (by rw [hmemFreeSize]; decide) (by decide)
      (by rw [hmemFreeSize]; native_decide)
    dsimp [memLen, auctionSettleAuctionTransferFromPayoutNonemptyMemLen, memFree,
      oszWord]
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
    hlenNe hsrc (by rw [hmemLenSize]; decide) (by decide)
  dsimp [memCopy, auctionSettleAuctionTransferFromPayoutNonemptyMemCopy, memLen,
    oszWord]
  rw [hpres]
  exact hreadLen

theorem auctionSettleAuctionTransferFromPayoutNonemptyNewFree_memCopy_gap
    (noun amount start finish bidder settled caller : UInt256) {o : ByteArray}
    (hosmall : o.size < 2 ^ 138) (hne : o.size ≠ 0) :
    (auctionSettleAuctionPayoutNonemptyNewFree o).toNat -
        (auctionSettleAuctionTransferFromPayoutNonemptyMemCopy noun amount start
          finish bidder settled caller o).size <
      USize.size := by
  have hroundLe := auctionSettleAuctionPayoutNonemptyRounded_toNat_le (o := o) hosmall
  have hmemSize :=
    auctionSettleAuctionTransferFromPayoutNonemptyMemCopy_size_ge
      noun amount start finish bidder settled caller hosmall hne
  rw [auctionSettleAuctionPayoutNonemptyNewFree_toNat (o := o) hosmall]
  have hU : 31 < USize.size := by native_decide
  omega

theorem auctionSettleAuctionTransferFromPayoutNonemptyDepositMem_read64
    (noun amount start finish bidder settled caller : UInt256) {o : ByteArray}
    (hosmall : o.size < 2 ^ 138) (hne : o.size ≠ 0) :
    (auctionSettleAuctionDynDepositMem
        (auctionSettleAuctionTransferFromPayoutNonemptyMemCopy noun amount start
          finish bidder settled caller o)
        (auctionSettleAuctionTransferFromPayoutNonemptyAwCopy o)).readWithPadding
        64 32 =
      UInt256.toByteArray (auctionSettleAuctionPayoutNonemptyNewFree o) := by
  let memCopy :=
    auctionSettleAuctionTransferFromPayoutNonemptyMemCopy noun amount start finish
      bidder settled caller o
  let awCopy := auctionSettleAuctionTransferFromPayoutNonemptyAwCopy o
  let newFree := auctionSettleAuctionPayoutNonemptyNewFree o
  have hmload :
      auctionSettleAuctionDynMload64 memCopy awCopy = newFree := by
    simpa [memCopy, awCopy, newFree] using
      auctionSettleAuctionTransferFromPayoutNonemptyMemCopy_mload64
        noun amount start finish bidder settled caller hosmall hne
  have hreadCopy : memCopy.readWithPadding 64 32 = UInt256.toByteArray newFree := by
    simpa [memCopy, newFree] using
      auctionSettleAuctionTransferFromPayoutNonemptyMemCopy_read64
        noun amount start finish bidder settled caller hosmall hne
  have hmemSizeGe : 384 + o.size ≤ memCopy.size := by
    simpa [memCopy] using
      auctionSettleAuctionTransferFromPayoutNonemptyMemCopy_size_ge
        noun amount start finish bidder settled caller hosmall hne
  have hgap : newFree.toNat - memCopy.size < USize.size := by
    simpa [memCopy, newFree] using
      auctionSettleAuctionTransferFromPayoutNonemptyNewFree_memCopy_gap
        noun amount start finish bidder settled caller hosmall hne
  have hnewFreeGe : 96 ≤ newFree.toNat := by
    simpa [newFree] using auctionSettleAuctionPayoutNonemptyNewFree_ge96 (o := o) hosmall
  have hpres := toByteArray_write_read_below_of_gap
    auctionSettleAuctionDepositSelectorShifted memCopy newFree.toNat 64
    (by omega) hnewFreeGe hgap
  dsimp [auctionSettleAuctionDynDepositMem]
  rw [hmload, hpres]
  exact hreadCopy

theorem auctionSettleAuctionTransferFromPayoutNonemptyDepositFreeStable
    (noun amount start finish bidder settled caller : UInt256) {o : ByteArray}
    (hosmall : o.size < 2 ^ 138) (hne : o.size ≠ 0) :
    auctionSettleAuctionDynMload64
        (auctionSettleAuctionDynDepositMem
          (auctionSettleAuctionTransferFromPayoutNonemptyMemCopy noun amount start
            finish bidder settled caller o)
          (auctionSettleAuctionTransferFromPayoutNonemptyAwCopy o))
        (auctionSettleAuctionDynDepositAw
          (auctionSettleAuctionTransferFromPayoutNonemptyMemCopy noun amount start
            finish bidder settled caller o)
          (auctionSettleAuctionTransferFromPayoutNonemptyAwCopy o)) =
      auctionSettleAuctionDynMload64
        (auctionSettleAuctionTransferFromPayoutNonemptyMemCopy noun amount start
          finish bidder settled caller o)
        (auctionSettleAuctionTransferFromPayoutNonemptyAwCopy o) := by
  let memCopy :=
    auctionSettleAuctionTransferFromPayoutNonemptyMemCopy noun amount start finish
      bidder settled caller o
  let awCopy := auctionSettleAuctionTransferFromPayoutNonemptyAwCopy o
  let newFree := auctionSettleAuctionPayoutNonemptyNewFree o
  have hmload :
      auctionSettleAuctionDynMload64 memCopy awCopy = newFree := by
    simpa [memCopy, awCopy, newFree] using
      auctionSettleAuctionTransferFromPayoutNonemptyMemCopy_mload64
        noun amount start finish bidder settled caller hosmall hne
  have hreadDeposit :
      (auctionSettleAuctionDynDepositMem memCopy awCopy).readWithPadding 64 32 =
        UInt256.toByteArray newFree := by
    simpa [memCopy, awCopy, newFree] using
      auctionSettleAuctionTransferFromPayoutNonemptyDepositMem_read64
        noun amount start finish bidder settled caller hosmall hne
  have hmemSizeGe : 384 + o.size ≤ memCopy.size := by
    simpa [memCopy] using
      auctionSettleAuctionTransferFromPayoutNonemptyMemCopy_size_ge
        noun amount start finish bidder settled caller hosmall hne
  have hgap : newFree.toNat - memCopy.size < USize.size := by
    simpa [memCopy, newFree] using
      auctionSettleAuctionTransferFromPayoutNonemptyNewFree_memCopy_gap
        noun amount start finish bidder settled caller hosmall hne
  have hnewFreeGe : 96 ≤ newFree.toNat := by
    simpa [newFree] using auctionSettleAuctionPayoutNonemptyNewFree_ge96 (o := o) hosmall
  have hdepositSize :
      64 < (auctionSettleAuctionDynDepositMem memCopy awCopy).size := by
    have hwrite :
        newFree.toNat + 32 ≤
          ((UInt256.toByteArray auctionSettleAuctionDepositSelectorShifted).write 0
            memCopy newFree.toNat 32).size :=
      toByteArray_write_size_ge_off_add32 auctionSettleAuctionDepositSelectorShifted memCopy
        newFree.toNat hgap
    dsimp [auctionSettleAuctionDynDepositMem]
    rw [hmload]
    omega
  have hawCopy := auctionSettleAuctionTransferFromPayoutNonemptyAwCopy_bounds (o := o) hosmall
  have hawDeposit :=
    auctionSettleAuctionDynDepositAw_bounds_of_mload
      (mem := memCopy) (aw := awCopy) (ptr := newFree) hmload hawCopy.1 hawCopy.2
      (auctionSettleAuctionPayoutNonemptyNewFree_add63_lt (o := o) hosmall)
  calc
    auctionSettleAuctionDynMload64
        (auctionSettleAuctionDynDepositMem memCopy awCopy)
        (auctionSettleAuctionDynDepositAw memCopy awCopy) = newFree := by
      exact auctionSettleAuctionDynMload64_of_readWithPadding_of_aw hdepositSize
        hreadDeposit hawDeposit.1 hawDeposit.2
    _ = auctionSettleAuctionDynMload64 memCopy awCopy := hmload.symm

theorem auctionSettleAuctionTransferFromPayoutNonemptyDepositCallFreeStable
    (noun amount start finish bidder settled caller : UInt256) {o : ByteArray}
    (hosmall : o.size < 2 ^ 138) (hne : o.size ≠ 0) :
    auctionSettleAuctionDynMload64
        (auctionSettleAuctionDynDepositMem
          (auctionSettleAuctionTransferFromPayoutNonemptyMemCopy noun amount start
            finish bidder settled caller o)
          (auctionSettleAuctionTransferFromPayoutNonemptyAwCopy o))
        (auctionSettleAuctionDynDepositCallAw
          (auctionSettleAuctionTransferFromPayoutNonemptyMemCopy noun amount start
            finish bidder settled caller o)
          (auctionSettleAuctionTransferFromPayoutNonemptyAwCopy o)) =
      auctionSettleAuctionDynMload64
        (auctionSettleAuctionTransferFromPayoutNonemptyMemCopy noun amount start
          finish bidder settled caller o)
        (auctionSettleAuctionTransferFromPayoutNonemptyAwCopy o) := by
  let memCopy :=
    auctionSettleAuctionTransferFromPayoutNonemptyMemCopy noun amount start finish
      bidder settled caller o
  let awCopy := auctionSettleAuctionTransferFromPayoutNonemptyAwCopy o
  let newFree := auctionSettleAuctionPayoutNonemptyNewFree o
  let memDeposit := auctionSettleAuctionDynDepositMem memCopy awCopy
  let awCall := auctionSettleAuctionDynDepositCallAw memCopy awCopy
  have hmload :
      auctionSettleAuctionDynMload64 memCopy awCopy = newFree := by
    simpa [memCopy, awCopy, newFree] using
      auctionSettleAuctionTransferFromPayoutNonemptyMemCopy_mload64
        noun amount start finish bidder settled caller hosmall hne
  have hreadDeposit : memDeposit.readWithPadding 64 32 = UInt256.toByteArray newFree := by
    simpa [memDeposit, memCopy, awCopy, newFree] using
      auctionSettleAuctionTransferFromPayoutNonemptyDepositMem_read64
        noun amount start finish bidder settled caller hosmall hne
  have hgap : newFree.toNat - memCopy.size < USize.size := by
    simpa [memCopy, newFree] using
      auctionSettleAuctionTransferFromPayoutNonemptyNewFree_memCopy_gap
        noun amount start finish bidder settled caller hosmall hne
  have hnewFreeGe : 96 ≤ newFree.toNat := by
    simpa [newFree] using auctionSettleAuctionPayoutNonemptyNewFree_ge96 (o := o) hosmall
  have hdepositSize : 64 < memDeposit.size := by
    have hwrite :
        newFree.toNat + 32 ≤
          ((UInt256.toByteArray auctionSettleAuctionDepositSelectorShifted).write 0
            memCopy newFree.toNat 32).size :=
      toByteArray_write_size_ge_off_add32 auctionSettleAuctionDepositSelectorShifted memCopy
        newFree.toNat hgap
    dsimp [memDeposit, auctionSettleAuctionDynDepositMem]
    rw [hmload]
    omega
  have hawCopy := auctionSettleAuctionTransferFromPayoutNonemptyAwCopy_bounds (o := o) hosmall
  have hptr := auctionSettleAuctionPayoutNonemptyNewFree_add63_lt (o := o) hosmall
  have hawDeposit :=
    auctionSettleAuctionDynDepositAw_bounds_of_mload
      (mem := memCopy) (aw := awCopy) (ptr := newFree) hmload hawCopy.1 hawCopy.2 hptr
  have hawAfterEq :
      auctionSettleAuctionDynDepositAwAfterMload64 memCopy awCopy =
        auctionSettleAuctionDynDepositAw memCopy awCopy := by
    simpa [auctionSettleAuctionDynDepositAwAfterMload64,
      auctionSettleAuctionDynMload64Aw] using
      auctionSettleAuctionDynMload64Aw_eq_of_bounds
        (aw := auctionSettleAuctionDynDepositAw memCopy awCopy) hawDeposit.1
  have hawCallEq :
      awCall = auctionSettleAuctionDynDepositAwAfterMload64 memCopy awCopy := by
    simpa [awCall] using
      auctionSettleAuctionDynDepositCallAw_eq_afterMload64_of_mload
        (mem := memCopy) (aw := awCopy) (ptr := newFree)
        hmload hawCopy.1 hawCopy.2 hptr
  have hawCall : 3 ≤ awCall.toNat ∧ awCall.toNat * 32 < UInt256.size := by
    rw [hawCallEq, hawAfterEq]
    exact hawDeposit
  calc
    auctionSettleAuctionDynMload64 memDeposit awCall = newFree := by
      exact auctionSettleAuctionDynMload64_of_readWithPadding_of_aw
        hdepositSize hreadDeposit hawCall.1 hawCall.2
    _ = auctionSettleAuctionDynMload64 memCopy awCopy := hmload.symm

theorem auctionSettleAuctionTransferFromPayoutNonemptyDepositLen
    (noun amount start finish bidder settled caller : UInt256) {o : ByteArray}
    (hosmall : o.size < 2 ^ 138) (hne : o.size ≠ 0) :
    UInt256.sub
        (⟨4⟩ +
          auctionSettleAuctionDynMload64
            (auctionSettleAuctionTransferFromPayoutNonemptyMemCopy noun amount start
              finish bidder settled caller o)
            (auctionSettleAuctionTransferFromPayoutNonemptyAwCopy o))
        (auctionSettleAuctionDynMload64
          (auctionSettleAuctionTransferFromPayoutNonemptyMemCopy noun amount start
            finish bidder settled caller o)
          (auctionSettleAuctionTransferFromPayoutNonemptyAwCopy o)) =
      ⟨4⟩ := by
  rw [auctionSettleAuctionTransferFromPayoutNonemptyMemCopy_mload64
    noun amount start finish bidder settled caller hosmall hne]
  exact u256_sub_lit4_add_cancel (by
    have h := auctionSettleAuctionPayoutNonemptyNewFree_add63_lt (o := o) hosmall
    omega)

theorem auctionSettleAuctionTransferFromPayoutNonemptyDepositEncode_eq
    (noun amount start finish bidder settled caller : UInt256) {o : ByteArray}
    (hosmall : o.size < 2 ^ 138) (hne : o.size ≠ 0) :
    auctionConfig.externalABI.encode? "deposit" [] =
      some ((auctionSettleAuctionDynDepositMem
          (auctionSettleAuctionTransferFromPayoutNonemptyMemCopy noun amount start
            finish bidder settled caller o)
          (auctionSettleAuctionTransferFromPayoutNonemptyAwCopy o)).readWithPadding
        (auctionSettleAuctionDynMload64
          (auctionSettleAuctionTransferFromPayoutNonemptyMemCopy noun amount start
            finish bidder settled caller o)
          (auctionSettleAuctionTransferFromPayoutNonemptyAwCopy o)).toNat 4) := by
  exact auctionSettleAuctionDynDepositEncode_eq
    (mem := auctionSettleAuctionTransferFromPayoutNonemptyMemCopy noun amount start
      finish bidder settled caller o)
    (aw := auctionSettleAuctionTransferFromPayoutNonemptyAwCopy o)
    (by
      rw [auctionSettleAuctionTransferFromPayoutNonemptyMemCopy_mload64
        noun amount start finish bidder settled caller hosmall hne]
      exact auctionSettleAuctionTransferFromPayoutNonemptyNewFree_memCopy_gap
        noun amount start finish bidder settled caller hosmall hne)

theorem auctionSettleAuctionTransferFromPayoutNonemptyTransferMem_read64
    (noun amount start finish bidder settled caller owner : UInt256) {o : ByteArray}
    (hosmall : o.size < 2 ^ 138) (hne : o.size ≠ 0) :
    (auctionSettleAuctionDynTransferMem
        (auctionSettleAuctionDynDepositMem
          (auctionSettleAuctionTransferFromPayoutNonemptyMemCopy noun amount start
            finish bidder settled caller o)
          (auctionSettleAuctionTransferFromPayoutNonemptyAwCopy o))
        (auctionSettleAuctionDynMload64
          (auctionSettleAuctionTransferFromPayoutNonemptyMemCopy noun amount start
            finish bidder settled caller o)
          (auctionSettleAuctionTransferFromPayoutNonemptyAwCopy o))
        amount owner).readWithPadding 64 32 =
      UInt256.toByteArray (auctionSettleAuctionPayoutNonemptyNewFree o) := by
  let memCopy :=
    auctionSettleAuctionTransferFromPayoutNonemptyMemCopy noun amount start finish
      bidder settled caller o
  let awCopy := auctionSettleAuctionTransferFromPayoutNonemptyAwCopy o
  let freePtr := auctionSettleAuctionDynMload64 memCopy awCopy
  let newFree := auctionSettleAuctionPayoutNonemptyNewFree o
  let memDeposit := auctionSettleAuctionDynDepositMem memCopy awCopy
  let memSel := auctionSettleAuctionDynTransferSelMem memDeposit freePtr
  let memArg := auctionSettleAuctionDynTransferArgMem memDeposit freePtr amount owner
  have hmload : auctionSettleAuctionDynMload64 memCopy awCopy = newFree := by
    simpa [memCopy, awCopy, newFree] using
      auctionSettleAuctionTransferFromPayoutNonemptyMemCopy_mload64
        noun amount start finish bidder settled caller hosmall hne
  have hreadDeposit : memDeposit.readWithPadding 64 32 = UInt256.toByteArray newFree := by
    simpa [memDeposit, memCopy, awCopy, newFree] using
      auctionSettleAuctionTransferFromPayoutNonemptyDepositMem_read64
        noun amount start finish bidder settled caller hosmall hne
  have hgap : newFree.toNat - memCopy.size < USize.size := by
    simpa [memCopy, newFree] using
      auctionSettleAuctionTransferFromPayoutNonemptyNewFree_memCopy_gap
        noun amount start finish bidder settled caller hosmall hne
  have hnewFreeGe : 96 ≤ newFree.toNat := by
    simpa [newFree] using auctionSettleAuctionPayoutNonemptyNewFree_ge96 (o := o) hosmall
  have hnewFree99 : newFree.toNat + 99 < UInt256.size := by
    simpa [newFree] using auctionSettleAuctionPayoutNonemptyNewFree_add99_lt (o := o) hosmall
  have hdepositSize : newFree.toNat + 32 ≤ memDeposit.size := by
    have hwrite :
        newFree.toNat + 32 ≤
          ((UInt256.toByteArray auctionSettleAuctionDepositSelectorShifted).write 0
            memCopy newFree.toNat 32).size :=
      toByteArray_write_size_ge_off_add32 auctionSettleAuctionDepositSelectorShifted memCopy
        newFree.toNat hgap
    dsimp [memDeposit, auctionSettleAuctionDynDepositMem, memCopy, awCopy]
    rw [hmload]
    exact hwrite
  have hreadSel : memSel.readWithPadding 64 32 = UInt256.toByteArray newFree := by
    have hpres := toByteArray_write_read_below_of_gap
      auctionSettleAuctionTransferSelectorShifted memDeposit newFree.toNat 64
      (by omega) hnewFreeGe (by omega)
    dsimp [memSel, auctionSettleAuctionDynTransferSelMem, freePtr]
    rw [hmload, hpres]
    exact hreadDeposit
  have hmemSelSize : newFree.toNat + 32 ≤ memSel.size := by
    have hwrite :
        newFree.toNat + 32 ≤
          ((UInt256.toByteArray auctionSettleAuctionTransferSelectorShifted).write 0
            memDeposit newFree.toNat 32).size :=
      toByteArray_write_size_ge_off_add32 auctionSettleAuctionTransferSelectorShifted
        memDeposit newFree.toNat (by omega)
    dsimp [memSel, auctionSettleAuctionDynTransferSelMem, freePtr]
    rw [hmload]
    exact hwrite
  have hmemSelEq :
      auctionSettleAuctionDynTransferSelMem memDeposit newFree = memSel := by
    dsimp [memSel, freePtr]
    rw [hmload]
  have hptr4 : (newFree + (⟨4⟩ : UInt256)).toNat = newFree.toNat + 4 := by
    rw [uadd_toNat, show ((⟨4⟩ : UInt256).toNat = 4) by decide]
    rw [show newFree.toNat + 4 = 4 + newFree.toNat by omega]
    exact Nat.mod_eq_of_lt (by omega)
  have hreadArg : memArg.readWithPadding 64 32 = UInt256.toByteArray newFree := by
    have hpres := toByteArray_write_read_below_of_gap
      (UInt256.land solcAddrMask owner) memSel (newFree.toNat + 4) 64
      (by omega) (by omega) (by omega)
    dsimp [memArg, auctionSettleAuctionDynTransferArgMem, freePtr]
    rw [hmload, hptr4]
    rw [hmemSelEq]
    rw [hpres]
    exact hreadSel
  have hmemArgSize : newFree.toNat + 36 ≤ memArg.size := by
    have hwrite :
        newFree.toNat + 4 + 32 ≤
          ((UInt256.toByteArray (UInt256.land solcAddrMask owner)).write 0
            memSel (newFree.toNat + 4) 32).size :=
      toByteArray_write_size_ge_off_add32 (UInt256.land solcAddrMask owner)
        memSel (newFree.toNat + 4) (by omega)
    dsimp [memArg, auctionSettleAuctionDynTransferArgMem, freePtr]
    rw [hmload, hptr4]
    rw [hmemSelEq]
    omega
  have hmemArgEq :
      auctionSettleAuctionDynTransferArgMem memDeposit newFree amount owner = memArg := by
    dsimp [memArg, freePtr]
    rw [hmload]
  have hptr36 : (newFree + (⟨36⟩ : UInt256)).toNat = newFree.toNat + 36 := by
    rw [uadd_toNat, show ((⟨36⟩ : UInt256).toNat = 36) by decide]
    rw [show newFree.toNat + 36 = 36 + newFree.toNat by omega]
    exact Nat.mod_eq_of_lt (by omega)
  have hreadTransfer :
      (auctionSettleAuctionDynTransferMem memDeposit freePtr amount owner).readWithPadding
          64 32 =
        UInt256.toByteArray newFree := by
    have hpres := toByteArray_write_read_below_of_gap amount memArg
      (newFree.toNat + 36) 64 (by omega) (by omega) (by omega)
    dsimp [auctionSettleAuctionDynTransferMem, freePtr]
    rw [hmload, hptr36]
    rw [hmemArgEq]
    rw [hpres]
    exact hreadArg
  simpa [memDeposit, memCopy, awCopy, freePtr, newFree] using hreadTransfer

theorem auctionSettleAuctionTransferFromPayoutNonemptyTransferMem_size_ge
    (noun amount start finish bidder settled caller owner : UInt256) {o : ByteArray}
    (hosmall : o.size < 2 ^ 138) (hne : o.size ≠ 0) :
    (auctionSettleAuctionPayoutNonemptyNewFree o).toNat + 68 ≤
      (auctionSettleAuctionDynTransferMem
        (auctionSettleAuctionDynDepositMem
          (auctionSettleAuctionTransferFromPayoutNonemptyMemCopy noun amount start
            finish bidder settled caller o)
          (auctionSettleAuctionTransferFromPayoutNonemptyAwCopy o))
        (auctionSettleAuctionDynMload64
          (auctionSettleAuctionTransferFromPayoutNonemptyMemCopy noun amount start
            finish bidder settled caller o)
          (auctionSettleAuctionTransferFromPayoutNonemptyAwCopy o))
        amount owner).size := by
  let memCopy :=
    auctionSettleAuctionTransferFromPayoutNonemptyMemCopy noun amount start finish
      bidder settled caller o
  let awCopy := auctionSettleAuctionTransferFromPayoutNonemptyAwCopy o
  let freePtr := auctionSettleAuctionDynMload64 memCopy awCopy
  let newFree := auctionSettleAuctionPayoutNonemptyNewFree o
  let memDeposit := auctionSettleAuctionDynDepositMem memCopy awCopy
  let memSel := auctionSettleAuctionDynTransferSelMem memDeposit freePtr
  let memArg := auctionSettleAuctionDynTransferArgMem memDeposit freePtr amount owner
  have hmload : auctionSettleAuctionDynMload64 memCopy awCopy = newFree := by
    simpa [memCopy, awCopy, newFree] using
      auctionSettleAuctionTransferFromPayoutNonemptyMemCopy_mload64
        noun amount start finish bidder settled caller hosmall hne
  have hgap : newFree.toNat - memCopy.size < USize.size := by
    simpa [memCopy, newFree] using
      auctionSettleAuctionTransferFromPayoutNonemptyNewFree_memCopy_gap
        noun amount start finish bidder settled caller hosmall hne
  have hnewFree99 : newFree.toNat + 99 < UInt256.size := by
    simpa [newFree] using auctionSettleAuctionPayoutNonemptyNewFree_add99_lt (o := o) hosmall
  have hdepositSize : newFree.toNat + 32 ≤ memDeposit.size := by
    have hwrite :
        newFree.toNat + 32 ≤
          ((UInt256.toByteArray auctionSettleAuctionDepositSelectorShifted).write 0
            memCopy newFree.toNat 32).size :=
      toByteArray_write_size_ge_off_add32 auctionSettleAuctionDepositSelectorShifted memCopy
        newFree.toNat hgap
    dsimp [memDeposit, auctionSettleAuctionDynDepositMem, memCopy, awCopy]
    rw [hmload]
    exact hwrite
  have hmemSelSize : newFree.toNat + 32 ≤ memSel.size := by
    have hwrite :
        newFree.toNat + 32 ≤
          ((UInt256.toByteArray auctionSettleAuctionTransferSelectorShifted).write 0
            memDeposit newFree.toNat 32).size :=
      toByteArray_write_size_ge_off_add32 auctionSettleAuctionTransferSelectorShifted
        memDeposit newFree.toNat (by omega)
    dsimp [memSel, auctionSettleAuctionDynTransferSelMem, freePtr]
    rw [hmload]
    exact hwrite
  have hptr4 : (newFree + (⟨4⟩ : UInt256)).toNat = newFree.toNat + 4 := by
    rw [uadd_toNat, show ((⟨4⟩ : UInt256).toNat = 4) by decide]
    rw [show newFree.toNat + 4 = 4 + newFree.toNat by omega]
    exact Nat.mod_eq_of_lt (by omega)
  have hmemSelEq :
      auctionSettleAuctionDynTransferSelMem memDeposit newFree = memSel := by
    dsimp [memSel, freePtr]
    rw [hmload]
  have hmemArgSize : newFree.toNat + 36 ≤ memArg.size := by
    have hwrite :
        newFree.toNat + 4 + 32 ≤
          ((UInt256.toByteArray (UInt256.land solcAddrMask owner)).write 0
            memSel (newFree.toNat + 4) 32).size :=
      toByteArray_write_size_ge_off_add32 (UInt256.land solcAddrMask owner)
        memSel (newFree.toNat + 4) (by omega)
    dsimp [memArg, auctionSettleAuctionDynTransferArgMem, freePtr]
    rw [hmload, hptr4]
    rw [hmemSelEq]
    omega
  have hptr36 : (newFree + (⟨36⟩ : UInt256)).toNat = newFree.toNat + 36 := by
    rw [uadd_toNat, show ((⟨36⟩ : UInt256).toNat = 36) by decide]
    rw [show newFree.toNat + 36 = 36 + newFree.toNat by omega]
    exact Nat.mod_eq_of_lt (by omega)
  have hmemArgEq :
      auctionSettleAuctionDynTransferArgMem memDeposit newFree amount owner = memArg := by
    dsimp [memArg, freePtr]
    rw [hmload]
  have hwrite :
      newFree.toNat + 36 + 32 ≤
        ((UInt256.toByteArray amount).write 0 memArg (newFree.toNat + 36) 32).size :=
    toByteArray_write_size_ge_off_add32 amount memArg (newFree.toNat + 36) (by omega)
  dsimp [auctionSettleAuctionDynTransferMem, memDeposit, memCopy, awCopy, freePtr, newFree]
  rw [hmload, hptr36]
  rw [hmemArgEq]
  omega

theorem auctionSettleAuctionTransferFromPayoutNonemptyTransferFreeStable
    (noun amount start finish bidder settled caller owner : UInt256) {o : ByteArray}
    (hosmall : o.size < 2 ^ 138) (hne : o.size ≠ 0) :
    auctionSettleAuctionDynMload64
        (auctionSettleAuctionDynTransferMem
          (auctionSettleAuctionDynDepositMem
            (auctionSettleAuctionTransferFromPayoutNonemptyMemCopy noun amount start
              finish bidder settled caller o)
            (auctionSettleAuctionTransferFromPayoutNonemptyAwCopy o))
          (auctionSettleAuctionDynMload64
            (auctionSettleAuctionTransferFromPayoutNonemptyMemCopy noun amount start
              finish bidder settled caller o)
            (auctionSettleAuctionTransferFromPayoutNonemptyAwCopy o))
          amount owner)
        (auctionSettleAuctionDynTransferAw
          (auctionSettleAuctionDynDepositCallAw
            (auctionSettleAuctionTransferFromPayoutNonemptyMemCopy noun amount start
              finish bidder settled caller o)
            (auctionSettleAuctionTransferFromPayoutNonemptyAwCopy o))
          (auctionSettleAuctionDynMload64
            (auctionSettleAuctionTransferFromPayoutNonemptyMemCopy noun amount start
              finish bidder settled caller o)
            (auctionSettleAuctionTransferFromPayoutNonemptyAwCopy o))) =
      auctionSettleAuctionDynMload64
        (auctionSettleAuctionTransferFromPayoutNonemptyMemCopy noun amount start
          finish bidder settled caller o)
        (auctionSettleAuctionTransferFromPayoutNonemptyAwCopy o) := by
  let memCopy :=
    auctionSettleAuctionTransferFromPayoutNonemptyMemCopy noun amount start finish
      bidder settled caller o
  let awCopy := auctionSettleAuctionTransferFromPayoutNonemptyAwCopy o
  let freePtr := auctionSettleAuctionDynMload64 memCopy awCopy
  let newFree := auctionSettleAuctionPayoutNonemptyNewFree o
  let memDeposit := auctionSettleAuctionDynDepositMem memCopy awCopy
  let awCall := auctionSettleAuctionDynDepositCallAw memCopy awCopy
  let memTransfer := auctionSettleAuctionDynTransferMem memDeposit freePtr amount owner
  let awTransfer := auctionSettleAuctionDynTransferAw awCall freePtr
  have hmload : auctionSettleAuctionDynMload64 memCopy awCopy = newFree := by
    simpa [memCopy, awCopy, newFree] using
      auctionSettleAuctionTransferFromPayoutNonemptyMemCopy_mload64
        noun amount start finish bidder settled caller hosmall hne
  have hreadTransfer : memTransfer.readWithPadding 64 32 = UInt256.toByteArray newFree := by
    simpa [memTransfer, memDeposit, memCopy, awCopy, freePtr, newFree] using
      auctionSettleAuctionTransferFromPayoutNonemptyTransferMem_read64
        noun amount start finish bidder settled caller owner hosmall hne
  have hsizeGe : newFree.toNat + 68 ≤ memTransfer.size := by
    simpa [memTransfer, memDeposit, memCopy, awCopy, freePtr, newFree] using
      auctionSettleAuctionTransferFromPayoutNonemptyTransferMem_size_ge
        noun amount start finish bidder settled caller owner hosmall hne
  have hmemTransferSize : 64 < memTransfer.size := by
    omega
  have hawCopy := auctionSettleAuctionTransferFromPayoutNonemptyAwCopy_bounds (o := o) hosmall
  have hptr63 := auctionSettleAuctionPayoutNonemptyNewFree_add63_lt (o := o) hosmall
  have hptr99 : freePtr.toNat + 99 < UInt256.size := by
    dsimp [freePtr]
    rw [hmload]
    exact auctionSettleAuctionPayoutNonemptyNewFree_add99_lt (o := o) hosmall
  have hawDeposit :=
    auctionSettleAuctionDynDepositAw_bounds_of_mload
      (mem := memCopy) (aw := awCopy) (ptr := newFree)
      hmload hawCopy.1 hawCopy.2 hptr63
  have hawAfterEq :
      auctionSettleAuctionDynDepositAwAfterMload64 memCopy awCopy =
        auctionSettleAuctionDynDepositAw memCopy awCopy := by
    simpa [auctionSettleAuctionDynDepositAwAfterMload64,
      auctionSettleAuctionDynMload64Aw] using
      auctionSettleAuctionDynMload64Aw_eq_of_bounds
        (aw := auctionSettleAuctionDynDepositAw memCopy awCopy) hawDeposit.1
  have hawCallEq :
      awCall = auctionSettleAuctionDynDepositAwAfterMload64 memCopy awCopy := by
    simpa [awCall] using
      auctionSettleAuctionDynDepositCallAw_eq_afterMload64_of_mload
        (mem := memCopy) (aw := awCopy) (ptr := newFree)
        hmload hawCopy.1 hawCopy.2 hptr63
  have hawCall : 3 ≤ awCall.toNat ∧ awCall.toNat * 32 < UInt256.size := by
    rw [hawCallEq, hawAfterEq]
    exact hawDeposit
  have hawTransfer :=
    auctionSettleAuctionDynTransferAw_bounds
      (aw := awCall) (freePtr := freePtr) hawCall.1 hawCall.2 hptr99
  calc
    auctionSettleAuctionDynMload64 memTransfer awTransfer = newFree := by
      exact auctionSettleAuctionDynMload64_of_readWithPadding_of_aw
        hmemTransferSize hreadTransfer hawTransfer.1 hawTransfer.2
    _ = auctionSettleAuctionDynMload64 memCopy awCopy := hmload.symm

theorem auctionSettleAuctionTransferFromPayoutNonemptyTransferLen
    (noun amount start finish bidder settled caller : UInt256) {o : ByteArray}
    (hosmall : o.size < 2 ^ 138) (hne : o.size ≠ 0) :
    UInt256.sub
        (⟨68⟩ +
          auctionSettleAuctionDynMload64
            (auctionSettleAuctionTransferFromPayoutNonemptyMemCopy noun amount start
              finish bidder settled caller o)
            (auctionSettleAuctionTransferFromPayoutNonemptyAwCopy o))
        (auctionSettleAuctionDynMload64
          (auctionSettleAuctionTransferFromPayoutNonemptyMemCopy noun amount start
            finish bidder settled caller o)
          (auctionSettleAuctionTransferFromPayoutNonemptyAwCopy o)) =
      ⟨68⟩ := by
  rw [auctionSettleAuctionTransferFromPayoutNonemptyMemCopy_mload64
    noun amount start finish bidder settled caller hosmall hne]
  exact u256_sub_lit68_add_cancel (by
    have hroundLe := auctionSettleAuctionPayoutNonemptyRounded_toNat_le (o := o) hosmall
    rw [auctionSettleAuctionPayoutNonemptyNewFree_toNat (o := o) hosmall]
    norm_num [UInt256.size] at hosmall ⊢
    omega)

theorem auctionSettleAuctionTransferFromPayoutCallFailureNonemptyReturnToFallbackFixed
    {cA gh bl σ σ₀ A I}
    {g : Sat256} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {noun amount start finish bidder settled caller owner : UInt256}
    {o : ByteArray} {k C : ℕ}
    (hosz : o.size < UInt256.size)
    (hne : o.size ≠ 0)
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4828⟩
      [⟨0⟩, ⟨352⟩, amount, ⟨30000⟩, owner, ⟨0⟩, ⟨0⟩, amount, owner,
        ⟨3347⟩, amount, owner, ⟨4688⟩, ⟨128⟩, ⟨2471⟩, ⟨413⟩,
        auctionSelWord I]
      (auctionSettleAuctionTransferFromPayoutLoopMem noun amount start finish
        bidder settled caller)
      (UInt256.ofNat 14) o acc k C) :
    ∃ k' C', RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3347⟩
      [⟨0⟩, amount, owner, ⟨4688⟩, ⟨128⟩, ⟨2471⟩, ⟨413⟩,
        auctionSelWord I]
      (auctionSettleAuctionTransferFromPayoutNonemptyMemCopy noun amount start
        finish bidder settled caller o)
      (auctionSettleAuctionTransferFromPayoutNonemptyAwCopy o) o acc k' C' := by
  have hrd :=
    auctionSettleAuctionPayoutCallFailureNonemptyReturnToFallbackExact
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (acc := acc) (owner := owner) (amount := amount)
      (aw := UInt256.ofNat 14)
      (mem := auctionSettleAuctionTransferFromPayoutLoopMem noun amount start
        finish bidder settled caller)
      (o := o) hosz hne rd
  simpa [auctionSettleAuctionTransferFromPayoutLoopMem_mload64,
    auctionSettleAuctionTransferFromPayoutNonemptyMemCopy,
    auctionSettleAuctionTransferFromPayoutNonemptyMemLen,
    auctionSettleAuctionTransferFromPayoutNonemptyMemFree,
    auctionSettleAuctionTransferFromPayoutNonemptyAwCopy,
    auctionSettleAuctionPayoutNonemptyNewFree,
    auctionSettleAuctionPayoutNonemptyRounded,
    auctionSettleAuctionPayoutNonemptyOszWord] using hrd

theorem transferBranchPayoutInsufficientBalanceCase {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' σ'_solm : AccountMap}
    {A'_solm : Substate} {o memPay : ByteArray} {awPay : UInt256}
    {kFallback CFallback : ℕ}
    (_hcode : I.code = auctionBytecode)
    (_hperm : I.perm = true)
    (hdispatch : dispatchMsg auctionContract I.calldata = some settleAuctionTransition)
    (hdecode :
      decodeCalldataWithMode auctionConfig.abiDecodeMode
        (settleAuctionTransition.params.map Param.name)
        (transitionSignature settleAuctionTransition).paramTypes I.calldata = some ∅)
    (hwv : I.weiValue = ⟨0⟩)
    (hpausedSolm :
      let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      UInt256.land (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨51⟩)
          ⟨255⟩ ≠
        ⟨0⟩)
    (hstatusSolm :
      let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨101⟩ ≠ ⟨2⟩)
    (hstartSolm :
      let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩)
    (hsettledSolm :
      let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      auctionPackedSettledWord
          (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨211⟩) =
        ⟨0⟩)
    (htimeSolmLe :
      let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨210⟩).toNat ≤
        (UInt256.ofNat evmS.executionEnv.header.timestamp).toNat)
    (hbidderSolm :
      let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨211⟩)).toNat ≠
        AccountAddress.ofNat 0)
    (hnounsCodeSolmEval :
      let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      evalExpr? auctionConfig
          { contract := auctionContract,
            locals := auctionSettleAuctionSnapshotStore
              (auctionSettleAuctionEnterState evmS) }
          (auctionSettleAuctionMarkSettledState
            (auctionSettleAuctionEnterState evmS))
          (.binary .gt (.extCodeSize (.storage nounsRef)) (.intLit 0)) =
        .ok (.bool true))
    (hcallSolm :
      let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmEnter := auctionSettleAuctionEnterState evmS
      let evmMark := auctionSettleAuctionMarkSettledState evmEnter
      typedCallViaEVM auctionConfig evmMark
        (EVM.address (AccountAddress.ofNat
          ((UInt256.land
            (Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨201⟩)
            solcAddrMask).toNat))) "transferFrom" 0
        [.address evmEnter.executionEnv.codeOwner,
          .address (AccountAddress.ofNat
            (auctionPackedBidderWord
              (Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨211⟩)).toNat),
          .int (Int.ofNat
            (Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨207⟩).toNat)]
        (true,
          { evmMark with
              accountMap := σ'_solm
              substate := A'_solm
              createdAccounts := cA' },
          o) true)
    (hpostTf : accountMapEquiv σ' σ'_solm)
    (hamountEq :
      let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmEnter := auctionSettleAuctionEnterState evmS
      auctionAuctionAmountWord (auctionSettleAuctionEnterMap σ_evm I) I =
        auctionSettleAuctionAmount evmEnter)
    (hamountSolm :
      let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmEnter := auctionSettleAuctionEnterState evmS
      0 < (auctionSettleAuctionAmount evmEnter).toNat)
    (hdepth : I.depth.val < 1024)
    (hpayBalance :
      let amountWord := auctionAuctionAmountWord (auctionSettleAuctionEnterMap σ_evm I) I
      ¬ amountWord ≤ (σ'.find? I.codeOwner |>.elim ⟨0⟩ (·.balance)))
    (hfreeStable :
      auctionSettleAuctionDynMload64
          (auctionSettleAuctionDynDepositMem memPay awPay)
          (auctionSettleAuctionDynDepositAw memPay awPay) =
        auctionSettleAuctionDynMload64 memPay awPay)
    (hdepositLen :
      UInt256.sub (⟨4⟩ + auctionSettleAuctionDynMload64 memPay awPay)
          (auctionSettleAuctionDynMload64 memPay awPay) =
        ⟨4⟩)
    (hdepositGap :
      (auctionSettleAuctionDynMload64 memPay awPay).toNat - memPay.size < USize.size)
    (hrdFallback :
      let σ1 := auctionSettleAuctionEnterMap σ_evm I
      let amountWord := auctionAuctionAmountWord σ1 I
      let ownerWord := UInt256.land (auctionSlotWord ⟨151⟩ σ' I) solcAddrMask
      RD auctionBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3347⟩
        [⟨0⟩, amountWord, ownerWord, ⟨4688⟩, ⟨128⟩, ⟨2471⟩, ⟨413⟩,
          auctionSelWord I]
        memPay awPay ByteArray.empty (cA', σ') kFallback CFallback) :
    RuntimeCase (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) g := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmEnter := auctionSettleAuctionEnterState evmS
  let evmMark := auctionSettleAuctionMarkSettledState evmEnter
  let evmTf :=
    { evmMark with
      accountMap := σ'_solm,
      substate := A'_solm,
      createdAccounts := cA' }
  let amountWord := auctionAuctionAmountWord (auctionSettleAuctionEnterMap σ_evm I) I
  let ownerWord := UInt256.land (auctionSlotWord ⟨151⟩ σ' I) solcAddrMask
  have htfOwner : evmTf.executionEnv.codeOwner = I.codeOwner := by
    simp [evmTf, evmMark, evmEnter, evmS, auctionSettleAuctionMarkSettledState,
      auctionSettleAuctionEnterState, initState, storageStore_executionEnv]
  let payTarget := EVM.address (auctionOwnerAddressAt evmTf)
  let evmPay :=
    { evmTf with
      substate := (evmTf.addAccessedAccount payTarget).substate }
  have hbalanceEq :
      ((σ'.find? I.codeOwner).elim (⟨0⟩ : UInt256)
          (fun acc => acc.balance)) =
        ((σ'_solm.find? I.codeOwner).elim
          (⟨0⟩ : UInt256) (fun acc => acc.balance)) := by
    have hmap := hpostTf I.codeOwner
    cases hσ : σ'.find? I.codeOwner <;>
      cases hτ : σ'_solm.find? I.codeOwner <;>
      simp [hσ, hτ] at hmap ⊢
    exact hmap.2.1
  have hbalanceSolm :
      ¬ amountWord ≤
        (evmTf.accountMap.find? evmTf.executionEnv.codeOwner
          |>.elim ⟨0⟩ (·.balance)) := by
    intro hbal
    apply hpayBalance
    rw [hbalanceEq]
    simpa [evmTf, evmMark, evmEnter, evmS, amountWord,
      auctionSettleAuctionMarkSettledState, auctionSettleAuctionEnterState,
      initState, storageStore_executionEnv] using hbal
  have hbalancePaySolm :
      ¬ amountWord ≤
        (evmPay.accountMap.find? evmPay.executionEnv.codeOwner
          |>.elim ⟨0⟩ (·.balance)) := by
    simpa [evmPay] using hbalanceSolm
  have hpaySolm :
      callViaEVM evmTf payTarget
        (Int.ofNat (auctionSettleAuctionAmount evmEnter).toNat)
        ByteArray.empty (false, evmPay, ByteArray.empty) true := by
    rw [← hamountEq]
    apply callViaEVM.callNotMade
    · rfl
    · rfl
    · intro hmade
      have hmadeBalance := hmade.1
      rw [wordOfInt_ofNat_toNat amountWord] at hmadeBalance
      exact hbalanceSolm hmadeBalance
  have hpayOwner : evmPay.executionEnv.codeOwner = I.codeOwner := by
    simpa [evmPay] using htfOwner
  have hwethWordPayEqBase :
      UInt256.land
          (Solm.EVM.storageLoad evmPay
            evmPay.executionEnv.codeOwner ⟨202⟩)
          solcAddrMask =
        UInt256.land (auctionSlotWord ⟨202⟩ σ' I) solcAddrMask := by
    simpa using
      transferBranchWethWordAt
        (σ := σ') (τ := σ'_solm) (evm := evmPay) (I := I)
        hpostTf (by simp [evmPay, evmTf]) hpayOwner
  let nounWord := auctionAuctionNounWord (auctionSettleAuctionEnterMap σ_evm I) I
  let startWord := auctionAuctionStartWord (auctionSettleAuctionEnterMap σ_evm I) I
  let finishWord := auctionAuctionEndWord (auctionSettleAuctionEnterMap σ_evm I) I
  let bidderWord :=
    auctionPackedBidderWord (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ_evm I) I)
  let settledWord :=
    auctionPackedSettledEVMReturnWord
      (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ_evm I) I)
  let memLoop := memPay
  by_cases hwethCodeE :
      Reasoning.Theory.uniswapExtCodeSizeWord σ'
          (UInt256.land (auctionSlotWord ⟨202⟩ σ' I)
            solcAddrMask) ≠
        ⟨0⟩
  · obtain ⟨gasWord, kDep, CDep, hrdDepositCall⟩ :=
      auctionSettleAuctionPayoutFallbackToDepositCallAnyMem
        (mem := memLoop) (aw := awPay)
        hwethCodeE (by simpa [memLoop] using hfreeStable)
        (by simpa [memLoop] using hdepositLen)
        (by simpa [memLoop, amountWord, ownerWord] using hrdFallback)
    let memDeposit :=
      auctionSettleAuctionDynDepositMem memLoop awPay
    let wethWord :=
      UInt256.land (auctionSlotWord ⟨202⟩ σ' I) solcAddrMask
    obtain ⟨kAfterDep, CAfterDep, hrdAfterDepRaw⟩ :=
      RD.callValueInsufficientBalance hrdDepositCall _hperm
        (by native_decide)
        (by simpa [amountWord] using hpayBalance)
        hdepth
        (by
          change 12 ≤ 1024
          native_decide)
    have hmin :
        (min (⟨0⟩ : UInt256)
          (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
      native_decide
    let evmDeposit :=
      { evmPay with
        substate :=
          (evmPay.addAccessedAccount
            (AccountAddress.ofUInt256 wethWord)).substate }
    have hwethWordPayEq :
        UInt256.land
            (Solm.EVM.storageLoad evmPay
              evmPay.executionEnv.codeOwner ⟨202⟩)
            solcAddrMask =
          wethWord := by
      simpa [wethWord] using hwethWordPayEqBase
    have hdepositRawFalse :
        callViaEVM evmPay (AccountAddress.ofUInt256 wethWord)
          (Int.ofNat amountWord.toNat)
          (memDeposit.readWithPadding
            (auctionSettleAuctionDynMload64 memLoop awPay).toNat 4)
          (false, evmDeposit, ByteArray.empty) true := by
      apply callViaEVM.callNotMade
      · rfl
      · rfl
      · intro hmade
        have hmadeBalance := hmade.1
        rw [wordOfInt_ofNat_toNat amountWord] at hmadeBalance
        exact hbalancePaySolm hmadeBalance
    have hwethTarget :
        EVM.address (AccountAddress.ofNat
            ((UInt256.land
              (Solm.EVM.storageLoad evmPay
                evmPay.executionEnv.codeOwner ⟨202⟩)
              solcAddrMask).toNat)) =
          AccountAddress.ofUInt256 wethWord := by
      exact transferBranchWethTarget
        (σ := σ') (I := I) hwethWordPayEq (by simp [wethWord])
    have hwethCodeSolm :
        0 < (UInt256.ofNat (((evmPay.lookupAccount
          (AccountAddress.ofNat
            ((UInt256.land
              (Solm.EVM.storageLoad evmPay
                evmPay.executionEnv.codeOwner ⟨202⟩)
              solcAddrMask).toNat))).option 0
            (fun acc => acc.code.size)))).toNat := by
      exact transferBranchWethLookupCodePos
        (σ := σ') (τ := σ'_solm) (evm := evmPay)
        (wethWord := wethWord) hpostTf (by simp [evmPay, evmTf])
        hwethWordPayEq (by simpa [wethWord] using hwethCodeE)
    have hdeposit :
        typedCallViaEVM auctionConfig evmPay
          (EVM.address (AccountAddress.ofNat
            ((UInt256.land
              (Solm.EVM.storageLoad evmPay
                evmPay.executionEnv.codeOwner ⟨202⟩)
              solcAddrMask).toNat))) "deposit"
          (Int.ofNat
            (auctionSettleAuctionAmount evmEnter).toNat) []
          (false, evmDeposit, ByteArray.empty) true := by
      refine ⟨memDeposit.readWithPadding
        (auctionSettleAuctionDynMload64 memLoop awPay).toNat 4, ?_, ?_⟩
      · simpa [memLoop, memDeposit] using
          auctionSettleAuctionDynDepositEncode_eq
            (mem := memLoop) (aw := awPay)
            (by simpa [memLoop] using hdepositGap)
      · rw [hwethTarget, ← hamountEq]
        exact hdepositRawFalse
    have hrdDepositFailRev :
        RDrev auctionBytecode (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀
            (Sat256.ofUInt256 g) A I) := by
      exact auctionCallSuccessGuardMissingPush0
        (pc := ⟨3432⟩) (okPc := ⟨3446⟩)
        (status := ⟨0⟩)
        (R := [⟨4⟩ + auctionSettleAuctionDynMload64 memLoop awPay,
          amountWord, ⟨3504541104⟩, wethWord,
          amountWord, ownerWord, ⟨4688⟩, ⟨128⟩, ⟨2471⟩,
          ⟨413⟩, auctionSelWord I])
        (by
          have htmp := hrdAfterDepRaw
          rw [hmin, byteArray_write_len_zero] at htmp
          simpa [memLoop, memDeposit, amountWord, ownerWord, wethWord] using htmp)
        rfl
        (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)
        (by simp [UInt256.size])
        (by
          change 11 + 5 ≤ 1024
          native_decide)
    have hbody :
        ExecTransitionBody auctionConfig auctionContract evmS ∅
          settleAuctionTransition.body .reverted :=
      auctionSettleAuctionTransitionReverts_transferFromPayoutLowLevelFailureWethDepositFailure
        evmS evmTf evmPay evmDeposit
        (by simpa only [evmS, initState] using hwv) hpausedSolm
        hstatusSolm hstartSolm hsettledSolm htimeSolmLe
        hbidderSolm hnounsCodeSolmEval
        (by simpa [evmTf, evmMark, evmEnter] using hcallSolm)
        hamountSolm hpaySolm hwethCodeSolm hdeposit
    exact hrdDepositFailRev.reEquivExecutionRevert _hcode hdispatch hdecode hbody
  · let wethWord :=
        UInt256.land (auctionSlotWord ⟨202⟩ σ' I) solcAddrMask
    have hwethCodeZero :
        Reasoning.Theory.uniswapExtCodeSizeWord σ'
            (UInt256.land (auctionSlotWord ⟨202⟩ σ' I)
              solcAddrMask) =
          ⟨0⟩ := by
      by_contra hne
      exact hwethCodeE hne
    have hrdNoCodeRev :
        RDrev auctionBytecode (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀
            (Sat256.ofUInt256 g) A I) :=
      auctionSettleAuctionPayoutFallbackWethNoCodeRevertAnyMem
        hwethCodeZero hrdFallback
    have hwethWordPayEq :
        UInt256.land
            (Solm.EVM.storageLoad evmPay
              evmPay.executionEnv.codeOwner ⟨202⟩)
            solcAddrMask =
          wethWord := by
      simpa [wethWord] using hwethWordPayEqBase
    have hwethCodeSolm :
        (UInt256.ofNat (((evmPay.lookupAccount
          (AccountAddress.ofNat
            ((UInt256.land
              (Solm.EVM.storageLoad evmPay
                evmPay.executionEnv.codeOwner ⟨202⟩)
              solcAddrMask).toNat))).option 0
            (fun acc => acc.code.size)))).toNat = 0 := by
      exact transferBranchWethLookupCodeZero
        (σ := σ') (τ := σ'_solm) (evm := evmPay)
        (wethWord := wethWord) hpostTf (by simp [evmPay, evmTf])
        hwethWordPayEq (by simpa [wethWord] using hwethCodeZero)
    have hbody :
        ExecTransitionBody auctionConfig auctionContract evmS ∅
          settleAuctionTransition.body .reverted :=
      auctionSettleAuctionTransitionReverts_transferFromPayoutLowLevelFailureWethNoCode
        evmS evmTf evmPay
        (by simpa only [evmS, initState] using hwv) hpausedSolm
        hstatusSolm hstartSolm hsettledSolm htimeSolmLe
        hbidderSolm hnounsCodeSolmEval
        (by simpa [evmTf, evmMark, evmEnter] using hcallSolm)
        hamountSolm hpaySolm hwethCodeSolm
    exact hrdNoCodeRev.reEquivExecutionRevert _hcode hdispatch hdecode hbody

theorem transferBranchPayoutInsufficientBalanceFromCall {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' σ'_solm : AccountMap}
    {A'_solm : Substate} {o : ByteArray} {kPay CPay : ℕ}
    (_hcode : I.code = auctionBytecode)
    (_hperm : I.perm = true)
    (hdispatch : dispatchMsg auctionContract I.calldata = some settleAuctionTransition)
    (hdecode :
      decodeCalldataWithMode auctionConfig.abiDecodeMode
        (settleAuctionTransition.params.map Param.name)
        (transitionSignature settleAuctionTransition).paramTypes I.calldata = some ∅)
    (hwv : I.weiValue = ⟨0⟩)
    (hpausedSolm :
      let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      UInt256.land (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨51⟩)
          ⟨255⟩ ≠
        ⟨0⟩)
    (hstatusSolm :
      let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨101⟩ ≠ ⟨2⟩)
    (hstartSolm :
      let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩)
    (hsettledSolm :
      let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      auctionPackedSettledWord
          (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨211⟩) =
        ⟨0⟩)
    (htimeSolmLe :
      let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨210⟩).toNat ≤
        (UInt256.ofNat evmS.executionEnv.header.timestamp).toNat)
    (hbidderSolm :
      let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨211⟩)).toNat ≠
        AccountAddress.ofNat 0)
    (hnounsCodeSolmEval :
      let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      evalExpr? auctionConfig
          { contract := auctionContract,
            locals := auctionSettleAuctionSnapshotStore
              (auctionSettleAuctionEnterState evmS) }
          (auctionSettleAuctionMarkSettledState
            (auctionSettleAuctionEnterState evmS))
          (.binary .gt (.extCodeSize (.storage nounsRef)) (.intLit 0)) =
        .ok (.bool true))
    (hcallSolm :
      let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmEnter := auctionSettleAuctionEnterState evmS
      let evmMark := auctionSettleAuctionMarkSettledState evmEnter
      typedCallViaEVM auctionConfig evmMark
        (EVM.address (AccountAddress.ofNat
          ((UInt256.land
            (Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨201⟩)
            solcAddrMask).toNat))) "transferFrom" 0
        [.address evmEnter.executionEnv.codeOwner,
          .address (AccountAddress.ofNat
            (auctionPackedBidderWord
              (Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨211⟩)).toNat),
          .int (Int.ofNat
            (Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨207⟩).toNat)]
        (true,
          { evmMark with
              accountMap := σ'_solm
              substate := A'_solm
              createdAccounts := cA' },
          o) true)
    (hpostTf : accountMapEquiv σ' σ'_solm)
    (hamountEq :
      let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmEnter := auctionSettleAuctionEnterState evmS
      auctionAuctionAmountWord (auctionSettleAuctionEnterMap σ_evm I) I =
        auctionSettleAuctionAmount evmEnter)
    (hamountSolm :
      let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmEnter := auctionSettleAuctionEnterState evmS
      0 < (auctionSettleAuctionAmount evmEnter).toNat)
    (hdepth : I.depth.val < 1024)
    (hpayBalance :
      let amountWord := auctionAuctionAmountWord (auctionSettleAuctionEnterMap σ_evm I) I
      ¬ amountWord ≤ (σ'.find? I.codeOwner |>.elim ⟨0⟩ (·.balance)))
    (hrdPayCall :
      let amountWord := auctionAuctionAmountWord (auctionSettleAuctionEnterMap σ_evm I) I
      let ownerWord := UInt256.land (auctionSlotWord ⟨151⟩ σ' I) solcAddrMask
      RD auctionBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨4827⟩
        [⟨30000⟩, ownerWord, amountWord, ⟨352⟩, ⟨0⟩, ⟨352⟩,
          ⟨0⟩, ⟨352⟩, amountWord, ⟨30000⟩, ownerWord, ⟨0⟩, ⟨0⟩,
          amountWord, ownerWord, ⟨3347⟩, amountWord, ownerWord, ⟨4688⟩,
          ⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I]
        (auctionSettleAuctionTransferFromPayoutLoopMem
          (auctionAuctionNounWord (auctionSettleAuctionEnterMap σ_evm I) I)
          amountWord
          (auctionAuctionStartWord (auctionSettleAuctionEnterMap σ_evm I) I)
          (auctionAuctionEndWord (auctionSettleAuctionEnterMap σ_evm I) I)
          (auctionPackedBidderWord
            (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ_evm I) I))
          (auctionPackedSettledEVMReturnWord
            (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ_evm I) I))
          (UInt256.ofNat ↑I.codeOwner))
        (UInt256.ofNat 14) o (cA', σ') kPay CPay) :
    RuntimeCase (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) g := by
  let amountWord := auctionAuctionAmountWord (auctionSettleAuctionEnterMap σ_evm I) I
  let ownerWord := UInt256.land (auctionSlotWord ⟨151⟩ σ' I) solcAddrMask
  let nounWord := auctionAuctionNounWord (auctionSettleAuctionEnterMap σ_evm I) I
  let startWord := auctionAuctionStartWord (auctionSettleAuctionEnterMap σ_evm I) I
  let finishWord := auctionAuctionEndWord (auctionSettleAuctionEnterMap σ_evm I) I
  let bidderWord :=
    auctionPackedBidderWord (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ_evm I) I)
  let settledWord :=
    auctionPackedSettledEVMReturnWord
      (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ_evm I) I)
  let memPay :=
    auctionSettleAuctionTransferFromPayoutLoopMem nounWord amountWord startWord finishWord
      bidderWord settledWord (UInt256.ofNat ↑I.codeOwner)
  have hrdPayCall' :
      RD auctionBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨4827⟩
        [⟨30000⟩, ownerWord, amountWord, ⟨352⟩, ⟨0⟩, ⟨352⟩,
          ⟨0⟩, ⟨352⟩, amountWord, ⟨30000⟩, ownerWord, ⟨0⟩, ⟨0⟩,
          amountWord, ownerWord, ⟨3347⟩, amountWord, ownerWord, ⟨4688⟩,
          ⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I]
        memPay (UInt256.ofNat 14) o (cA', σ') kPay CPay := by
    simpa [memPay, nounWord, startWord, finishWord, bidderWord, settledWord,
      amountWord, ownerWord] using hrdPayCall
  obtain ⟨_, _, hrdAfterPayRaw⟩ :=
    RD.callValueInsufficientBalanceEmptyInOut hrdPayCall' _hperm
      (by native_decide)
      (by simpa [amountWord] using hpayBalance)
      hdepth
      (by
        change 17 ≤ 1024
        native_decide)
  have hawPay :
      UInt256.ofNat
          (MachineState.M
          (MachineState.M (UInt256.ofNat 14).toNat
            (⟨352⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat)
          (⟨352⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) =
        UInt256.ofNat 14 := by
    native_decide
  obtain ⟨kFallback, CFallback, hrdFallback⟩ :=
    auctionSettleAuctionPayoutCallFailureEmptyReturnToFallback
      rfl hrdAfterPayRaw
  rw [hawPay] at hrdFallback
  have hfreeStable :
      auctionSettleAuctionDynMload64
          (auctionSettleAuctionDynDepositMem memPay (UInt256.ofNat 14))
          (auctionSettleAuctionDynDepositAw memPay (UInt256.ofNat 14)) =
        auctionSettleAuctionDynMload64 memPay (UInt256.ofNat 14) := by
    simpa [memPay, nounWord, startWord, finishWord, bidderWord, settledWord] using
      transferBranchTransferFromPayoutLoopDynDepositFreeStableAw14
        nounWord amountWord startWord finishWord bidderWord settledWord
        (UInt256.ofNat ↑I.codeOwner)
  have hdepositLen :
      UInt256.sub
          (⟨4⟩ + auctionSettleAuctionDynMload64 memPay (UInt256.ofNat 14))
          (auctionSettleAuctionDynMload64 memPay (UInt256.ofNat 14)) =
        ⟨4⟩ := by
    simpa [memPay, nounWord, startWord, finishWord, bidderWord, settledWord] using
      transferBranchTransferFromPayoutLoopDynDepositLenAw14
        nounWord amountWord startWord finishWord bidderWord settledWord
        (UInt256.ofNat ↑I.codeOwner)
  have hdepositGap :
      (auctionSettleAuctionDynMload64 memPay (UInt256.ofNat 14)).toNat -
          memPay.size <
        USize.size := by
    simpa [memPay, nounWord, startWord, finishWord, bidderWord, settledWord] using
      transferBranchTransferFromPayoutLoopDynDepositGapAw14
        nounWord amountWord startWord finishWord bidderWord settledWord
        (UInt256.ofNat ↑I.codeOwner)
  have hrdFallback' :
      RD auctionBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3347⟩
        [⟨0⟩, amountWord, ownerWord, ⟨4688⟩, ⟨128⟩, ⟨2471⟩, ⟨413⟩,
          auctionSelWord I]
        memPay (UInt256.ofNat 14) ByteArray.empty (cA', σ') kFallback CFallback := by
    simpa [memPay, nounWord, startWord, finishWord, bidderWord, settledWord,
      amountWord, ownerWord] using hrdFallback
  exact transferBranchPayoutInsufficientBalanceCase
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
    (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (cA' := cA') (σ' := σ') (σ'_solm := σ'_solm)
    (A'_solm := A'_solm) (o := o)
    (memPay := memPay) (awPay := UInt256.ofNat 14)
    (kFallback := kFallback) (CFallback := CFallback)
    _hcode _hperm hdispatch hdecode hwv
    hpausedSolm hstatusSolm hstartSolm hsettledSolm
    htimeSolmLe hbidderSolm hnounsCodeSolmEval hcallSolm
    hpostTf hamountEq hamountSolm hdepth hpayBalance
    hfreeStable hdepositLen hdepositGap hrdFallback'

theorem transferBranchPayoutInsufficientBalanceFromCallNamed
    {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' σ'_solm : AccountMap}
    {A'_solm : Substate} {o : ByteArray} {kPay CPay : ℕ}
    {evmS evmEnter evmMark evmTf : State} {amountWord ownerWord : UInt256}
    (_hcode : I.code = auctionBytecode)
    (_hperm : I.perm = true)
    (hdispatch : dispatchMsg auctionContract I.calldata = some settleAuctionTransition)
    (hdecode :
      decodeCalldataWithMode auctionConfig.abiDecodeMode
        (settleAuctionTransition.params.map Param.name)
        (transitionSignature settleAuctionTransition).paramTypes I.calldata = some ∅)
    (hevmS : evmS = initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
    (hevmEnter : evmEnter = auctionSettleAuctionEnterState evmS)
    (hevmMark : evmMark = auctionSettleAuctionMarkSettledState evmEnter)
    (hevmTf :
      evmTf =
        { evmMark with
          accountMap := σ'_solm
          substate := A'_solm
          createdAccounts := cA' })
    (hamountWord :
      amountWord = auctionAuctionAmountWord (auctionSettleAuctionEnterMap σ_evm I) I)
    (hownerWord : ownerWord = UInt256.land (auctionSlotWord ⟨151⟩ σ' I) solcAddrMask)
    (hwv : I.weiValue = ⟨0⟩)
    (hpausedSolm :
      UInt256.land (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨51⟩)
          ⟨255⟩ ≠
        ⟨0⟩)
    (hstatusSolm : Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨101⟩ ≠ ⟨2⟩)
    (hstartSolm : Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩)
    (hsettledSolm :
      auctionPackedSettledWord
          (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨211⟩) =
        ⟨0⟩)
    (htimeSolmLe :
      (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨210⟩).toNat ≤
        (UInt256.ofNat evmS.executionEnv.header.timestamp).toNat)
    (hbidderSolm :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨211⟩)).toNat ≠
        AccountAddress.ofNat 0)
    (hnounsCodeSolmEval :
      evalExpr? auctionConfig
          { contract := auctionContract,
            locals := auctionSettleAuctionSnapshotStore evmEnter }
          evmMark
          (.binary .gt (.extCodeSize (.storage nounsRef)) (.intLit 0)) =
        .ok (.bool true))
    (hcallSolm :
      typedCallViaEVM auctionConfig evmMark
        (EVM.address (AccountAddress.ofNat
          ((UInt256.land
            (Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨201⟩)
            solcAddrMask).toNat))) "transferFrom" 0
        [.address evmEnter.executionEnv.codeOwner,
          .address (AccountAddress.ofNat
            (auctionPackedBidderWord
              (Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨211⟩)).toNat),
          .int (Int.ofNat
            (Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨207⟩).toNat)]
        (true, evmTf, o) true)
    (hpostTf : accountMapEquiv σ' σ'_solm)
    (hamountEq : amountWord = auctionSettleAuctionAmount evmEnter)
    (hamountSolm : 0 < (auctionSettleAuctionAmount evmEnter).toNat)
    (hdepth : I.depth.val < 1024)
    (hpayBalance : ¬ amountWord ≤ (σ'.find? I.codeOwner |>.elim ⟨0⟩ (·.balance)))
    (hrdPayCall :
      RD auctionBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨4827⟩
        [⟨30000⟩, ownerWord, amountWord, ⟨352⟩, ⟨0⟩, ⟨352⟩,
          ⟨0⟩, ⟨352⟩, amountWord, ⟨30000⟩, ownerWord, ⟨0⟩, ⟨0⟩,
          amountWord, ownerWord, ⟨3347⟩, amountWord, ownerWord, ⟨4688⟩,
          ⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I]
        (auctionSettleAuctionTransferFromPayoutLoopMem
          (auctionAuctionNounWord (auctionSettleAuctionEnterMap σ_evm I) I)
          amountWord
          (auctionAuctionStartWord (auctionSettleAuctionEnterMap σ_evm I) I)
          (auctionAuctionEndWord (auctionSettleAuctionEnterMap σ_evm I) I)
          (auctionPackedBidderWord
            (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ_evm I) I))
          (auctionPackedSettledEVMReturnWord
            (auctionAuctionPackedWord (auctionSettleAuctionEnterMap σ_evm I) I))
          (UInt256.ofNat ↑I.codeOwner))
        (UInt256.ofNat 14) o (cA', σ') kPay CPay) :
    RuntimeCase (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) g := by
  subst evmTf
  subst evmMark
  subst evmEnter
  subst evmS
  subst amountWord
  subst ownerWord
  exact transferBranchPayoutInsufficientBalanceFromCall
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
    (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (cA' := cA') (σ' := σ') (σ'_solm := σ'_solm)
    (A'_solm := A'_solm) (o := o)
    (kPay := kPay) (CPay := CPay)
    _hcode _hperm hdispatch hdecode hwv
    hpausedSolm hstatusSolm hstartSolm hsettledSolm
    htimeSolmLe hbidderSolm hnounsCodeSolmEval hcallSolm
    hpostTf hamountEq hamountSolm hdepth hpayBalance hrdPayCall

end Auction
