import Benchmarks.Auction.SettleAuctionTransferBranchPayoutInsufficient

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Auction

theorem auctionSettleAuctionTransferFromPayoutNonemptyTransferMem_readFree_68
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
        amount owner).readWithPadding
        (auctionSettleAuctionDynMload64
          (auctionSettleAuctionTransferFromPayoutNonemptyMemCopy noun amount start
            finish bidder settled caller o)
          (auctionSettleAuctionTransferFromPayoutNonemptyAwCopy o)).toNat 68 =
      transferSelector ++ UInt256.toByteArray (UInt256.land solcAddrMask owner) ++
        UInt256.toByteArray amount := by
  let memCopy :=
    auctionSettleAuctionTransferFromPayoutNonemptyMemCopy noun amount start finish
      bidder settled caller o
  let awCopy := auctionSettleAuctionTransferFromPayoutNonemptyAwCopy o
  let freePtr := auctionSettleAuctionDynMload64 memCopy awCopy
  let newFree := auctionSettleAuctionPayoutNonemptyNewFree o
  let memDeposit := auctionSettleAuctionDynDepositMem memCopy awCopy
  let memSel := auctionSettleAuctionDynTransferSelMem memDeposit freePtr
  let memArg := auctionSettleAuctionDynTransferArgMem memDeposit freePtr amount owner
  let memTransfer := auctionSettleAuctionDynTransferMem memDeposit freePtr amount owner
  have hmload : auctionSettleAuctionDynMload64 memCopy awCopy = newFree := by
    simpa [memCopy, awCopy, newFree] using
      auctionSettleAuctionTransferFromPayoutNonemptyMemCopy_mload64
        noun amount start finish bidder settled caller hosmall hne
  have hfreeNat : freePtr.toNat = newFree.toNat := by
    dsimp [freePtr]
    rw [hmload]
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
    dsimp [memDeposit, auctionSettleAuctionDynDepositMem, memCopy, awCopy, freePtr]
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
  have hmemSelEq : auctionSettleAuctionDynTransferSelMem memDeposit newFree = memSel := by
    dsimp [memSel, freePtr]
    rw [hmload]
  have hptr4 : (newFree + (⟨4⟩ : UInt256)).toNat = newFree.toNat + 4 := by
    rw [uadd_toNat, show ((⟨4⟩ : UInt256).toNat = 4) by decide]
    rw [show newFree.toNat + 4 = 4 + newFree.toNat by omega]
    exact Nat.mod_eq_of_lt (by omega)
  have hmemArgSize : newFree.toNat + 36 ≤ memArg.size := by
    have hwrite :
        newFree.toNat + 4 + 32 ≤
          ((UInt256.toByteArray (UInt256.land solcAddrMask owner)).write 0
            memSel (newFree.toNat + 4) 32).size :=
      toByteArray_write_size_ge_off_add32 (UInt256.land solcAddrMask owner)
        memSel (newFree.toNat + 4) (by omega)
    dsimp [memArg, auctionSettleAuctionDynTransferArgMem, freePtr]
    rw [hmload, hptr4, hmemSelEq]
    omega
  have hptr36 : (newFree + (⟨36⟩ : UInt256)).toNat = newFree.toNat + 36 := by
    rw [uadd_toNat, show ((⟨36⟩ : UInt256).toNat = 36) by decide]
    rw [show newFree.toNat + 36 = 36 + newFree.toNat by omega]
    exact Nat.mod_eq_of_lt (by omega)
  have hmemArgEq :
      auctionSettleAuctionDynTransferArgMem memDeposit newFree amount owner = memArg := by
    dsimp [memArg, freePtr]
    rw [hmload]
  have hreadSel : memTransfer.readWithPadding newFree.toNat 4 = transferSelector := by
    have hpresAmount := toByteArray_write_read_below_len_of_gap amount memArg
      (newFree.toNat + 36) newFree.toNat 4 (by omega) (by omega) (by omega) (by omega)
      (by omega)
    have hpresOwner := toByteArray_write_read_below_len_of_gap
      (UInt256.land solcAddrMask owner) memSel (newFree.toNat + 4) newFree.toNat 4
      (by omega) (by omega) (by omega) (by omega) (by omega)
    have hreadWindow := toByteArray_write_read_window_of_gap
      auctionSettleAuctionTransferSelectorShifted memDeposit newFree.toNat 0 4
      (by omega) (by omega) (by omega) (by omega)
    dsimp [memTransfer, auctionSettleAuctionDynTransferMem, freePtr]
    rw [hmload, hptr36, hmemArgEq, hpresAmount]
    dsimp [memArg, auctionSettleAuctionDynTransferArgMem, freePtr]
    rw [hmload, hptr4, hmemSelEq, hpresOwner]
    dsimp [memSel, auctionSettleAuctionDynTransferSelMem, freePtr]
    rw [hmload]
    have hselectorShift :
        (auctionSettleAuctionTransferSelectorShifted.toByteArray.write 0 memDeposit
            newFree.toNat 32).readWithPadding newFree.toNat 4 =
          auctionSettleAuctionTransferSelectorShifted.toByteArray.extract 0 (0 + 4) := by
      simpa [Nat.add_zero] using hreadWindow
    rw [hselectorShift]
    native_decide
  have hreadOwner :
      memTransfer.readWithPadding (newFree.toNat + 4) 32 =
        UInt256.toByteArray (UInt256.land solcAddrMask owner) := by
    have hpresAmount := toByteArray_write_read_below_len_of_gap amount memArg
      (newFree.toNat + 36) (newFree.toNat + 4) 32
      (by omega) (by omega) (by omega) (by omega) (by omega)
    have hreadBack := toByteArray_write_read_back_of_gap
      (UInt256.land solcAddrMask owner) memSel (newFree.toNat + 4) (by omega)
    dsimp [memTransfer, auctionSettleAuctionDynTransferMem, freePtr]
    rw [hmload, hptr36, hmemArgEq, hpresAmount]
    dsimp [memArg, auctionSettleAuctionDynTransferArgMem, freePtr]
    rw [hmload, hptr4, hmemSelEq]
    exact hreadBack
  have hreadAmount :
      memTransfer.readWithPadding (newFree.toNat + 36) 32 = UInt256.toByteArray amount := by
    have hreadBack := toByteArray_write_read_back_of_gap amount memArg
      (newFree.toNat + 36) (by omega)
    dsimp [memTransfer, auctionSettleAuctionDynTransferMem, freePtr]
    rw [hmload, hptr36, hmemArgEq]
    exact hreadBack
  have hsizeGe : newFree.toNat + 68 ≤ memTransfer.size := by
    simpa [memTransfer, memDeposit, memCopy, awCopy, freePtr, newFree] using
      auctionSettleAuctionTransferFromPayoutNonemptyTransferMem_size_ge
        noun amount start finish bidder settled caller owner hosmall hne
  have hread68 : memTransfer.readWithPadding freePtr.toNat 68 =
      transferSelector ++ UInt256.toByteArray (UInt256.land solcAddrMask owner) ++
        UInt256.toByteArray amount := by
    rw [show 68 = 4 + 64 from rfl,
      byteArray_readWithPadding_split memTransfer freePtr.toNat 4 64
        (by omega) (by omega) (by omega) (by omega) (by omega) (by
          rw [hfreeNat]
          omega)]
    rw [show 64 = 32 + 32 from rfl,
      byteArray_readWithPadding_split memTransfer (freePtr.toNat + 4) 32 32
        (by omega) (by omega) (by omega) (by omega) (by omega) (by
          rw [hfreeNat]
          omega)]
    rw [hfreeNat, hreadSel, hreadOwner]
    rw [show newFree.toNat + 4 + 32 = newFree.toNat + 36 by omega, hreadAmount]
    simp [ByteArray.append_assoc]
  simpa [memTransfer, memDeposit, memCopy, awCopy, freePtr] using hread68

theorem auctionSettleAuctionTransferFromPayoutNonemptyTransferEncode_eq
    (noun amount start finish bidder settled caller owner : UInt256) {o : ByteArray}
    (hosmall : o.size < 2 ^ 138) (hne : o.size ≠ 0)
    (howner : UInt256.toNat (UInt256.land solcAddrMask owner) < EVM.addressModulus) :
    auctionConfig.externalABI.encode? "transfer"
        [.address (AccountAddress.ofUInt256 (UInt256.land solcAddrMask owner)),
          .int (Int.ofNat amount.toNat)] =
      some ((auctionSettleAuctionDynTransferMem
        (auctionSettleAuctionDynDepositMem
          (auctionSettleAuctionTransferFromPayoutNonemptyMemCopy noun amount start
            finish bidder settled caller o)
          (auctionSettleAuctionTransferFromPayoutNonemptyAwCopy o))
        (auctionSettleAuctionDynMload64
          (auctionSettleAuctionTransferFromPayoutNonemptyMemCopy noun amount start
            finish bidder settled caller o)
          (auctionSettleAuctionTransferFromPayoutNonemptyAwCopy o))
        amount owner).readWithPadding
        (auctionSettleAuctionDynMload64
          (auctionSettleAuctionTransferFromPayoutNonemptyMemCopy noun amount start
            finish bidder settled caller o)
          (auctionSettleAuctionTransferFromPayoutNonemptyAwCopy o)).toNat 68) := by
  have hfixed :=
    auctionSettleAuctionWethTransferEncode_eq noun amount start finish bidder settled owner howner
  rw [auctionSettleAuctionWethTransferMem_read352_68] at hfixed
  rw [auctionSettleAuctionTransferFromPayoutNonemptyTransferMem_readFree_68
    noun amount start finish bidder settled caller owner hosmall hne]
  exact hfixed

theorem auctionSettleAuctionTransferFromPayoutNonemptyTransferReturnMem_size_any
    (noun amount start finish bidder settled caller owner : UInt256) {o out : ByteArray}
    (hosmall : o.size < 2 ^ 138) (hne : o.size ≠ 0)
    (houtSize : out.size < UInt256.size) :
    let memCopy := auctionSettleAuctionTransferFromPayoutNonemptyMemCopy noun amount start finish bidder settled caller o
    let awCopy := auctionSettleAuctionTransferFromPayoutNonemptyAwCopy o
    let freePtr := auctionSettleAuctionDynMload64 memCopy awCopy
    let memDeposit := auctionSettleAuctionDynDepositMem memCopy awCopy
    let memTransfer := auctionSettleAuctionDynTransferMem memDeposit freePtr amount owner
    let len := (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat
    (out.write 0 memTransfer freePtr.toNat len).size = memTransfer.size := by
  let memCopy := auctionSettleAuctionTransferFromPayoutNonemptyMemCopy noun amount start finish bidder settled caller o
  let awCopy := auctionSettleAuctionTransferFromPayoutNonemptyAwCopy o
  let freePtr := auctionSettleAuctionDynMload64 memCopy awCopy
  let newFree := auctionSettleAuctionPayoutNonemptyNewFree o
  let memDeposit := auctionSettleAuctionDynDepositMem memCopy awCopy
  let memTransfer := auctionSettleAuctionDynTransferMem memDeposit freePtr amount owner
  let len := (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat
  have hmload : freePtr = newFree := by
    simpa [freePtr, memCopy, awCopy, newFree] using
      auctionSettleAuctionTransferFromPayoutNonemptyMemCopy_mload64
        noun amount start finish bidder settled caller hosmall hne
  have hsrc : len ≤ out.size := by
    simpa [len] using auctionSettleAuctionTransferReturnCopyLen_le_size (out := out) houtSize
  have hlen32 : len ≤ 32 := by
    simpa [len] using auctionSettleAuctionTransferReturnCopyLen_le32 (out := out)
  have hsizeGe : newFree.toNat + 68 ≤ memTransfer.size := by
    simpa [memTransfer, memDeposit, memCopy, awCopy, freePtr, newFree, hmload] using
      auctionSettleAuctionTransferFromPayoutNonemptyTransferMem_size_ge
        noun amount start finish bidder settled caller owner hosmall hne
  have hfreeNat : freePtr.toNat = newFree.toNat := by rw [hmload]
  change (out.write 0 memTransfer freePtr.toNat len).size = memTransfer.size
  by_cases hlen0 : len = 0
  · simp [hlen0, byteArray_write_len_zero]
  · rw [write_eq_gen out memTransfer freePtr.toNat len hlen0 hsrc]
    · rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
        ByteArray.size_extract, ByteArray.size_extract]
      omega
    · rw [hfreeNat]
      omega

theorem auctionSettleAuctionTransferFromPayoutNonemptyTransferReturnMem_read64_any
    (noun amount start finish bidder settled caller owner : UInt256) {o out : ByteArray}
    (hosmall : o.size < 2 ^ 138) (hne : o.size ≠ 0)
    (houtSize : out.size < UInt256.size) :
    let memCopy := auctionSettleAuctionTransferFromPayoutNonemptyMemCopy noun amount start finish bidder settled caller o
    let awCopy := auctionSettleAuctionTransferFromPayoutNonemptyAwCopy o
    let freePtr := auctionSettleAuctionDynMload64 memCopy awCopy
    let memDeposit := auctionSettleAuctionDynDepositMem memCopy awCopy
    let memTransfer := auctionSettleAuctionDynTransferMem memDeposit freePtr amount owner
    let len := (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat
    (out.write 0 memTransfer freePtr.toNat len).readWithPadding 64 32 =
      memTransfer.readWithPadding 64 32 := by
  let memCopy := auctionSettleAuctionTransferFromPayoutNonemptyMemCopy noun amount start finish bidder settled caller o
  let awCopy := auctionSettleAuctionTransferFromPayoutNonemptyAwCopy o
  let freePtr := auctionSettleAuctionDynMload64 memCopy awCopy
  let newFree := auctionSettleAuctionPayoutNonemptyNewFree o
  let memDeposit := auctionSettleAuctionDynDepositMem memCopy awCopy
  let memTransfer := auctionSettleAuctionDynTransferMem memDeposit freePtr amount owner
  let len := (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat
  have hmload : freePtr = newFree := by
    simpa [freePtr, memCopy, awCopy, newFree] using
      auctionSettleAuctionTransferFromPayoutNonemptyMemCopy_mload64
        noun amount start finish bidder settled caller hosmall hne
  have hsrc : len ≤ out.size := by
    simpa [len] using auctionSettleAuctionTransferReturnCopyLen_le_size (out := out) houtSize
  have hnewFreeGe : 96 ≤ newFree.toNat := by
    simpa [newFree] using auctionSettleAuctionPayoutNonemptyNewFree_ge96 (o := o) hosmall
  have hsizeGe : newFree.toNat + 68 ≤ memTransfer.size := by
    simpa [memTransfer, memDeposit, memCopy, awCopy, freePtr, newFree, hmload] using
      auctionSettleAuctionTransferFromPayoutNonemptyTransferMem_size_ge
        noun amount start finish bidder settled caller owner hosmall hne
  have hfreeNat : freePtr.toNat = newFree.toNat := by rw [hmload]
  change (out.write 0 memTransfer freePtr.toNat len).readWithPadding 64 32 =
    memTransfer.readWithPadding 64 32
  by_cases hlen0 : len = 0
  · simp [hlen0, byteArray_write_len_zero]
  · exact write_read_below_gen_extend out memTransfer freePtr.toNat len 64
      hlen0 hsrc (by rw [hfreeNat]; omega) (by rw [hfreeNat]; omega)

theorem auctionSettleAuctionTransferFromPayoutNonemptyTransferCallAw_bounds
    (noun amount start finish bidder settled caller owner : UInt256) {o : ByteArray}
    (hosmall : o.size < 2 ^ 138) (hne : o.size ≠ 0) :
    let memCopy := auctionSettleAuctionTransferFromPayoutNonemptyMemCopy noun amount start finish bidder settled caller o
    let awCopy := auctionSettleAuctionTransferFromPayoutNonemptyAwCopy o
    let freePtr := auctionSettleAuctionDynMload64 memCopy awCopy
    let awCall := auctionSettleAuctionDynDepositCallAw memCopy awCopy
    let awTransfer := auctionSettleAuctionDynTransferAw awCall freePtr
    let awReturn := UInt256.ofNat (MachineState.M awTransfer.toNat freePtr.toNat 32)
    3 ≤ awReturn.toNat ∧ awReturn.toNat * 32 < UInt256.size ∧
      freePtr.toNat + 32 ≤ 32 * awReturn.toNat := by
  let memCopy := auctionSettleAuctionTransferFromPayoutNonemptyMemCopy noun amount start finish bidder settled caller o
  let awCopy := auctionSettleAuctionTransferFromPayoutNonemptyAwCopy o
  let freePtr := auctionSettleAuctionDynMload64 memCopy awCopy
  let newFree := auctionSettleAuctionPayoutNonemptyNewFree o
  let awCall := auctionSettleAuctionDynDepositCallAw memCopy awCopy
  let awTransfer := auctionSettleAuctionDynTransferAw awCall freePtr
  let awReturn := UInt256.ofNat (MachineState.M awTransfer.toNat freePtr.toNat 32)
  have hmload : freePtr = newFree := by
    simpa [freePtr, memCopy, awCopy, newFree] using
      auctionSettleAuctionTransferFromPayoutNonemptyMemCopy_mload64
        noun amount start finish bidder settled caller hosmall hne
  have hawCopy := auctionSettleAuctionTransferFromPayoutNonemptyAwCopy_bounds (o := o) hosmall
  have hptr63 := auctionSettleAuctionPayoutNonemptyNewFree_add63_lt (o := o) hosmall
  have hawDeposit :=
    auctionSettleAuctionDynDepositAw_bounds_of_mload
      (mem := memCopy) (aw := awCopy) (ptr := newFree) (by simpa [memCopy, awCopy, newFree] using hmload)
      hawCopy.1 hawCopy.2 hptr63
  have hawAfterEq :
      auctionSettleAuctionDynDepositAwAfterMload64 memCopy awCopy =
        auctionSettleAuctionDynDepositAw memCopy awCopy := by
    simpa [auctionSettleAuctionDynDepositAwAfterMload64,
      auctionSettleAuctionDynMload64Aw] using
      auctionSettleAuctionDynMload64Aw_eq_of_bounds
        (aw := auctionSettleAuctionDynDepositAw memCopy awCopy) hawDeposit.1
  have hawCallEq : awCall = auctionSettleAuctionDynDepositAwAfterMload64 memCopy awCopy := by
    simpa [awCall] using
      auctionSettleAuctionDynDepositCallAw_eq_afterMload64_of_mload
        (mem := memCopy) (aw := awCopy) (ptr := newFree)
        (by simpa [memCopy, awCopy, newFree] using hmload) hawCopy.1 hawCopy.2 hptr63
  have hawCall : 3 ≤ awCall.toNat ∧ awCall.toNat * 32 < UInt256.size := by
    rw [hawCallEq, hawAfterEq]
    exact hawDeposit
  have hptr99 : freePtr.toNat + 99 < UInt256.size := by
    rw [hmload]
    exact auctionSettleAuctionPayoutNonemptyNewFree_add99_lt (o := o) hosmall
  have hawTransfer :=
    auctionSettleAuctionDynTransferAw_bounds
      (aw := awCall) (freePtr := freePtr) hawCall.1 hawCall.2 hptr99
  have hword :=
    auctionMachineState_M_word_bounds
      (s := awTransfer.toNat) (f := freePtr.toNat) hawTransfer.1 hawTransfer.2
      (by
        rw [hmload]
        exact auctionSettleAuctionPayoutNonemptyNewFree_add63_lt (o := o) hosmall)
  have hawReturnNat :
      awReturn.toNat = MachineState.M awTransfer.toNat freePtr.toNat 32 := by
    dsimp [awReturn]
    exact UInt256.toNat_ofNat_of_lt hword.2.2.2
  constructor
  · rw [hawReturnNat]
    exact hword.1
  constructor
  · rw [hawReturnNat]
    exact hword.2.1
  · rw [hawReturnNat]
    exact hword.2.2.1

theorem auctionSettleAuctionTransferFromPayoutNonemptyTransferAw_cover
    (noun amount start finish bidder settled caller owner : UInt256) {o : ByteArray}
    (hosmall : o.size < 2 ^ 138) (hne : o.size ≠ 0) :
    let memCopy :=
      auctionSettleAuctionTransferFromPayoutNonemptyMemCopy noun amount start finish bidder settled caller o
    let awCopy := auctionSettleAuctionTransferFromPayoutNonemptyAwCopy o
    let freePtr := auctionSettleAuctionDynMload64 memCopy awCopy
    let awCall := auctionSettleAuctionDynDepositCallAw memCopy awCopy
    freePtr.toNat + 68 ≤ 32 * (auctionSettleAuctionDynTransferAw awCall freePtr).toNat := by
  let memCopy :=
    auctionSettleAuctionTransferFromPayoutNonemptyMemCopy noun amount start finish bidder settled caller o
  let awCopy := auctionSettleAuctionTransferFromPayoutNonemptyAwCopy o
  let freePtr := auctionSettleAuctionDynMload64 memCopy awCopy
  let newFree := auctionSettleAuctionPayoutNonemptyNewFree o
  let awCall := auctionSettleAuctionDynDepositCallAw memCopy awCopy
  let awTransfer := auctionSettleAuctionDynTransferAw awCall freePtr
  have hmload : freePtr = newFree := by
    simpa [freePtr, memCopy, awCopy, newFree] using
      auctionSettleAuctionTransferFromPayoutNonemptyMemCopy_mload64
        noun amount start finish bidder settled caller hosmall hne
  have hawCopy := auctionSettleAuctionTransferFromPayoutNonemptyAwCopy_bounds (o := o) hosmall
  have hptr63 := auctionSettleAuctionPayoutNonemptyNewFree_add63_lt (o := o) hosmall
  have hawDeposit :=
    auctionSettleAuctionDynDepositAw_bounds_of_mload
      (mem := memCopy) (aw := awCopy) (ptr := newFree)
      (by simpa [memCopy, awCopy, newFree] using hmload)
      hawCopy.1 hawCopy.2 hptr63
  have hawAfterEq :
      auctionSettleAuctionDynDepositAwAfterMload64 memCopy awCopy =
        auctionSettleAuctionDynDepositAw memCopy awCopy := by
    simpa [auctionSettleAuctionDynDepositAwAfterMload64,
      auctionSettleAuctionDynMload64Aw] using
      auctionSettleAuctionDynMload64Aw_eq_of_bounds
        (aw := auctionSettleAuctionDynDepositAw memCopy awCopy) hawDeposit.1
  have hawCallEq : awCall = auctionSettleAuctionDynDepositAwAfterMload64 memCopy awCopy := by
    simpa [awCall] using
      auctionSettleAuctionDynDepositCallAw_eq_afterMload64_of_mload
        (mem := memCopy) (aw := awCopy) (ptr := newFree)
        (by simpa [memCopy, awCopy, newFree] using hmload) hawCopy.1 hawCopy.2 hptr63
  have hawCall : 3 ≤ awCall.toNat ∧ awCall.toNat * 32 < UInt256.size := by
    rw [hawCallEq, hawAfterEq]
    exact hawDeposit
  have hptr99 : freePtr.toNat + 99 < UInt256.size := by
    rw [hmload]
    exact auctionSettleAuctionPayoutNonemptyNewFree_add99_lt (o := o) hosmall
  have hptr4 : (freePtr + (⟨4⟩ : UInt256)).toNat = freePtr.toNat + 4 := by
    rw [uadd_toNat, show ((⟨4⟩ : UInt256).toNat = 4) by decide]
    rw [show freePtr.toNat + 4 = 4 + freePtr.toNat by omega]
    exact Nat.mod_eq_of_lt (by omega)
  have hptr36 : (freePtr + (⟨36⟩ : UInt256)).toNat = freePtr.toNat + 36 := by
    rw [uadd_toNat, show ((⟨36⟩ : UInt256).toNat = 36) by decide]
    rw [show freePtr.toNat + 36 = 36 + freePtr.toNat by omega]
    exact Nat.mod_eq_of_lt (by omega)
  have hselWord :=
    auctionMachineState_M_word_bounds (s := awCall.toNat) (f := freePtr.toNat)
      hawCall.1 hawCall.2
      (by
        rw [hmload]
        exact auctionSettleAuctionPayoutNonemptyNewFree_add63_lt (o := o) hosmall)
  have hawFreeEq : auctionSettleAuctionDynMload64Aw awCall = awCall :=
    auctionSettleAuctionDynMload64Aw_eq_of_bounds (aw := awCall) hawCall.1
  have hselNat :
      (auctionSettleAuctionDynTransferSelAw awCall freePtr).toNat =
        MachineState.M awCall.toNat freePtr.toNat 32 := by
    dsimp [auctionSettleAuctionDynTransferSelAw]
    rw [hawFreeEq]
    exact UInt256.toNat_ofNat_of_lt hselWord.2.2.2
  have hselBounds :
      3 ≤ (auctionSettleAuctionDynTransferSelAw awCall freePtr).toNat ∧
        (auctionSettleAuctionDynTransferSelAw awCall freePtr).toNat * 32 < UInt256.size := by
    constructor
    · rw [hselNat]
      exact hselWord.1
    · rw [hselNat]
      exact hselWord.2.1
  have hargWord :=
    auctionMachineState_M_word_bounds
      (s := (auctionSettleAuctionDynTransferSelAw awCall freePtr).toNat)
      (f := freePtr.toNat + 4)
      hselBounds.1 hselBounds.2 (by omega)
  have hargNat :
      (auctionSettleAuctionDynTransferArgAw awCall freePtr).toNat =
        MachineState.M (auctionSettleAuctionDynTransferSelAw awCall freePtr).toNat
          (freePtr.toNat + 4) 32 := by
    dsimp [auctionSettleAuctionDynTransferArgAw]
    rw [hptr4]
    exact UInt256.toNat_ofNat_of_lt hargWord.2.2.2
  have hargBounds :
      3 ≤ (auctionSettleAuctionDynTransferArgAw awCall freePtr).toNat ∧
        (auctionSettleAuctionDynTransferArgAw awCall freePtr).toNat * 32 <
          UInt256.size := by
    constructor
    · rw [hargNat]
      exact hargWord.1
    · rw [hargNat]
      exact hargWord.2.1
  have htransferWord :=
    auctionMachineState_M_word_bounds
      (s := (auctionSettleAuctionDynTransferArgAw awCall freePtr).toNat)
      (f := freePtr.toNat + 36)
      hargBounds.1 hargBounds.2 (by omega)
  have htransferNat :
      awTransfer.toNat =
        MachineState.M (auctionSettleAuctionDynTransferArgAw awCall freePtr).toNat
          (freePtr.toNat + 36) 32 := by
    dsimp [awTransfer, auctionSettleAuctionDynTransferAw]
    rw [hptr36]
    exact UInt256.toNat_ofNat_of_lt htransferWord.2.2.2
  have hcover :=
    auctionMachineState_M_pos_offset_len_le_words_mul
      (s := (auctionSettleAuctionDynTransferArgAw awCall freePtr).toNat)
      (f := freePtr.toNat + 36) (l := 32) (by native_decide)
  change freePtr.toNat + 68 ≤ 32 * awTransfer.toNat
  rw [htransferNat]
  omega

theorem auctionSettleAuctionTransferFromPayoutNonemptyTransferReturnAwAfterCall_eq
    (noun amount start finish bidder settled caller owner : UInt256) {o : ByteArray}
    (hosmall : o.size < 2 ^ 138) (hne : o.size ≠ 0) :
    let memCopy :=
      auctionSettleAuctionTransferFromPayoutNonemptyMemCopy noun amount start finish bidder settled caller o
    let awCopy := auctionSettleAuctionTransferFromPayoutNonemptyAwCopy o
    let freePtr := auctionSettleAuctionDynMload64 memCopy awCopy
    let awCall := auctionSettleAuctionDynDepositCallAw memCopy awCopy
    let awTransfer := auctionSettleAuctionDynTransferAw awCall freePtr
    UInt256.ofNat
        (MachineState.M
          (MachineState.M
            (auctionSettleAuctionDynTransferAwAfterMload64 awCall freePtr).toNat
            freePtr.toNat 68)
          freePtr.toNat 32) =
      UInt256.ofNat (MachineState.M awTransfer.toNat freePtr.toNat 32) := by
  let memCopy :=
    auctionSettleAuctionTransferFromPayoutNonemptyMemCopy noun amount start finish bidder settled caller o
  let awCopy := auctionSettleAuctionTransferFromPayoutNonemptyAwCopy o
  let freePtr := auctionSettleAuctionDynMload64 memCopy awCopy
  let awCall := auctionSettleAuctionDynDepositCallAw memCopy awCopy
  let awTransfer := auctionSettleAuctionDynTransferAw awCall freePtr
  have hcover :
      freePtr.toNat + 68 ≤ 32 * awTransfer.toNat := by
    simpa [memCopy, awCopy, freePtr, awCall, awTransfer] using
      auctionSettleAuctionTransferFromPayoutNonemptyTransferAw_cover
        noun amount start finish bidder settled caller owner hosmall hne
  have htransfer3 : 3 ≤ awTransfer.toNat := by
    have hfreeGe : 96 ≤ freePtr.toNat := by
      have hmload :
          freePtr = auctionSettleAuctionPayoutNonemptyNewFree o := by
        simpa [freePtr, memCopy, awCopy] using
          auctionSettleAuctionTransferFromPayoutNonemptyMemCopy_mload64
            noun amount start finish bidder settled caller hosmall hne
      rw [hmload]
      exact auctionSettleAuctionPayoutNonemptyNewFree_ge96 (o := o) hosmall
    have hle : 96 ≤ 32 * awTransfer.toNat := by omega
    omega
  have hawAfterEq :
      auctionSettleAuctionDynTransferAwAfterMload64 awCall freePtr = awTransfer := by
    simpa [auctionSettleAuctionDynTransferAwAfterMload64,
      auctionSettleAuctionDynMload64Aw, awTransfer] using
      auctionSettleAuctionDynMload64Aw_eq_of_bounds (aw := awTransfer) htransfer3
  have hM68 :
      MachineState.M
          (auctionSettleAuctionDynTransferAwAfterMload64 awCall freePtr).toNat
          freePtr.toNat 68 =
        awTransfer.toNat := by
    rw [hawAfterEq]
    exact auctionMachineState_M_inBounds hcover
  change
    UInt256.ofNat
        (MachineState.M
          (MachineState.M
            (auctionSettleAuctionDynTransferAwAfterMload64 awCall freePtr).toNat
            freePtr.toNat 68)
          freePtr.toNat 32) =
      UInt256.ofNat (MachineState.M awTransfer.toNat freePtr.toNat 32)
  rw [hM68]

theorem auctionSettleAuctionTransferFromPayoutNonemptyTransferReturnMload64_any
    (noun amount start finish bidder settled caller owner : UInt256) {o out : ByteArray}
    (hosmall : o.size < 2 ^ 138) (hne : o.size ≠ 0)
    (houtSize : out.size < UInt256.size) :
    let memCopy := auctionSettleAuctionTransferFromPayoutNonemptyMemCopy noun amount start finish bidder settled caller o
    let awCopy := auctionSettleAuctionTransferFromPayoutNonemptyAwCopy o
    let freePtr := auctionSettleAuctionDynMload64 memCopy awCopy
    let memDeposit := auctionSettleAuctionDynDepositMem memCopy awCopy
    let awCall := auctionSettleAuctionDynDepositCallAw memCopy awCopy
    let memTransfer := auctionSettleAuctionDynTransferMem memDeposit freePtr amount owner
    let awTransfer := auctionSettleAuctionDynTransferAw awCall freePtr
    let len := (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat
    let memReturn := out.write 0 memTransfer freePtr.toNat len
    let awReturn := UInt256.ofNat (MachineState.M awTransfer.toNat freePtr.toNat 32)
    auctionSettleAuctionDynMload64 memReturn awReturn = freePtr := by
  let memCopy := auctionSettleAuctionTransferFromPayoutNonemptyMemCopy noun amount start finish bidder settled caller o
  let awCopy := auctionSettleAuctionTransferFromPayoutNonemptyAwCopy o
  let freePtr := auctionSettleAuctionDynMload64 memCopy awCopy
  let newFree := auctionSettleAuctionPayoutNonemptyNewFree o
  let memDeposit := auctionSettleAuctionDynDepositMem memCopy awCopy
  let awCall := auctionSettleAuctionDynDepositCallAw memCopy awCopy
  let memTransfer := auctionSettleAuctionDynTransferMem memDeposit freePtr amount owner
  let awTransfer := auctionSettleAuctionDynTransferAw awCall freePtr
  let len := (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat
  let memReturn := out.write 0 memTransfer freePtr.toNat len
  let awReturn := UInt256.ofNat (MachineState.M awTransfer.toNat freePtr.toNat 32)
  have hmload : freePtr = newFree := by
    simpa [freePtr, memCopy, awCopy, newFree] using
      auctionSettleAuctionTransferFromPayoutNonemptyMemCopy_mload64
        noun amount start finish bidder settled caller hosmall hne
  have hmemReturnSize : memReturn.size = memTransfer.size := by
    simpa [memReturn, memTransfer, memDeposit, memCopy, awCopy, freePtr, len] using
      auctionSettleAuctionTransferFromPayoutNonemptyTransferReturnMem_size_any
        noun amount start finish bidder settled caller owner hosmall hne houtSize
  have hreadReturn :
      memReturn.readWithPadding 64 32 = UInt256.toByteArray freePtr := by
    have hreadCopy :
        memReturn.readWithPadding 64 32 = memTransfer.readWithPadding 64 32 := by
      simpa [memReturn, memTransfer, memDeposit, memCopy, awCopy, freePtr, len] using
        auctionSettleAuctionTransferFromPayoutNonemptyTransferReturnMem_read64_any
          noun amount start finish bidder settled caller owner hosmall hne houtSize
    have hreadTransfer :
        memTransfer.readWithPadding 64 32 = UInt256.toByteArray newFree := by
      simpa [memTransfer, memDeposit, memCopy, awCopy, freePtr, newFree, hmload] using
        auctionSettleAuctionTransferFromPayoutNonemptyTransferMem_read64
          noun amount start finish bidder settled caller owner hosmall hne
    rw [hreadCopy, hreadTransfer, hmload]
  have hsizeGe : newFree.toNat + 68 ≤ memTransfer.size := by
    simpa [memTransfer, memDeposit, memCopy, awCopy, freePtr, newFree, hmload] using
      auctionSettleAuctionTransferFromPayoutNonemptyTransferMem_size_ge
        noun amount start finish bidder settled caller owner hosmall hne
  have hmem64 : 64 < memReturn.size := by
    rw [hmemReturnSize]
    have hnewFreeGe : 96 ≤ newFree.toNat := by
      simpa [newFree] using auctionSettleAuctionPayoutNonemptyNewFree_ge96 (o := o) hosmall
    omega
  have hawReturn :=
    auctionSettleAuctionTransferFromPayoutNonemptyTransferCallAw_bounds
      noun amount start finish bidder settled caller owner hosmall hne
  exact auctionSettleAuctionDynMload64_of_readWithPadding_of_aw
    hmem64 hreadReturn hawReturn.1 hawReturn.2.1

theorem auctionSettleAuctionTransferFromPayoutNonemptyTransferReturnMloadFree
    (noun amount start finish bidder settled caller owner : UInt256) {o out : ByteArray}
    (hosmall : o.size < 2 ^ 138) (hne : o.size ≠ 0)
    (hout32 : 32 ≤ out.size) (houtSize : out.size < UInt256.size) :
    let memCopy := auctionSettleAuctionTransferFromPayoutNonemptyMemCopy noun amount start finish bidder settled caller o
    let awCopy := auctionSettleAuctionTransferFromPayoutNonemptyAwCopy o
    let freePtr := auctionSettleAuctionDynMload64 memCopy awCopy
    let memDeposit := auctionSettleAuctionDynDepositMem memCopy awCopy
    let awCall := auctionSettleAuctionDynDepositCallAw memCopy awCopy
    let memTransfer := auctionSettleAuctionDynTransferMem memDeposit freePtr amount owner
    let awTransfer := auctionSettleAuctionDynTransferAw awCall freePtr
    let len := (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat
    let memReturn := out.write 0 memTransfer freePtr.toNat len
    let awReturn := UInt256.ofNat (MachineState.M awTransfer.toNat freePtr.toNat 32)
    let osz := UInt256.ofNat out.size
    let rounded := UInt256.land (UInt256.add osz ⟨31⟩) (UInt256.lnot ⟨31⟩)
    let newFree := UInt256.add freePtr rounded
    let aw64 := UInt256.ofNat (MachineState.M awReturn.toNat (⟨64⟩ : UInt256).toNat 32)
    let memRet := (UInt256.toByteArray newFree).write 0 memReturn (⟨64⟩ : UInt256).toNat 32
    let awStore := UInt256.ofNat (MachineState.M aw64.toNat (⟨64⟩ : UInt256).toNat 32)
    (if freePtr.toNat ≥ memRet.size ∨ freePtr ≥ awStore * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian (memRet.readWithPadding freePtr.toNat 32))) =
    UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) := by
  let memCopy := auctionSettleAuctionTransferFromPayoutNonemptyMemCopy noun amount start finish bidder settled caller o
  let awCopy := auctionSettleAuctionTransferFromPayoutNonemptyAwCopy o
  let freePtr := auctionSettleAuctionDynMload64 memCopy awCopy
  let newFree0 := auctionSettleAuctionPayoutNonemptyNewFree o
  let memDeposit := auctionSettleAuctionDynDepositMem memCopy awCopy
  let awCall := auctionSettleAuctionDynDepositCallAw memCopy awCopy
  let memTransfer := auctionSettleAuctionDynTransferMem memDeposit freePtr amount owner
  let awTransfer := auctionSettleAuctionDynTransferAw awCall freePtr
  let len := (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat
  let memReturn := out.write 0 memTransfer freePtr.toNat len
  let awReturn := UInt256.ofNat (MachineState.M awTransfer.toNat freePtr.toNat 32)
  let osz := UInt256.ofNat out.size
  let rounded := UInt256.land (UInt256.add osz ⟨31⟩) (UInt256.lnot ⟨31⟩)
  let newFree := UInt256.add freePtr rounded
  let aw64 := UInt256.ofNat (MachineState.M awReturn.toNat (⟨64⟩ : UInt256).toNat 32)
  let memRet := (UInt256.toByteArray newFree).write 0 memReturn (⟨64⟩ : UInt256).toNat 32
  let awStore := UInt256.ofNat (MachineState.M aw64.toNat (⟨64⟩ : UInt256).toNat 32)
  have hmload : freePtr = newFree0 := by
    simpa [freePtr, memCopy, awCopy, newFree0] using
      auctionSettleAuctionTransferFromPayoutNonemptyMemCopy_mload64
        noun amount start finish bidder settled caller hosmall hne
  have hmemReturnSize : memReturn.size = memTransfer.size := by
    simpa [memReturn, memTransfer, memDeposit, memCopy, awCopy, freePtr, len] using
      auctionSettleAuctionTransferFromPayoutNonemptyTransferReturnMem_size_any
        noun amount start finish bidder settled caller owner hosmall hne houtSize
  have hsizeGe : newFree0.toNat + 68 ≤ memTransfer.size := by
    simpa [memTransfer, memDeposit, memCopy, awCopy, freePtr, newFree0, hmload] using
      auctionSettleAuctionTransferFromPayoutNonemptyTransferMem_size_ge
        noun amount start finish bidder settled caller owner hosmall hne
  have hnewFreeGe : 96 ≤ newFree0.toNat := by
    simpa [newFree0] using auctionSettleAuctionPayoutNonemptyNewFree_ge96 (o := o) hosmall
  have hlen32 :
      len = 32 := by
    simpa [len] using auctionSettleAuctionTransferReturnCopyLen hout32 houtSize
  have hreadCopy : memReturn.readWithPadding freePtr.toNat 32 = out.extract 0 32 := by
    change (out.write 0 memTransfer freePtr.toNat len).readWithPadding freePtr.toNat 32 =
      out.extract 0 32
    rw [hlen32]
    exact write32_read_back out memTransfer freePtr.toNat hout32
      (by rw [hmload]; omega)
  have hmemRetSize : memRet.size = memReturn.size := by
    dsimp [memRet]
    exact toByteArray_write32_size_of_le memReturn newFree 64 memReturn.size memReturn.size
      rfl
      (by
        rw [hmemReturnSize]
        omega)
      (by
        have hle : 64 + 32 ≤ memReturn.size := by
          rw [hmemReturnSize]
          omega
        exact max_eq_left hle)
  have hreadRet : memRet.readWithPadding freePtr.toNat 32 = out.extract 0 32 := by
    have habove : 64 + 32 ≤ freePtr.toNat := by
      rw [hmload]
      simpa [newFree0] using auctionSettleAuctionPayoutNonemptyNewFree_ge96 (o := o) hosmall
    have hin : freePtr.toNat + 32 ≤ memReturn.size := by
      rw [hmemReturnSize, hmload]
      omega
    dsimp [memRet]
    rw [write32_read_above (UInt256.toByteArray newFree) memReturn
      (⟨64⟩ : UInt256).toNat freePtr.toNat
      (by rw [toByteArray_size])
      (by
        rw [show ((⟨64⟩ : UInt256).toNat) = 64 by native_decide, hmemReturnSize]
        omega)
      (by simpa using habove) hin]
    exact hreadCopy
  have hawReturn :=
    auctionSettleAuctionTransferFromPayoutNonemptyTransferCallAw_bounds
      noun amount start finish bidder settled caller owner hosmall hne
  have haw64Eq : aw64 = awReturn := by
    simpa [aw64, auctionSettleAuctionDynMload64Aw] using
      auctionSettleAuctionDynMload64Aw_eq_of_bounds (aw := awReturn) hawReturn.1
  have hawStoreEq : awStore = awReturn := by
    dsimp [awStore]
    rw [haw64Eq]
    simpa [auctionSettleAuctionDynMload64Aw] using
      auctionSettleAuctionDynMload64Aw_eq_of_bounds (aw := awReturn) hawReturn.1
  have hnotGe : ¬ freePtr ≥ awStore * ⟨32⟩ := by
    rw [hawStoreEq]
    exact u256_not_ge_mul32_of_cover hawReturn.2.1 hawReturn.2.2
  change
    (if freePtr.toNat ≥ memRet.size ∨ freePtr ≥ awStore * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian (memRet.readWithPadding freePtr.toNat 32))) =
    UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))
  rw [if_neg]
  · simpa [hreadRet]
  · exact not_or.mpr
      ⟨by
        rw [hmemRetSize, hmemReturnSize, hmload]
        omega,
       hnotGe⟩

theorem auctionSettleAuctionTransferFromPayoutNonemptyTransferReturn_baseAddHi
    (noun amount start finish bidder settled caller : UInt256) {outPay outTransfer : ByteArray}
    (hosmall : outPay.size < 2 ^ 138) (hne : outPay.size ≠ 0)
    (hhi : outTransfer.size < 2 ^ 255) :
    (auctionSettleAuctionDynMload64
        (auctionSettleAuctionTransferFromPayoutNonemptyMemCopy noun amount start finish bidder settled caller outPay)
        (auctionSettleAuctionTransferFromPayoutNonemptyAwCopy outPay)).toNat +
      outTransfer.size < UInt256.size := by
  rw [auctionSettleAuctionTransferFromPayoutNonemptyMemCopy_mload64
    noun amount start finish bidder settled caller hosmall hne]
  rw [auctionSettleAuctionPayoutNonemptyNewFree_toNat (o := outPay) hosmall]
  have hroundLe := auctionSettleAuctionPayoutNonemptyRounded_toNat_le (o := outPay) hosmall
  norm_num [UInt256.size] at hosmall hhi ⊢
  omega

theorem auctionSettleAuctionTransferFromPayoutNonemptyTransferReturnShortRevertDyn
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (noun amount start finish bidder settled caller owner weth : UInt256)
    {outPay outTransfer : ByteArray} {k C : ℕ}
    (hosmall : outPay.size < 2 ^ 138) (hne : outPay.size ≠ 0)
    (hshort : outTransfer.size < 32) (houtSize : outTransfer.size < UInt256.size)
    (rd :
      let memCopy :=
        auctionSettleAuctionTransferFromPayoutNonemptyMemCopy noun amount start finish bidder settled caller outPay
      let awCopy := auctionSettleAuctionTransferFromPayoutNonemptyAwCopy outPay
      let freePtr := auctionSettleAuctionDynMload64 memCopy awCopy
      let memDeposit := auctionSettleAuctionDynDepositMem memCopy awCopy
      let awCall := auctionSettleAuctionDynDepositCallAw memCopy awCopy
      let memTransfer := auctionSettleAuctionDynTransferMem memDeposit freePtr amount owner
      let awTransfer := auctionSettleAuctionDynTransferAw awCall freePtr
      let len := (min (⟨32⟩ : UInt256) (UInt256.ofNat outTransfer.size)).toNat
      let memReturn := outTransfer.write 0 memTransfer freePtr.toNat len
      let awReturn := UInt256.ofNat (MachineState.M awTransfer.toNat freePtr.toNat 32)
      RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3518⟩
        [⟨1⟩, (⟨68⟩ : UInt256) + freePtr, ⟨2835717307⟩, weth, amount, owner,
          ⟨4688⟩, ⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I]
        memReturn awReturn outTransfer acc k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let memCopy :=
    auctionSettleAuctionTransferFromPayoutNonemptyMemCopy noun amount start finish bidder settled caller outPay
  let awCopy := auctionSettleAuctionTransferFromPayoutNonemptyAwCopy outPay
  let freePtr := auctionSettleAuctionDynMload64 memCopy awCopy
  let memDeposit := auctionSettleAuctionDynDepositMem memCopy awCopy
  let awCall := auctionSettleAuctionDynDepositCallAw memCopy awCopy
  let memTransfer := auctionSettleAuctionDynTransferMem memDeposit freePtr amount owner
  let awTransfer := auctionSettleAuctionDynTransferAw awCall freePtr
  let len := (min (⟨32⟩ : UInt256) (UInt256.ofNat outTransfer.size)).toNat
  let memReturn := outTransfer.write 0 memTransfer freePtr.toNat len
  let awReturn := UInt256.ofNat (MachineState.M awTransfer.toNat freePtr.toNat 32)
  have hbaseAdd : freePtr.toNat + outTransfer.size < UInt256.size := by
    exact auctionSettleAuctionTransferFromPayoutNonemptyTransferReturn_baseAddHi
      noun amount start finish bidder settled caller hosmall hne (by omega)
  have hfp :
      (if (⟨64⟩ : UInt256).toNat ≥ memReturn.size ∨
          (⟨64⟩ : UInt256) ≥ awReturn * ⟨32⟩
        then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (memReturn.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        freePtr := by
    simpa [auctionSettleAuctionDynMload64, memCopy, awCopy, freePtr, memDeposit, awCall,
      memTransfer, awTransfer, len, memReturn, awReturn] using
      auctionSettleAuctionTransferFromPayoutNonemptyTransferReturnMload64_any
        noun amount start finish bidder settled caller owner hosmall hne houtSize
  exact auctionSettleAuctionTransferReturnShortRevertAt
    (base := freePtr) (amount := amount) (owner := owner) (weth := weth)
    (rd := rd) hshort hbaseAdd hfp

theorem auctionSettleAuctionTransferFromPayoutNonemptyTransferReturnHugeRevertDyn
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (noun amount start finish bidder settled caller owner weth : UInt256)
    {outPay outTransfer : ByteArray} {k C : ℕ}
    (hosmall : outPay.size < 2 ^ 138) (hne : outPay.size ≠ 0)
    (hhuge : (2 : Nat) ^ 255 ≤ outTransfer.size)
    (houtSize : outTransfer.size < UInt256.size)
    (rd :
      let memCopy :=
        auctionSettleAuctionTransferFromPayoutNonemptyMemCopy noun amount start finish bidder settled caller outPay
      let awCopy := auctionSettleAuctionTransferFromPayoutNonemptyAwCopy outPay
      let freePtr := auctionSettleAuctionDynMload64 memCopy awCopy
      let memDeposit := auctionSettleAuctionDynDepositMem memCopy awCopy
      let awCall := auctionSettleAuctionDynDepositCallAw memCopy awCopy
      let memTransfer := auctionSettleAuctionDynTransferMem memDeposit freePtr amount owner
      let awTransfer := auctionSettleAuctionDynTransferAw awCall freePtr
      let len := (min (⟨32⟩ : UInt256) (UInt256.ofNat outTransfer.size)).toNat
      let memReturn := outTransfer.write 0 memTransfer freePtr.toNat len
      let awReturn := UInt256.ofNat (MachineState.M awTransfer.toNat freePtr.toNat 32)
      RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3518⟩
        [⟨1⟩, (⟨68⟩ : UInt256) + freePtr, ⟨2835717307⟩, weth, amount, owner,
          ⟨4688⟩, ⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I]
        memReturn awReturn outTransfer acc k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let memCopy :=
    auctionSettleAuctionTransferFromPayoutNonemptyMemCopy noun amount start finish bidder settled caller outPay
  let awCopy := auctionSettleAuctionTransferFromPayoutNonemptyAwCopy outPay
  let freePtr := auctionSettleAuctionDynMload64 memCopy awCopy
  let memDeposit := auctionSettleAuctionDynDepositMem memCopy awCopy
  let awCall := auctionSettleAuctionDynDepositCallAw memCopy awCopy
  let memTransfer := auctionSettleAuctionDynTransferMem memDeposit freePtr amount owner
  let awTransfer := auctionSettleAuctionDynTransferAw awCall freePtr
  let len := (min (⟨32⟩ : UInt256) (UInt256.ofNat outTransfer.size)).toNat
  let memReturn := outTransfer.write 0 memTransfer freePtr.toNat len
  let awReturn := UInt256.ofNat (MachineState.M awTransfer.toNat freePtr.toNat 32)
  have hfp :
      (if (⟨64⟩ : UInt256).toNat ≥ memReturn.size ∨
          (⟨64⟩ : UInt256) ≥ awReturn * ⟨32⟩
        then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (memReturn.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        freePtr := by
    simpa [auctionSettleAuctionDynMload64, memCopy, awCopy, freePtr, memDeposit, awCall,
      memTransfer, awTransfer, len, memReturn, awReturn] using
      auctionSettleAuctionTransferFromPayoutNonemptyTransferReturnMload64_any
        noun amount start finish bidder settled caller owner hosmall hne houtSize
  exact auctionSettleAuctionTransferReturnHugeRevertAt
    (base := freePtr) (amount := amount) (owner := owner) (weth := weth)
    (rd := rd) hhuge houtSize hfp

set_option maxHeartbeats 1000000 in
theorem auctionSettleAuctionTransferFromPayoutNonemptyTransferReturnBoolToEventDyn
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (noun amount start finish bidder settled caller owner weth : UInt256)
    {outPay outTransfer : ByteArray} {k C : ℕ}
    (hosmall : outPay.size < 2 ^ 138) (hne : outPay.size ≠ 0)
    (hout32 : 32 ≤ outTransfer.size) (houtHi : outTransfer.size < 2 ^ 255)
    (houtSize : outTransfer.size < UInt256.size)
    (hcanon :
      let retWord := UInt256.ofNat (fromByteArrayBigEndian (outTransfer.extract 0 32))
      retWord = ⟨0⟩ ∨ retWord = ⟨1⟩)
    (rd :
      let memCopy :=
        auctionSettleAuctionTransferFromPayoutNonemptyMemCopy noun amount start finish bidder settled caller outPay
      let awCopy := auctionSettleAuctionTransferFromPayoutNonemptyAwCopy outPay
      let freePtr := auctionSettleAuctionDynMload64 memCopy awCopy
      let memDeposit := auctionSettleAuctionDynDepositMem memCopy awCopy
      let awCall := auctionSettleAuctionDynDepositCallAw memCopy awCopy
      let memTransfer := auctionSettleAuctionDynTransferMem memDeposit freePtr amount owner
      let awTransfer := auctionSettleAuctionDynTransferAw awCall freePtr
      let len := (min (⟨32⟩ : UInt256) (UInt256.ofNat outTransfer.size)).toNat
      let memReturn := outTransfer.write 0 memTransfer freePtr.toNat len
      let awReturn := UInt256.ofNat (MachineState.M awTransfer.toNat freePtr.toNat 32)
      RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3518⟩
        [⟨1⟩, (⟨68⟩ : UInt256) + freePtr, ⟨2835717307⟩, weth, amount, owner,
          ⟨4688⟩, ⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I]
        memReturn awReturn outTransfer acc k C) :
    ∃ mem' aw' k' C',
      RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4688⟩
        [⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I]
        mem' aw' outTransfer acc k' C' := by
  let memCopy :=
    auctionSettleAuctionTransferFromPayoutNonemptyMemCopy noun amount start finish bidder settled caller outPay
  let awCopy := auctionSettleAuctionTransferFromPayoutNonemptyAwCopy outPay
  let freePtr := auctionSettleAuctionDynMload64 memCopy awCopy
  let memDeposit := auctionSettleAuctionDynDepositMem memCopy awCopy
  let awCall := auctionSettleAuctionDynDepositCallAw memCopy awCopy
  let memTransfer := auctionSettleAuctionDynTransferMem memDeposit freePtr amount owner
  let awTransfer := auctionSettleAuctionDynTransferAw awCall freePtr
  let len := (min (⟨32⟩ : UInt256) (UInt256.ofNat outTransfer.size)).toNat
  let memReturn := outTransfer.write 0 memTransfer freePtr.toNat len
  let awReturn := UInt256.ofNat (MachineState.M awTransfer.toNat freePtr.toNat 32)
  let retWord := UInt256.ofNat (fromByteArrayBigEndian (outTransfer.extract 0 32))
  have hbaseAdd : freePtr.toNat + outTransfer.size < UInt256.size :=
    auctionSettleAuctionTransferFromPayoutNonemptyTransferReturn_baseAddHi
      noun amount start finish bidder settled caller hosmall hne houtHi
  have hfp :
      (if (⟨64⟩ : UInt256).toNat ≥ memReturn.size ∨
          (⟨64⟩ : UInt256) ≥ awReturn * ⟨32⟩
        then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (memReturn.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        freePtr := by
    simpa [auctionSettleAuctionDynMload64, memCopy, awCopy, freePtr, memDeposit, awCall,
      memTransfer, awTransfer, len, memReturn, awReturn] using
      auctionSettleAuctionTransferFromPayoutNonemptyTransferReturnMload64_any
        noun amount start finish bidder settled caller owner hosmall hne houtSize
  have hword :
      let osz := UInt256.ofNat outTransfer.size
      let rounded := UInt256.land (UInt256.add osz ⟨31⟩) (UInt256.lnot ⟨31⟩)
      let newFree := UInt256.add freePtr rounded
      let aw64 := UInt256.ofNat (MachineState.M awReturn.toNat (⟨64⟩ : UInt256).toNat 32)
      let memRet := (UInt256.toByteArray newFree).write 0 memReturn (⟨64⟩ : UInt256).toNat 32
      let awStore := UInt256.ofNat (MachineState.M aw64.toNat (⟨64⟩ : UInt256).toNat 32)
      (if freePtr.toNat ≥ memRet.size ∨ freePtr ≥ awStore * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (memRet.readWithPadding freePtr.toNat 32))) =
      retWord := by
    simpa [retWord, memCopy, awCopy, freePtr, memDeposit, awCall, memTransfer, awTransfer,
      len, memReturn, awReturn] using
      auctionSettleAuctionTransferFromPayoutNonemptyTransferReturnMloadFree
        noun amount start finish bidder settled caller owner hosmall hne hout32 houtSize
  exact auctionSettleAuctionTransferReturnBoolToEventAt
    (base := freePtr) (amount := amount) (owner := owner) (weth := weth)
    (retWord := retWord) (rd := rd) hout32 houtHi hbaseAdd hfp hword
    (by simpa [retWord] using hcanon)

set_option maxHeartbeats 1000000 in
theorem auctionSettleAuctionTransferFromPayoutNonemptyTransferReturnNoncanonRevertDyn
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (noun amount start finish bidder settled caller owner weth : UInt256)
    {outPay outTransfer : ByteArray} {k C : ℕ}
    (hosmall : outPay.size < 2 ^ 138) (hne : outPay.size ≠ 0)
    (hout32 : 32 ≤ outTransfer.size) (houtHi : outTransfer.size < 2 ^ 255)
    (houtSize : outTransfer.size < UInt256.size)
    (hnz :
      let retWord := UInt256.ofNat (fromByteArrayBigEndian (outTransfer.extract 0 32))
      retWord ≠ ⟨0⟩)
    (hno :
      let retWord := UInt256.ofNat (fromByteArrayBigEndian (outTransfer.extract 0 32))
      retWord ≠ ⟨1⟩)
    (rd :
      let memCopy :=
        auctionSettleAuctionTransferFromPayoutNonemptyMemCopy noun amount start finish bidder settled caller outPay
      let awCopy := auctionSettleAuctionTransferFromPayoutNonemptyAwCopy outPay
      let freePtr := auctionSettleAuctionDynMload64 memCopy awCopy
      let memDeposit := auctionSettleAuctionDynDepositMem memCopy awCopy
      let awCall := auctionSettleAuctionDynDepositCallAw memCopy awCopy
      let memTransfer := auctionSettleAuctionDynTransferMem memDeposit freePtr amount owner
      let awTransfer := auctionSettleAuctionDynTransferAw awCall freePtr
      let len := (min (⟨32⟩ : UInt256) (UInt256.ofNat outTransfer.size)).toNat
      let memReturn := outTransfer.write 0 memTransfer freePtr.toNat len
      let awReturn := UInt256.ofNat (MachineState.M awTransfer.toNat freePtr.toNat 32)
      RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3518⟩
        [⟨1⟩, (⟨68⟩ : UInt256) + freePtr, ⟨2835717307⟩, weth, amount, owner,
          ⟨4688⟩, ⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I]
        memReturn awReturn outTransfer acc k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let memCopy :=
    auctionSettleAuctionTransferFromPayoutNonemptyMemCopy noun amount start finish bidder settled caller outPay
  let awCopy := auctionSettleAuctionTransferFromPayoutNonemptyAwCopy outPay
  let freePtr := auctionSettleAuctionDynMload64 memCopy awCopy
  let memDeposit := auctionSettleAuctionDynDepositMem memCopy awCopy
  let awCall := auctionSettleAuctionDynDepositCallAw memCopy awCopy
  let memTransfer := auctionSettleAuctionDynTransferMem memDeposit freePtr amount owner
  let awTransfer := auctionSettleAuctionDynTransferAw awCall freePtr
  let len := (min (⟨32⟩ : UInt256) (UInt256.ofNat outTransfer.size)).toNat
  let memReturn := outTransfer.write 0 memTransfer freePtr.toNat len
  let awReturn := UInt256.ofNat (MachineState.M awTransfer.toNat freePtr.toNat 32)
  let retWord := UInt256.ofNat (fromByteArrayBigEndian (outTransfer.extract 0 32))
  have hbaseAdd : freePtr.toNat + outTransfer.size < UInt256.size :=
    auctionSettleAuctionTransferFromPayoutNonemptyTransferReturn_baseAddHi
      noun amount start finish bidder settled caller hosmall hne houtHi
  have hfp :
      (if (⟨64⟩ : UInt256).toNat ≥ memReturn.size ∨
          (⟨64⟩ : UInt256) ≥ awReturn * ⟨32⟩
        then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (memReturn.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        freePtr := by
    simpa [auctionSettleAuctionDynMload64, memCopy, awCopy, freePtr, memDeposit, awCall,
      memTransfer, awTransfer, len, memReturn, awReturn] using
      auctionSettleAuctionTransferFromPayoutNonemptyTransferReturnMload64_any
        noun amount start finish bidder settled caller owner hosmall hne houtSize
  have hword :
      let osz := UInt256.ofNat outTransfer.size
      let rounded := UInt256.land (UInt256.add osz ⟨31⟩) (UInt256.lnot ⟨31⟩)
      let newFree := UInt256.add freePtr rounded
      let aw64 := UInt256.ofNat (MachineState.M awReturn.toNat (⟨64⟩ : UInt256).toNat 32)
      let memRet := (UInt256.toByteArray newFree).write 0 memReturn (⟨64⟩ : UInt256).toNat 32
      let awStore := UInt256.ofNat (MachineState.M aw64.toNat (⟨64⟩ : UInt256).toNat 32)
      (if freePtr.toNat ≥ memRet.size ∨ freePtr ≥ awStore * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (memRet.readWithPadding freePtr.toNat 32))) =
      retWord := by
    simpa [retWord, memCopy, awCopy, freePtr, memDeposit, awCall, memTransfer, awTransfer,
      len, memReturn, awReturn] using
      auctionSettleAuctionTransferFromPayoutNonemptyTransferReturnMloadFree
        noun amount start finish bidder settled caller owner hosmall hne hout32 houtSize
  exact auctionSettleAuctionTransferReturnNoncanonRevertAt
    (base := freePtr) (amount := amount) (owner := owner) (weth := weth)
    (retWord := retWord) (rd := rd) hout32 houtHi hbaseAdd hfp hword
    (by simpa [retWord] using hnz) (by simpa [retWord] using hno)

end Auction
