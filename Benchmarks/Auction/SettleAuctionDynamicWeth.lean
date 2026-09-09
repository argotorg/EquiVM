import Benchmarks.Auction.SettleAuctionDynamicWethBase
import Benchmarks.Auction.SafeTransferETHReturn

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Auction

theorem auctionSettleAuctionPayoutNonemptyMemCopy_mload64
    (noun amount start finish bidder settled : UInt256) {o : ByteArray}
    (hosmall : o.size < 2 ^ 138) (hne : o.size ≠ 0) :
    auctionSettleAuctionDynMload64
        (auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled o)
        (auctionSettleAuctionPayoutNonemptyAwCopy o) =
      auctionSettleAuctionPayoutNonemptyNewFree o := by
  let memLoop := auctionSettleAuctionPayoutLoopMem noun amount start finish bidder settled
  let memFree := auctionSettleAuctionPayoutNonemptyMemFree noun amount start finish bidder settled o
  let memLen := auctionSettleAuctionPayoutNonemptyMemLen noun amount start finish bidder settled o
  let memCopy := auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled o
  let oszWord := auctionSettleAuctionPayoutNonemptyOszWord o
  let newFree := auctionSettleAuctionPayoutNonemptyNewFree o
  have hmemLoopSize : memLoop.size = 384 := by
    simpa [memLoop] using
      auctionSettleAuctionPayoutLoopMem_size noun amount start finish bidder settled
  have hgap64 : 64 - memLoop.size < USize.size := by
    rw [hmemLoopSize]
    native_decide
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
  have hsrc0 : 0 + oszWord.toNat ≤ o.size := by
    simpa using hsrc
  have hreadCopy : memCopy.readWithPadding 64 32 = UInt256.toByteArray newFree := by
    have hpres := write_read_below_gen_extend o memLen 384 oszWord.toNat 64
      hlenNe hsrc (by rw [hmemLenSize]) (by decide)
    dsimp [memCopy, auctionSettleAuctionPayoutNonemptyMemCopy, memLen, oszWord]
    rw [hpres]
    exact hreadLen
  have hmemCopySize : 64 < memCopy.size := by
    have hsize := write_end_size_from o memLen 0 oszWord.toNat hlenNe hsrc0
    change 64 < (o.write 0 memLen 384 oszWord.toNat).size
    rw [← hmemLenSize, hsize, hmemLenSize]
    omega
  have haw := auctionSettleAuctionPayoutNonemptyAwCopy_bounds (o := o) hosmall
  exact auctionSettleAuctionDynMload64_of_readWithPadding_of_aw hmemCopySize hreadCopy
    haw.1 haw.2

theorem auctionSettleAuctionPayoutNonemptyDepositFreeStable
    (noun amount start finish bidder settled : UInt256) {o : ByteArray}
    (hosmall : o.size < 2 ^ 138) (hne : o.size ≠ 0) :
    auctionSettleAuctionDynMload64
        (auctionSettleAuctionDynDepositMem
          (auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled o)
          (auctionSettleAuctionPayoutNonemptyAwCopy o))
        (auctionSettleAuctionDynDepositAw
          (auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled o)
          (auctionSettleAuctionPayoutNonemptyAwCopy o)) =
      auctionSettleAuctionDynMload64
        (auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled o)
        (auctionSettleAuctionPayoutNonemptyAwCopy o) := by
  let memCopy := auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled o
  let awCopy := auctionSettleAuctionPayoutNonemptyAwCopy o
  let newFree := auctionSettleAuctionPayoutNonemptyNewFree o
  have hmload :
      auctionSettleAuctionDynMload64 memCopy awCopy = newFree := by
    simpa [memCopy, awCopy, newFree] using
      auctionSettleAuctionPayoutNonemptyMemCopy_mload64
        noun amount start finish bidder settled hosmall hne
  have hreadCopy : memCopy.readWithPadding 64 32 = UInt256.toByteArray newFree := by
    simpa [memCopy, newFree] using
      auctionSettleAuctionPayoutNonemptyMemCopy_read64
        noun amount start finish bidder settled hosmall hne
  have hmemSize : memCopy.size = 384 + o.size := by
    simpa [memCopy] using
      auctionSettleAuctionPayoutNonemptyMemCopy_size
        noun amount start finish bidder settled hosmall hne
  have hgap : newFree.toNat - memCopy.size < USize.size := by
    simpa [memCopy, newFree] using
      auctionSettleAuctionPayoutNonemptyNewFree_memCopy_gap
        noun amount start finish bidder settled hosmall hne
  have hnewFree99 : newFree.toNat + 99 < UInt256.size := by
    simpa [newFree] using auctionSettleAuctionPayoutNonemptyNewFree_add99_lt (o := o) hosmall
  have hnewFreeGe : 96 ≤ newFree.toNat := by
    simpa [newFree] using auctionSettleAuctionPayoutNonemptyNewFree_ge96 (o := o) hosmall
  have hnewFree99 : newFree.toNat + 99 < UInt256.size := by
    simpa [newFree] using auctionSettleAuctionPayoutNonemptyNewFree_add99_lt (o := o) hosmall
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
  have hreadDeposit :
      (auctionSettleAuctionDynDepositMem memCopy awCopy).readWithPadding 64 32 =
        UInt256.toByteArray newFree := by
    have hpres := toByteArray_write_read_below_of_gap
      auctionSettleAuctionDepositSelectorShifted memCopy newFree.toNat 64
      (by rw [hmemSize]; omega) hnewFreeGe hgap
    dsimp [auctionSettleAuctionDynDepositMem]
    rw [hmload, hpres]
    exact hreadCopy
  have hawCopy := auctionSettleAuctionPayoutNonemptyAwCopy_bounds (o := o) hosmall
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

theorem auctionSettleAuctionPayoutNonemptyDepositMem_read64
    (noun amount start finish bidder settled : UInt256) {o : ByteArray}
    (hosmall : o.size < 2 ^ 138) (hne : o.size ≠ 0) :
    (auctionSettleAuctionDynDepositMem
        (auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled o)
        (auctionSettleAuctionPayoutNonemptyAwCopy o)).readWithPadding 64 32 =
      UInt256.toByteArray (auctionSettleAuctionPayoutNonemptyNewFree o) := by
  let memCopy := auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled o
  let awCopy := auctionSettleAuctionPayoutNonemptyAwCopy o
  let newFree := auctionSettleAuctionPayoutNonemptyNewFree o
  have hmload :
      auctionSettleAuctionDynMload64 memCopy awCopy = newFree := by
    simpa [memCopy, awCopy, newFree] using
      auctionSettleAuctionPayoutNonemptyMemCopy_mload64
        noun amount start finish bidder settled hosmall hne
  have hreadCopy : memCopy.readWithPadding 64 32 = UInt256.toByteArray newFree := by
    simpa [memCopy, newFree] using
      auctionSettleAuctionPayoutNonemptyMemCopy_read64
        noun amount start finish bidder settled hosmall hne
  have hmemSize : memCopy.size = 384 + o.size := by
    simpa [memCopy] using
      auctionSettleAuctionPayoutNonemptyMemCopy_size
        noun amount start finish bidder settled hosmall hne
  have hgap : newFree.toNat - memCopy.size < USize.size := by
    simpa [memCopy, newFree] using
      auctionSettleAuctionPayoutNonemptyNewFree_memCopy_gap
        noun amount start finish bidder settled hosmall hne
  have hnewFreeGe : 96 ≤ newFree.toNat := by
    simpa [newFree] using auctionSettleAuctionPayoutNonemptyNewFree_ge96 (o := o) hosmall
  have hpres := toByteArray_write_read_below_of_gap
    auctionSettleAuctionDepositSelectorShifted memCopy newFree.toNat 64
    (by rw [hmemSize]; omega) hnewFreeGe hgap
  dsimp [auctionSettleAuctionDynDepositMem]
  rw [hmload, hpres]
  exact hreadCopy

theorem auctionSettleAuctionPayoutNonemptyDepositCallFreeStable
    (noun amount start finish bidder settled : UInt256) {o : ByteArray}
    (hosmall : o.size < 2 ^ 138) (hne : o.size ≠ 0) :
    auctionSettleAuctionDynMload64
        (auctionSettleAuctionDynDepositMem
          (auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled o)
          (auctionSettleAuctionPayoutNonemptyAwCopy o))
        (auctionSettleAuctionDynDepositCallAw
          (auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled o)
          (auctionSettleAuctionPayoutNonemptyAwCopy o)) =
      auctionSettleAuctionDynMload64
        (auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled o)
        (auctionSettleAuctionPayoutNonemptyAwCopy o) := by
  let memCopy := auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled o
  let awCopy := auctionSettleAuctionPayoutNonemptyAwCopy o
  let newFree := auctionSettleAuctionPayoutNonemptyNewFree o
  let memDeposit := auctionSettleAuctionDynDepositMem memCopy awCopy
  let awCall := auctionSettleAuctionDynDepositCallAw memCopy awCopy
  have hmload :
      auctionSettleAuctionDynMload64 memCopy awCopy = newFree := by
    simpa [memCopy, awCopy, newFree] using
      auctionSettleAuctionPayoutNonemptyMemCopy_mload64
        noun amount start finish bidder settled hosmall hne
  have hreadDeposit : memDeposit.readWithPadding 64 32 = UInt256.toByteArray newFree := by
    simpa [memDeposit, memCopy, awCopy, newFree] using
      auctionSettleAuctionPayoutNonemptyDepositMem_read64
        noun amount start finish bidder settled hosmall hne
  have hmemSize : memCopy.size = 384 + o.size := by
    simpa [memCopy] using
      auctionSettleAuctionPayoutNonemptyMemCopy_size
        noun amount start finish bidder settled hosmall hne
  have hgap : newFree.toNat - memCopy.size < USize.size := by
    simpa [memCopy, newFree] using
      auctionSettleAuctionPayoutNonemptyNewFree_memCopy_gap
        noun amount start finish bidder settled hosmall hne
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
  have hawCopy := auctionSettleAuctionPayoutNonemptyAwCopy_bounds (o := o) hosmall
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

theorem auctionSettleAuctionPayoutNonemptyTransferMem_read64
    (noun amount start finish bidder settled owner : UInt256) {o : ByteArray}
    (hosmall : o.size < 2 ^ 138) (hne : o.size ≠ 0) :
    (auctionSettleAuctionDynTransferMem
        (auctionSettleAuctionDynDepositMem
          (auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled o)
          (auctionSettleAuctionPayoutNonemptyAwCopy o))
        (auctionSettleAuctionDynMload64
          (auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled o)
          (auctionSettleAuctionPayoutNonemptyAwCopy o))
        amount owner).readWithPadding 64 32 =
      UInt256.toByteArray (auctionSettleAuctionPayoutNonemptyNewFree o) := by
  let memCopy := auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled o
  let awCopy := auctionSettleAuctionPayoutNonemptyAwCopy o
  let freePtr := auctionSettleAuctionDynMload64 memCopy awCopy
  let newFree := auctionSettleAuctionPayoutNonemptyNewFree o
  let memDeposit := auctionSettleAuctionDynDepositMem memCopy awCopy
  let memSel := auctionSettleAuctionDynTransferSelMem memDeposit freePtr
  let memArg := auctionSettleAuctionDynTransferArgMem memDeposit freePtr amount owner
  have hmload : auctionSettleAuctionDynMload64 memCopy awCopy = newFree := by
    simpa [memCopy, awCopy, newFree] using
      auctionSettleAuctionPayoutNonemptyMemCopy_mload64
        noun amount start finish bidder settled hosmall hne
  have hreadDeposit : memDeposit.readWithPadding 64 32 = UInt256.toByteArray newFree := by
    simpa [memDeposit, memCopy, awCopy, newFree] using
      auctionSettleAuctionPayoutNonemptyDepositMem_read64
        noun amount start finish bidder settled hosmall hne
  have hmemCopySize : memCopy.size = 384 + o.size := by
    simpa [memCopy] using
      auctionSettleAuctionPayoutNonemptyMemCopy_size
        noun amount start finish bidder settled hosmall hne
  have hgap : newFree.toNat - memCopy.size < USize.size := by
    simpa [memCopy, newFree] using
      auctionSettleAuctionPayoutNonemptyNewFree_memCopy_gap
        noun amount start finish bidder settled hosmall hne
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

theorem auctionSettleAuctionPayoutNonemptyTransferMem_size_ge
    (noun amount start finish bidder settled owner : UInt256) {o : ByteArray}
    (hosmall : o.size < 2 ^ 138) (hne : o.size ≠ 0) :
    (auctionSettleAuctionPayoutNonemptyNewFree o).toNat + 68 ≤
      (auctionSettleAuctionDynTransferMem
        (auctionSettleAuctionDynDepositMem
          (auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled o)
          (auctionSettleAuctionPayoutNonemptyAwCopy o))
        (auctionSettleAuctionDynMload64
          (auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled o)
          (auctionSettleAuctionPayoutNonemptyAwCopy o))
        amount owner).size := by
  let memCopy := auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled o
  let awCopy := auctionSettleAuctionPayoutNonemptyAwCopy o
  let freePtr := auctionSettleAuctionDynMload64 memCopy awCopy
  let newFree := auctionSettleAuctionPayoutNonemptyNewFree o
  let memDeposit := auctionSettleAuctionDynDepositMem memCopy awCopy
  let memSel := auctionSettleAuctionDynTransferSelMem memDeposit freePtr
  let memArg := auctionSettleAuctionDynTransferArgMem memDeposit freePtr amount owner
  have hmload : auctionSettleAuctionDynMload64 memCopy awCopy = newFree := by
    simpa [memCopy, awCopy, newFree] using
      auctionSettleAuctionPayoutNonemptyMemCopy_mload64
        noun amount start finish bidder settled hosmall hne
  have hgap : newFree.toNat - memCopy.size < USize.size := by
    simpa [memCopy, newFree] using
      auctionSettleAuctionPayoutNonemptyNewFree_memCopy_gap
        noun amount start finish bidder settled hosmall hne
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

theorem auctionSettleAuctionPayoutNonemptyTransferMem_readFree_68
    (noun amount start finish bidder settled owner : UInt256) {o : ByteArray}
    (hosmall : o.size < 2 ^ 138) (hne : o.size ≠ 0) :
    (auctionSettleAuctionDynTransferMem
        (auctionSettleAuctionDynDepositMem
          (auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled o)
          (auctionSettleAuctionPayoutNonemptyAwCopy o))
        (auctionSettleAuctionDynMload64
          (auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled o)
          (auctionSettleAuctionPayoutNonemptyAwCopy o))
        amount owner).readWithPadding
        (auctionSettleAuctionDynMload64
          (auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled o)
          (auctionSettleAuctionPayoutNonemptyAwCopy o)).toNat 68 =
      transferSelector ++ UInt256.toByteArray (UInt256.land solcAddrMask owner) ++
        UInt256.toByteArray amount := by
  let memCopy := auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled o
  let awCopy := auctionSettleAuctionPayoutNonemptyAwCopy o
  let freePtr := auctionSettleAuctionDynMload64 memCopy awCopy
  let newFree := auctionSettleAuctionPayoutNonemptyNewFree o
  let memDeposit := auctionSettleAuctionDynDepositMem memCopy awCopy
  let memSel := auctionSettleAuctionDynTransferSelMem memDeposit freePtr
  let memArg := auctionSettleAuctionDynTransferArgMem memDeposit freePtr amount owner
  let memTransfer := auctionSettleAuctionDynTransferMem memDeposit freePtr amount owner
  have hmload : auctionSettleAuctionDynMload64 memCopy awCopy = newFree := by
    simpa [memCopy, awCopy, newFree] using
      auctionSettleAuctionPayoutNonemptyMemCopy_mload64
        noun amount start finish bidder settled hosmall hne
  have hfreeNat : freePtr.toNat = newFree.toNat := by
    dsimp [freePtr]
    rw [hmload]
  have hgap : newFree.toNat - memCopy.size < USize.size := by
    simpa [memCopy, newFree] using
      auctionSettleAuctionPayoutNonemptyNewFree_memCopy_gap
        noun amount start finish bidder settled hosmall hne
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
      auctionSettleAuctionPayoutNonemptyTransferMem_size_ge
        noun amount start finish bidder settled owner hosmall hne
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

theorem auctionSettleAuctionPayoutNonemptyTransferEncode_eq
    (noun amount start finish bidder settled owner : UInt256) {o : ByteArray}
    (hosmall : o.size < 2 ^ 138) (hne : o.size ≠ 0)
    (howner : UInt256.toNat (UInt256.land solcAddrMask owner) < EVM.addressModulus) :
    auctionConfig.externalABI.encode? "transfer"
        [.address (AccountAddress.ofUInt256 (UInt256.land solcAddrMask owner)),
          .int (Int.ofNat amount.toNat)] =
      some ((auctionSettleAuctionDynTransferMem
        (auctionSettleAuctionDynDepositMem
          (auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled o)
          (auctionSettleAuctionPayoutNonemptyAwCopy o))
        (auctionSettleAuctionDynMload64
          (auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled o)
          (auctionSettleAuctionPayoutNonemptyAwCopy o))
        amount owner).readWithPadding
        (auctionSettleAuctionDynMload64
          (auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled o)
          (auctionSettleAuctionPayoutNonemptyAwCopy o)).toNat 68) := by
  have hfixed :=
    auctionSettleAuctionWethTransferEncode_eq noun amount start finish bidder settled owner howner
  rw [auctionSettleAuctionWethTransferMem_read352_68] at hfixed
  rw [auctionSettleAuctionPayoutNonemptyTransferMem_readFree_68
    noun amount start finish bidder settled owner hosmall hne]
  exact hfixed

theorem auctionSettleAuctionPayoutNonemptyTransferFreeStable
    (noun amount start finish bidder settled owner : UInt256) {o : ByteArray}
    (hosmall : o.size < 2 ^ 138) (hne : o.size ≠ 0) :
    auctionSettleAuctionDynMload64
        (auctionSettleAuctionDynTransferMem
          (auctionSettleAuctionDynDepositMem
            (auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled o)
            (auctionSettleAuctionPayoutNonemptyAwCopy o))
          (auctionSettleAuctionDynMload64
            (auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled o)
            (auctionSettleAuctionPayoutNonemptyAwCopy o))
          amount owner)
        (auctionSettleAuctionDynTransferAw
          (auctionSettleAuctionDynDepositCallAw
            (auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled o)
            (auctionSettleAuctionPayoutNonemptyAwCopy o))
          (auctionSettleAuctionDynMload64
            (auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled o)
            (auctionSettleAuctionPayoutNonemptyAwCopy o))) =
      auctionSettleAuctionDynMload64
        (auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled o)
        (auctionSettleAuctionPayoutNonemptyAwCopy o) := by
  let memCopy := auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled o
  let awCopy := auctionSettleAuctionPayoutNonemptyAwCopy o
  let freePtr := auctionSettleAuctionDynMload64 memCopy awCopy
  let newFree := auctionSettleAuctionPayoutNonemptyNewFree o
  let memDeposit := auctionSettleAuctionDynDepositMem memCopy awCopy
  let awCall := auctionSettleAuctionDynDepositCallAw memCopy awCopy
  let memTransfer := auctionSettleAuctionDynTransferMem memDeposit freePtr amount owner
  let awTransfer := auctionSettleAuctionDynTransferAw awCall freePtr
  have hmload : auctionSettleAuctionDynMload64 memCopy awCopy = newFree := by
    simpa [memCopy, awCopy, newFree] using
      auctionSettleAuctionPayoutNonemptyMemCopy_mload64
        noun amount start finish bidder settled hosmall hne
  have hreadTransfer : memTransfer.readWithPadding 64 32 = UInt256.toByteArray newFree := by
    simpa [memTransfer, memDeposit, memCopy, awCopy, freePtr, newFree] using
      auctionSettleAuctionPayoutNonemptyTransferMem_read64
        noun amount start finish bidder settled owner hosmall hne
  have hsizeGe : newFree.toNat + 68 ≤ memTransfer.size := by
    simpa [memTransfer, memDeposit, memCopy, awCopy, freePtr, newFree] using
      auctionSettleAuctionPayoutNonemptyTransferMem_size_ge
        noun amount start finish bidder settled owner hosmall hne
  have hnewFreeGe : 96 ≤ newFree.toNat := by
    simpa [newFree] using auctionSettleAuctionPayoutNonemptyNewFree_ge96 (o := o) hosmall
  have hmemTransferSize : 64 < memTransfer.size := by
    omega
  have hawCopy := auctionSettleAuctionPayoutNonemptyAwCopy_bounds (o := o) hosmall
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

theorem auctionSettleAuctionPayoutNonemptyTransferReturnMem_size_any
    (noun amount start finish bidder settled owner : UInt256) {o out : ByteArray}
    (hosmall : o.size < 2 ^ 138) (hne : o.size ≠ 0)
    (houtSize : out.size < UInt256.size) :
    let memCopy := auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled o
    let awCopy := auctionSettleAuctionPayoutNonemptyAwCopy o
    let freePtr := auctionSettleAuctionDynMload64 memCopy awCopy
    let memDeposit := auctionSettleAuctionDynDepositMem memCopy awCopy
    let memTransfer := auctionSettleAuctionDynTransferMem memDeposit freePtr amount owner
    let len := (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat
    (out.write 0 memTransfer freePtr.toNat len).size = memTransfer.size := by
  let memCopy := auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled o
  let awCopy := auctionSettleAuctionPayoutNonemptyAwCopy o
  let freePtr := auctionSettleAuctionDynMload64 memCopy awCopy
  let newFree := auctionSettleAuctionPayoutNonemptyNewFree o
  let memDeposit := auctionSettleAuctionDynDepositMem memCopy awCopy
  let memTransfer := auctionSettleAuctionDynTransferMem memDeposit freePtr amount owner
  let len := (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat
  have hmload : freePtr = newFree := by
    simpa [freePtr, memCopy, awCopy, newFree] using
      auctionSettleAuctionPayoutNonemptyMemCopy_mload64
        noun amount start finish bidder settled hosmall hne
  have hsrc : len ≤ out.size := by
    simpa [len] using auctionSettleAuctionTransferReturnCopyLen_le_size (out := out) houtSize
  have hlen32 : len ≤ 32 := by
    simpa [len] using auctionSettleAuctionTransferReturnCopyLen_le32 (out := out)
  have hsizeGe : newFree.toNat + 68 ≤ memTransfer.size := by
    simpa [memTransfer, memDeposit, memCopy, awCopy, freePtr, newFree, hmload] using
      auctionSettleAuctionPayoutNonemptyTransferMem_size_ge
        noun amount start finish bidder settled owner hosmall hne
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

theorem auctionSettleAuctionPayoutNonemptyTransferReturnMem_read64_any
    (noun amount start finish bidder settled owner : UInt256) {o out : ByteArray}
    (hosmall : o.size < 2 ^ 138) (hne : o.size ≠ 0)
    (houtSize : out.size < UInt256.size) :
    let memCopy := auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled o
    let awCopy := auctionSettleAuctionPayoutNonemptyAwCopy o
    let freePtr := auctionSettleAuctionDynMload64 memCopy awCopy
    let memDeposit := auctionSettleAuctionDynDepositMem memCopy awCopy
    let memTransfer := auctionSettleAuctionDynTransferMem memDeposit freePtr amount owner
    let len := (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat
    (out.write 0 memTransfer freePtr.toNat len).readWithPadding 64 32 =
      memTransfer.readWithPadding 64 32 := by
  let memCopy := auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled o
  let awCopy := auctionSettleAuctionPayoutNonemptyAwCopy o
  let freePtr := auctionSettleAuctionDynMload64 memCopy awCopy
  let newFree := auctionSettleAuctionPayoutNonemptyNewFree o
  let memDeposit := auctionSettleAuctionDynDepositMem memCopy awCopy
  let memTransfer := auctionSettleAuctionDynTransferMem memDeposit freePtr amount owner
  let len := (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat
  have hmload : freePtr = newFree := by
    simpa [freePtr, memCopy, awCopy, newFree] using
      auctionSettleAuctionPayoutNonemptyMemCopy_mload64
        noun amount start finish bidder settled hosmall hne
  have hsrc : len ≤ out.size := by
    simpa [len] using auctionSettleAuctionTransferReturnCopyLen_le_size (out := out) houtSize
  have hnewFreeGe : 96 ≤ newFree.toNat := by
    simpa [newFree] using auctionSettleAuctionPayoutNonemptyNewFree_ge96 (o := o) hosmall
  have hsizeGe : newFree.toNat + 68 ≤ memTransfer.size := by
    simpa [memTransfer, memDeposit, memCopy, awCopy, freePtr, newFree, hmload] using
      auctionSettleAuctionPayoutNonemptyTransferMem_size_ge
        noun amount start finish bidder settled owner hosmall hne
  have hfreeNat : freePtr.toNat = newFree.toNat := by rw [hmload]
  change (out.write 0 memTransfer freePtr.toNat len).readWithPadding 64 32 =
    memTransfer.readWithPadding 64 32
  by_cases hlen0 : len = 0
  · simp [hlen0, byteArray_write_len_zero]
  · exact write_read_below_gen_extend out memTransfer freePtr.toNat len 64
      hlen0 hsrc (by rw [hfreeNat]; omega) (by rw [hfreeNat]; omega)

theorem auctionSettleAuctionPayoutNonemptyTransferCallAw_bounds
    (noun amount start finish bidder settled owner : UInt256) {o : ByteArray}
    (hosmall : o.size < 2 ^ 138) (hne : o.size ≠ 0) :
    let memCopy := auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled o
    let awCopy := auctionSettleAuctionPayoutNonemptyAwCopy o
    let freePtr := auctionSettleAuctionDynMload64 memCopy awCopy
    let awCall := auctionSettleAuctionDynDepositCallAw memCopy awCopy
    let awTransfer := auctionSettleAuctionDynTransferAw awCall freePtr
    let awReturn := UInt256.ofNat (MachineState.M awTransfer.toNat freePtr.toNat 32)
    3 ≤ awReturn.toNat ∧ awReturn.toNat * 32 < UInt256.size ∧
      freePtr.toNat + 32 ≤ 32 * awReturn.toNat := by
  let memCopy := auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled o
  let awCopy := auctionSettleAuctionPayoutNonemptyAwCopy o
  let freePtr := auctionSettleAuctionDynMload64 memCopy awCopy
  let newFree := auctionSettleAuctionPayoutNonemptyNewFree o
  let awCall := auctionSettleAuctionDynDepositCallAw memCopy awCopy
  let awTransfer := auctionSettleAuctionDynTransferAw awCall freePtr
  let awReturn := UInt256.ofNat (MachineState.M awTransfer.toNat freePtr.toNat 32)
  have hmload : freePtr = newFree := by
    simpa [freePtr, memCopy, awCopy, newFree] using
      auctionSettleAuctionPayoutNonemptyMemCopy_mload64
        noun amount start finish bidder settled hosmall hne
  have hawCopy := auctionSettleAuctionPayoutNonemptyAwCopy_bounds (o := o) hosmall
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

theorem auctionSettleAuctionPayoutNonemptyTransferReturnMload64_any
    (noun amount start finish bidder settled owner : UInt256) {o out : ByteArray}
    (hosmall : o.size < 2 ^ 138) (hne : o.size ≠ 0)
    (houtSize : out.size < UInt256.size) :
    let memCopy := auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled o
    let awCopy := auctionSettleAuctionPayoutNonemptyAwCopy o
    let freePtr := auctionSettleAuctionDynMload64 memCopy awCopy
    let memDeposit := auctionSettleAuctionDynDepositMem memCopy awCopy
    let awCall := auctionSettleAuctionDynDepositCallAw memCopy awCopy
    let memTransfer := auctionSettleAuctionDynTransferMem memDeposit freePtr amount owner
    let awTransfer := auctionSettleAuctionDynTransferAw awCall freePtr
    let len := (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat
    let memReturn := out.write 0 memTransfer freePtr.toNat len
    let awReturn := UInt256.ofNat (MachineState.M awTransfer.toNat freePtr.toNat 32)
    auctionSettleAuctionDynMload64 memReturn awReturn = freePtr := by
  let memCopy := auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled o
  let awCopy := auctionSettleAuctionPayoutNonemptyAwCopy o
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
      auctionSettleAuctionPayoutNonemptyMemCopy_mload64
        noun amount start finish bidder settled hosmall hne
  have hmemReturnSize : memReturn.size = memTransfer.size := by
    simpa [memReturn, memTransfer, memDeposit, memCopy, awCopy, freePtr, len] using
      auctionSettleAuctionPayoutNonemptyTransferReturnMem_size_any
        noun amount start finish bidder settled owner hosmall hne houtSize
  have hreadReturn :
      memReturn.readWithPadding 64 32 = UInt256.toByteArray freePtr := by
    have hreadCopy :
        memReturn.readWithPadding 64 32 = memTransfer.readWithPadding 64 32 := by
      simpa [memReturn, memTransfer, memDeposit, memCopy, awCopy, freePtr, len] using
        auctionSettleAuctionPayoutNonemptyTransferReturnMem_read64_any
          noun amount start finish bidder settled owner hosmall hne houtSize
    have hreadTransfer :
        memTransfer.readWithPadding 64 32 = UInt256.toByteArray newFree := by
      simpa [memTransfer, memDeposit, memCopy, awCopy, freePtr, newFree, hmload] using
        auctionSettleAuctionPayoutNonemptyTransferMem_read64
          noun amount start finish bidder settled owner hosmall hne
    rw [hreadCopy, hreadTransfer, hmload]
  have hsizeGe : newFree.toNat + 68 ≤ memTransfer.size := by
    simpa [memTransfer, memDeposit, memCopy, awCopy, freePtr, newFree, hmload] using
      auctionSettleAuctionPayoutNonemptyTransferMem_size_ge
        noun amount start finish bidder settled owner hosmall hne
  have hmem64 : 64 < memReturn.size := by
    rw [hmemReturnSize]
    have hnewFreeGe : 96 ≤ newFree.toNat := by
      simpa [newFree] using auctionSettleAuctionPayoutNonemptyNewFree_ge96 (o := o) hosmall
    omega
  have hawReturn :=
    auctionSettleAuctionPayoutNonemptyTransferCallAw_bounds
      noun amount start finish bidder settled owner hosmall hne
  exact auctionSettleAuctionDynMload64_of_readWithPadding_of_aw
    hmem64 hreadReturn hawReturn.1 hawReturn.2.1

theorem auctionSettleAuctionPayoutNonemptyTransferReturnMloadFree
    (noun amount start finish bidder settled owner : UInt256) {o out : ByteArray}
    (hosmall : o.size < 2 ^ 138) (hne : o.size ≠ 0)
    (hout32 : 32 ≤ out.size) (houtSize : out.size < UInt256.size) :
    let memCopy := auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled o
    let awCopy := auctionSettleAuctionPayoutNonemptyAwCopy o
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
  let memCopy := auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled o
  let awCopy := auctionSettleAuctionPayoutNonemptyAwCopy o
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
      auctionSettleAuctionPayoutNonemptyMemCopy_mload64
        noun amount start finish bidder settled hosmall hne
  have hmemReturnSize : memReturn.size = memTransfer.size := by
    simpa [memReturn, memTransfer, memDeposit, memCopy, awCopy, freePtr, len] using
      auctionSettleAuctionPayoutNonemptyTransferReturnMem_size_any
        noun amount start finish bidder settled owner hosmall hne houtSize
  have hsizeGe : newFree0.toNat + 68 ≤ memTransfer.size := by
    simpa [memTransfer, memDeposit, memCopy, awCopy, freePtr, newFree0, hmload] using
      auctionSettleAuctionPayoutNonemptyTransferMem_size_ge
        noun amount start finish bidder settled owner hosmall hne
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
    auctionSettleAuctionPayoutNonemptyTransferCallAw_bounds
      noun amount start finish bidder settled owner hosmall hne
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

theorem auctionSettleAuctionPayoutNonemptyTransferReturn_baseAddHi
    (noun amount start finish bidder settled : UInt256) {outPay outTransfer : ByteArray}
    (hosmall : outPay.size < 2 ^ 138) (hne : outPay.size ≠ 0)
    (hhi : outTransfer.size < 2 ^ 255) :
    (auctionSettleAuctionDynMload64
        (auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled outPay)
        (auctionSettleAuctionPayoutNonemptyAwCopy outPay)).toNat +
      outTransfer.size < UInt256.size := by
  rw [auctionSettleAuctionPayoutNonemptyMemCopy_mload64
    noun amount start finish bidder settled hosmall hne]
  rw [auctionSettleAuctionPayoutNonemptyNewFree_toNat (o := outPay) hosmall]
  have hroundLe := auctionSettleAuctionPayoutNonemptyRounded_toNat_le (o := outPay) hosmall
  norm_num [UInt256.size] at hosmall hhi ⊢
  omega

theorem auctionSettleAuctionPayoutNonemptyTransferReturnShortRevertDyn
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (noun amount start finish bidder settled owner weth : UInt256)
    {outPay outTransfer : ByteArray} {k C : ℕ}
    (hosmall : outPay.size < 2 ^ 138) (hne : outPay.size ≠ 0)
    (hshort : outTransfer.size < 32) (houtSize : outTransfer.size < UInt256.size)
    (rd :
      let memCopy :=
        auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled outPay
      let awCopy := auctionSettleAuctionPayoutNonemptyAwCopy outPay
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
    auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled outPay
  let awCopy := auctionSettleAuctionPayoutNonemptyAwCopy outPay
  let freePtr := auctionSettleAuctionDynMload64 memCopy awCopy
  let memDeposit := auctionSettleAuctionDynDepositMem memCopy awCopy
  let awCall := auctionSettleAuctionDynDepositCallAw memCopy awCopy
  let memTransfer := auctionSettleAuctionDynTransferMem memDeposit freePtr amount owner
  let awTransfer := auctionSettleAuctionDynTransferAw awCall freePtr
  let len := (min (⟨32⟩ : UInt256) (UInt256.ofNat outTransfer.size)).toNat
  let memReturn := outTransfer.write 0 memTransfer freePtr.toNat len
  let awReturn := UInt256.ofNat (MachineState.M awTransfer.toNat freePtr.toNat 32)
  have hbaseAdd : freePtr.toNat + outTransfer.size < UInt256.size := by
    exact auctionSettleAuctionPayoutNonemptyTransferReturn_baseAddHi
      noun amount start finish bidder settled hosmall hne (by omega)
  have hfp :
      (if (⟨64⟩ : UInt256).toNat ≥ memReturn.size ∨
          (⟨64⟩ : UInt256) ≥ awReturn * ⟨32⟩
        then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (memReturn.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        freePtr := by
    simpa [auctionSettleAuctionDynMload64, memCopy, awCopy, freePtr, memDeposit, awCall,
      memTransfer, awTransfer, len, memReturn, awReturn] using
      auctionSettleAuctionPayoutNonemptyTransferReturnMload64_any
        noun amount start finish bidder settled owner hosmall hne houtSize
  exact auctionSettleAuctionTransferReturnShortRevertAt
    (base := freePtr) (amount := amount) (owner := owner) (weth := weth)
    (rd := rd) hshort hbaseAdd hfp

theorem auctionSettleAuctionPayoutNonemptyTransferReturnHugeRevertDyn
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (noun amount start finish bidder settled owner weth : UInt256)
    {outPay outTransfer : ByteArray} {k C : ℕ}
    (hosmall : outPay.size < 2 ^ 138) (hne : outPay.size ≠ 0)
    (hhuge : (2 : Nat) ^ 255 ≤ outTransfer.size)
    (houtSize : outTransfer.size < UInt256.size)
    (rd :
      let memCopy :=
        auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled outPay
      let awCopy := auctionSettleAuctionPayoutNonemptyAwCopy outPay
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
    auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled outPay
  let awCopy := auctionSettleAuctionPayoutNonemptyAwCopy outPay
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
      auctionSettleAuctionPayoutNonemptyTransferReturnMload64_any
        noun amount start finish bidder settled owner hosmall hne houtSize
  exact auctionSettleAuctionTransferReturnHugeRevertAt
    (base := freePtr) (amount := amount) (owner := owner) (weth := weth)
    (rd := rd) hhuge houtSize hfp

set_option maxHeartbeats 1000000 in
theorem auctionSettleAuctionPayoutNonemptyTransferReturnBoolToEventDyn
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (noun amount start finish bidder settled owner weth : UInt256)
    {outPay outTransfer : ByteArray} {k C : ℕ}
    (hosmall : outPay.size < 2 ^ 138) (hne : outPay.size ≠ 0)
    (hout32 : 32 ≤ outTransfer.size) (houtHi : outTransfer.size < 2 ^ 255)
    (houtSize : outTransfer.size < UInt256.size)
    (hcanon :
      let retWord := UInt256.ofNat (fromByteArrayBigEndian (outTransfer.extract 0 32))
      retWord = ⟨0⟩ ∨ retWord = ⟨1⟩)
    (rd :
      let memCopy :=
        auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled outPay
      let awCopy := auctionSettleAuctionPayoutNonemptyAwCopy outPay
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
    auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled outPay
  let awCopy := auctionSettleAuctionPayoutNonemptyAwCopy outPay
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
    auctionSettleAuctionPayoutNonemptyTransferReturn_baseAddHi
      noun amount start finish bidder settled hosmall hne houtHi
  have hfp :
      (if (⟨64⟩ : UInt256).toNat ≥ memReturn.size ∨
          (⟨64⟩ : UInt256) ≥ awReturn * ⟨32⟩
        then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (memReturn.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        freePtr := by
    simpa [auctionSettleAuctionDynMload64, memCopy, awCopy, freePtr, memDeposit, awCall,
      memTransfer, awTransfer, len, memReturn, awReturn] using
      auctionSettleAuctionPayoutNonemptyTransferReturnMload64_any
        noun amount start finish bidder settled owner hosmall hne houtSize
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
      auctionSettleAuctionPayoutNonemptyTransferReturnMloadFree
        noun amount start finish bidder settled owner hosmall hne hout32 houtSize
  exact auctionSettleAuctionTransferReturnBoolToEventAt
    (base := freePtr) (amount := amount) (owner := owner) (weth := weth)
    (retWord := retWord) (rd := rd) hout32 houtHi hbaseAdd hfp hword
    (by simpa [retWord] using hcanon)

set_option maxHeartbeats 1000000 in
theorem auctionSettleAuctionPayoutNonemptyTransferReturnNoncanonRevertDyn
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (noun amount start finish bidder settled owner weth : UInt256)
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
        auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled outPay
      let awCopy := auctionSettleAuctionPayoutNonemptyAwCopy outPay
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
    auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled outPay
  let awCopy := auctionSettleAuctionPayoutNonemptyAwCopy outPay
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
    auctionSettleAuctionPayoutNonemptyTransferReturn_baseAddHi
      noun amount start finish bidder settled hosmall hne houtHi
  have hfp :
      (if (⟨64⟩ : UInt256).toNat ≥ memReturn.size ∨
          (⟨64⟩ : UInt256) ≥ awReturn * ⟨32⟩
        then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (memReturn.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        freePtr := by
    simpa [auctionSettleAuctionDynMload64, memCopy, awCopy, freePtr, memDeposit, awCall,
      memTransfer, awTransfer, len, memReturn, awReturn] using
      auctionSettleAuctionPayoutNonemptyTransferReturnMload64_any
        noun amount start finish bidder settled owner hosmall hne houtSize
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
      auctionSettleAuctionPayoutNonemptyTransferReturnMloadFree
        noun amount start finish bidder settled owner hosmall hne hout32 houtSize
  exact auctionSettleAuctionTransferReturnNoncanonRevertAt
    (base := freePtr) (amount := amount) (owner := owner) (weth := weth)
    (retWord := retWord) (rd := rd) hout32 houtHi hbaseAdd hfp hword
    (by simpa [retWord] using hnz) (by simpa [retWord] using hno)

theorem auctionSettleAuctionPayoutNonemptyDepositLen
    (noun amount start finish bidder settled : UInt256) {o : ByteArray}
    (hosmall : o.size < 2 ^ 138) (hne : o.size ≠ 0) :
    UInt256.sub
        (⟨4⟩ +
          auctionSettleAuctionDynMload64
            (auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled o)
            (auctionSettleAuctionPayoutNonemptyAwCopy o))
        (auctionSettleAuctionDynMload64
          (auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled o)
          (auctionSettleAuctionPayoutNonemptyAwCopy o)) =
      ⟨4⟩ := by
  rw [auctionSettleAuctionPayoutNonemptyMemCopy_mload64
    noun amount start finish bidder settled hosmall hne]
  exact u256_sub_lit4_add_cancel (by
    have h := auctionSettleAuctionPayoutNonemptyNewFree_add63_lt (o := o) hosmall
    omega)

theorem auctionSettleAuctionPayoutNonemptyTransferLen
    (noun amount start finish bidder settled : UInt256) {o : ByteArray}
    (hosmall : o.size < 2 ^ 138) (hne : o.size ≠ 0) :
    UInt256.sub
        (⟨68⟩ +
          auctionSettleAuctionDynMload64
            (auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled o)
            (auctionSettleAuctionPayoutNonemptyAwCopy o))
        (auctionSettleAuctionDynMload64
          (auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled o)
          (auctionSettleAuctionPayoutNonemptyAwCopy o)) =
      ⟨68⟩ := by
  rw [auctionSettleAuctionPayoutNonemptyMemCopy_mload64
    noun amount start finish bidder settled hosmall hne]
  exact u256_sub_lit68_add_cancel (by
    have hroundLe := auctionSettleAuctionPayoutNonemptyRounded_toNat_le (o := o) hosmall
    rw [auctionSettleAuctionPayoutNonemptyNewFree_toNat (o := o) hosmall]
    norm_num [UInt256.size] at hosmall ⊢
    omega)

theorem auctionSettleAuctionDynDepositMem_readPtr_4 {mem : ByteArray} {aw : UInt256}
    (hgap : (auctionSettleAuctionDynMload64 mem aw).toNat - mem.size < USize.size) :
    (auctionSettleAuctionDynDepositMem mem aw).readWithPadding
        (auctionSettleAuctionDynMload64 mem aw).toNat 4 =
      depositSelector := by
  unfold auctionSettleAuctionDynDepositMem
  have hread := toByteArray_write_read_window_of_gap auctionSettleAuctionDepositSelectorShifted
    mem (auctionSettleAuctionDynMload64 mem aw).toNat 0 4
    (by omega) (by omega) (by omega) hgap
  have hread' :
      (auctionSettleAuctionDepositSelectorShifted.toByteArray.write 0 mem
            (auctionSettleAuctionDynMload64 mem aw).toNat 32).readWithPadding
          (auctionSettleAuctionDynMload64 mem aw).toNat 4 =
        auctionSettleAuctionDepositSelectorShifted.toByteArray.extract 0 4 := by
    simpa [Nat.add_zero] using hread
  rw [hread']
  native_decide

theorem auctionSettleAuctionDynDepositEncode_eq {mem : ByteArray} {aw : UInt256}
    (hgap : (auctionSettleAuctionDynMload64 mem aw).toNat - mem.size < USize.size) :
    auctionConfig.externalABI.encode? "deposit" [] =
      some ((auctionSettleAuctionDynDepositMem mem aw).readWithPadding
        (auctionSettleAuctionDynMload64 mem aw).toNat 4) := by
  rw [auctionSettleAuctionDynDepositMem_readPtr_4 (mem := mem) (aw := aw) hgap]
  simp [auctionConfig, auctionExternalABI]

theorem auctionSettleAuctionPayoutNonemptyDepositEncode_eq
    (noun amount start finish bidder settled : UInt256) {o : ByteArray}
    (hosmall : o.size < 2 ^ 138) (hne : o.size ≠ 0) :
    auctionConfig.externalABI.encode? "deposit" [] =
      some ((auctionSettleAuctionDynDepositMem
          (auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled o)
          (auctionSettleAuctionPayoutNonemptyAwCopy o)).readWithPadding
        (auctionSettleAuctionDynMload64
          (auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled o)
          (auctionSettleAuctionPayoutNonemptyAwCopy o)).toNat 4) := by
  exact auctionSettleAuctionDynDepositEncode_eq
    (mem := auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled o)
    (aw := auctionSettleAuctionPayoutNonemptyAwCopy o)
    (by
      rw [auctionSettleAuctionPayoutNonemptyMemCopy_mload64
        noun amount start finish bidder settled hosmall hne]
      exact auctionSettleAuctionPayoutNonemptyNewFree_memCopy_gap
        noun amount start finish bidder settled hosmall hne)

theorem auctionSettleAuctionPayoutCallFailureNonemptyReturnToFallbackExact
    {cA gh bl σ σ₀ A I}
    {g : Sat256} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {owner amount aw : UInt256} {mem o : ByteArray} {k C : ℕ}
    (hosz : o.size < UInt256.size)
    (hne : o.size ≠ 0)
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4828⟩
      [⟨0⟩, ⟨352⟩, amount, ⟨30000⟩, owner, ⟨0⟩, ⟨0⟩, amount, owner,
        ⟨3347⟩, amount, owner, ⟨4688⟩, ⟨128⟩, ⟨2471⟩, ⟨413⟩,
        auctionSelWord I]
      mem aw o acc k C) :
    let oszWord := UInt256.ofNat o.size
    let freePtr :=
      if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))
    let awFree : UInt256 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
    let rounded := UInt256.land (oszWord + ⟨63⟩) (UInt256.lnot ⟨31⟩)
    let newFree := freePtr + rounded
    let memFree := (UInt256.toByteArray newFree).write 0 mem (⟨64⟩ : UInt256).toNat 32
    let awStoreFree : UInt256 :=
      UInt256.ofNat (MachineState.M awFree.toNat (⟨64⟩ : UInt256).toNat 32)
    let memLen := (UInt256.toByteArray oszWord).write 0 memFree freePtr.toNat 32
    let awLen : UInt256 := UInt256.ofNat (MachineState.M awStoreFree.toNat freePtr.toNat 32)
    let dataPtr := freePtr + ⟨32⟩
    let memCopy := o.write 0 memLen dataPtr.toNat oszWord.toNat
    let awCopy : UInt256 := UInt256.ofNat (MachineState.M awLen.toNat dataPtr.toNat oszWord.toNat)
    ∃ k' C', RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3347⟩
      [⟨0⟩, amount, owner, ⟨4688⟩, ⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I]
      memCopy awCopy o acc k' C' := by
  exact auctionSafeTransferETHReturnNonempty (by simp) hosz hne rd

theorem auctionSettleAuctionPayoutCallFailureNonemptyReturnToFallbackFixed
    {cA gh bl σ σ₀ A I}
    {g : Sat256} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {noun amount start finish bidder settled owner : UInt256} {o : ByteArray} {k C : ℕ}
    (hosz : o.size < UInt256.size)
    (hne : o.size ≠ 0)
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4828⟩
      [⟨0⟩, ⟨352⟩, amount, ⟨30000⟩, owner, ⟨0⟩, ⟨0⟩, amount, owner,
        ⟨3347⟩, amount, owner, ⟨4688⟩, ⟨128⟩, ⟨2471⟩, ⟨413⟩,
        auctionSelWord I]
      (auctionSettleAuctionPayoutLoopMem noun amount start finish bidder settled)
      (UInt256.ofNat 12) o acc k C) :
    ∃ k' C', RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3347⟩
      [⟨0⟩, amount, owner, ⟨4688⟩, ⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionPayoutNonemptyMemCopy noun amount start finish bidder settled o)
      (auctionSettleAuctionPayoutNonemptyAwCopy o) o acc k' C' := by
  have hrd :=
    auctionSettleAuctionPayoutCallFailureNonemptyReturnToFallbackExact
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
      (g := g) (acc := acc) (owner := owner) (amount := amount)
      (aw := UInt256.ofNat 12)
      (mem := auctionSettleAuctionPayoutLoopMem noun amount start finish bidder settled)
      (o := o) hosz hne rd
  simpa [auctionSettleAuctionPayoutLoopMem_mload64, auctionSettleAuctionPayoutNonemptyMemCopy,
    auctionSettleAuctionPayoutNonemptyMemLen, auctionSettleAuctionPayoutNonemptyMemFree,
    auctionSettleAuctionPayoutNonemptyAwCopy, auctionSettleAuctionPayoutNonemptyNewFree,
    auctionSettleAuctionPayoutNonemptyRounded, auctionSettleAuctionPayoutNonemptyOszWord] using hrd

set_option maxHeartbeats 1000000 in
theorem auctionSettleAuctionPayoutFallbackToDepositCallAnyMem {cA gh bl σ σ₀ A I}
    {g : Sat256} {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {amount owner aw : UInt256} {mem o : ByteArray} {k C : ℕ}
    (hwethCode :
      Reasoning.Theory.uniswapExtCodeSizeWord σ'
          (UInt256.land (auctionSlotWord ⟨202⟩ σ' I) solcAddrMask) ≠ ⟨0⟩)
    (hfreeStable :
      auctionSettleAuctionDynMload64
          (auctionSettleAuctionDynDepositMem mem aw)
          (auctionSettleAuctionDynDepositAw mem aw) =
        auctionSettleAuctionDynMload64 mem aw)
    (hlen :
      UInt256.sub (⟨4⟩ + auctionSettleAuctionDynMload64 mem aw)
          (auctionSettleAuctionDynMload64 mem aw) =
        ⟨4⟩)
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3347⟩
      [⟨0⟩, amount, owner, ⟨4688⟩, ⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I]
      mem aw o (cA', σ') k C) :
    let weth := UInt256.land (auctionSlotWord ⟨202⟩ σ' I) solcAddrMask
    let freePtr := auctionSettleAuctionDynMload64 mem aw
    let memDeposit := auctionSettleAuctionDynDepositMem mem aw
    let awAfterLoad := auctionSettleAuctionDynDepositAwAfterMload64 mem aw
    ∃ gasWord k' C',
      RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3431⟩
        [gasWord, weth, amount, freePtr, ⟨4⟩, freePtr, ⟨0⟩, ⟨4⟩ + freePtr,
          amount, ⟨3504541104⟩, weth, amount, owner, ⟨4688⟩, ⟨128⟩, ⟨2471⟩,
          ⟨413⟩, auctionSelWord I]
        memDeposit awAfterLoad o (cA', σ') k' C' := by
  let weth := UInt256.land (auctionSlotWord ⟨202⟩ σ' I) solcAddrMask
  let freePtr := auctionSettleAuctionDynMload64 mem aw
  let awFree := auctionSettleAuctionDynMload64Aw aw
  let memDeposit := auctionSettleAuctionDynDepositMem mem aw
  let awDeposit := auctionSettleAuctionDynDepositAw mem aw
  let freePtr2 := auctionSettleAuctionDynMload64 memDeposit awDeposit
  let awAfterLoad := auctionSettleAuctionDynDepositAwAfterMload64 mem aw
  have rd3356 := evm_run rd with [
    jumpdest, push2 ⟨3570⟩, jumpiNT (by native_decide), push1 ⟨202⟩, push0, swap1]
  obtain ⟨_, _, rd3357₀⟩ := rd3356.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3357⟩ : ∃ k' C', RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3357⟩
      (auctionSlotWord ⟨202⟩ σ' I ::
        [⟨0⟩, amount, owner, ⟨4688⟩, ⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I])
      mem aw o (cA', σ') k' C' := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd3357₀⟩
  have rd3417₀ := evm_run rd3357 with [
    swap1, push2 ⟨256⟩, exp, swap1, div,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and,
    push4 ⟨3504541104⟩, dup3, push1 ⟨64⟩,
    raw mload (Cₘ awFree - Cₘ aw) freePtr awFree (by native_decide)
      (fun _ haws hstks => auctionMloadCost_of_stack haws hstks (by rfl))
      (by rfl) (by rfl) (by evm_ov),
    dup3, push4 ⟨0xffffffff⟩, and, push1 ⟨224⟩, shl, dup2,
    raw mstore (Cₘ awDeposit - Cₘ awFree) memDeposit awDeposit (by native_decide)
      (fun _ haws hstks => mstoreCost_of_stack haws hstks (by rfl))
      (by rfl) (by rfl) (by evm_ov),
    push1 ⟨4⟩, add, push0, push1 ⟨64⟩,
    raw mload (Cₘ awAfterLoad - Cₘ awDeposit) freePtr2 awAfterLoad (by native_decide)
      (fun _ haws hstks => auctionMloadCost_of_stack haws hstks (by rfl))
      (by rfl) (by rfl) (by evm_ov),
    dup1, dup4, sub, dup2, dup6, dup9, dup1]
  have hdiv :
      UInt256.div (auctionSlotWord ⟨202⟩ σ' I)
        (UInt256.exp (⟨256⟩ : UInt256) ⟨0⟩) =
      auctionSlotWord ⟨202⟩ σ' I := by
    apply u256_inj
    rw [show UInt256.exp (⟨256⟩ : UInt256) ⟨0⟩ = ⟨1⟩ by native_decide]
    rw [udiv_toNat]
    exact Nat.div_one (auctionSlotWord ⟨202⟩ σ' I).toNat
  have hmaskConst :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    decide
  have hwethMask :
      UInt256.land solcAddrMask (UInt256.land solcAddrMask (auctionSlotWord ⟨202⟩ σ' I)) =
        weth := by
    change UInt256.land solcAddrMask (UInt256.land solcAddrMask (auctionSlotWord ⟨202⟩ σ' I)) =
      UInt256.land (auctionSlotWord ⟨202⟩ σ' I) solcAddrMask
    rw [u256_land_comm solcAddrMask (auctionSlotWord ⟨202⟩ σ' I)]
    exact solcAddrMask_clean_left
      (solcAddrMask_result_canonical (auctionSlotWord ⟨202⟩ σ' I))
  have rd3417 := rd3417₀
  rw [hdiv, hmaskConst, hwethMask] at rd3417
  have rd3417Stable := rd3417
  have hfreeStableLocal : freePtr2 = freePtr := by
    simpa [freePtr2, freePtr, memDeposit, awDeposit] using hfreeStable
  have hlenLocal : UInt256.sub (⟨4⟩ + freePtr) freePtr = ⟨4⟩ := by
    simpa [freePtr] using hlen
  rw [hfreeStableLocal, hlenLocal] at rd3417Stable
  exact RD.uniswapExtcodesizeGuardOkGas (pc := ⟨3417⟩) (okPc := ⟨3428⟩) rd3417Stable
    hwethCode (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
    (by native_decide) (by native_decide) (by simp)

theorem auctionSettleAuctionDepositSuccessToTransferLoadWethAnyMem
    {cA gh bl σ σ₀ A I}
    {g : Sat256} {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {amount owner wethBefore aw freePtr : UInt256} {mem o : ByteArray} {k C : ℕ}
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3432⟩
      [⟨1⟩, ⟨4⟩ + freePtr, amount, ⟨3504541104⟩, wethBefore, amount, owner,
        ⟨4688⟩, ⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I]
      mem aw o (cA', σ') k C) :
    ∃ k' C', RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3452⟩
      (auctionSlotWord ⟨202⟩ σ' I ::
        [amount, ⟨3504541104⟩, wethBefore, amount, owner, ⟨4688⟩, ⟨128⟩,
          ⟨2471⟩, ⟨413⟩, auctionSelWord I])
      mem aw o (cA', σ') k' C' := by
  have rd3449 := evm_run rd with [
    iszero, dup1, iszero, push2 ⟨3446⟩, jumpiT (by native_decide) (by jump_dest),
    jumpdest, pop, pop, push1 ⟨202⟩]
  obtain ⟨_, _, rd3452₀⟩ := rd3449.sload (by native_decide) (by evm_ov)
  exact ⟨_, _, by simpa [auctionSlotWord] using rd3452₀⟩

theorem auctionSettleAuctionAfterDepositLoadFreePtrAnyMem
    {cA gh bl σ σ₀ A I}
    {g : Sat256} {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {amount owner wethBefore aw freePtr : UInt256} {mem o : ByteArray} {k C : ℕ}
    (hfree : auctionSettleAuctionDynMload64 mem aw = freePtr)
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3452⟩
      (auctionSlotWord ⟨202⟩ σ' I ::
        [amount, ⟨3504541104⟩, wethBefore, amount, owner, ⟨4688⟩, ⟨128⟩,
          ⟨2471⟩, ⟨413⟩, auctionSelWord I])
      mem aw o (cA', σ') k C) :
    ∃ k' C', RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3455⟩
      [freePtr, auctionSlotWord ⟨202⟩ σ' I, amount, ⟨3504541104⟩, wethBefore, amount,
        owner, ⟨4688⟩, ⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I]
      mem (auctionSettleAuctionDynMload64Aw aw) o (cA', σ') k' C' := by
  have rdPart := evm_run rd with [
    push1 ⟨64⟩,
    raw mload
      (Cₘ (auctionSettleAuctionDynMload64Aw aw) - Cₘ aw)
      freePtr (auctionSettleAuctionDynMload64Aw aw) (by native_decide)
      (fun _ haws hstks => auctionMloadCost_of_stack haws hstks (by rfl))
      (by simpa [auctionSettleAuctionDynMload64] using hfree)
      (by rfl) (by evm_ov)]
  exact ⟨_, _, by simpa using rdPart⟩

theorem auctionSettleAuctionAfterDepositStoreTransferSelectorAnyMem
    {cA gh bl σ σ₀ A I}
    {g : Sat256} {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {amount owner wethBefore aw freePtr : UInt256} {mem o : ByteArray} {k C : ℕ}
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3455⟩
      [freePtr, auctionSlotWord ⟨202⟩ σ' I, amount, ⟨3504541104⟩, wethBefore, amount,
        owner, ⟨4688⟩, ⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I]
      mem (auctionSettleAuctionDynMload64Aw aw) o (cA', σ') k C) :
    ∃ k' C', RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3465⟩
      [freePtr, auctionSlotWord ⟨202⟩ σ' I, amount, ⟨3504541104⟩, wethBefore, amount,
        owner, ⟨4688⟩, ⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionDynTransferSelMem mem freePtr)
      (auctionSettleAuctionDynTransferSelAw aw freePtr) o (cA', σ') k' C' := by
  let awFree := auctionSettleAuctionDynMload64Aw aw
  let memSel := auctionSettleAuctionDynTransferSelMem mem freePtr
  let awSel := auctionSettleAuctionDynTransferSelAw aw freePtr
  have rdPart := evm_run rd with [
    push4 ⟨2835717307⟩, push1 ⟨224⟩, shl, dup2,
    raw mstore (Cₘ awSel - Cₘ awFree) memSel awSel (by native_decide)
      (fun _ haws hstks => mstoreCost_of_stack haws hstks (by rfl))
      (by rfl) (by rfl) (by evm_ov)]
  exact ⟨_, _, by simpa [memSel, awSel] using rdPart⟩

theorem auctionSettleAuctionAfterDepositStoreTransferOwnerAnyMem
    {cA gh bl σ σ₀ A I}
    {g : Sat256} {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {amount owner wethBefore aw freePtr : UInt256} {mem o : ByteArray} {k C : ℕ}
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3465⟩
      [freePtr, auctionSlotWord ⟨202⟩ σ' I, amount, ⟨3504541104⟩, wethBefore, amount,
        owner, ⟨4688⟩, ⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionDynTransferSelMem mem freePtr)
      (auctionSettleAuctionDynTransferSelAw aw freePtr) o (cA', σ') k C) :
    ∃ k' C', RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3481⟩
      [solcAddrMask, freePtr, auctionSlotWord ⟨202⟩ σ' I, amount, ⟨3504541104⟩,
        wethBefore, amount, owner, ⟨4688⟩, ⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionDynTransferArgMem mem freePtr amount owner)
      (auctionSettleAuctionDynTransferArgAw aw freePtr) o (cA', σ') k' C' := by
  let memArg := auctionSettleAuctionDynTransferArgMem mem freePtr amount owner
  let awSel := auctionSettleAuctionDynTransferSelAw aw freePtr
  let awArg := auctionSettleAuctionDynTransferArgAw aw freePtr
  have rdPart := evm_run rd with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup8, dup2, and,
    push1 ⟨4⟩, dup4, add,
    raw mstore (Cₘ awArg - Cₘ awSel) memArg awArg (by native_decide)
      (fun _ haws hstks => mstoreCost_of_stack haws hstks (by
        dsimp [awArg, awSel, auctionSettleAuctionDynTransferArgAw]))
      (by rfl) (by rfl) (by evm_ov)]
  have hmaskConst :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    decide
  have rdPart' := rdPart
  rw [hmaskConst] at rdPart'
  exact ⟨_, _, by simpa [memArg, awArg] using rdPart'⟩

theorem auctionSettleAuctionAfterDepositStoreTransferAmountAnyMem
    {cA gh bl σ σ₀ A I}
    {g : Sat256} {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {amount owner wethBefore aw freePtr : UInt256} {mem o : ByteArray} {k C : ℕ}
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3481⟩
      [solcAddrMask, freePtr, auctionSlotWord ⟨202⟩ σ' I, amount, ⟨3504541104⟩,
        wethBefore, amount, owner, ⟨4688⟩, ⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionDynTransferArgMem mem freePtr amount owner)
      (auctionSettleAuctionDynTransferArgAw aw freePtr) o (cA', σ') k C) :
    ∃ k' C', RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3488⟩
      [solcAddrMask, freePtr, auctionSlotWord ⟨202⟩ σ' I, amount, ⟨3504541104⟩,
        wethBefore, amount, owner, ⟨4688⟩, ⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionDynTransferMem mem freePtr amount owner)
      (auctionSettleAuctionDynTransferAw aw freePtr) o (cA', σ') k' C' := by
  let memTransfer := auctionSettleAuctionDynTransferMem mem freePtr amount owner
  let awArg := auctionSettleAuctionDynTransferArgAw aw freePtr
  let awTransfer := auctionSettleAuctionDynTransferAw aw freePtr
  have rdPart := evm_run rd with [
    push1 ⟨36⟩, dup3, add, dup8, swap1,
    raw mstore (Cₘ awTransfer - Cₘ awArg) memTransfer awTransfer (by native_decide)
      (fun _ haws hstks => mstoreCost_of_stack haws hstks (by
        dsimp [awTransfer, awArg, auctionSettleAuctionDynTransferAw]))
      (by rfl) (by rfl) (by evm_ov)]
  exact ⟨_, _, by simpa [memTransfer, awTransfer] using rdPart⟩

theorem auctionSettleAuctionAfterDepositPrepTransferCallAnyMem
    {cA gh bl σ σ₀ A I}
    {g : Sat256} {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {amount owner wethBefore aw freePtr : UInt256} {mem o : ByteArray} {k C : ℕ}
    (hfree :
      auctionSettleAuctionDynMload64
          (auctionSettleAuctionDynTransferMem mem freePtr amount owner)
          (auctionSettleAuctionDynTransferAw aw freePtr) =
        freePtr)
    (hlen : UInt256.sub ((⟨68⟩ : UInt256) + freePtr) freePtr = ⟨68⟩)
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3488⟩
      [solcAddrMask, freePtr, auctionSlotWord ⟨202⟩ σ' I, amount, ⟨3504541104⟩,
        wethBefore, amount, owner, ⟨4688⟩, ⟨128⟩, ⟨2471⟩, ⟨413⟩, auctionSelWord I]
      (auctionSettleAuctionDynTransferMem mem freePtr amount owner)
      (auctionSettleAuctionDynTransferAw aw freePtr) o (cA', σ') k C) :
    let weth := UInt256.land (auctionSlotWord ⟨202⟩ σ' I) solcAddrMask
    ∃ gasWord k' C',
      RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3517⟩
        [gasWord, weth, ⟨0⟩, freePtr, ⟨68⟩, freePtr, ⟨32⟩, ⟨68⟩ + freePtr,
          ⟨2835717307⟩, weth, amount, owner, ⟨4688⟩, ⟨128⟩, ⟨2471⟩, ⟨413⟩,
          auctionSelWord I]
        (auctionSettleAuctionDynTransferMem mem freePtr amount owner)
        (auctionSettleAuctionDynTransferAwAfterMload64 aw freePtr)
        o (cA', σ') k' C' := by
  let weth := UInt256.land (auctionSlotWord ⟨202⟩ σ' I) solcAddrMask
  let memTransfer := auctionSettleAuctionDynTransferMem mem freePtr amount owner
  let awTransfer := auctionSettleAuctionDynTransferAw aw freePtr
  let awAfterLoad := auctionSettleAuctionDynTransferAwAfterMload64 aw freePtr
  have rd3516Fn := evm_run rd with [
    swap1, swap2, and, swap4, pop, push4 ⟨2835717307⟩, swap3, pop,
    push1 ⟨68⟩, add, swap1, pop, push1 ⟨32⟩, push1 ⟨64⟩,
    raw mload (Cₘ awAfterLoad - Cₘ awTransfer) freePtr awAfterLoad (by native_decide)
      (fun _ haws hstks => auctionMloadCost_of_stack haws hstks (by
        dsimp [awAfterLoad, awTransfer, auctionSettleAuctionDynTransferAwAfterMload64]))
      (by simpa [memTransfer, awTransfer, auctionSettleAuctionDynMload64] using hfree)
      (by rfl) (by evm_ov),
    dup1, dup4, sub, dup2, push0, dup8]
  have rd3516 := rd3516Fn
  rw [hlen] at rd3516
  obtain ⟨gasWord, rd3517⟩ := rd3516.gas (by native_decide) (by evm_ov)
  exact ⟨gasWord, _, _, by simpa [weth, memTransfer, awAfterLoad] using rd3517⟩

end Auction
