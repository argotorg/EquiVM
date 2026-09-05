import Benchmarks.Auction.SettleAuctionTransferBranchPayoutEmpty

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Auction

theorem transferBranchTransferFromPayoutLoopDynTransferAwAw14
    (noun amount start finish bidder settled caller : UInt256) :
    auctionSettleAuctionDynTransferAw
        (auctionSettleAuctionDynDepositCallAw
          (auctionSettleAuctionTransferFromPayoutLoopMem
            noun amount start finish bidder settled caller)
          (UInt256.ofNat 14))
        (auctionSettleAuctionDynMload64
          (auctionSettleAuctionTransferFromPayoutLoopMem
            noun amount start finish bidder settled caller)
          (UInt256.ofNat 14)) =
      UInt256.ofNat 14 := by
  rw [transferBranchTransferFromPayoutLoopDynMload64Aw14]
  rw [transferBranchTransferFromPayoutLoopDynDepositCallAwAw14]
  unfold auctionSettleAuctionDynTransferAw auctionSettleAuctionDynTransferArgAw
    auctionSettleAuctionDynTransferSelAw auctionSettleAuctionDynMload64Aw
  native_decide

theorem transferBranchTransferFromPayoutLoopDynTransferLenAw14
    (noun amount start finish bidder settled caller : UInt256) :
    UInt256.sub
        ((⟨68⟩ : UInt256) +
          auctionSettleAuctionDynMload64
            (auctionSettleAuctionTransferFromPayoutLoopMem
              noun amount start finish bidder settled caller)
            (UInt256.ofNat 14))
        (auctionSettleAuctionDynMload64
          (auctionSettleAuctionTransferFromPayoutLoopMem
            noun amount start finish bidder settled caller)
          (UInt256.ofNat 14)) =
      ⟨68⟩ := by
  rw [transferBranchTransferFromPayoutLoopDynMload64Aw14]
  native_decide

theorem transferBranchTransferFromPayoutLoopDynTransferMload64FixedAw14
    (noun amount start finish bidder settled caller owner : UInt256) :
    let memLoop :=
      auctionSettleAuctionTransferFromPayoutLoopMem
        noun amount start finish bidder settled caller
    let memDeposit := auctionSettleAuctionDynDepositMem memLoop (UInt256.ofNat 14)
    auctionSettleAuctionDynMload64
        (auctionSettleAuctionDynTransferMem memDeposit (⟨352⟩ : UInt256) amount owner)
        (UInt256.ofNat 14) =
      ⟨352⟩ := by
  intro memLoop memDeposit
  let memSel := auctionSettleAuctionDynTransferSelMem memDeposit (⟨352⟩ : UInt256)
  let memArg := auctionSettleAuctionDynTransferArgMem memDeposit (⟨352⟩ : UInt256)
    amount owner
  have hbase : auctionSettleAuctionDynMload64 memLoop (UInt256.ofNat 14) = ⟨352⟩ := by
    simpa [memLoop] using
      transferBranchTransferFromPayoutLoopDynMload64Aw14
        noun amount start finish bidder settled caller
  have hmemDepositSize : memDeposit.size = 420 := by
    dsimp [memDeposit, auctionSettleAuctionDynDepositMem]
    rw [hbase]
    exact toByteArray_write32_size_of_le memLoop
      auctionSettleAuctionDepositSelectorShifted 352 420 420
      (auctionSettleAuctionTransferFromPayoutLoopMem_size
        noun amount start finish bidder settled caller)
      (by
        rw [auctionSettleAuctionTransferFromPayoutLoopMem_size]
        omega)
      (by decide)
  have hmemSelSize : memSel.size = 420 := by
    dsimp [memSel, auctionSettleAuctionDynTransferSelMem]
    exact toByteArray_write32_size_of_le memDeposit
      auctionSettleAuctionTransferSelectorShifted 352 420 420
      hmemDepositSize
      (by rw [hmemDepositSize]; omega)
      (by decide)
  have hmemArgSize : memArg.size = 420 := by
    dsimp [memArg, auctionSettleAuctionDynTransferArgMem]
    rw [show ((⟨352⟩ : UInt256) + (⟨4⟩ : UInt256)).toNat = 356 by native_decide]
    exact toByteArray_write32_size_of_le memSel (UInt256.land solcAddrMask owner)
      356 420 420 hmemSelSize (by rw [hmemSelSize]; omega) (by decide)
  unfold auctionSettleAuctionDynMload64
  rw [if_neg (by
    show ¬((⟨64⟩ : UInt256).toNat ≥
        (auctionSettleAuctionDynTransferMem memDeposit (⟨352⟩ : UInt256) amount owner).size ∨
      (⟨64⟩ : UInt256) ≥ UInt256.ofNat 14 * ⟨32⟩)
    dsimp [auctionSettleAuctionDynTransferMem]
    rw [show ((⟨352⟩ : UInt256) + (⟨36⟩ : UInt256)).toNat = 388 by native_decide]
    have htransferSize :
        ((UInt256.toByteArray amount).write 0 memArg 388 32).size = 420 := by
      exact toByteArray_write32_size_of_le memArg amount 388 420 420 hmemArgSize
        (by rw [hmemArgSize]; omega) (by decide)
    rw [htransferSize]
    native_decide)]
  dsimp [auctionSettleAuctionDynTransferMem]
  rw [show ((⟨352⟩ : UInt256) + (⟨36⟩ : UInt256)).toNat = 388 by native_decide]
  rw [toByteArray_write_read_below_of_gap amount
    memArg 388 (⟨64⟩ : UInt256).toNat
    (by rw [hmemArgSize]; decide) (by decide) (by rw [hmemArgSize]; native_decide)]
  dsimp [memArg, auctionSettleAuctionDynTransferArgMem]
  rw [show ((⟨352⟩ : UInt256) + (⟨4⟩ : UInt256)).toNat = 356 by native_decide]
  rw [toByteArray_write_read_below_of_gap (UInt256.land solcAddrMask owner)
    memSel 356 (⟨64⟩ : UInt256).toNat
    (by rw [hmemSelSize]; decide) (by decide) (by rw [hmemSelSize]; native_decide)]
  dsimp [memSel, auctionSettleAuctionDynTransferSelMem]
  rw [show ((⟨352⟩ : UInt256).toNat) = 352 by native_decide]
  rw [toByteArray_write_read_below_len_of_gap auctionSettleAuctionTransferSelectorShifted
    memDeposit 352 (⟨64⟩ : UInt256).toNat 32
    (by rw [hmemDepositSize]; decide)
    (by decide) (by decide) (by decide)
    (by rw [hmemDepositSize]; native_decide)]
  dsimp [memDeposit, auctionSettleAuctionDynDepositMem]
  rw [hbase]
  rw [show ((⟨352⟩ : UInt256).toNat) = 352 by native_decide]
  rw [toByteArray_write_read_below_len_of_gap auctionSettleAuctionDepositSelectorShifted
    memLoop 352 (⟨64⟩ : UInt256).toNat 32
    (by rw [auctionSettleAuctionTransferFromPayoutLoopMem_size]; decide)
    (by decide) (by decide) (by decide)
    (by rw [auctionSettleAuctionTransferFromPayoutLoopMem_size]; native_decide)]
  have hloop :=
    auctionSettleAuctionTransferFromPayoutLoopMem_mload64
      noun amount start finish bidder settled caller
  have hloopCond :
      ¬((⟨64⟩ : UInt256).toNat ≥ memLoop.size ∨
        (⟨64⟩ : UInt256) ≥ UInt256.ofNat 14 * ⟨32⟩) := by
    rw [auctionSettleAuctionTransferFromPayoutLoopMem_size]
    decide
  rw [if_neg hloopCond] at hloop
  simpa [memLoop] using hloop

theorem transferBranchTransferFromPayoutLoopDynTransferFreeStableAw14
    (noun amount start finish bidder settled caller owner : UInt256) :
    auctionSettleAuctionDynMload64
        (auctionSettleAuctionDynTransferMem
          (auctionSettleAuctionDynDepositMem
            (auctionSettleAuctionTransferFromPayoutLoopMem
              noun amount start finish bidder settled caller)
            (UInt256.ofNat 14))
          (auctionSettleAuctionDynMload64
            (auctionSettleAuctionTransferFromPayoutLoopMem
              noun amount start finish bidder settled caller)
            (UInt256.ofNat 14))
          amount owner)
        (auctionSettleAuctionDynTransferAw
          (auctionSettleAuctionDynDepositCallAw
            (auctionSettleAuctionTransferFromPayoutLoopMem
              noun amount start finish bidder settled caller)
            (UInt256.ofNat 14))
          (auctionSettleAuctionDynMload64
            (auctionSettleAuctionTransferFromPayoutLoopMem
              noun amount start finish bidder settled caller)
            (UInt256.ofNat 14))) =
      auctionSettleAuctionDynMload64
        (auctionSettleAuctionTransferFromPayoutLoopMem
          noun amount start finish bidder settled caller)
        (UInt256.ofNat 14) := by
  rw [transferBranchTransferFromPayoutLoopDynTransferAwAw14]
  rw [transferBranchTransferFromPayoutLoopDynMload64Aw14]
  exact transferBranchTransferFromPayoutLoopDynTransferMload64FixedAw14
    noun amount start finish bidder settled caller owner

theorem transferBranchTransferFromPayoutLoopDynTransferMemSizesAw14
    (noun amount start finish bidder settled caller owner : UInt256) :
    let memLoop :=
      auctionSettleAuctionTransferFromPayoutLoopMem
        noun amount start finish bidder settled caller
    let memDeposit := auctionSettleAuctionDynDepositMem memLoop (UInt256.ofNat 14)
    let memSel := auctionSettleAuctionDynTransferSelMem memDeposit (⟨352⟩ : UInt256)
    let memArg := auctionSettleAuctionDynTransferArgMem memDeposit (⟨352⟩ : UInt256)
      amount owner
    memDeposit.size = 420 ∧ memSel.size = 420 ∧ memArg.size = 420 := by
  intro memLoop memDeposit memSel memArg
  have hbase : auctionSettleAuctionDynMload64 memLoop (UInt256.ofNat 14) = ⟨352⟩ := by
    simpa [memLoop] using
      transferBranchTransferFromPayoutLoopDynMload64Aw14
        noun amount start finish bidder settled caller
  have hmemDepositSize : memDeposit.size = 420 := by
    dsimp [memDeposit, auctionSettleAuctionDynDepositMem]
    rw [hbase]
    exact toByteArray_write32_size_of_le memLoop
      auctionSettleAuctionDepositSelectorShifted 352 420 420
      (auctionSettleAuctionTransferFromPayoutLoopMem_size
        noun amount start finish bidder settled caller)
      (by
        rw [auctionSettleAuctionTransferFromPayoutLoopMem_size]
        omega)
      (by decide)
  have hmemSelSize : memSel.size = 420 := by
    dsimp [memSel, auctionSettleAuctionDynTransferSelMem]
    exact toByteArray_write32_size_of_le memDeposit
      auctionSettleAuctionTransferSelectorShifted 352 420 420
      hmemDepositSize
      (by rw [hmemDepositSize]; omega)
      (by decide)
  have hmemArgSize : memArg.size = 420 := by
    dsimp [memArg, auctionSettleAuctionDynTransferArgMem]
    rw [show ((⟨352⟩ : UInt256) + (⟨4⟩ : UInt256)).toNat = 356 by native_decide]
    exact toByteArray_write32_size_of_le memSel (UInt256.land solcAddrMask owner)
      356 420 420 hmemSelSize (by rw [hmemSelSize]; omega) (by decide)
  exact ⟨hmemDepositSize, hmemSelSize, hmemArgSize⟩

theorem transferBranchTransferFromPayoutLoopDynTransferMemRead352_4Aw14
    (noun amount start finish bidder settled caller owner : UInt256) :
    (auctionSettleAuctionDynTransferMem
        (auctionSettleAuctionDynDepositMem
          (auctionSettleAuctionTransferFromPayoutLoopMem
            noun amount start finish bidder settled caller)
          (UInt256.ofNat 14))
        (⟨352⟩ : UInt256) amount owner).readWithPadding 352 4 =
      transferSelector := by
  let memLoop :=
    auctionSettleAuctionTransferFromPayoutLoopMem
      noun amount start finish bidder settled caller
  let memDeposit := auctionSettleAuctionDynDepositMem memLoop (UInt256.ofNat 14)
  let memSel := auctionSettleAuctionDynTransferSelMem memDeposit (⟨352⟩ : UInt256)
  let memArg := auctionSettleAuctionDynTransferArgMem memDeposit (⟨352⟩ : UInt256)
    amount owner
  have hsizes :=
    transferBranchTransferFromPayoutLoopDynTransferMemSizesAw14
      noun amount start finish bidder settled caller owner
  have hmemDepositSize : memDeposit.size = 420 := by
    simpa [memLoop, memDeposit, memSel, memArg] using hsizes.1
  have hmemSelSize : memSel.size = 420 := by
    simpa [memLoop, memDeposit, memSel, memArg] using hsizes.2.1
  have hmemArgSize : memArg.size = 420 := by
    simpa [memLoop, memDeposit, memSel, memArg] using hsizes.2.2
  dsimp [auctionSettleAuctionDynTransferMem]
  rw [show ((⟨352⟩ : UInt256) + (⟨36⟩ : UInt256)).toNat = 388 by native_decide]
  rw [toByteArray_write_read_below_len_of_gap amount memArg 388 352 4
    (by rw [hmemArgSize]; omega) (by omega) (by omega) (by omega)
    (by rw [hmemArgSize]; native_decide)]
  dsimp [memArg, auctionSettleAuctionDynTransferArgMem]
  rw [show ((⟨352⟩ : UInt256) + (⟨4⟩ : UInt256)).toNat = 356 by native_decide]
  rw [toByteArray_write_read_below_len_of_gap (UInt256.land solcAddrMask owner)
    memSel 356 352 4 (by rw [hmemSelSize]; omega) (by omega) (by omega) (by omega)
    (by rw [hmemSelSize]; native_decide)]
  dsimp [memSel, auctionSettleAuctionDynTransferSelMem]
  rw [show ((⟨352⟩ : UInt256).toNat) = 352 by native_decide]
  rw [toByteArray_write_read_window_of_gap auctionSettleAuctionTransferSelectorShifted
    memDeposit 352 0 4
    (by omega) (by omega) (by omega)
    (by rw [hmemDepositSize]; native_decide)]
  native_decide

theorem transferBranchTransferFromPayoutLoopDynTransferMemRead356_32Aw14
    (noun amount start finish bidder settled caller owner : UInt256) :
    (auctionSettleAuctionDynTransferMem
        (auctionSettleAuctionDynDepositMem
          (auctionSettleAuctionTransferFromPayoutLoopMem
            noun amount start finish bidder settled caller)
          (UInt256.ofNat 14))
        (⟨352⟩ : UInt256) amount owner).readWithPadding 356 32 =
      UInt256.toByteArray (UInt256.land solcAddrMask owner) := by
  let memLoop :=
    auctionSettleAuctionTransferFromPayoutLoopMem
      noun amount start finish bidder settled caller
  let memDeposit := auctionSettleAuctionDynDepositMem memLoop (UInt256.ofNat 14)
  let memSel := auctionSettleAuctionDynTransferSelMem memDeposit (⟨352⟩ : UInt256)
  let memArg := auctionSettleAuctionDynTransferArgMem memDeposit (⟨352⟩ : UInt256)
    amount owner
  have hsizes :=
    transferBranchTransferFromPayoutLoopDynTransferMemSizesAw14
      noun amount start finish bidder settled caller owner
  have hmemSelSize : memSel.size = 420 := by
    simpa [memLoop, memDeposit, memSel, memArg] using hsizes.2.1
  have hmemArgSize : memArg.size = 420 := by
    simpa [memLoop, memDeposit, memSel, memArg] using hsizes.2.2
  dsimp [auctionSettleAuctionDynTransferMem]
  rw [show ((⟨352⟩ : UInt256) + (⟨36⟩ : UInt256)).toNat = 388 by native_decide]
  rw [toByteArray_write_read_below_len_of_gap amount memArg 388 356 32
    (by rw [hmemArgSize]; omega) (by omega) (by omega) (by omega)
    (by rw [hmemArgSize]; native_decide)]
  dsimp [memArg, auctionSettleAuctionDynTransferArgMem]
  rw [show ((⟨352⟩ : UInt256) + (⟨4⟩ : UInt256)).toNat = 356 by native_decide]
  exact toByteArray_write_read_back_of_gap (UInt256.land solcAddrMask owner)
    memSel 356 (by rw [hmemSelSize]; native_decide)

theorem transferBranchTransferFromPayoutLoopDynTransferMemRead388_32Aw14
    (noun amount start finish bidder settled caller owner : UInt256) :
    (auctionSettleAuctionDynTransferMem
        (auctionSettleAuctionDynDepositMem
          (auctionSettleAuctionTransferFromPayoutLoopMem
            noun amount start finish bidder settled caller)
          (UInt256.ofNat 14))
        (⟨352⟩ : UInt256) amount owner).readWithPadding 388 32 =
      UInt256.toByteArray amount := by
  let memLoop :=
    auctionSettleAuctionTransferFromPayoutLoopMem
      noun amount start finish bidder settled caller
  let memDeposit := auctionSettleAuctionDynDepositMem memLoop (UInt256.ofNat 14)
  let memSel := auctionSettleAuctionDynTransferSelMem memDeposit (⟨352⟩ : UInt256)
  let memArg := auctionSettleAuctionDynTransferArgMem memDeposit (⟨352⟩ : UInt256)
    amount owner
  have hsizes :=
    transferBranchTransferFromPayoutLoopDynTransferMemSizesAw14
      noun amount start finish bidder settled caller owner
  have hmemArgSize : memArg.size = 420 := by
    simpa [memLoop, memDeposit, memSel, memArg] using hsizes.2.2
  dsimp [auctionSettleAuctionDynTransferMem]
  rw [show ((⟨352⟩ : UInt256) + (⟨36⟩ : UInt256)).toNat = 388 by native_decide]
  exact toByteArray_write_read_back_of_gap amount memArg 388
    (by rw [hmemArgSize]; native_decide)

theorem transferBranchTransferFromPayoutLoopDynTransferMemRead352_68Aw14
    (noun amount start finish bidder settled caller owner : UInt256) :
    (auctionSettleAuctionDynTransferMem
        (auctionSettleAuctionDynDepositMem
          (auctionSettleAuctionTransferFromPayoutLoopMem
            noun amount start finish bidder settled caller)
          (UInt256.ofNat 14))
        (⟨352⟩ : UInt256) amount owner).readWithPadding 352 68 =
      transferSelector ++ UInt256.toByteArray (UInt256.land solcAddrMask owner) ++
        UInt256.toByteArray amount := by
  let memTransfer :=
    auctionSettleAuctionDynTransferMem
      (auctionSettleAuctionDynDepositMem
        (auctionSettleAuctionTransferFromPayoutLoopMem
          noun amount start finish bidder settled caller)
        (UInt256.ofNat 14))
      (⟨352⟩ : UInt256) amount owner
  have hsize : memTransfer.size = 420 := by
    let memLoop :=
      auctionSettleAuctionTransferFromPayoutLoopMem
        noun amount start finish bidder settled caller
    let memDeposit := auctionSettleAuctionDynDepositMem memLoop (UInt256.ofNat 14)
    let memSel := auctionSettleAuctionDynTransferSelMem memDeposit (⟨352⟩ : UInt256)
    let memArg := auctionSettleAuctionDynTransferArgMem memDeposit (⟨352⟩ : UInt256)
      amount owner
    have hsizes :=
      transferBranchTransferFromPayoutLoopDynTransferMemSizesAw14
        noun amount start finish bidder settled caller owner
    have hmemArgSize : memArg.size = 420 := by
      simpa [memLoop, memDeposit, memSel, memArg] using hsizes.2.2
    dsimp [memTransfer, auctionSettleAuctionDynTransferMem]
    rw [show ((⟨352⟩ : UInt256) + (⟨36⟩ : UInt256)).toNat = 388 by native_decide]
    exact toByteArray_write32_size_of_le memArg amount 388 420 420 hmemArgSize
      (by rw [hmemArgSize]; omega) (by decide)
  rw [show 68 = 4 + 64 from rfl,
    byteArray_readWithPadding_split memTransfer 352 4 64
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [show 64 = 32 + 32 from rfl,
    byteArray_readWithPadding_split memTransfer 356 32 32
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [show memTransfer.readWithPadding 352 4 = transferSelector by
    simpa [memTransfer] using
      transferBranchTransferFromPayoutLoopDynTransferMemRead352_4Aw14
        noun amount start finish bidder settled caller owner]
  rw [show memTransfer.readWithPadding 356 32 =
      UInt256.toByteArray (UInt256.land solcAddrMask owner) by
    simpa [memTransfer] using
      transferBranchTransferFromPayoutLoopDynTransferMemRead356_32Aw14
        noun amount start finish bidder settled caller owner]
  rw [show memTransfer.readWithPadding 388 32 = UInt256.toByteArray amount by
    simpa [memTransfer] using
      transferBranchTransferFromPayoutLoopDynTransferMemRead388_32Aw14
        noun amount start finish bidder settled caller owner]
  simp [ByteArray.append_assoc]

theorem transferBranchTransferFromPayoutLoopDynTransferEncodeEqAw14
    (noun amount start finish bidder settled caller owner : UInt256)
    (howner :
      UInt256.toNat (UInt256.land solcAddrMask owner) < EVM.addressModulus) :
    auctionConfig.externalABI.encode? "transfer"
        [.address (AccountAddress.ofUInt256 (UInt256.land solcAddrMask owner)),
          .int (Int.ofNat amount.toNat)] =
      some ((auctionSettleAuctionDynTransferMem
        (auctionSettleAuctionDynDepositMem
          (auctionSettleAuctionTransferFromPayoutLoopMem
            noun amount start finish bidder settled caller)
          (UInt256.ofNat 14))
        (⟨352⟩ : UInt256) amount owner).readWithPadding 352 68) := by
  have hfixed :=
    auctionSettleAuctionWethTransferEncode_eq noun amount start finish bidder settled owner howner
  rw [auctionSettleAuctionWethTransferMem_read352_68] at hfixed
  rw [transferBranchTransferFromPayoutLoopDynTransferMemRead352_68Aw14
    noun amount start finish bidder settled caller owner]
  exact hfixed

theorem transferBranchTransferFromPayoutLoopDynTransferMemSizeAw14
    (noun amount start finish bidder settled caller owner : UInt256) :
    let memLoop :=
      auctionSettleAuctionTransferFromPayoutLoopMem
        noun amount start finish bidder settled caller
    let memDeposit := auctionSettleAuctionDynDepositMem memLoop (UInt256.ofNat 14)
    let memTransfer := auctionSettleAuctionDynTransferMem memDeposit (⟨352⟩ : UInt256)
      amount owner
    memTransfer.size = 420 := by
  intro memLoop memDeposit memTransfer
  let memSel := auctionSettleAuctionDynTransferSelMem memDeposit (⟨352⟩ : UInt256)
  let memArg := auctionSettleAuctionDynTransferArgMem memDeposit (⟨352⟩ : UInt256)
    amount owner
  have hsizes :=
    transferBranchTransferFromPayoutLoopDynTransferMemSizesAw14
      noun amount start finish bidder settled caller owner
  have hmemArgSize : memArg.size = 420 := by
    simpa [memLoop, memDeposit, memSel, memArg] using hsizes.2.2
  dsimp [memTransfer, auctionSettleAuctionDynTransferMem]
  rw [show ((⟨352⟩ : UInt256) + (⟨36⟩ : UInt256)).toNat = 388 by native_decide]
  exact toByteArray_write32_size_of_le memArg amount 388 420 420 hmemArgSize
    (by rw [hmemArgSize]; omega) (by decide)

theorem transferBranchTransferFromPayoutLoopDynTransferReturnMemSizeAw14
    (noun amount start finish bidder settled caller owner : UInt256) {out : ByteArray}
    (houtSize : out.size < UInt256.size) :
    let memLoop :=
      auctionSettleAuctionTransferFromPayoutLoopMem
        noun amount start finish bidder settled caller
    let memDeposit := auctionSettleAuctionDynDepositMem memLoop (UInt256.ofNat 14)
    let memTransfer := auctionSettleAuctionDynTransferMem memDeposit (⟨352⟩ : UInt256)
      amount owner
    (out.write 0 memTransfer 352
      (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat).size = 420 := by
  intro memLoop memDeposit memTransfer
  let len := (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat
  have hsrc : len ≤ out.size := by
    simpa [len] using auctionSettleAuctionTransferReturnCopyLen_le_size (out := out) houtSize
  have hlen32 : len ≤ 32 := by
    simpa [len] using auctionSettleAuctionTransferReturnCopyLen_le32 (out := out)
  have hmem : memTransfer.size = 420 := by
    simpa [memLoop, memDeposit, memTransfer] using
      transferBranchTransferFromPayoutLoopDynTransferMemSizeAw14
        noun amount start finish bidder settled caller owner
  change (out.write 0 memTransfer 352 len).size = 420
  by_cases hlen0 : len = 0
  · simpa [hlen0, byteArray_write_len_zero] using hmem
  · rw [write_eq_gen out memTransfer 352 len hlen0 hsrc (by rw [hmem]; omega)]
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, hmem]
    omega

theorem transferBranchTransferFromPayoutLoopDynTransferReturnMemRead64Aw14
    (noun amount start finish bidder settled caller owner : UInt256) {out : ByteArray}
    (houtSize : out.size < UInt256.size) :
    let memLoop :=
      auctionSettleAuctionTransferFromPayoutLoopMem
        noun amount start finish bidder settled caller
    let memDeposit := auctionSettleAuctionDynDepositMem memLoop (UInt256.ofNat 14)
    let memTransfer := auctionSettleAuctionDynTransferMem memDeposit (⟨352⟩ : UInt256)
      amount owner
    (out.write 0 memTransfer 352
      (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat).readWithPadding 64 32 =
    memTransfer.readWithPadding 64 32 := by
  intro memLoop memDeposit memTransfer
  let len := (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat
  have hsrc : len ≤ out.size := by
    simpa [len] using auctionSettleAuctionTransferReturnCopyLen_le_size (out := out) houtSize
  have hmem : memTransfer.size = 420 := by
    simpa [memLoop, memDeposit, memTransfer] using
      transferBranchTransferFromPayoutLoopDynTransferMemSizeAw14
        noun amount start finish bidder settled caller owner
  change (out.write 0 memTransfer 352 len).readWithPadding 64 32 =
    memTransfer.readWithPadding 64 32
  by_cases hlen0 : len = 0
  · simpa [hlen0, byteArray_write_len_zero]
  · exact write_read_below_gen_extend out memTransfer 352 len 64
      hlen0 hsrc (by rw [hmem]; decide) (by decide)

theorem transferBranchTransferFromPayoutLoopDynTransferReturnMload64Aw14
    (noun amount start finish bidder settled caller owner : UInt256) {out : ByteArray}
    (houtSize : out.size < UInt256.size) :
    let memLoop :=
      auctionSettleAuctionTransferFromPayoutLoopMem
        noun amount start finish bidder settled caller
    let memDeposit := auctionSettleAuctionDynDepositMem memLoop (UInt256.ofNat 14)
    let awCall := auctionSettleAuctionDynDepositCallAw memLoop (UInt256.ofNat 14)
    let memTransfer := auctionSettleAuctionDynTransferMem memDeposit (⟨352⟩ : UInt256)
      amount owner
    let awTransfer := auctionSettleAuctionDynTransferAw awCall (⟨352⟩ : UInt256)
    let len := (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat
    let memReturn := out.write 0 memTransfer 352 len
    let awReturn := UInt256.ofNat (MachineState.M awTransfer.toNat 352 32)
    (if (⟨64⟩ : UInt256).toNat ≥ memReturn.size ∨
        (⟨64⟩ : UInt256) ≥ awReturn * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian (memReturn.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
    (⟨352⟩ : UInt256) := by
  intro memLoop memDeposit awCall memTransfer awTransfer len memReturn awReturn
  have hmemSize : memReturn.size = 420 := by
    simpa [memLoop, memDeposit, memTransfer, len, memReturn] using
      transferBranchTransferFromPayoutLoopDynTransferReturnMemSizeAw14
        noun amount start finish bidder settled caller owner houtSize
  have hread : memReturn.readWithPadding 64 32 = memTransfer.readWithPadding 64 32 := by
    simpa [memLoop, memDeposit, memTransfer, len, memReturn] using
      transferBranchTransferFromPayoutLoopDynTransferReturnMemRead64Aw14
        noun amount start finish bidder settled caller owner houtSize
  have hawTransfer : awTransfer = UInt256.ofNat 14 := by
    have hptr : auctionSettleAuctionDynMload64 memLoop (UInt256.ofNat 14) =
        (⟨352⟩ : UInt256) := by
      simpa [memLoop] using
        transferBranchTransferFromPayoutLoopDynMload64Aw14
          noun amount start finish bidder settled caller
    simpa [memLoop, awCall, awTransfer, hptr] using
      transferBranchTransferFromPayoutLoopDynTransferAwAw14
        noun amount start finish bidder settled caller
  have hawReturn : awReturn = UInt256.ofNat 14 := by
    dsimp [awReturn]
    rw [hawTransfer]
    native_decide
  have hbase :
      (if (⟨64⟩ : UInt256).toNat ≥ memTransfer.size ∨
          (⟨64⟩ : UInt256) ≥ UInt256.ofNat 14 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (memTransfer.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      (⟨352⟩ : UInt256) := by
    simpa [auctionSettleAuctionDynMload64, memLoop, memDeposit, memTransfer] using
      transferBranchTransferFromPayoutLoopDynTransferMload64FixedAw14
        noun amount start finish bidder settled caller owner
  have hbaseRead :
      UInt256.ofNat
          (fromByteArrayBigEndian
            (memTransfer.readWithPadding (⟨64⟩ : UInt256).toNat 32)) =
        (⟨352⟩ : UInt256) := by
    have hmemTransferSize : memTransfer.size = 420 := by
      simpa [memLoop, memDeposit, memTransfer] using
        transferBranchTransferFromPayoutLoopDynTransferMemSizeAw14
          noun amount start finish bidder settled caller owner
    have hcond :
        ¬((⟨64⟩ : UInt256).toNat ≥ memTransfer.size ∨
          (⟨64⟩ : UInt256) ≥ UInt256.ofNat 14 * ⟨32⟩) := by
      exact not_or.mpr ⟨by rw [hmemTransferSize]; decide, by native_decide⟩
    simpa [hcond] using hbase
  change
    (if (⟨64⟩ : UInt256).toNat ≥ memReturn.size ∨
        (⟨64⟩ : UInt256) ≥ awReturn * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian (memReturn.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
    (⟨352⟩ : UInt256)
  rw [hawReturn, if_neg]
  · simpa [show (⟨64⟩ : UInt256).toNat = 64 by native_decide, hread] using hbaseRead
  · exact not_or.mpr ⟨by rw [hmemSize]; decide, by native_decide⟩

theorem transferBranchTransferFromPayoutLoopDynTransferReturnMemRead352Aw14
    (noun amount start finish bidder settled caller owner : UInt256) {out : ByteArray}
    (hout32 : 32 ≤ out.size) (houtSize : out.size < UInt256.size) :
    let memLoop :=
      auctionSettleAuctionTransferFromPayoutLoopMem
        noun amount start finish bidder settled caller
    let memDeposit := auctionSettleAuctionDynDepositMem memLoop (UInt256.ofNat 14)
    let memTransfer := auctionSettleAuctionDynTransferMem memDeposit (⟨352⟩ : UInt256)
      amount owner
    (out.write 0 memTransfer 352
      (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat).readWithPadding 352 32 =
    out.extract 0 32 := by
  intro memLoop memDeposit memTransfer
  have hlen := auctionSettleAuctionTransferReturnCopyLen hout32 houtSize
  have hmem : memTransfer.size = 420 := by
    simpa [memLoop, memDeposit, memTransfer] using
      transferBranchTransferFromPayoutLoopDynTransferMemSizeAw14
        noun amount start finish bidder settled caller owner
  change (out.write 0 memTransfer 352
      (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat).readWithPadding 352 32 =
    out.extract 0 32
  rw [hlen]
  exact write32_read_back out memTransfer 352 hout32 (by rw [hmem]; decide)

theorem transferBranchTransferFromPayoutLoopDynTransferReturnMload352Aw14
    (noun amount start finish bidder settled caller owner : UInt256) {out : ByteArray}
    (hout32 : 32 ≤ out.size) (houtSize : out.size < UInt256.size) :
    let memLoop :=
      auctionSettleAuctionTransferFromPayoutLoopMem
        noun amount start finish bidder settled caller
    let memDeposit := auctionSettleAuctionDynDepositMem memLoop (UInt256.ofNat 14)
    let awCall := auctionSettleAuctionDynDepositCallAw memLoop (UInt256.ofNat 14)
    let memTransfer := auctionSettleAuctionDynTransferMem memDeposit (⟨352⟩ : UInt256)
      amount owner
    let awTransfer := auctionSettleAuctionDynTransferAw awCall (⟨352⟩ : UInt256)
    let len := (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat
    let memReturn := out.write 0 memTransfer 352 len
    let awReturn := UInt256.ofNat (MachineState.M awTransfer.toNat 352 32)
    let osz := UInt256.ofNat out.size
    let rounded := UInt256.land (UInt256.add osz ⟨31⟩) (UInt256.lnot ⟨31⟩)
    let newFree := UInt256.add (⟨352⟩ : UInt256) rounded
    let aw64 := UInt256.ofNat (MachineState.M awReturn.toNat (⟨64⟩ : UInt256).toNat 32)
    let memRet := (UInt256.toByteArray newFree).write 0 memReturn (⟨64⟩ : UInt256).toNat 32
    let awStore := UInt256.ofNat (MachineState.M aw64.toNat (⟨64⟩ : UInt256).toNat 32)
    (if (⟨352⟩ : UInt256).toNat ≥ memRet.size ∨
        (⟨352⟩ : UInt256) ≥ awStore * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian (memRet.readWithPadding (⟨352⟩ : UInt256).toNat 32))) =
    UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) := by
  intro memLoop memDeposit awCall memTransfer awTransfer len memReturn awReturn osz rounded
    newFree aw64 memRet awStore
  have hmemSize : memReturn.size = 420 := by
    simpa [memLoop, memDeposit, memTransfer, len, memReturn] using
      transferBranchTransferFromPayoutLoopDynTransferReturnMemSizeAw14
        noun amount start finish bidder settled caller owner houtSize
  have hreadCopy : memReturn.readWithPadding 352 32 = out.extract 0 32 := by
    simpa [memLoop, memDeposit, memTransfer, len, memReturn] using
      transferBranchTransferFromPayoutLoopDynTransferReturnMemRead352Aw14
        noun amount start finish bidder settled caller owner hout32 houtSize
  have hmemRetSize : memRet.size = 420 := by
    simpa [memRet] using
      toByteArray_write32_size_of_le memReturn newFree 64 420 420 hmemSize
        (by rw [hmemSize]; decide) (by decide)
  have hreadRet : memRet.readWithPadding 352 32 = out.extract 0 32 := by
    have hraw :=
      write32_read_above (UInt256.toByteArray newFree) memReturn 64 352
        (by rw [toByteArray_size]) (by rw [hmemSize]; decide)
        (by decide) (by rw [hmemSize]; decide)
    simpa [memRet, hreadCopy] using hraw
  have hawTransfer : awTransfer = UInt256.ofNat 14 := by
    have hptr : auctionSettleAuctionDynMload64 memLoop (UInt256.ofNat 14) =
        (⟨352⟩ : UInt256) := by
      simpa [memLoop] using
        transferBranchTransferFromPayoutLoopDynMload64Aw14
          noun amount start finish bidder settled caller
    simpa [memLoop, awCall, awTransfer, hptr] using
      transferBranchTransferFromPayoutLoopDynTransferAwAw14
        noun amount start finish bidder settled caller
  have hawReturn : awReturn = UInt256.ofNat 14 := by
    dsimp [awReturn]
    rw [hawTransfer]
    native_decide
  have hawStore : awStore = UInt256.ofNat 14 := by
    dsimp [awStore, aw64]
    rw [hawReturn]
    native_decide
  change
    (if (⟨352⟩ : UInt256).toNat ≥ memRet.size ∨
        (⟨352⟩ : UInt256) ≥ awStore * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian (memRet.readWithPadding (⟨352⟩ : UInt256).toNat 32))) =
    UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))
  rw [if_neg]
  · simpa [show (⟨352⟩ : UInt256).toNat = 352 by native_decide, hreadRet]
  · exact not_or.mpr ⟨by rw [hmemRetSize]; decide, by rw [hawStore]; native_decide⟩

theorem transferBranchTransferFromPayoutLoopDynTransferReturnAwAfterCallEqAw14
    (noun amount start finish bidder settled caller : UInt256) :
    let memLoop :=
      auctionSettleAuctionTransferFromPayoutLoopMem
        noun amount start finish bidder settled caller
    let freePtr := auctionSettleAuctionDynMload64 memLoop (UInt256.ofNat 14)
    let awCall := auctionSettleAuctionDynDepositCallAw memLoop (UInt256.ofNat 14)
    let awTransfer := auctionSettleAuctionDynTransferAw awCall freePtr
    UInt256.ofNat
        (MachineState.M
          (MachineState.M
            (auctionSettleAuctionDynTransferAwAfterMload64 awCall freePtr).toNat
            freePtr.toNat 68)
          freePtr.toNat 32) =
      UInt256.ofNat (MachineState.M awTransfer.toNat freePtr.toNat 32) := by
  intro memLoop freePtr awCall awTransfer
  have hfree : freePtr = (⟨352⟩ : UInt256) := by
    simpa [memLoop, freePtr] using
      transferBranchTransferFromPayoutLoopDynMload64Aw14
        noun amount start finish bidder settled caller
  have hawCall : awCall = UInt256.ofNat 14 := by
    simpa [memLoop, awCall] using
      transferBranchTransferFromPayoutLoopDynDepositCallAwAw14
        noun amount start finish bidder settled caller
  have hawTransfer : awTransfer = UInt256.ofNat 14 := by
    simpa [memLoop, freePtr, awCall, awTransfer, hfree] using
      transferBranchTransferFromPayoutLoopDynTransferAwAw14
        noun amount start finish bidder settled caller
  rw [hfree, hawCall, hawTransfer]
  native_decide

end Auction
