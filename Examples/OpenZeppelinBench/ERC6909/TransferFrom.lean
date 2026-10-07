import Examples.OpenZeppelinBench.ERC6909.TransferFrom.Cases
import Examples.OpenZeppelinBench.ERC6909.TransferFrom.Traces

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unnecessarySimpa false

namespace OpenZeppelinBench.ERC6909

set_option maxHeartbeats 20000000 in
theorem erc6909TransferFromBodyCore
    {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = erc6909BenchBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (erc6909SelBytes 7))
    (hreach : ∃ k C, RD erc6909BenchBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨388⟩
      [erc6909SelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      σ k C) :
    runtimeRefinementFor config contract
      σ σ₀ g A I := by
  have hsz4 := erc6909TransferFromSelector_size hsel
  have hd := erc6909Dispatch_transferFrom (cd := I.calldata) hsel
  let evmE := initState σ σ₀ (Sat256.ofUInt256 g) A I
  let evmS := initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hOperator : transferFromOperatorWord evmE I = transferFromOperatorWord evmS I := rfl
  have hAllowance :
      transferFromCurrentAllowanceWord evmE I = transferFromCurrentAllowanceWord evmS I := rfl
  have hAllowanceDebit :
      transferFromAllowanceDebitWord evmE I = transferFromAllowanceDebitWord evmS I := rfl
  have hAfterAllowanceSenderBalance :
      transferFromSenderBalanceWord (transferFromAfterAllowanceState evmE I) I =
        transferFromSenderBalanceWord (transferFromAfterAllowanceState evmS I) I := rfl
  have hSenderDebit :
      transferFromSenderDebitWord evmE I = transferFromSenderDebitWord evmS I := rfl
  have hReceiverBalance :
      transferFromReceiverBalanceWord evmE I = transferFromReceiverBalanceWord evmS I := rfl
  have hReceiverCreditNat :
      transferFromReceiverCreditNat evmE I = transferFromReceiverCreditNat evmS I := rfl
  have hReceiverCreditWord :
      transferFromReceiverCreditWord evmE I = transferFromReceiverCreditWord evmS I := rfl
  have hTailSenderBalance :
      transferFromSenderBalanceWord evmE I = transferFromSenderBalanceWord evmS I := rfl
  have hTailSenderDebit :
      transferFromTailSenderDebitWord evmE I = transferFromTailSenderDebitWord evmS I := rfl
  have hTailReceiverBalance :
      transferFromTailReceiverBalanceWord evmE I = transferFromTailReceiverBalanceWord evmS I := rfl
  have hTailReceiverCreditNat :
      transferFromTailReceiverCreditNat evmE I = transferFromTailReceiverCreditNat evmS I := rfl
  have hTailReceiverCreditWord :
      transferFromTailReceiverCreditWord evmE I = transferFromTailReceiverCreditWord evmS I := rfl
  by_cases hsz132 : 132 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus
      · by_cases hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus
        · have hdec := erc6909Decode_transferFrom_ok (I := I) hsz132 hbig
            hcanonSender hcanonReceiver
          have hsenderZeroAddr :
              transferFromSenderWord I = ⟨0⟩ →
                AccountAddress.ofNat (transferFromSenderWord I).toNat = zeroAccountAddress := by
            intro hz
            simpa [zeroAccountAddress] using
              (approveAccountAddress_ofNat_zero_iff hcanonSender).mpr hz
          have hsenderNZAddr :
              transferFromSenderWord I ≠ ⟨0⟩ →
                AccountAddress.ofNat (transferFromSenderWord I).toNat ≠
                  zeroAccountAddress := by
            intro hnz hz
            exact hnz ((approveAccountAddress_ofNat_zero_iff hcanonSender).mp
              (by simpa [zeroAccountAddress] using hz))
          have hreceiverZeroAddr :
              transferFromReceiverWord I = ⟨0⟩ →
                AccountAddress.ofNat (transferFromReceiverWord I).toNat =
                  zeroAccountAddress := by
            intro hz
            simpa [zeroAccountAddress] using
              (approveAccountAddress_ofNat_zero_iff hcanonReceiver).mpr hz
          have hreceiverNZAddr :
              transferFromReceiverWord I ≠ ⟨0⟩ →
                AccountAddress.ofNat (transferFromReceiverWord I).toNat ≠
                  zeroAccountAddress := by
            intro hnz hz
            exact hnz ((approveAccountAddress_ofNat_zero_iff hcanonReceiver).mp
              (by simpa [zeroAccountAddress] using hz))
          by_cases hsenderCaller : transferFromSenderWord I = transferFromCallerWord I
          · have hgate :=
              evalExpr_transferFrom_allowance_gate_false_sender evmS I
                (by simp [evmS, initState]) hsenderCaller
            by_cases hsenderZero : transferFromSenderWord I = ⟨0⟩
            · have hbody := erc6909TransferFromBodyRevertsNoAllowance_sender_zero evmS I
                (by simp only [evmS, initState]; exact hwv) hgate
                (hsenderZeroAddr hsenderZero)
              exact (erc6909TransferFromX_skipCaller_revert_sender_zero
                  (g := Sat256.ofUInt256 g) hsz132 hsize hbig hcanonSender
                  hcanonReceiver hsenderCaller hsenderZero hreach)
                |>.reEquivExecutionRevert hcode hd hdec hbody
            · by_cases hreceiverZero : transferFromReceiverWord I = ⟨0⟩
              · have hbody := erc6909TransferFromBodyRevertsNoAllowance_receiver_zero evmS I
                  (by simp only [evmS, initState]; exact hwv) hgate
                  (hsenderNZAddr hsenderZero) (hreceiverZeroAddr hreceiverZero)
                exact (erc6909TransferFromX_skipCaller_revert_receiver_zero
                    (g := Sat256.ofUInt256 g) hsz132 hsize hbig hcanonSender
                    hcanonReceiver hsenderCaller hsenderZero hreceiverZero hreach)
                  |>.reEquivExecutionRevert hcode hd hdec hbody
              · by_cases henough :
                  (transferFromAmountWord I).toNat ≤
                    (transferFromSenderBalanceWord evmE I).toNat
                · by_cases hfit : transferFromTailReceiverCreditNat evmE I < UInt256.size
                  · have henoughS :
                        (transferFromAmountWord I).toNat ≤
                          (transferFromSenderBalanceWord evmS I).toNat := by
                      simpa [hTailSenderBalance] using henough
                    have hfitS : transferFromTailReceiverCreditNat evmS I < UInt256.size := by
                      simpa [hTailReceiverCreditNat] using hfit
                    have hbody := erc6909TransferFromBodyCoreNoAllowance evmS I
                      (by simp only [evmS, initState]; exact hwv) hgate
                      (evalExpr_transferFrom_sender_nonzero_true_of_get evmS
                        (transferFromStore I) I (transferFromStore_sender I)
                        (hsenderNZAddr hsenderZero))
                      (evalExpr_transferFrom_receiver_nonzero_true_of_get evmS
                        (transferFromStore I) I (transferFromStore_receiver I)
                        (hreceiverNZAddr hreceiverZero))
                      henoughS hfitS
                    exact (erc6909TransferFromX_skipCaller_success
                        (g := Sat256.ofUInt256 g) hsz132 hsize hbig hperm hcanonSender
                        hcanonReceiver hsenderCaller hsenderZero hreceiverZero henough
                        hfit hreach)
                      |>.reEquivExecutionGen hcode hd hdec hbody
                        (by simp [evmS, initState, transferFromTailPostState,
                          transferFromTailAfterSenderBalanceState, storageStore_accountMap])
                        (returnEquiv_of_encode
                          (by simpa [boolTy] using boolTrueReturnEncoding))
                  · have hover : UInt256.size ≤ transferFromTailReceiverCreditNat evmE I := by
                      omega
                    have henoughS :
                        (transferFromAmountWord I).toNat ≤
                          (transferFromSenderBalanceWord evmS I).toNat := by
                      simpa [hTailSenderBalance] using henough
                    have hoverS :
                        UInt256.size ≤ transferFromTailReceiverCreditNat evmS I := by
                      simpa [hTailReceiverCreditNat] using hover
                    have hbody := erc6909TransferFromBodyRevertsNoAllowance_overflow evmS I
                      (by simp only [evmS, initState]; exact hwv) hgate
                      (hsenderNZAddr hsenderZero) (hreceiverNZAddr hreceiverZero)
                      henoughS hoverS
                    exact (erc6909TransferFromX_skipCaller_overflow
                        (g := Sat256.ofUInt256 g) hsz132 hsize hbig hperm hcanonSender
                        hcanonReceiver hsenderCaller hsenderZero hreceiverZero henough hover
                        hreach)
                      |>.reEquivExecutionRevert hcode hd hdec hbody
                · have hlt :
                      (transferFromSenderBalanceWord evmE I).toNat <
                        (transferFromAmountWord I).toNat := by
                    omega
                  have hltS :
                      (transferFromSenderBalanceWord evmS I).toNat <
                        (transferFromAmountWord I).toNat := by
                    simpa [hTailSenderBalance] using hlt
                  have hbody := erc6909TransferFromBodyRevertsNoAllowance_insufficient evmS I
                    (by simp only [evmS, initState]; exact hwv) hgate
                    (hsenderNZAddr hsenderZero) (hreceiverNZAddr hreceiverZero) hltS
                  exact (erc6909TransferFromX_skipCaller_insufficient
                      (g := Sat256.ofUInt256 g) hsz132 hsize hbig hcanonSender
                      hcanonReceiver hsenderCaller hsenderZero hreceiverZero hlt hreach)
                    |>.reEquivExecutionRevert hcode hd hdec hbody
          · have hsenderNeSource :
                AccountAddress.ofNat (transferFromSenderWord I).toNat ≠ I.source := by
              intro haddr
              apply hsenderCaller
              calc
                transferFromSenderWord I =
                    keyValueToWord
                      (.address (AccountAddress.ofNat (transferFromSenderWord I).toNat)) := by
                  exact (keyValueToWord_address_of_canonical _
                    hcanonSender).symm
                _ = keyValueToWord (.address I.source) := by rw [haddr]
                _ = keyValueToWord
                    (.address (AccountAddress.ofNat (transferFromCallerWord I).toNat)) := by
                  rw [← transferFromCaller_ofNat I]
                _ = transferFromCallerWord I := by
                  exact keyValueToWord_address_of_canonical _
                    (transferFromCallerWord_canonical I)
            by_cases hopZero : transferFromOperatorWord evmE I = ⟨0⟩
            · have hgate :=
                evalExpr_transferFrom_allowance_gate_true evmS I
                  (by simp [evmS, initState]) hsenderNeSource
                  (by simpa [hOperator] using hopZero)
              by_cases hallowanceMax :
                  UInt256.size - 1 ≤ (transferFromCurrentAllowanceWord evmE I).toNat
              · have hallowanceMaxS :
                    UInt256.size - 1 ≤
                      (transferFromCurrentAllowanceWord evmS I).toNat := by
                  simpa [hAllowance] using hallowanceMax
                have hallowanceMaxExpr :=
                  evalExpr_transferFrom_allowance_lt_max_false evmS I hallowanceMaxS
                by_cases hsenderZero : transferFromSenderWord I = ⟨0⟩
                · have hbody :=
                    erc6909TransferFromBodyRevertsAllowanceMax_sender_zero evmS I
                      (by simp only [evmS, initState]; exact hwv) hgate
                      hallowanceMaxExpr (hsenderZeroAddr hsenderZero)
                  exact (erc6909TransferFromX_operatorFalse_allowanceMax_revert_sender_zero
                      (g := Sat256.ofUInt256 g) hsz132 hsize hbig hcanonSender
                      hcanonReceiver hsenderCaller hopZero hallowanceMax hsenderZero hreach)
                    |>.reEquivExecutionRevert hcode hd hdec hbody
                · by_cases hreceiverZero : transferFromReceiverWord I = ⟨0⟩
                  · have hbody :=
                      erc6909TransferFromBodyRevertsAllowanceMax_receiver_zero evmS I
                        (by simp only [evmS, initState]; exact hwv) hgate
                        hallowanceMaxExpr (hsenderNZAddr hsenderZero)
                        (hreceiverZeroAddr hreceiverZero)
                    exact (erc6909TransferFromX_operatorFalse_allowanceMax_revert_receiver_zero
                        (g := Sat256.ofUInt256 g) hsz132 hsize hbig hcanonSender
                        hcanonReceiver hsenderCaller hopZero hallowanceMax hsenderZero
                        hreceiverZero hreach)
                      |>.reEquivExecutionRevert hcode hd hdec hbody
                  · by_cases henough :
                      (transferFromAmountWord I).toNat ≤
                        (transferFromSenderBalanceWord evmE I).toNat
                    · by_cases hfit :
                        transferFromTailReceiverCreditNat evmE I < UInt256.size
                      · have henoughS :
                            (transferFromAmountWord I).toNat ≤
                              (transferFromSenderBalanceWord evmS I).toNat := by
                          simpa [hTailSenderBalance] using henough
                        have hfitS :
                            transferFromTailReceiverCreditNat evmS I < UInt256.size := by
                          simpa [hTailReceiverCreditNat] using hfit
                        rcases erc6909TransferFromBodyCoreAllowanceMax evmS I
                          (by simp only [evmS, initState]; exact hwv) hgate
                          hallowanceMaxExpr
                          (evalExpr_transferFrom_sender_nonzero_true_of_get evmS
                            (transferFromStoreCurrentAllowance evmS I) I
                            (transferFromStoreCurrentAllowance_sender evmS I)
                            (hsenderNZAddr hsenderZero))
                          (evalExpr_transferFrom_receiver_nonzero_true_of_get evmS
                            (transferFromStoreCurrentAllowance evmS I) I
                            (transferFromStoreCurrentAllowance_receiver evmS I)
                            (hreceiverNZAddr hreceiverZero))
                          henoughS hfitS with ⟨cs, hbody⟩
                        exact (erc6909TransferFromX_operatorFalse_allowanceMax_success
                            (g := Sat256.ofUInt256 g) hsz132 hsize hbig hperm
                            hcanonSender hcanonReceiver hsenderCaller hopZero hallowanceMax
                            hsenderZero hreceiverZero henough hfit hreach)
                          |>.reEquivExecutionGen hcode hd hdec hbody
                            (by simp [evmS, initState, transferFromTailPostState,
                              transferFromTailAfterSenderBalanceState, storageStore_accountMap])
                              (returnEquiv_of_encode
                              (by simpa [boolTy] using boolTrueReturnEncoding))
                      · have hover :
                            UInt256.size ≤ transferFromTailReceiverCreditNat evmE I := by
                          omega
                        have henoughS :
                            (transferFromAmountWord I).toNat ≤
                              (transferFromSenderBalanceWord evmS I).toNat := by
                          simpa [hTailSenderBalance] using henough
                        have hoverS :
                            UInt256.size ≤ transferFromTailReceiverCreditNat evmS I := by
                          simpa [hTailReceiverCreditNat] using hover
                        have hbody :=
                          erc6909TransferFromBodyRevertsAllowanceMax_overflow evmS I
                            (by simp only [evmS, initState]; exact hwv) hgate
                            hallowanceMaxExpr (hsenderNZAddr hsenderZero)
                            (hreceiverNZAddr hreceiverZero) henoughS hoverS
                        exact (erc6909TransferFromX_operatorFalse_allowanceMax_overflow
                            (g := Sat256.ofUInt256 g) hsz132 hsize hbig hperm
                            hcanonSender hcanonReceiver hsenderCaller hopZero hallowanceMax
                            hsenderZero hreceiverZero henough hover hreach)
                          |>.reEquivExecutionRevert hcode hd hdec hbody
                    · have hlt :
                          (transferFromSenderBalanceWord evmE I).toNat <
                            (transferFromAmountWord I).toNat := by
                        omega
                      have hltS :
                          (transferFromSenderBalanceWord evmS I).toNat <
                            (transferFromAmountWord I).toNat := by
                        simpa [hTailSenderBalance] using hlt
                      have hbody :=
                        erc6909TransferFromBodyRevertsAllowanceMax_insufficient_balance evmS I
                          (by simp only [evmS, initState]; exact hwv) hgate
                          hallowanceMaxExpr (hsenderNZAddr hsenderZero)
                          (hreceiverNZAddr hreceiverZero) hltS
                      exact (erc6909TransferFromX_operatorFalse_allowanceMax_insufficient
                          (g := Sat256.ofUInt256 g) hsz132 hsize hbig hcanonSender
                          hcanonReceiver hsenderCaller hopZero hallowanceMax hsenderZero
                          hreceiverZero hlt hreach)
                        |>.reEquivExecutionRevert hcode hd hdec hbody
              · have hallowanceNotMax :
                    (transferFromCurrentAllowanceWord evmE I).toNat < UInt256.size - 1 := by
                  omega
                have hallowanceNotMaxS :
                    (transferFromCurrentAllowanceWord evmS I).toNat < UInt256.size - 1 := by
                  simpa [hAllowance] using hallowanceNotMax
                have hallowanceNotMaxExpr :=
                  evalExpr_transferFrom_allowance_lt_max_true evmS I hallowanceNotMaxS
                by_cases hallowanceEnough :
                    (transferFromAmountWord I).toNat ≤
                      (transferFromCurrentAllowanceWord evmE I).toNat
                · have hallowanceEnoughS :
                      (transferFromAmountWord I).toNat ≤
                        (transferFromCurrentAllowanceWord evmS I).toNat := by
                    simpa [hAllowance] using hallowanceEnough
                  let σAllowance := sstoreAccountMap I.codeOwner σ
                    (transferFromAllowanceSlotI I) (transferFromAllowanceDebitWord evmE I)
                  have hAfterAllowanceInit :
                      transferFromAfterAllowanceState evmE I =
                        initState σAllowance σ₀ (Sat256.ofUInt256 g) A I := by
                    cases hfind : σ.get? I.codeOwner <;>
                      simp [-Std.ExtTreeMap.get?_eq_getElem?, evmE, σAllowance, transferFromAfterAllowanceState,
                        transferFromAllowanceSlot, transferFromAllowanceSlotI, initState,
                        Solm.EVM.storageStore, State.lookupAccount, hfind, sstoreAccountMap,
                        Option.option, State.setAccount, Account.updateStorage]
                  have hAfterAllowanceMap :
                      (transferFromAfterAllowanceState evmE I).accountMap =
                        σAllowance := by
                    simpa [initState] using congrArg (fun s : EVM.State => s.accountMap)
                      hAfterAllowanceInit
                  have hPostAsTail :
                      transferFromPostState evmE I =
                        transferFromTailPostState
                          (initState σAllowance σ₀
                            (Sat256.ofUInt256 g) A I) I := by
                    rw [← hAfterAllowanceInit]
                    simp [transferFromPostState, transferFromTailPostState,
                      transferFromAfterSenderBalanceState,
                      transferFromTailAfterSenderBalanceState,
                      transferFromSenderDebitWord, transferFromTailSenderDebitWord,
                      transferFromReceiverCreditWord, transferFromTailReceiverCreditWord,
                      transferFromReceiverCreditNat, transferFromTailReceiverCreditNat,
                      transferFromReceiverBalanceWord, transferFromTailReceiverBalanceWord,
                      transferFromAfterAllowance_codeOwner]
                  have hbase := transferFromOperatorAllowanceScratchMem_size I
                  have hread64 := transferFromOperatorAllowanceScratchMem_read64 I
                  obtain ⟨_, _, rd1193⟩ :=
                    erc6909TransferFromX_operatorFalse_afterAllowanceLoad
                      (σ := σ)
                      (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g)
                      (sel := erc6909SelWord I) hsz132 hsize hbig hcanonSender
                      hcanonReceiver hsenderCaller hopZero hreach
                  obtain ⟨_, _, rd661⟩ :=
                    erc6909TransferFromX_from1193_allowanceDebit_to661_base
                      (σ := σ)
                      (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g)
                      (sel := erc6909SelWord I)
                      (base := transferFromOperatorAllowanceScratchMem I)
                      hbase hperm hcanonSender hallowanceNotMax hallowanceEnough rd1193
                  by_cases hsenderZero : transferFromSenderWord I = ⟨0⟩
                  · have hbody :=
                      erc6909TransferFromBodyRevertsAllowance_sender_zero evmS I
                        (by simp only [evmS, initState]; exact hwv) hgate
                        hallowanceNotMaxExpr hallowanceEnoughS
                        (hsenderZeroAddr hsenderZero)
                    exact (erc6909TransferFromX_from661_revert_sender_zero_base
                        (σ := σ)
                        (σ₀ := σ₀) (σcur := σAllowance) (A := A)
                        (g := Sat256.ofUInt256 g) (sel := erc6909SelWord I)
                        (base := transferFromAllowanceScratchMem
                          (transferFromOperatorAllowanceScratchMem I) I)
                        (transferFromAllowanceScratchMem_size I hbase)
                        (transferFromAllowanceScratchMem_read64 I hbase hread64)
                        hsenderZero
                        (by simpa [evmE, σAllowance] using rd661))
                      |>.reEquivExecutionRevert hcode hd hdec hbody
                  · by_cases hreceiverZero : transferFromReceiverWord I = ⟨0⟩
                    · have hbody :=
                        erc6909TransferFromBodyRevertsAllowance_receiver_zero evmS I
                          (by simp only [evmS, initState]; exact hwv) hgate
                          hallowanceNotMaxExpr hallowanceEnoughS
                          (hsenderNZAddr hsenderZero) (hreceiverZeroAddr hreceiverZero)
                      exact (erc6909TransferFromX_from661_revert_receiver_zero_base
                          (σ := σ)
                          (σ₀ := σ₀) (σcur := σAllowance) (A := A)
                          (g := Sat256.ofUInt256 g) (sel := erc6909SelWord I)
                          (base := transferFromAllowanceScratchMem
                            (transferFromOperatorAllowanceScratchMem I) I)
                          (transferFromAllowanceScratchMem_size I hbase)
                          (transferFromAllowanceScratchMem_read64 I hbase hread64)
                          hcanonSender hsenderZero hreceiverZero
                          (by simpa [evmE, σAllowance] using rd661))
                        |>.reEquivExecutionRevert hcode hd hdec hbody
                    · obtain ⟨_, _, rd1323⟩ := erc6909TransferFromX_from661_toUpdateHelper_base
                        (σ := σ)
                        (σ₀ := σ₀) (σcur := σAllowance) (A := A)
                        (g := Sat256.ofUInt256 g) (sel := erc6909SelWord I)
                        (base := transferFromAllowanceScratchMem
                          (transferFromOperatorAllowanceScratchMem I) I)
                        hcanonSender hcanonReceiver hsenderZero hreceiverZero
                        (by simpa [evmE, σAllowance] using rd661)
                      by_cases hbalanceEnough :
                          (transferFromAmountWord I).toNat ≤
                            (transferFromSenderBalanceWord
                              (transferFromAfterAllowanceState evmE I) I).toNat
                      · by_cases hfit : transferFromReceiverCreditNat evmE I < UInt256.size
                        · have hbalanceEnoughS :
                              (transferFromAmountWord I).toNat ≤
                                (transferFromSenderBalanceWord
                                  (transferFromAfterAllowanceState evmS I) I).toNat := by
                            simpa [hAfterAllowanceSenderBalance] using hbalanceEnough
                          have hfitS : transferFromReceiverCreditNat evmS I < UInt256.size := by
                            simpa [hReceiverCreditNat] using hfit
                          have hbody := erc6909TransferFromBodyCoreAllowanceDebit evmS I
                            (by simp only [evmS, initState]; exact hwv) hgate
                            hallowanceNotMaxExpr hallowanceEnoughS
                            (evalExpr_transferFrom_sender_nonzero_true_of_get
                              (transferFromAfterAllowanceState evmS I)
                              (transferFromStoreCurrentAllowance evmS I) I
                              (transferFromStoreCurrentAllowance_sender evmS I)
                              (hsenderNZAddr hsenderZero))
                            (evalExpr_transferFrom_receiver_nonzero_true_of_get
                              (transferFromAfterAllowanceState evmS I)
                              (transferFromStoreCurrentAllowance evmS I) I
                              (transferFromStoreCurrentAllowance_receiver evmS I)
                              (hreceiverNZAddr hreceiverZero))
                            hbalanceEnoughS hfitS
                          exact (erc6909TransferFromX_from1323_successCaller_base
                              (σ := σ)
                              (σ₀ := σ₀) (σcur := σAllowance) (A := A)
                              (g := Sat256.ofUInt256 g) (sel := erc6909SelWord I)
                              (base := transferFromAllowanceScratchMem
                                (transferFromOperatorAllowanceScratchMem I) I)
                              (transferFromAllowanceScratchMem_size I hbase)
                              (transferFromAllowanceScratchMem_read64 I hbase hread64)
                              hperm hcanonSender hcanonReceiver hsenderZero hreceiverZero
                              (by simpa [← hAfterAllowanceInit] using hbalanceEnough)
                              (by
                                simpa [← hAfterAllowanceInit, transferFromReceiverCreditNat,
                                  transferFromReceiverBalanceWord,
                                  transferFromAfterSenderBalanceState,
                                  transferFromAfterAllowance_codeOwner,
                                  transferFromTailReceiverCreditNat,
                                  transferFromTailReceiverBalanceWord,
                                  transferFromTailAfterSenderBalanceState,
                                  transferFromSenderDebitWord,
                                  transferFromTailSenderDebitWord] using hfit)
                              rd1323)
                            |>.reEquivExecutionGen hcode hd hdec hbody
                              (by
                                rw [hPostAsTail]
                                simp [evmS, initState, transferFromTailPostState,
                                  transferFromTailAfterSenderBalanceState,
                                  storageStore_accountMap])
                              (returnEquiv_of_encode
                                (by simpa [boolTy] using boolTrueReturnEncoding))
                        · have hover : UInt256.size ≤ transferFromReceiverCreditNat evmE I := by
                            omega
                          have hbalanceEnoughS :
                              (transferFromAmountWord I).toNat ≤
                                (transferFromSenderBalanceWord
                                  (transferFromAfterAllowanceState evmS I) I).toNat := by
                            simpa [hAfterAllowanceSenderBalance] using hbalanceEnough
                          have hoverS :
                              UInt256.size ≤ transferFromReceiverCreditNat evmS I := by
                            simpa [hReceiverCreditNat] using hover
                          have hbody :=
                            erc6909TransferFromBodyRevertsAllowance_overflow evmS I
                              (by simp only [evmS, initState]; exact hwv) hgate
                              hallowanceNotMaxExpr hallowanceEnoughS
                              (hsenderNZAddr hsenderZero) (hreceiverNZAddr hreceiverZero)
                              hbalanceEnoughS hoverS
                          exact (erc6909TransferFromX_from1323_overflow_base
                              (σ := σ)
                              (σ₀ := σ₀) (σcur := σAllowance) (A := A)
                              (g := Sat256.ofUInt256 g) (sel := erc6909SelWord I)
                              (base := transferFromAllowanceScratchMem
                                (transferFromOperatorAllowanceScratchMem I) I)
                              (transferFromAllowanceScratchMem_size I hbase)
                              (transferFromAllowanceScratchMem_read64 I hbase hread64)
                              hperm hcanonSender hcanonReceiver hsenderZero hreceiverZero
                              (by simpa [← hAfterAllowanceInit] using hbalanceEnough)
                              (by
                                simpa [← hAfterAllowanceInit, transferFromReceiverCreditNat,
                                  transferFromReceiverBalanceWord,
                                  transferFromAfterSenderBalanceState,
                                  transferFromAfterAllowance_codeOwner,
                                  transferFromTailReceiverCreditNat,
                                  transferFromTailReceiverBalanceWord,
                                  transferFromTailAfterSenderBalanceState,
                                  transferFromSenderDebitWord,
                                  transferFromTailSenderDebitWord] using hover)
                              rd1323)
                            |>.reEquivExecutionRevert hcode hd hdec hbody
                      · have hlt :
                            (transferFromSenderBalanceWord
                              (transferFromAfterAllowanceState evmE I) I).toNat <
                              (transferFromAmountWord I).toNat := by
                          omega
                        have hltS :
                            (transferFromSenderBalanceWord
                              (transferFromAfterAllowanceState evmS I) I).toNat <
                              (transferFromAmountWord I).toNat := by
                          simpa [hAfterAllowanceSenderBalance] using hlt
                        have hbody :=
                          erc6909TransferFromBodyRevertsAllowance_insufficient_balance evmS I
                            (by simp only [evmS, initState]; exact hwv) hgate
                            hallowanceNotMaxExpr hallowanceEnoughS
                            (hsenderNZAddr hsenderZero) (hreceiverNZAddr hreceiverZero)
                            hltS
                        exact (erc6909TransferFromX_from1323_insufficient_base
                            (σ := σ)
                            (σ₀ := σ₀) (σcur := σAllowance) (A := A)
                            (g := Sat256.ofUInt256 g) (sel := erc6909SelWord I)
                            (base := transferFromAllowanceScratchMem
                              (transferFromOperatorAllowanceScratchMem I) I)
                            (transferFromAllowanceScratchMem_size I hbase)
                            (transferFromAllowanceScratchMem_read64 I hbase hread64)
                            hcanonSender hsenderZero
                            (by simpa [← hAfterAllowanceInit] using hlt)
                            rd1323)
                          |>.reEquivExecutionRevert hcode hd hdec hbody
                · have hltAllowance :
                      (transferFromCurrentAllowanceWord evmE I).toNat <
                        (transferFromAmountWord I).toNat := by
                    omega
                  have hltAllowanceS :
                      (transferFromCurrentAllowanceWord evmS I).toNat <
                        (transferFromAmountWord I).toNat := by
                    simpa [hAllowance] using hltAllowance
                  have hbody := erc6909TransferFromBodyRevertsAllowance_insufficient evmS I
                    (by simp only [evmS, initState]; exact hwv) hgate
                    hallowanceNotMaxExpr hltAllowanceS
                  exact (erc6909TransferFromX_operatorFalse_insufficientAllowance
                      (g := Sat256.ofUInt256 g) hsz132 hsize hbig hcanonSender
                      hcanonReceiver hsenderCaller hopZero hallowanceNotMax hltAllowance
                      hreach)
                    |>.reEquivExecutionRevert hcode hd hdec hbody
            · have hgate :=
                evalExpr_transferFrom_allowance_gate_false_operator evmS I
                  (by simp [evmS, initState]) hsenderNeSource
                  (by simpa [hOperator] using hopZero)
              by_cases hsenderZero : transferFromSenderWord I = ⟨0⟩
              · have hbody := erc6909TransferFromBodyRevertsNoAllowance_sender_zero evmS I
                  (by simp only [evmS, initState]; exact hwv) hgate
                  (hsenderZeroAddr hsenderZero)
                exact (erc6909TransferFromX_operatorApproved_revert_sender_zero
                    (g := Sat256.ofUInt256 g) hsz132 hsize hbig hcanonSender
                    hcanonReceiver hsenderCaller hopZero hsenderZero hreach)
                  |>.reEquivExecutionRevert hcode hd hdec hbody
              · by_cases hreceiverZero : transferFromReceiverWord I = ⟨0⟩
                · have hbody := erc6909TransferFromBodyRevertsNoAllowance_receiver_zero evmS I
                    (by simp only [evmS, initState]; exact hwv) hgate
                    (hsenderNZAddr hsenderZero) (hreceiverZeroAddr hreceiverZero)
                  exact (erc6909TransferFromX_operatorApproved_revert_receiver_zero
                      (g := Sat256.ofUInt256 g) hsz132 hsize hbig hcanonSender
                      hcanonReceiver hsenderCaller hopZero hsenderZero hreceiverZero hreach)
                    |>.reEquivExecutionRevert hcode hd hdec hbody
                · by_cases henough :
                    (transferFromAmountWord I).toNat ≤
                      (transferFromSenderBalanceWord evmE I).toNat
                  · by_cases hfit : transferFromTailReceiverCreditNat evmE I < UInt256.size
                    · have henoughS :
                          (transferFromAmountWord I).toNat ≤
                            (transferFromSenderBalanceWord evmS I).toNat := by
                        simpa [hTailSenderBalance] using henough
                      have hfitS : transferFromTailReceiverCreditNat evmS I < UInt256.size := by
                        simpa [hTailReceiverCreditNat] using hfit
                      have hbody := erc6909TransferFromBodyCoreNoAllowance evmS I
                        (by simp only [evmS, initState]; exact hwv) hgate
                        (evalExpr_transferFrom_sender_nonzero_true_of_get evmS
                          (transferFromStore I) I (transferFromStore_sender I)
                          (hsenderNZAddr hsenderZero))
                        (evalExpr_transferFrom_receiver_nonzero_true_of_get evmS
                          (transferFromStore I) I (transferFromStore_receiver I)
                          (hreceiverNZAddr hreceiverZero))
                        henoughS hfitS
                      exact (erc6909TransferFromX_operatorApproved_success
                          (g := Sat256.ofUInt256 g) hsz132 hsize hbig hperm
                          hcanonSender hcanonReceiver hsenderCaller hopZero hsenderZero
                          hreceiverZero henough hfit hreach)
                        |>.reEquivExecutionGen hcode hd hdec hbody
                          (by simp [evmS, initState, transferFromTailPostState,
                            transferFromTailAfterSenderBalanceState, storageStore_accountMap])
                          (returnEquiv_of_encode
                            (by simpa [boolTy] using boolTrueReturnEncoding))
                    · have hover :
                          UInt256.size ≤ transferFromTailReceiverCreditNat evmE I := by
                        omega
                      have henoughS :
                          (transferFromAmountWord I).toNat ≤
                            (transferFromSenderBalanceWord evmS I).toNat := by
                        simpa [hTailSenderBalance] using henough
                      have hoverS :
                          UInt256.size ≤ transferFromTailReceiverCreditNat evmS I := by
                        simpa [hTailReceiverCreditNat] using hover
                      have hbody := erc6909TransferFromBodyRevertsNoAllowance_overflow evmS I
                        (by simp only [evmS, initState]; exact hwv) hgate
                        (hsenderNZAddr hsenderZero) (hreceiverNZAddr hreceiverZero)
                        henoughS hoverS
                      exact (erc6909TransferFromX_operatorApproved_overflow
                          (g := Sat256.ofUInt256 g) hsz132 hsize hbig hperm
                          hcanonSender hcanonReceiver hsenderCaller hopZero hsenderZero
                          hreceiverZero henough hover hreach)
                        |>.reEquivExecutionRevert hcode hd hdec hbody
                  · have hlt :
                        (transferFromSenderBalanceWord evmE I).toNat <
                          (transferFromAmountWord I).toNat := by
                      omega
                    have hltS :
                        (transferFromSenderBalanceWord evmS I).toNat <
                          (transferFromAmountWord I).toNat := by
                      simpa [hTailSenderBalance] using hlt
                    have hbody := erc6909TransferFromBodyRevertsNoAllowance_insufficient evmS I
                      (by simp only [evmS, initState]; exact hwv) hgate
                      (hsenderNZAddr hsenderZero) (hreceiverNZAddr hreceiverZero) hltS
                    exact (erc6909TransferFromX_operatorApproved_insufficient
                        (g := Sat256.ofUInt256 g) hsz132 hsize hbig hcanonSender
                        hcanonReceiver hsenderCaller hopZero hsenderZero hreceiverZero hlt
                        hreach)
                      |>.reEquivExecutionRevert hcode hd hdec hbody
        · have hdec := erc6909Decode_transferFrom_none_noncanon_receiver (I := I)
            hsz132 hbig hcanonSender hcanonReceiver
          have hnc : UInt256.eq (transferFromReceiverWord I)
              (UInt256.land (transferFromReceiverWord I) solcAddrMask) = ⟨0⟩ :=
            uInt256_eq_zero_of_ne
              (fun he => hcanonReceiver (solcAddrCanonical_of_clean he))
          exact (erc6909TransferFromX_noncanon_receiver (g := Sat256.ofUInt256 g)
              hsz132 hsize hbig hcanonSender hnc hreach)
            |>.reEquivDecodingFailed hcode hd hdec
      · have hdec := erc6909Decode_transferFrom_none_noncanon_sender (I := I)
          hsz132 hbig hcanonSender
        have hnc : UInt256.eq (transferFromSenderWord I)
            (UInt256.land (transferFromSenderWord I) solcAddrMask) = ⟨0⟩ :=
          uInt256_eq_zero_of_ne
            (fun he => hcanonSender (solcAddrCanonical_of_clean he))
        exact (erc6909TransferFromX_noncanon_sender (g := Sat256.ofUInt256 g)
            hsz132 hsize hbig hnc hreach)
          |>.reEquivDecodingFailed hcode hd hdec
    · have hbigge : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      have hdec := erc6909Decode_transferFrom_none_huge (I := I) hbigge
      exact (erc6909TransferFromX_hugearg (g := Sat256.ofUInt256 g)
          hsize hbigge hreach)
        |>.reEquivDecodingFailed hcode hd hdec
  · have hshort : I.calldata.size < 132 := by omega
    have hdec := erc6909Decode_transferFrom_none_short (I := I) hsz4 hshort
    exact (erc6909TransferFromX_shortarg (g := Sat256.ofUInt256 g)
        hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec


end OpenZeppelinBench.ERC6909
