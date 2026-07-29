import Examples.VyperERC20.TransferFrom

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

namespace VyperERC20

theorem erc20TransferFromX_insufficientAllowanceFromEntry {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus)
    (hlt : (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat <
      (transferFromValueWord I).toNat)
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨331⟩
      [transferFromSelectorWord] transferFromDispatchMem (UInt256.ofNat 1) ByteArray.empty
      (cA, σ) k C) :
    RDrev vyperERC20Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h412 := erc20X_transferFromAfterAllowanceLoad
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hwv hsz100 hsize hcanonFrom hcanonTo hreach
  exact erc20TransferFromX_insufficientAllowance
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hlt h412

theorem erc20TransferFromX_insufficientBalanceFromEntry {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus)
    (hallowance : (transferFromValueWord I).toNat ≤
      (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hlt : (transferFromFromBalanceWord (initState cA gh bl σ σ₀ g A I) I).toNat <
      (transferFromValueWord I).toNat)
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨331⟩
      [transferFromSelectorWord] transferFromDispatchMem (UInt256.ofNat 1) ByteArray.empty
      (cA, σ) k C) :
    RDrev vyperERC20Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h412 := erc20X_transferFromAfterAllowanceLoad
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hwv hsz100 hsize hcanonFrom hcanonTo hreach
  have h423 := erc20X_transferFromAfterAllowanceGuard
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hallowance h412
  exact erc20TransferFromX_insufficientBalance
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcanonFrom hlt h423

theorem erc20TransferFromX_balanceDebitUnderflowFromEntry {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hperm : I.perm = true)
    (hsz100 : 100 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus)
    (hallowance : (transferFromValueWord I).toNat ≤
      (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hbalance : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hltDebit : (transferFromFromBalanceWord
      (transferFromAfterAllowanceState (initState cA gh bl σ σ₀ g A I) I) I).toNat <
      (transferFromValueWord I).toNat)
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨331⟩
      [transferFromSelectorWord] transferFromDispatchMem (UInt256.ofNat 1) ByteArray.empty
      (cA, σ) k C) :
    RDrev vyperERC20Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h412 := erc20X_transferFromAfterAllowanceLoad
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hwv hsz100 hsize hcanonFrom hcanonTo hreach
  have h423 := erc20X_transferFromAfterAllowanceGuard
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hallowance h412
  have h445 := erc20X_transferFromAfterBalanceGuard
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hcanonFrom hbalance h423
  have h492 := erc20X_transferFromBeforeAllowanceStore
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hcanonFrom hallowance h445
  have h493 := erc20X_transferFromAfterAllowanceStore
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hperm h492
  exact erc20TransferFromX_balanceDebitUnderflow
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcanonFrom hltDebit h493

theorem erc20X_transferFromRuntimeEntry {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hperm : I.perm = true)
    (hsz100 : 100 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus)
    (hallowance : (transferFromValueWord I).toNat ≤
      (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hbalance : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hbalanceDebit : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord
        (transferFromAfterAllowanceState (initState cA gh bl σ σ₀ g A I) I) I).toNat)
    (hfit : transferFromNewToNat (initState cA gh bl σ σ₀ g A I) I < UInt256.size)
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨331⟩
      [transferFromSelectorWord] transferFromDispatchMem (UInt256.ofNat 1) ByteArray.empty
      (cA, σ) k C) :
    RDret vyperERC20Bytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ (transferFromAllowanceSlotI I)
            (transferFromAllowanceDebitWord (initState cA gh bl σ σ₀ g A I) I))
          (transferFromFromSlot I)
          (transferFromBalanceDebitWord
            (transferFromAfterAllowanceState (initState cA gh bl σ σ₀ g A I) I) I))
        (transferFromToSlot I) (transferFromNewToWord (initState cA gh bl σ σ₀ g A I) I))
      (UInt256.toByteArray (⟨1⟩ : UInt256)) := by
  have h412 := erc20X_transferFromAfterAllowanceLoad
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hwv hsz100 hsize hcanonFrom hcanonTo hreach
  have h423 := erc20X_transferFromAfterAllowanceGuard
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hallowance h412
  have h445 := erc20X_transferFromAfterBalanceGuard
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hcanonFrom hbalance h423
  have h492 := erc20X_transferFromBeforeAllowanceStore
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hcanonFrom hallowance h445
  have h493 := erc20X_transferFromAfterAllowanceStore
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hperm h492
  have h526 := erc20X_transferFromBeforeFromStore
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hcanonFrom hbalanceDebit h493
  have h528 := erc20X_transferFromAfterFromStore
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hperm h526
  have h543 := erc20X_transferFromAfterToLoad
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hcanonTo h528
  have h561 := erc20X_transferFromBeforeToStore
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hfit h543
  have h563 := erc20X_transferFromAfterToStore
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hperm h561
  have h602 := erc20X_transferFromAfterLogTopics
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) h563
  have h612 := erc20X_transferFromBeforeLog
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) h602
  have h613 := erc20X_transferFromAfterLog
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hperm h612
  simpa [transferFromAccountMapAfterToI, transferFromAccountMapAfterBalanceI,
    transferFromAccountMapAfterAllowanceI, transferFromAllowanceDebitI] using
    (erc20X_transferFromReturnFromAfterLog
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) h613)

theorem erc20TransferFromX_overflow {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hperm : I.perm = true)
    (hsz100 : 100 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus)
    (hallowance : (transferFromValueWord I).toNat ≤
      (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hbalance : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hbalanceDebit : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord
        (transferFromAfterAllowanceState (initState cA gh bl σ σ₀ g A I) I) I).toNat)
    (hover : UInt256.size ≤ transferFromNewToNat (initState cA gh bl σ σ₀ g A I) I)
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨331⟩
      [transferFromSelectorWord] transferFromDispatchMem (UInt256.ofNat 1) ByteArray.empty
      (cA, σ) k C) :
    RDrev vyperERC20Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  let evm0 := initState cA gh bl σ σ₀ g A I
  have h412 := erc20X_transferFromAfterAllowanceLoad
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hwv hsz100 hsize hcanonFrom hcanonTo hreach
  have h423 := erc20X_transferFromAfterAllowanceGuard
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hallowance h412
  have h445 := erc20X_transferFromAfterBalanceGuard
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hcanonFrom hbalance h423
  have h492 := erc20X_transferFromBeforeAllowanceStore
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hcanonFrom hallowance h445
  have h493 := erc20X_transferFromAfterAllowanceStore
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hperm h492
  have h526 := erc20X_transferFromBeforeFromStore
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hcanonFrom hbalanceDebit h493
  have h528 := erc20X_transferFromAfterFromStore
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hperm h526
  obtain ⟨k, C, rd528⟩ := h528
  have htoLoadRaw :
      transferFromToBalanceRawAfterBalance σ I
          (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g)
          (transferFromBalanceDebitWord (transferFromAfterAllowanceState evm0 I) I) =
        transferFromToBalanceWord evm0 I := by
    simpa [evm0] using
      (transferFromToBalanceRawAfterBalance_initState (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g))
  have hoverRaw :
      UInt256.size ≤
        (transferFromToBalanceRawAfterBalance σ I
          (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g)
          (transferFromBalanceDebitWord (transferFromAfterAllowanceState evm0 I) I)).toNat +
          (transferFromValueWord I).toNat := by
    rw [htoLoadRaw]
    simpa [evm0, transferFromNewToNat] using hover
  have hcreditGuardRaw :
      UInt256.lt
          (transferFromToBalanceRawAfterBalance σ I
            (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g)
            (transferFromBalanceDebitWord (transferFromAfterAllowanceState evm0 I) I) +
            transferFromValueWord I)
          (transferFromToBalanceRawAfterBalance σ I
            (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g)
            (transferFromBalanceDebitWord (transferFromAfterAllowanceState evm0 I) I)) = ⟨1⟩ := by
    simpa [u256_add_comm] using
      constructorCheckedAddOverflowLt
        (transferFromToBalanceRawAfterBalance σ I
          (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g)
          (transferFromBalanceDebitWord (transferFromAfterAllowanceState evm0 I) I))
        (transferFromValueWord I) hoverRaw
  have h543 := erc20X_transferFromAfterToLoad
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hcanonTo ⟨k, C, rd528⟩
  obtain ⟨k1, C1, rdAfterLoad⟩ := h543
  have rd801 := evm_run rdAfterLoad with [
    push1 ⟨68⟩, calldataload,
    dup1, dup3, add, dup3, dup2, lt, push2 ⟨801⟩,
    jumpiT (by rw [show
        UInt256.lt
          (transferFromToBalanceRawAfterBalance σ I
            (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g)
            (transferFromBalanceDebitWord (transferFromAfterAllowanceState evm0 I) I) +
            uInt256OfByteArray (I.calldata.readBytes (⟨68⟩ : UInt256).toNat 32))
          (transferFromToBalanceRawAfterBalance σ I
            (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g)
            (transferFromBalanceDebitWord (transferFromAfterAllowanceState evm0 I) I)) = ⟨1⟩ by
          simpa [transferFromValueWord] using hcreditGuardRaw]; decide)
      (by vyper_erc20_transferFrom_decode)]
  exact vyperRuntimeRevert801 (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) rd801 rfl (by
      simp only [List.length_cons, List.length_nil]
      omega)

theorem erc20TransferFromBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vyperERC20Bytecode) (hwv : I.weiValue = ⟨0⟩)
    (hperm : I.perm = true)
    (hsize : I.calldata.size < UInt256.size)
    (hd : dispatchMsg erc20Contract I.calldata = some ERC20.transferFromTransition)
    (hsel : ((⟨#[0x23, 0xb8, 0x72, 0xdd]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hreach : ∃ k C, RD vyperERC20Bytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨331⟩
      [transferFromSelectorWord] transferFromDispatchMem (UInt256.ofNat 1) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor vyperERC20Config erc20Contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz4 := erc20TransferFromSelector_size hsel
  let evmE := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hσ : EVMStateEquiv evmE evmS := by
    simpa [evmE, evmS] using EVMStateEquiv.initState (g := Sat256.ofUInt256 g) hAccounts
  have hAllowance :
      transferFromCurrentAllowanceWord evmE I = transferFromCurrentAllowanceWord evmS I := by
    simpa [transferFromCurrentAllowanceWord, transferFromAllowanceSlot, evmE, evmS, initState]
      using hσ.storageLoad_codeOwner
        (erc20AllowanceSlot (.address (AccountAddress.ofNat (transferFromFromWord I).toNat))
          (.address I.source))
  have hσAllowance : EVMStateEquiv (transferFromAfterAllowanceState evmE I)
      (transferFromAfterAllowanceState evmS I) := by
    simpa [transferFromAfterAllowanceState, transferFromAllowanceSlot, evmE, evmS, initState]
      using hσ.storageStore_codeOwner
        (erc20AllowanceSlot (.address (AccountAddress.ofNat (transferFromFromWord I).toNat))
          (.address I.source)) (by
            simpa [transferFromAllowanceDebitWord, evmE, evmS] using
              congrArg
                (fun w : UInt256 =>
                  UInt256.ofNat (w.toNat - (transferFromValueWord I).toNat))
                hAllowance)
  have hFromBalance :
      transferFromFromBalanceWord evmE I = transferFromFromBalanceWord evmS I := by
    simpa [transferFromFromBalanceWord] using
      hσ.storageLoad_codeOwner (transferFromFromSlot I)
  have hAfterAllowanceFromBalance :
      transferFromFromBalanceWord (transferFromAfterAllowanceState evmE I) I =
        transferFromFromBalanceWord (transferFromAfterAllowanceState evmS I) I := by
    simpa [transferFromFromBalanceWord] using
      hσAllowance.storageLoad_codeOwner (transferFromFromSlot I)
  have hσBalance : EVMStateEquiv (transferFromAfterBalanceState evmE I)
      (transferFromAfterBalanceState evmS I) := by
    simpa [transferFromAfterBalanceState] using
      hσAllowance.storageStore (congrArg ExecutionEnv.codeOwner hσ.executionEnv)
        (transferFromFromSlot I)
        (by simp [transferFromBalanceDebitWord, hAfterAllowanceFromBalance])
  have hToBalance :
      transferFromToBalanceWord evmE I = transferFromToBalanceWord evmS I := by
    simpa [transferFromToBalanceWord] using
      hσBalance.storageLoad (congrArg ExecutionEnv.codeOwner hσ.executionEnv)
        (transferFromToSlot I)
  have hNewToNat : transferFromNewToNat evmE I = transferFromNewToNat evmS I := by
    simp [transferFromNewToNat, hToBalance]
  have hσPost : EVMStateEquiv (transferFromPostState evmE I) (transferFromPostState evmS I) := by
    simpa [transferFromPostState] using
      hσBalance.storageStore (congrArg ExecutionEnv.codeOwner hσ.executionEnv)
        (transferFromToSlot I)
        (by simp [transferFromNewToWord, hNewToNat])
  by_cases hsz100 : 100 ≤ I.calldata.size
  · by_cases hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus
    · by_cases hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus
      · have hdec := erc20Decode_transferFrom_ok (I := I) hsz100 hcanonFrom hcanonTo
        by_cases hallowance : (transferFromValueWord I).toNat ≤
            (transferFromCurrentAllowanceWord evmE I).toNat
        · by_cases hbalance : (transferFromValueWord I).toNat ≤
            (transferFromFromBalanceWord evmE I).toNat
          · by_cases hbalanceDebit : (transferFromValueWord I).toNat ≤
              (transferFromFromBalanceWord (transferFromAfterAllowanceState evmE I) I).toNat
            · by_cases hfit : transferFromNewToNat evmE I < UInt256.size
              · have hallowanceS :
                    (transferFromValueWord I).toNat ≤
                      (transferFromCurrentAllowanceWord evmS I).toNat := by
                  simpa [hAllowance] using hallowance
                have hbalanceS :
                    (transferFromValueWord I).toNat ≤
                      (transferFromFromBalanceWord evmS I).toNat := by
                  simpa [hFromBalance] using hbalance
                have hbalanceDebitS :
                    (transferFromValueWord I).toNat ≤
                      (transferFromFromBalanceWord
                        (transferFromAfterAllowanceState evmS I) I).toNat := by
                  simpa [hAfterAllowanceFromBalance] using hbalanceDebit
                have hbody := erc20TransferFromBodyReturns evmS I
                  (by simp only [evmS, initState]; exact hwv)
                  hallowanceS hbalanceS hbalanceDebitS
                  (by simpa [hNewToNat] using hfit)
                exact (erc20X_transferFromRuntimeEntry (g := Sat256.ofUInt256 g)
                    hwv hperm hsz100 hsize hcanonFrom hcanonTo
                    (by simpa [evmE] using hallowance)
                    (by simpa [evmE] using hbalance)
                    (by simpa [evmE] using hbalanceDebit)
                    (by simpa [evmE] using hfit) hreach)
                  |>.reEquivExecutionGenEVMStateEquiv hcode hd hdec hbody
                    (by simp [evmE, initState, transferFromPostState, transferFromAfterBalanceState,
                      transferFromAfterAllowanceState, transferFromAllowanceSlot,
                      transferFromAllowanceSlotI, vyperERC20StorageStore_createdAccounts])
                    (accountMapEquiv.of_eq (by
                      simp [evmE, initState, transferFromPostState, transferFromAfterBalanceState,
                        transferFromAfterAllowanceState, transferFromAllowanceSlot,
                        transferFromAllowanceSlotI, vyperERC20StorageStore_accountMap]))
                    hσPost
                    (returnEquiv_of_encode ERC20.erc20BoolTrueReturnEncoding)
              · have hover : UInt256.size ≤ transferFromNewToNat evmE I := by
                  omega
                have hallowanceS :
                    (transferFromValueWord I).toNat ≤
                      (transferFromCurrentAllowanceWord evmS I).toNat := by
                  simpa [hAllowance] using hallowance
                have hbalanceS :
                    (transferFromValueWord I).toNat ≤
                      (transferFromFromBalanceWord evmS I).toNat := by
                  simpa [hFromBalance] using hbalance
                have hbalanceDebitS :
                    (transferFromValueWord I).toNat ≤
                      (transferFromFromBalanceWord
                        (transferFromAfterAllowanceState evmS I) I).toNat := by
                  simpa [hAfterAllowanceFromBalance] using hbalanceDebit
                have hbody := erc20TransferFromBodyReverts_overflow evmS I
                  (by simp only [evmS, initState]; exact hwv)
                  hallowanceS hbalanceS hbalanceDebitS
                  (by simpa [hNewToNat] using hover)
                exact (erc20TransferFromX_overflow (g := Sat256.ofUInt256 g)
                    hwv hperm hsz100 hsize hcanonFrom hcanonTo
                    (by simpa [evmE] using hallowance)
                    (by simpa [evmE] using hbalance)
                    (by simpa [evmE] using hbalanceDebit)
                    (by simpa [evmE] using hover) hreach)
                  |>.reEquivExecutionRevert hcode hd hdec hbody
            · have hltDebit :
                  (transferFromFromBalanceWord (transferFromAfterAllowanceState evmE I) I).toNat <
                    (transferFromValueWord I).toNat := by
                omega
              have hbody := erc20TransferFromBodyReverts_balanceDebit evmS I
                (by simp only [evmS, initState]; exact hwv)
                (by simpa [hAllowance] using hallowance)
                (by simpa [hFromBalance] using hbalance)
                (by simpa [hAfterAllowanceFromBalance] using hltDebit)
              exact (erc20TransferFromX_balanceDebitUnderflowFromEntry (g := Sat256.ofUInt256 g)
                  hwv hperm hsz100 hsize hcanonFrom hcanonTo
                  (by simpa [evmE] using hallowance)
                  (by simpa [evmE] using hbalance)
                  (by simpa [evmE] using hltDebit) hreach)
                |>.reEquivExecutionRevert hcode hd hdec hbody
          · have hlt : (transferFromFromBalanceWord evmE I).toNat <
                (transferFromValueWord I).toNat := by
              omega
            have hbody := erc20TransferFromBodyReverts_balance evmS I
              (by simp only [evmS, initState]; exact hwv)
              (by simpa [hAllowance] using hallowance)
              (by simpa [hFromBalance] using hlt)
            exact (erc20TransferFromX_insufficientBalanceFromEntry (g := Sat256.ofUInt256 g)
                hwv hsz100 hsize hcanonFrom hcanonTo
                (by simpa [evmE] using hallowance)
                (by simpa [evmE] using hlt) hreach)
              |>.reEquivExecutionRevert hcode hd hdec hbody
        · have hlt :
              (transferFromCurrentAllowanceWord evmE I).toNat <
                (transferFromValueWord I).toNat := by
            omega
          have hbody := erc20TransferFromBodyReverts_allowance evmS I
            (by simp only [evmS, initState]; exact hwv)
            (by simpa [hAllowance] using hlt)
          exact (erc20TransferFromX_insufficientAllowanceFromEntry (g := Sat256.ofUInt256 g)
              hwv hsz100 hsize hcanonFrom hcanonTo
              (by simpa [evmE] using hlt) hreach)
            |>.reEquivExecutionRevert hcode hd hdec hbody
      · have hdec := erc20Decode_transferFrom_none_noncanon_to (I := I) hsz100 hcanonFrom hcanonTo
        exact (erc20TransferFromX_noncanon_to (g := Sat256.ofUInt256 g)
            hwv hsz100 hsize hcanonFrom hcanonTo hreach)
          |>.reEquivDecodingFailed hcode hd hdec
    · have hdec := erc20Decode_transferFrom_none_noncanon_from (I := I) hsz100 hcanonFrom
      exact (erc20TransferFromX_noncanon_from (g := Sat256.ofUInt256 g)
          hwv hsz100 hsize hcanonFrom hreach)
        |>.reEquivDecodingFailed hcode hd hdec
  · have hshort : I.calldata.size < 100 := by
      omega
    have hdec := erc20Decode_transferFrom_none_short (I := I) hsz4 hshort
    exact (erc20TransferFromX_shortarg (g := Sat256.ofUInt256 g) hwv hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

end VyperERC20
