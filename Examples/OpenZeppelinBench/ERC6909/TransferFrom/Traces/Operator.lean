import Examples.OpenZeppelinBench.ERC6909.TransferFrom.Traces.DebitTail

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unnecessarySimpa false

namespace OpenZeppelinBench.ERC6909

theorem erc6909TransferFromX_operatorFalse_allowanceMax_revert_sender_zero
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderNe : transferFromSenderWord I ≠ transferFromCallerWord I)
    (hopZero : transferFromOperatorWord (initState cA gh bl σ σ₀ g A I) I = ⟨0⟩)
    (hallowanceMax : UInt256.size - 1 ≤
      (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hsenderZero : transferFromSenderWord I = ⟨0⟩)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hbase := transferFromOperatorAllowanceScratchMem_size I
  have hread64 := transferFromOperatorAllowanceScratchMem_read64 I
  obtain ⟨_, _, rd661⟩ := erc6909TransferFromX_operatorFalse_allowanceMax_to661
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := g) (sel := sel) hsz132 hsize hszhi hcanonSender hcanonReceiver
    hsenderNe hopZero hallowanceMax hreach
  exact erc6909TransferFromX_from661_revert_sender_zero_base
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (σcur := σ)
    (A := A) (g := g) (sel := sel) (base := transferFromOperatorAllowanceScratchMem I)
    hbase hread64 hsenderZero rd661

theorem erc6909TransferFromX_operatorFalse_allowanceMax_revert_receiver_zero
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderNe : transferFromSenderWord I ≠ transferFromCallerWord I)
    (hopZero : transferFromOperatorWord (initState cA gh bl σ σ₀ g A I) I = ⟨0⟩)
    (hallowanceMax : UInt256.size - 1 ≤
      (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (hreceiverZero : transferFromReceiverWord I = ⟨0⟩)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hbase := transferFromOperatorAllowanceScratchMem_size I
  have hread64 := transferFromOperatorAllowanceScratchMem_read64 I
  obtain ⟨_, _, rd661⟩ := erc6909TransferFromX_operatorFalse_allowanceMax_to661
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := g) (sel := sel) hsz132 hsize hszhi hcanonSender hcanonReceiver
    hsenderNe hopZero hallowanceMax hreach
  exact erc6909TransferFromX_from661_revert_receiver_zero_base
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (σcur := σ)
    (A := A) (g := g) (sel := sel) (base := transferFromOperatorAllowanceScratchMem I)
    hbase hread64 hcanonSender hsenderNZ hreceiverZero rd661

theorem erc6909TransferFromX_operatorFalse_allowanceMax_insufficient
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderNe : transferFromSenderWord I ≠ transferFromCallerWord I)
    (hopZero : transferFromOperatorWord (initState cA gh bl σ σ₀ g A I) I = ⟨0⟩)
    (hallowanceMax : UInt256.size - 1 ≤
      (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (hreceiverNZ : transferFromReceiverWord I ≠ ⟨0⟩)
    (hlt : (transferFromSenderBalanceWord (initState cA gh bl σ σ₀ g A I) I).toNat <
      (transferFromAmountWord I).toNat)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hbase := transferFromOperatorAllowanceScratchMem_size I
  have hread64 := transferFromOperatorAllowanceScratchMem_read64 I
  obtain ⟨_, _, rd1323⟩ := erc6909TransferFromX_operatorFalse_allowanceMax_to1323
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := g) (sel := sel) hsz132 hsize hszhi hcanonSender hcanonReceiver
    hsenderNe hopZero hallowanceMax hsenderNZ hreceiverNZ hreach
  exact erc6909TransferFromX_from1323_insufficient_base
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (σcur := σ)
    (A := A) (g := g) (sel := sel) (base := transferFromOperatorAllowanceScratchMem I)
    hbase hread64 hcanonSender hsenderNZ hlt rd1323

theorem erc6909TransferFromX_operatorFalse_allowanceMax_overflow
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hperm : I.perm = true)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderNe : transferFromSenderWord I ≠ transferFromCallerWord I)
    (hopZero : transferFromOperatorWord (initState cA gh bl σ σ₀ g A I) I = ⟨0⟩)
    (hallowanceMax : UInt256.size - 1 ≤
      (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (hreceiverNZ : transferFromReceiverWord I ≠ ⟨0⟩)
    (henough : (transferFromAmountWord I).toNat ≤
      (transferFromSenderBalanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hover : UInt256.size ≤
      transferFromTailReceiverCreditNat (initState cA gh bl σ σ₀ g A I) I)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hbase := transferFromOperatorAllowanceScratchMem_size I
  have hread64 := transferFromOperatorAllowanceScratchMem_read64 I
  obtain ⟨_, _, rd1323⟩ := erc6909TransferFromX_operatorFalse_allowanceMax_to1323
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := g) (sel := sel) hsz132 hsize hszhi hcanonSender hcanonReceiver
    hsenderNe hopZero hallowanceMax hsenderNZ hreceiverNZ hreach
  exact erc6909TransferFromX_from1323_overflow_base
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (σcur := σ)
    (A := A) (g := g) (sel := sel) (base := transferFromOperatorAllowanceScratchMem I)
    hbase hread64 hperm hcanonSender hcanonReceiver hsenderNZ hreceiverNZ henough hover
    rd1323

theorem erc6909TransferFromX_operatorFalse_allowanceMax_success
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hperm : I.perm = true)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderNe : transferFromSenderWord I ≠ transferFromCallerWord I)
    (hopZero : transferFromOperatorWord (initState cA gh bl σ σ₀ g A I) I = ⟨0⟩)
    (hallowanceMax : UInt256.size - 1 ≤
      (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (hreceiverNZ : transferFromReceiverWord I ≠ ⟨0⟩)
    (henough : (transferFromAmountWord I).toNat ≤
      (transferFromSenderBalanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hfit : transferFromTailReceiverCreditNat (initState cA gh bl σ σ₀ g A I) I <
      UInt256.size)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ (transferFromSenderBalanceSlot I)
          (transferFromTailSenderDebitWord (initState cA gh bl σ σ₀ g A I) I))
        (transferFromReceiverBalanceSlot I)
        (transferFromTailReceiverCreditWord (initState cA gh bl σ σ₀ g A I) I))
      (UInt256.toByteArray (⟨1⟩ : UInt256)) := by
  have hbase := transferFromOperatorAllowanceScratchMem_size I
  have hread64 := transferFromOperatorAllowanceScratchMem_read64 I
  obtain ⟨_, _, rd1323⟩ := erc6909TransferFromX_operatorFalse_allowanceMax_to1323
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := g) (sel := sel) hsz132 hsize hszhi hcanonSender hcanonReceiver
    hsenderNe hopZero hallowanceMax hsenderNZ hreceiverNZ hreach
  exact erc6909TransferFromX_from1323_successCaller_base
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (σcur := σ)
    (A := A) (g := g) (sel := sel) (base := transferFromOperatorAllowanceScratchMem I)
    hbase hread64 hperm hcanonSender hcanonReceiver hsenderNZ hreceiverNZ henough hfit
    rd1323

set_option maxHeartbeats 4000000 in
theorem erc6909TransferFromX_operatorFalse_insufficientAllowance
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderNe : transferFromSenderWord I ≠ transferFromCallerWord I)
    (hopZero : transferFromOperatorWord (initState cA gh bl σ σ₀ g A I) I = ⟨0⟩)
    (hallowanceNotMax :
      (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat <
        UInt256.size - 1)
    (hltAllowance :
      (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat <
        (transferFromAmountWord I).toNat)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hbase := transferFromOperatorAllowanceScratchMem_size I
  have hread64 := transferFromOperatorAllowanceScratchMem_read64 I
  obtain ⟨_, _, rd1193⟩ := erc6909TransferFromX_operatorFalse_afterAllowanceLoad
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := g) (sel := sel) hsz132 hsize hszhi hcanonSender hcanonReceiver
    hsenderNe hopZero hreach
  have hmaxToNat :
      (UInt256.ofNat (UInt256.size - 1)).toNat = UInt256.size - 1 := by
    exact ulit_toNat' _ (by
      have hpos : 0 < UInt256.size := by norm_num [UInt256.size]
      exact Nat.sub_lt hpos (by decide))
  have hltMax :
      UInt256.lt
        (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I)
        (UInt256.lnot (⟨0⟩ : UInt256)) = ⟨1⟩ := by
    rw [uint256_lnot_zero_max]
    exact ult_one (by simpa [hmaxToNat] using hallowanceNotMax)
  have hltAmount :
      UInt256.lt
        (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I)
        (transferFromAmountWord I) = ⟨1⟩ := ult_one hltAllowance
  have rd1202 := evm_run rd1193 with [
    push0, not, dup2, lt, iszero, push2 ⟨1316⟩,
    jumpiNT (by rw [hltMax]; decide) ]
  have rd1266 := evm_run rd1202 with [
    dup2, dup2, lt, iszero, push2 ⟨1266⟩,
    jumpiNT (by rw [hltAmount]; decide) ]
  exact evm_run rd1266 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost (erc6909ScratchMem_mload64 hbase hread64) (by decide) (by evm_ov),
    push4 ⟨0x2c51fead⟩, push1 ⟨225⟩, shl, dup2,
    raw mstore 6
      (transferFromInsufficientAllowanceSelectorBaseMem
        (transferFromOperatorAllowanceScratchMem I))
      (UInt256.ofNat 5) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup6, and,
    push1 ⟨4⟩, dup3, add,
    raw mstore 3
      (transferFromInsufficientAllowanceSenderBaseMem
        (transferFromOperatorAllowanceScratchMem I) (transferFromCallerWord I))
      (UInt256.ofNat 6) (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rw [solcAddrMask_clean (transferFromCallerWord_canonical I)]
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨36⟩, dup2, add, dup3, swap1,
    raw mstore 3
      (transferFromInsufficientAllowanceAllowanceBaseMem
        (transferFromOperatorAllowanceScratchMem I) (transferFromCallerWord I)
        (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I))
      (UInt256.ofNat 7) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨68⟩, dup2, add, dup4, swap1,
    raw mstore 3
      (transferFromInsufficientAllowanceAmountBaseMem
        (transferFromOperatorAllowanceScratchMem I) (transferFromCallerWord I)
        (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I)
        (transferFromAmountWord I))
      (UInt256.ofNat 8) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨100⟩, dup2, add, dup5, swap1,
    raw mstore 3
      (transferFromInsufficientAllowanceIdBaseMem
        (transferFromOperatorAllowanceScratchMem I) (transferFromCallerWord I)
        (transferFromIdWord I)
        (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I)
        (transferFromAmountWord I))
      (UInt256.ofNat 9) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨132⟩, add, push2 ⟨698⟩, jump (by jump_dest),
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 9) (by decide)
      mem_cost
      (transferFromInsufficientAllowanceIdBaseMem_mload64 (transferFromCallerWord I)
        (transferFromIdWord I)
        (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I)
        (transferFromAmountWord I) hbase hread64)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw rev 0 (by decide) mem_cost (by evm_ov) ]

theorem erc6909TransferFromX_operatorApproved_revert_sender_zero
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderNe : transferFromSenderWord I ≠ transferFromCallerWord I)
    (hop : transferFromOperatorWord (initState cA gh bl σ σ₀ g A I) I ≠ ⟨0⟩)
    (hsenderZero : transferFromSenderWord I = ⟨0⟩)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let base := isOperatorOuterHashMem (transferFromSenderWord I) (transferFromCallerWord I)
  have hbase : base.size = 96 := by
    dsimp [base]
    exact isOperatorOuterHashMem_size (transferFromSenderWord I) (transferFromCallerWord I)
  have hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [base]
    exact isOperatorOuterHashMem_read64 (transferFromSenderWord I) (transferFromCallerWord I)
  obtain ⟨_, _, rd661⟩ := erc6909TransferFromX_operatorApproved_toUpdate
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    (sel := sel) hsz132 hsize hszhi hcanonSender hcanonReceiver hsenderNe hop hreach
  exact erc6909TransferFromX_from661_revert_sender_zero_base
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (σcur := σ) (A := A)
    (g := g) (sel := sel) (base := base) hbase hread64 hsenderZero rd661

theorem erc6909TransferFromX_operatorApproved_revert_receiver_zero
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderNe : transferFromSenderWord I ≠ transferFromCallerWord I)
    (hop : transferFromOperatorWord (initState cA gh bl σ σ₀ g A I) I ≠ ⟨0⟩)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (hreceiverZero : transferFromReceiverWord I = ⟨0⟩)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let base := isOperatorOuterHashMem (transferFromSenderWord I) (transferFromCallerWord I)
  have hbase : base.size = 96 := by
    dsimp [base]
    exact isOperatorOuterHashMem_size (transferFromSenderWord I) (transferFromCallerWord I)
  have hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [base]
    exact isOperatorOuterHashMem_read64 (transferFromSenderWord I) (transferFromCallerWord I)
  obtain ⟨_, _, rd661⟩ := erc6909TransferFromX_operatorApproved_toUpdate
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    (sel := sel) hsz132 hsize hszhi hcanonSender hcanonReceiver hsenderNe hop hreach
  exact erc6909TransferFromX_from661_revert_receiver_zero_base
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (σcur := σ) (A := A)
    (g := g) (sel := sel) (base := base) hbase hread64 hcanonSender hsenderNZ
    hreceiverZero rd661

theorem erc6909TransferFromX_operatorApproved_insufficient
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderNe : transferFromSenderWord I ≠ transferFromCallerWord I)
    (hop : transferFromOperatorWord (initState cA gh bl σ σ₀ g A I) I ≠ ⟨0⟩)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (hreceiverNZ : transferFromReceiverWord I ≠ ⟨0⟩)
    (hlt : (transferFromSenderBalanceWord (initState cA gh bl σ σ₀ g A I) I).toNat <
      (transferFromAmountWord I).toNat)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let base := isOperatorOuterHashMem (transferFromSenderWord I) (transferFromCallerWord I)
  have hbase : base.size = 96 := by
    dsimp [base]
    exact isOperatorOuterHashMem_size (transferFromSenderWord I) (transferFromCallerWord I)
  have hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [base]
    exact isOperatorOuterHashMem_read64 (transferFromSenderWord I) (transferFromCallerWord I)
  obtain ⟨_, _, rd661⟩ := erc6909TransferFromX_operatorApproved_toUpdate
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    (sel := sel) hsz132 hsize hszhi hcanonSender hcanonReceiver hsenderNe hop hreach
  obtain ⟨_, _, rd1323⟩ := erc6909TransferFromX_from661_toUpdateHelper_base
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (σcur := σ) (A := A)
    (g := g) (sel := sel) (base := base) hcanonSender hcanonReceiver hsenderNZ
    hreceiverNZ rd661
  exact erc6909TransferFromX_from1323_insufficient_base
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (σcur := σ) (A := A)
    (g := g) (sel := sel) (base := base) hbase hread64 hcanonSender hsenderNZ hlt
    rd1323

theorem erc6909TransferFromX_operatorApproved_overflow
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hperm : I.perm = true)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderNe : transferFromSenderWord I ≠ transferFromCallerWord I)
    (hop : transferFromOperatorWord (initState cA gh bl σ σ₀ g A I) I ≠ ⟨0⟩)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (hreceiverNZ : transferFromReceiverWord I ≠ ⟨0⟩)
    (henough : (transferFromAmountWord I).toNat ≤
      (transferFromSenderBalanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hover : UInt256.size ≤
      transferFromTailReceiverCreditNat (initState cA gh bl σ σ₀ g A I) I)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let base := isOperatorOuterHashMem (transferFromSenderWord I) (transferFromCallerWord I)
  have hbase : base.size = 96 := by
    dsimp [base]
    exact isOperatorOuterHashMem_size (transferFromSenderWord I) (transferFromCallerWord I)
  have hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [base]
    exact isOperatorOuterHashMem_read64 (transferFromSenderWord I) (transferFromCallerWord I)
  obtain ⟨_, _, rd661⟩ := erc6909TransferFromX_operatorApproved_toUpdate
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    (sel := sel) hsz132 hsize hszhi hcanonSender hcanonReceiver hsenderNe hop hreach
  obtain ⟨_, _, rd1323⟩ := erc6909TransferFromX_from661_toUpdateHelper_base
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (σcur := σ) (A := A)
    (g := g) (sel := sel) (base := base) hcanonSender hcanonReceiver hsenderNZ
    hreceiverNZ rd661
  exact erc6909TransferFromX_from1323_overflow_base
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (σcur := σ) (A := A)
    (g := g) (sel := sel) (base := base) hbase hread64 hperm hcanonSender hcanonReceiver
    hsenderNZ hreceiverNZ henough hover rd1323

theorem erc6909TransferFromX_operatorApproved_success
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hperm : I.perm = true)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderNe : transferFromSenderWord I ≠ transferFromCallerWord I)
    (hop : transferFromOperatorWord (initState cA gh bl σ σ₀ g A I) I ≠ ⟨0⟩)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (hreceiverNZ : transferFromReceiverWord I ≠ ⟨0⟩)
    (henough : (transferFromAmountWord I).toNat ≤
      (transferFromSenderBalanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hfit : transferFromTailReceiverCreditNat (initState cA gh bl σ σ₀ g A I) I <
      UInt256.size)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ (transferFromSenderBalanceSlot I)
          (transferFromTailSenderDebitWord (initState cA gh bl σ σ₀ g A I) I))
        (transferFromReceiverBalanceSlot I)
        (transferFromTailReceiverCreditWord (initState cA gh bl σ σ₀ g A I) I))
      (UInt256.toByteArray (⟨1⟩ : UInt256)) := by
  let base := isOperatorOuterHashMem (transferFromSenderWord I) (transferFromCallerWord I)
  have hbase : base.size = 96 := by
    dsimp [base]
    exact isOperatorOuterHashMem_size (transferFromSenderWord I) (transferFromCallerWord I)
  have hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [base]
    exact isOperatorOuterHashMem_read64 (transferFromSenderWord I) (transferFromCallerWord I)
  obtain ⟨_, _, rd661⟩ := erc6909TransferFromX_operatorApproved_toUpdate
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    (sel := sel) hsz132 hsize hszhi hcanonSender hcanonReceiver hsenderNe hop hreach
  obtain ⟨_, _, rd1323⟩ := erc6909TransferFromX_from661_toUpdateHelper_base
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (σcur := σ) (A := A)
    (g := g) (sel := sel) (base := base) hcanonSender hcanonReceiver hsenderNZ
    hreceiverNZ rd661
  exact erc6909TransferFromX_from1323_successCaller_base
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (σcur := σ) (A := A)
    (g := g) (sel := sel) (base := base) hbase hread64 hperm hcanonSender hcanonReceiver
    hsenderNZ hreceiverNZ henough hfit rd1323

theorem erc6909TransferFromX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 132)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨128⟩ = ⟨1⟩ := by
    simpa using solcCalldataStaticLenCheckShort (words := 4) hsz4 hshort hsize
      (by norm_num)
  obtain ⟨_, _, rd⟩ := erc6909TransferFromX_toDecoder (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach
  exact evm_run rd with [
    jumpdest, push0, push0, push0, push0, push1 ⟨128⟩, dup6, dup8, sub, slt, iszero,
    push2 ⟨1973⟩, jumpiNT (by rw [hslt]; decide),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem erc6909TransferFromX_hugearg {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨128⟩ = ⟨1⟩ := by
    simpa using solcCalldataStaticLenCheckHuge (words := 4) hbig hsize (by norm_num)
  obtain ⟨_, _, rd⟩ := erc6909TransferFromX_toDecoder (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach
  exact evm_run rd with [
    jumpdest, push0, push0, push0, push0, push1 ⟨128⟩, dup6, dup8, sub, slt, iszero,
    push2 ⟨1973⟩, jumpiNT (by rw [hslt]; decide),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem erc6909TransferFromX_noncanon_sender {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : UInt256.eq (transferFromSenderWord I)
      (UInt256.land (transferFromSenderWord I) solcAddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd⟩ := erc6909TransferFromX_dec1629_sender (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz132 hsize hszhi hreach
  simpa [transferFromSenderWord, calldataWord] using
    erc6909DecodeAddrRevert rd hnc (by evm_ov)

theorem erc6909TransferFromX_noncanon_receiver {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hnc : UInt256.eq (transferFromReceiverWord I)
      (UInt256.land (transferFromReceiverWord I) solcAddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd⟩ := erc6909TransferFromX_dec1629_receiver (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz132 hsize hszhi hcanonSender hreach
  simpa [transferFromReceiverWord, calldataWord] using
    erc6909DecodeAddrRevert rd hnc (by evm_ov)


end OpenZeppelinBench.ERC6909
