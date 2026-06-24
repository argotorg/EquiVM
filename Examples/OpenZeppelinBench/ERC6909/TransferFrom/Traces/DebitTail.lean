import Examples.OpenZeppelinBench.ERC6909.TransferFrom.Traces.Allowance

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unnecessarySimpa false

namespace OpenZeppelinBench.ERC6909

theorem erc6909TransferFromX_operatorFalse_afterAllowanceLoad
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderNe : transferFromSenderWord I ≠ transferFromCallerWord I)
    (hopZero : transferFromOperatorWord (initState cA gh bl σ σ₀ g A I) I = ⟨0⟩)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1193⟩
      [transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I,
        transferFromAmountWord I, transferFromIdWord I, transferFromCallerWord I,
        transferFromSenderWord I, ⟨637⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      (transferFromOperatorAllowanceScratchMem I)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  let base := isOperatorOuterHashMem (transferFromSenderWord I) (transferFromCallerWord I)
  have hbase : base.size = 96 := by
    dsimp [base]
    exact isOperatorOuterHashMem_size (transferFromSenderWord I) (transferFromCallerWord I)
  have hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [base]
    exact isOperatorOuterHashMem_read64 (transferFromSenderWord I) (transferFromCallerWord I)
  obtain ⟨_, _, rd1147⟩ := erc6909TransferFromX_operatorFalse_toAllowanceHelper
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := g) (sel := sel) hsz132 hsize hszhi hcanonSender hcanonReceiver
    hsenderNe hopZero hreach
  obtain ⟨k1, C1, rd1193⟩ := erc6909TransferFromX_from1147_afterAllowanceLoad
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := g) (sel := sel) (base := base) hbase hread64 hcanonSender rd1147
  exact ⟨k1, C1, by
    simpa [base, transferFromOperatorAllowanceScratchMem, transferFromAllowanceScratchMem]
      using rd1193⟩

theorem erc6909TransferFromX_operatorFalse_allowanceMax_to661
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderNe : transferFromSenderWord I ≠ transferFromCallerWord I)
    (hopZero : transferFromOperatorWord (initState cA gh bl σ σ₀ g A I) I = ⟨0⟩)
    (hallowanceMax : UInt256.size - 1 ≤
      (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨661⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨649⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      (transferFromOperatorAllowanceScratchMem I)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1193⟩ := erc6909TransferFromX_operatorFalse_afterAllowanceLoad
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := g) (sel := sel) hsz132 hsize hszhi hcanonSender hcanonReceiver
    hsenderNe hopZero hreach
  exact erc6909TransferFromX_from1193_allowanceMax_to661_base
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) (sel := sel)
    (base := transferFromOperatorAllowanceScratchMem I)
    hallowanceMax rd1193

theorem erc6909TransferFromX_operatorFalse_allowanceMax_to1323
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderNe : transferFromSenderWord I ≠ transferFromCallerWord I)
    (hopZero : transferFromOperatorWord (initState cA gh bl σ σ₀ g A I) I = ⟨0⟩)
    (hallowanceMax : UInt256.size - 1 ≤
      (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (hreceiverNZ : transferFromReceiverWord I ≠ ⟨0⟩)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1323⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨760⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨649⟩, transferFromCallerWord I, ⟨0⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨193⟩, sel]
      (transferFromOperatorAllowanceScratchMem I)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd661⟩ := erc6909TransferFromX_operatorFalse_allowanceMax_to661
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := g) (sel := sel) hsz132 hsize hszhi hcanonSender hcanonReceiver
    hsenderNe hopZero hallowanceMax hreach
  exact erc6909TransferFromX_from661_toUpdateHelper_base
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (σcur := σ)
    (A := A) (g := g) (sel := sel)
    (base := transferFromOperatorAllowanceScratchMem I)
    hcanonSender hcanonReceiver hsenderNZ hreceiverNZ rd661

theorem erc6909TransferFromX_from661_revert_sender_zero_base
    {cA gh bl σ σ₀ σcur A I} {g : Sat256} {sel : UInt256} {k C : ℕ}
    {base : ByteArray}
    (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hsenderZero : transferFromSenderWord I = ⟨0⟩)
    (rd661 : RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨661⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨649⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      base (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have rd676 := evm_run rd661 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup5, and,
    push2 ⟨707⟩,
    jumpiNT (by
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      rw [hsenderZero]
      decide) ]
  exact evm_run rd676 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost (erc6909ScratchMem_mload64 hbase hread64) (by decide) (by evm_ov),
    push4 ⟨0x01486a41⟩, push1 ⟨231⟩, shl, dup2,
    raw mstore 6 (solcReturnBaseMem base transferFromInvalidSenderSelectorWord)
      (UInt256.ofNat 5) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push0, push1 ⟨4⟩, dup3, add,
    raw mstore 3 (approveErrorBaseMem base transferFromInvalidSenderSelectorWord ⟨0⟩)
      (UInt256.ofNat 6) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨36⟩, add,
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide)
      mem_cost (approveErrorBaseMem_mload64 transferFromInvalidSenderSelectorWord ⟨0⟩
        hbase hread64)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw rev 0 (by decide) mem_cost (by evm_ov) ]

theorem erc6909TransferFromX_from661_revert_receiver_zero_base
    {cA gh bl σ σ₀ σcur A I} {g : Sat256} {sel : UInt256} {k C : ℕ}
    {base : ByteArray}
    (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (hreceiverZero : transferFromReceiverWord I = ⟨0⟩)
    (rd661 : RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨661⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨649⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      base (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have rd722 := evm_run rd661 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup5, and,
    push2 ⟨707⟩,
    jumpiT (by
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      rw [solcAddrMask_clean hcanonSender]
      exact hsenderNZ)
      (by jump_dest),
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup4, and,
    push2 ⟨748⟩,
    jumpiNT (by
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      rw [hreceiverZero]
      decide) ]
  exact evm_run rd722 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost (erc6909ScratchMem_mload64 hbase hread64) (by decide) (by evm_ov),
    push4 ⟨0x0b8bbd61⟩, push1 ⟨228⟩, shl, dup2,
    raw mstore 6 (solcReturnBaseMem base transferFromInvalidReceiverSelectorWord)
      (UInt256.ofNat 5) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push0, push1 ⟨4⟩, dup3, add,
    raw mstore 3 (approveErrorBaseMem base transferFromInvalidReceiverSelectorWord ⟨0⟩)
      (UInt256.ofNat 6) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨36⟩, add, push2 ⟨698⟩, jump (by jump_dest),
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide)
      mem_cost (approveErrorBaseMem_mload64 transferFromInvalidReceiverSelectorWord ⟨0⟩
        hbase hread64)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw rev 0 (by decide) mem_cost (by evm_ov) ]

theorem erc6909TransferFromX_from1323_afterLoad {cA gh bl σ σ₀ σcur A I}
    {g : Sat256} {sel : UInt256} {k C : ℕ}
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (rd1323 : RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1323⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨760⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨649⟩, transferFromCallerWord I, ⟨0⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨193⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1373⟩
      [transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I,
        transferFromCallerWord I, transferFromAmountWord I, transferFromIdWord I,
        transferFromReceiverWord I, transferFromSenderWord I, ⟨760⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨649⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      (transferOuterHashMem (transferFromSenderWord I) (transferFromIdWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C := by
  have hslot := transferFromSenderBalanceKeccakSlot I hcanonSender
  have rd1340 := evm_run rd1323 with [
    jumpdest, caller, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup6, and,
    iszero, push2 ⟨1476⟩,
    jumpiNT (by
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      rw [solcAddrMask_clean hcanonSender]
      exact isZero_eq_zero_of_ne hsenderNZ) ]
  have rd1372 := evm_run rd1340 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup6, and, push0, swap1, dup2,
    raw mstore 0 (approveWordAt0Mem (transferFromSenderWord I) solcFreePtrMem)
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rw [solcAddrMask_clean hcanonSender]
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨32⟩, dup2, dup2,
    raw mstore 0 (transferInnerHashMem (transferFromSenderWord I))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, dup1, dup4,
    raw keccak256 0 (transferInnerSlot (transferFromSenderWord I))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    dup7, dup5,
    raw mstore 0 (approveWordAt0Mem (transferFromIdWord I)
        (transferInnerHashMem (transferFromSenderWord I)))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    swap1, swap2,
    raw mstore 0 (transferOuterHashMem (transferFromSenderWord I) (transferFromIdWord I))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    swap1,
    raw keccak256 0 (transferOuterSlot (transferFromSenderWord I) (transferFromIdWord I))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov) ]
  obtain ⟨k1, C1, rd1373₀⟩ := rd1372.sload (by decide) (by evm_ov)
  exact ⟨k1, C1, by
    simpa [transferFromSenderBalanceWord, transferFromSenderBalanceSlot,
      hslot, initState, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
      using rd1373₀⟩

theorem erc6909TransferFromX_from1323_afterRequire {cA gh bl σ σ₀ σcur A I}
    {g : Sat256} {sel : UInt256} {k C : ℕ}
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (henough : (transferFromAmountWord I).toNat ≤
      (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I).toNat)
    (rd1323 : RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1323⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨760⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨649⟩, transferFromCallerWord I, ⟨0⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨193⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1437⟩
      [transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I,
        transferFromCallerWord I, transferFromAmountWord I, transferFromIdWord I,
        transferFromReceiverWord I, transferFromSenderWord I, ⟨760⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨649⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      (transferOuterHashMem (transferFromSenderWord I) (transferFromIdWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C := by
  obtain ⟨_, _, rd1373⟩ := erc6909TransferFromX_from1323_afterLoad
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (σcur := σcur)
    (A := A) (g := g) (sel := sel) hcanonSender hsenderNZ rd1323
  have hlt : UInt256.lt
      (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I)
      (transferFromAmountWord I) = ⟨0⟩ := ult_zero henough
  exact ⟨_, _, evm_run rd1373 with [
    dup3, dup2, lt, iszero, push2 ⟨1437⟩,
    jumpiT (by rw [hlt]; decide) (by jump_dest) ]⟩

theorem erc6909TransferFromX_from1373_insufficient {cA gh bl σ σ₀ σcur A I}
    {g : Sat256} {sel : UInt256} {k C : ℕ}
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hlt : (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I).toNat <
      (transferFromAmountWord I).toNat)
    (rd1373 : RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1373⟩
      [transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I,
        transferFromCallerWord I, transferFromAmountWord I, transferFromIdWord I,
        transferFromReceiverWord I, transferFromSenderWord I, ⟨760⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨649⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      (transferOuterHashMem (transferFromSenderWord I) (transferFromIdWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hltw : UInt256.lt
      (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I)
      (transferFromAmountWord I) = ⟨1⟩ := ult_one hlt
  have rd1381 := evm_run rd1373 with [
    dup3, dup2, lt, iszero, push2 ⟨1437⟩,
    jumpiNT (by rw [hltw]; decide) ]
  exact evm_run rd1381 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide) mem_cost
      (transferOuterHashMem_mload64 (transferFromSenderWord I) (transferFromIdWord I))
      (by decide) (by evm_ov),
    push4 ⟨0x02c6d3fb⟩, push1 ⟨230⟩, shl, dup2,
    raw mstore 6 (transferInsufficientBalanceSelectorMem (transferFromSenderWord I)
        (transferFromIdWord I))
      (UInt256.ofNat 5) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup8, and,
    push1 ⟨4⟩, dup3, add,
    raw mstore 3 (transferInsufficientBalanceSenderMem (transferFromSenderWord I)
        (transferFromIdWord I))
      (UInt256.ofNat 6) (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rw [solcAddrMask_clean hcanonSender]
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨36⟩, dup2, add, dup3, swap1,
    raw mstore 3 (transferInsufficientBalanceBalanceMem (transferFromSenderWord I)
        (transferFromIdWord I)
        (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I))
      (UInt256.ofNat 7) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨68⟩, dup2, add, dup5, swap1,
    raw mstore 3 (transferInsufficientBalanceAmountMem (transferFromSenderWord I)
        (transferFromIdWord I)
        (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I)
        (transferFromAmountWord I))
      (UInt256.ofNat 8) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨100⟩, dup2, add, dup6, swap1,
    raw mstore 3 (transferInsufficientBalanceIdMem (transferFromSenderWord I)
        (transferFromIdWord I)
        (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I)
        (transferFromAmountWord I))
      (UInt256.ofNat 9) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨132⟩, add, push2 ⟨698⟩, jump (by jump_dest),
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 9) (by decide) mem_cost
      (transferInsufficientBalanceIdMem_mload64 (transferFromSenderWord I)
        (transferFromIdWord I)
        (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I)
        (transferFromAmountWord I))
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw rev 0 (by decide) mem_cost (by evm_ov) ]

theorem erc6909TransferFromX_from1323_insufficient {cA gh bl σ σ₀ σcur A I}
    {g : Sat256} {sel : UInt256} {k C : ℕ}
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (hlt : (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I).toNat <
      (transferFromAmountWord I).toNat)
    (rd1323 : RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1323⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨760⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨649⟩, transferFromCallerWord I, ⟨0⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨193⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd1373⟩ := erc6909TransferFromX_from1323_afterLoad
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (σcur := σcur)
    (A := A) (g := g) (sel := sel) hcanonSender hsenderNZ rd1323
  exact erc6909TransferFromX_from1373_insufficient hcanonSender hlt rd1373

theorem erc6909TransferFromX_from1323_afterLoad_base {cA gh bl σ σ₀ σcur A I}
    {g : Sat256} {sel : UInt256} {k C : ℕ} {base : ByteArray}
    (hbase : base.size = 96)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (rd1323 : RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1323⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨760⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨649⟩, transferFromCallerWord I, ⟨0⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨193⟩, sel]
      base (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1373⟩
      [transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I,
        transferFromCallerWord I, transferFromAmountWord I, transferFromIdWord I,
        transferFromReceiverWord I, transferFromSenderWord I, ⟨760⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨649⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      (transferMapScratchMem base (transferFromSenderWord I) (transferFromIdWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C := by
  have hslot := transferFromSenderBalanceKeccakSlot I hcanonSender
  have rd1340 := evm_run rd1323 with [
    jumpdest, caller, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup6, and,
    iszero, push2 ⟨1476⟩,
    jumpiNT (by
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      rw [solcAddrMask_clean hcanonSender]
      exact isZero_eq_zero_of_ne hsenderNZ) ]
  have rd1372 := evm_run rd1340 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup6, and, push0, swap1, dup2,
    raw mstore 0 (approveWordAt0Mem (transferFromSenderWord I) base)
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rw [solcAddrMask_clean hcanonSender]
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨32⟩, dup2, dup2,
    raw mstore 0 (approveTwoWordHashMem (transferFromSenderWord I) ⟨0⟩ base)
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, dup1, dup4,
    raw keccak256 0 (transferInnerSlot (transferFromSenderWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        unfold transferInnerSlot
        change UInt256.ofNat
            (fromByteArrayBigEndian
              (ffi.KEC
                ((approveTwoWordHashMem (transferFromSenderWord I) ⟨0⟩ base
                  ).readWithPadding 0 64))) =
          UInt256.ofNat
            (fromByteArrayBigEndian
              (ffi.KEC ((transferInnerHashMem (transferFromSenderWord I)).readWithPadding 0 64)))
        rw [approveTwoWordHashMem_read0_64 (transferFromSenderWord I) ⟨0⟩ hbase,
          transferInnerHashMem_read0_64])
      (by decide) (by evm_ov),
    dup7, dup5,
    raw mstore 0 (approveWordAt0Mem (transferFromIdWord I)
        (approveTwoWordHashMem (transferFromSenderWord I) ⟨0⟩ base))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    swap1, swap2,
    raw mstore 0 (transferMapScratchMem base (transferFromSenderWord I)
        (transferFromIdWord I))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    swap1,
    raw keccak256 0 (transferOuterSlot (transferFromSenderWord I) (transferFromIdWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        unfold transferOuterSlot
        change UInt256.ofNat
            (fromByteArrayBigEndian
              (ffi.KEC
                ((transferMapScratchMem base (transferFromSenderWord I)
                    (transferFromIdWord I)).readWithPadding 0 64))) =
          UInt256.ofNat
            (fromByteArrayBigEndian
              (ffi.KEC
                ((transferOuterHashMem (transferFromSenderWord I) (transferFromIdWord I)
                  ).readWithPadding 0 64)))
        rw [transferMapScratchMem_read0_64 (transferFromSenderWord I)
          (transferFromIdWord I) hbase, transferOuterHashMem_read0_64])
      (by decide) (by evm_ov) ]
  obtain ⟨k1, C1, rd1373₀⟩ := rd1372.sload (by decide) (by evm_ov)
  exact ⟨k1, C1, by
    simpa [transferFromSenderBalanceWord, transferFromSenderBalanceSlot,
      hslot, initState, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
      using rd1373₀⟩

theorem erc6909TransferFromX_from1323_afterRequire_base {cA gh bl σ σ₀ σcur A I}
    {g : Sat256} {sel : UInt256} {k C : ℕ} {base : ByteArray}
    (hbase : base.size = 96)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (henough : (transferFromAmountWord I).toNat ≤
      (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I).toNat)
    (rd1323 : RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1323⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨760⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨649⟩, transferFromCallerWord I, ⟨0⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨193⟩, sel]
      base (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1437⟩
      [transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I,
        transferFromCallerWord I, transferFromAmountWord I, transferFromIdWord I,
        transferFromReceiverWord I, transferFromSenderWord I, ⟨760⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨649⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      (transferMapScratchMem base (transferFromSenderWord I) (transferFromIdWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C := by
  obtain ⟨_, _, rd1373⟩ := erc6909TransferFromX_from1323_afterLoad_base
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (σcur := σcur)
    (A := A) (g := g) (sel := sel) hbase hcanonSender hsenderNZ rd1323
  have hlt : UInt256.lt
      (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I)
      (transferFromAmountWord I) = ⟨0⟩ := ult_zero henough
  exact ⟨_, _, evm_run rd1373 with [
    dup3, dup2, lt, iszero, push2 ⟨1437⟩,
    jumpiT (by rw [hlt]; decide) (by jump_dest) ]⟩

theorem erc6909TransferFromX_from1373_insufficient_base
    {cA gh bl σ σ₀ σcur A I} {g : Sat256} {sel : UInt256} {k C : ℕ}
    {base : ByteArray}
    (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hlt : (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I).toNat <
      (transferFromAmountWord I).toNat)
    (rd1373 : RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1373⟩
      [transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I,
        transferFromCallerWord I, transferFromAmountWord I, transferFromIdWord I,
        transferFromReceiverWord I, transferFromSenderWord I, ⟨760⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨649⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      (transferMapScratchMem base (transferFromSenderWord I) (transferFromIdWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let senderMem := transferMapScratchMem base (transferFromSenderWord I) (transferFromIdWord I)
  have hsenderMemSize : senderMem.size = 96 := by
    dsimp [senderMem]
    exact transferMapScratchMem_size (transferFromSenderWord I) (transferFromIdWord I) hbase
  have hsenderMemRead64 :
      senderMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [senderMem]
    exact transferMapScratchMem_read64 (transferFromSenderWord I) (transferFromIdWord I)
      hbase hread64
  have hltw : UInt256.lt
      (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I)
      (transferFromAmountWord I) = ⟨1⟩ := ult_one hlt
  have rd1381 := evm_run rd1373 with [
    dup3, dup2, lt, iszero, push2 ⟨1437⟩,
    jumpiNT (by rw [hltw]; decide) ]
  exact evm_run rd1381 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide) mem_cost
      (transferMapScratchMem_mload64 (transferFromSenderWord I) (transferFromIdWord I)
        hbase hread64)
      (by decide) (by evm_ov),
    push4 ⟨0x02c6d3fb⟩, push1 ⟨230⟩, shl, dup2,
    raw mstore 6 (transferInsufficientBalanceSelectorBaseMem senderMem)
      (UInt256.ofNat 5) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup8, and,
    push1 ⟨4⟩, dup3, add,
    raw mstore 3 (transferInsufficientBalanceSenderBaseMem senderMem
        (transferFromSenderWord I))
      (UInt256.ofNat 6) (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rw [solcAddrMask_clean hcanonSender]
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨36⟩, dup2, add, dup3, swap1,
    raw mstore 3 (transferInsufficientBalanceBalanceBaseMem senderMem
        (transferFromSenderWord I)
        (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I))
      (UInt256.ofNat 7) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨68⟩, dup2, add, dup5, swap1,
    raw mstore 3 (transferInsufficientBalanceAmountBaseMem senderMem
        (transferFromSenderWord I)
        (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I)
        (transferFromAmountWord I))
      (UInt256.ofNat 8) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨100⟩, dup2, add, dup6, swap1,
    raw mstore 3 (transferInsufficientBalanceIdBaseMem senderMem
        (transferFromSenderWord I) (transferFromIdWord I)
        (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I)
        (transferFromAmountWord I))
      (UInt256.ofNat 9) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨132⟩, add, push2 ⟨698⟩, jump (by jump_dest),
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 9) (by decide) mem_cost
      (transferInsufficientBalanceIdBaseMem_mload64 (transferFromSenderWord I)
        (transferFromIdWord I)
        (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I)
        (transferFromAmountWord I) hsenderMemSize hsenderMemRead64)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw rev 0 (by decide) mem_cost (by evm_ov) ]

theorem erc6909TransferFromX_from1323_insufficient_base
    {cA gh bl σ σ₀ σcur A I} {g : Sat256} {sel : UInt256} {k C : ℕ}
    {base : ByteArray}
    (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (hlt : (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I).toNat <
      (transferFromAmountWord I).toNat)
    (rd1323 : RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1323⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨760⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨649⟩, transferFromCallerWord I, ⟨0⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨193⟩, sel]
      base (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd1373⟩ := erc6909TransferFromX_from1323_afterLoad_base
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (σcur := σcur)
    (A := A) (g := g) (sel := sel) hbase hcanonSender hsenderNZ rd1323
  exact erc6909TransferFromX_from1373_insufficient_base
    hbase hread64 hcanonSender hlt rd1373

theorem erc6909TransferFromX_from1323_afterDebit {cA gh bl σ σ₀ σcur A I}
    {g : Sat256} {sel : UInt256} {k C : ℕ}
    (hperm : I.perm = true)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (henough : (transferFromAmountWord I).toNat ≤
      (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I).toNat)
    (rd1323 : RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1323⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨760⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨649⟩, transferFromCallerWord I, ⟨0⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨193⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1476⟩
      [transferFromCallerWord I, transferFromAmountWord I, transferFromIdWord I,
        transferFromReceiverWord I, transferFromSenderWord I, ⟨760⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨649⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      (transferMapScratchMem
        (transferOuterHashMem (transferFromSenderWord I) (transferFromIdWord I))
        (transferFromSenderWord I) (transferFromIdWord I))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σcur (transferFromSenderBalanceSlot I)
        (transferFromTailSenderDebitWord (initState cA gh bl σcur σ₀ g A I) I)) k C := by
  obtain ⟨_, _, rd1437⟩ := erc6909TransferFromX_from1323_afterRequire
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (σcur := σcur)
    (A := A) (g := g) (sel := sel) hcanonSender hsenderNZ henough rd1323
  have hslot := transferFromSenderBalanceKeccakSlot I hcanonSender
  have rd1451 := evm_run rd1437 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup7, and,
    push0, swap1, dup2,
    raw mstore 0 (approveWordAt0Mem (transferFromSenderWord I)
        (transferOuterHashMem (transferFromSenderWord I) (transferFromIdWord I)))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rw [solcAddrMask_clean hcanonSender]
        rfl)
      (by decide) (by evm_ov) ]
  have rd1456 := evm_run rd1451 with [
    push1 ⟨32⟩, dup2, dup2,
    raw mstore 0 (approveTwoWordHashMem (transferFromSenderWord I) ⟨0⟩
        (transferOuterHashMem (transferFromSenderWord I) (transferFromIdWord I)))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov) ]
  have rd1461 := evm_run rd1456 with [
    push1 ⟨64⟩, dup1, dup4,
    raw keccak256 0 (transferInnerSlot (transferFromSenderWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        unfold transferInnerSlot
        change UInt256.ofNat
            (fromByteArrayBigEndian
              (ffi.KEC
                ((approveTwoWordHashMem (transferFromSenderWord I) ⟨0⟩
                    (transferOuterHashMem (transferFromSenderWord I) (transferFromIdWord I))
                  ).readWithPadding 0 64))) =
          UInt256.ofNat
            (fromByteArrayBigEndian
              (ffi.KEC ((transferInnerHashMem (transferFromSenderWord I)).readWithPadding 0 64)))
        rw [approveTwoWordHashMem_read0_64 (transferFromSenderWord I) ⟨0⟩
          (transferOuterHashMem_size (transferFromSenderWord I) (transferFromIdWord I)),
          transferInnerHashMem_read0_64])
      (by decide) (by evm_ov) ]
  have rd1468 := evm_run rd1461 with [
    dup8, dup5,
    raw mstore 0 (approveWordAt0Mem (transferFromIdWord I)
        (approveTwoWordHashMem (transferFromSenderWord I) ⟨0⟩
          (transferOuterHashMem (transferFromSenderWord I) (transferFromIdWord I))))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    swap1, swap2,
    raw mstore 0
      (transferMapScratchMem
        (transferOuterHashMem (transferFromSenderWord I) (transferFromIdWord I))
        (transferFromSenderWord I) (transferFromIdWord I))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov) ]
  have rd1470 := evm_run rd1468 with [
    swap1,
    raw keccak256 0 (transferOuterSlot (transferFromSenderWord I) (transferFromIdWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        unfold transferOuterSlot
        change UInt256.ofNat
            (fromByteArrayBigEndian
              (ffi.KEC
                ((transferMapScratchMem
                    (transferOuterHashMem (transferFromSenderWord I) (transferFromIdWord I))
                    (transferFromSenderWord I) (transferFromIdWord I)).readWithPadding 0 64))) =
          UInt256.ofNat
            (fromByteArrayBigEndian
              (ffi.KEC
                ((transferOuterHashMem (transferFromSenderWord I) (transferFromIdWord I)
                  ).readWithPadding 0 64)))
        rw [transferMapScratchMem_read0_64 (transferFromSenderWord I) (transferFromIdWord I)
          (transferOuterHashMem_size (transferFromSenderWord I) (transferFromIdWord I)),
          transferOuterHashMem_read0_64])
      (by decide) (by evm_ov) ]
  have hdebit :
      UInt256.sub
          (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I)
          (transferFromAmountWord I) =
        transferFromTailSenderDebitWord (initState cA gh bl σcur σ₀ g A I) I := by
    apply u256_inj
    rw [usub_toNat henough]
    unfold transferFromTailSenderDebitWord
    rw [ulit_toNat' _ (lt_of_le_of_lt
      (Nat.sub_le
        (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I).toNat
        (transferFromAmountWord I).toNat)
      (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I).val.isLt)]
  have rd1475₀ := evm_run rd1470 with [
    swap1, dup4, swap1, sub, swap1 ]
  have rd1475 := rd1475₀
  rw [hdebit, hslot] at rd1475
  obtain ⟨_, _, rd1476⟩ := rd1475.sstore hperm (by decide) (by evm_ov)
  exact ⟨_, _, rd1476⟩

theorem erc6909TransferFromX_from1323_toCheckedAdd {cA gh bl σ σ₀ σcur A I}
    {g : Sat256} {sel : UInt256} {k C : ℕ}
    (hperm : I.perm = true)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (hreceiverNZ : transferFromReceiverWord I ≠ ⟨0⟩)
    (henough : (transferFromAmountWord I).toNat ≤
      (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I).toNat)
    (rd1323 : RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1323⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨760⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨649⟩, transferFromCallerWord I, ⟨0⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨193⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2017⟩
      [transferFromTailReceiverBalanceWord (initState cA gh bl σcur σ₀ g A I) I,
        transferFromAmountWord I, ⟨1539⟩, ⟨0⟩, transferFromReceiverBalanceSlot I,
        transferFromAmountWord I, transferFromCallerWord I, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨760⟩, transferFromAmountWord I, transferFromIdWord I,
        transferFromReceiverWord I, transferFromSenderWord I, ⟨649⟩,
        transferFromCallerWord I, ⟨0⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨193⟩, sel]
      (transferMapScratchMem
        (transferMapScratchMem
          (transferOuterHashMem (transferFromSenderWord I) (transferFromIdWord I))
          (transferFromSenderWord I) (transferFromIdWord I))
        (transferFromReceiverWord I) (transferFromIdWord I))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σcur (transferFromSenderBalanceSlot I)
        (transferFromTailSenderDebitWord (initState cA gh bl σcur σ₀ g A I) I)) k C := by
  obtain ⟨_, _, rd1476⟩ := erc6909TransferFromX_from1323_afterDebit
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (σcur := σcur)
    (A := A) (g := g) (sel := sel) hperm hcanonSender hsenderNZ henough rd1323
  let debitMem :=
    transferMapScratchMem (transferOuterHashMem (transferFromSenderWord I) (transferFromIdWord I))
      (transferFromSenderWord I) (transferFromIdWord I)
  have hdebitMemSize : debitMem.size = 96 := by
    dsimp [debitMem]
    exact transferMapScratchMem_size (transferFromSenderWord I) (transferFromIdWord I)
      (transferOuterHashMem_size (transferFromSenderWord I) (transferFromIdWord I))
  have hdebitMemRead64 :
      debitMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [debitMem]
    exact transferMapScratchMem_read64 (transferFromSenderWord I) (transferFromIdWord I)
      (transferOuterHashMem_size (transferFromSenderWord I) (transferFromIdWord I))
      (transferOuterHashMem_read64 (transferFromSenderWord I) (transferFromIdWord I))
  have hslot := transferFromReceiverBalanceKeccakSlot I hcanonReceiver
  have rd1492 := evm_run rd1476 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup5, and,
    iszero, push2 ⟨1545⟩,
    jumpiNT (by
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      rw [solcAddrMask_clean hcanonReceiver]
      exact isZero_eq_zero_of_ne hreceiverNZ) ]
  have rd1505 := evm_run rd1492 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup5, and, push0, swap1,
    dup2,
    raw mstore 0 (approveWordAt0Mem (transferFromReceiverWord I) debitMem)
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rw [solcAddrMask_clean hcanonReceiver]
        rfl)
      (by decide) (by evm_ov) ]
  have rd1510 := evm_run rd1505 with [
    push1 ⟨32⟩, dup2, dup2,
    raw mstore 0 (approveTwoWordHashMem (transferFromReceiverWord I) ⟨0⟩ debitMem)
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov) ]
  have rd1515 := evm_run rd1510 with [
    push1 ⟨64⟩, dup1, dup4,
    raw keccak256 0 (transferInnerSlot (transferFromReceiverWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        unfold transferInnerSlot
        change UInt256.ofNat
            (fromByteArrayBigEndian
              (ffi.KEC
                ((approveTwoWordHashMem (transferFromReceiverWord I) ⟨0⟩ debitMem
                  ).readWithPadding 0 64))) =
          UInt256.ofNat
            (fromByteArrayBigEndian
              (ffi.KEC
                ((transferInnerHashMem (transferFromReceiverWord I)).readWithPadding 0 64)))
        rw [approveTwoWordHashMem_read0_64 (transferFromReceiverWord I) ⟨0⟩
          hdebitMemSize, transferInnerHashMem_read0_64])
      (by decide) (by evm_ov) ]
  have rd1522 := evm_run rd1515 with [
    dup7, dup5,
    raw mstore 0 (approveWordAt0Mem (transferFromIdWord I)
        (approveTwoWordHashMem (transferFromReceiverWord I) ⟨0⟩ debitMem))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    swap1, swap2,
    raw mstore 0 (transferMapScratchMem debitMem (transferFromReceiverWord I)
        (transferFromIdWord I))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    dup2 ]
  have rd1524 := evm_run rd1522 with [
    raw keccak256 0 (transferOuterSlot (transferFromReceiverWord I) (transferFromIdWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        unfold transferOuterSlot
        change UInt256.ofNat
            (fromByteArrayBigEndian
              (ffi.KEC
                ((transferMapScratchMem debitMem (transferFromReceiverWord I)
                    (transferFromIdWord I)).readWithPadding 0 64))) =
          UInt256.ofNat
            (fromByteArrayBigEndian
              (ffi.KEC
                ((transferOuterHashMem (transferFromReceiverWord I) (transferFromIdWord I)
                  ).readWithPadding 0 64)))
        rw [transferMapScratchMem_read0_64 (transferFromReceiverWord I)
          (transferFromIdWord I) hdebitMemSize, transferOuterHashMem_read0_64])
      (by decide) (by evm_ov),
    dup1 ]
  obtain ⟨k1, C1, rd1526₀⟩ := rd1524.sload (by decide) (by evm_ov)
  have rd1526 : RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1526⟩
      [transferFromTailReceiverBalanceWord (initState cA gh bl σcur σ₀ g A I) I,
        transferFromReceiverBalanceSlot I, ⟨0⟩, transferFromCallerWord I,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨760⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨649⟩, transferFromCallerWord I, ⟨0⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨193⟩, sel]
      (transferMapScratchMem debitMem (transferFromReceiverWord I) (transferFromIdWord I))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σcur (transferFromSenderBalanceSlot I)
        (transferFromTailSenderDebitWord (initState cA gh bl σcur σ₀ g A I) I)) k1 C1 := by
    simpa [transferFromTailReceiverBalanceWord, transferFromTailAfterSenderBalanceState,
      transferFromSenderBalanceSlot, hslot, initState, Solm.EVM.storageLoad,
      State.lookupAccount, Account.lookupStorage, storageStore_accountMap, debitMem]
      using rd1526₀
  exact ⟨_, _, evm_run rd1526 with [
    dup5, swap3, swap1, push2 ⟨1539⟩, swap1, dup5, swap1, push2 ⟨2017⟩,
    jump (by jump_dest) ]⟩

theorem erc6909TransferFromX_from1545_successCaller_mem {cA gh bl σ σ₀ σcur A I}
    {g : Sat256} {sel : UInt256} {k C : ℕ} {mem : ByteArray}
    (hmemSize : mem.size = 96)
    (hmemRead64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hperm : I.perm = true)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (rd1545 : RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1545⟩
      [transferFromCallerWord I, transferFromAmountWord I, transferFromIdWord I,
        transferFromReceiverWord I, transferFromSenderWord I, ⟨760⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨649⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      mem
      (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C) :
    RDret erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σcur)
      (UInt256.toByteArray (⟨1⟩ : UInt256)) := by
  let creditMem := mem
  have hcreditMemSize : creditMem.size = 96 := by
    simpa [creditMem] using hmemSize
  have hcreditMemRead64 :
      creditMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [creditMem] using hmemRead64
  have rd1563 := evm_run rd1545 with [
    jumpdest, push1 ⟨64⟩, dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost
      (erc6909ScratchMem_mload64 hmemSize hmemRead64)
      (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup4, dup2, and, dup3,
    raw mstore 6 (transferEventFromBaseMem creditMem (transferFromCallerWord I))
      (UInt256.ofNat 5) (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        change (UInt256.toByteArray (UInt256.land solcAddrMask (transferFromCallerWord I))).write 0
          creditMem 128 32 = transferEventFromBaseMem creditMem (transferFromCallerWord I)
        rw [solcAddrMask_clean_left (transferFromCallerWord_canonical I)]
        rfl)
      (by decide) (by evm_ov) ]
  have rd1570 := evm_run rd1563 with [
    push1 ⟨32⟩, dup3, add, dup6, swap1,
    raw mstore 3 (transferEventBaseMem creditMem (transferFromCallerWord I)
        (transferFromAmountWord I))
      (UInt256.ofNat 6) (by decide) mem_cost (by rfl) (by decide) (by evm_ov) ]
  have rd1573 := evm_run rd1570 with [dup6, swap3, dup2]
  have rd1574 := RD.erc6909Dup9 rd1573 (by decide) (by evm_ov)
  have rd1577 := evm_run rd1574 with [and, swap3, swap2]
  have rd1578 := RD.erc6909Dup10 rd1577 (by decide) (by evm_ov)
  have rd1580₀ := evm_run rd1578 with [and, swap2]
  have rd1580 := rd1580₀
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide,
    solcAddrMask_clean hcanonSender,
    solcAddrMask_clean hcanonReceiver] at rd1580
  have rd1613 := rd1580.pushConst transferTransferTopic (width := 32) (op := .PUSH32)
    (by decide) (by decide) (by evm_ov)
  have rd1622 := evm_run rd1613 with [
    swap2, add, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide)
      mem_cost
      (transferEventBaseMem_mload64 (transferFromCallerWord I) (transferFromAmountWord I)
        hcreditMemSize hcreditMemRead64)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1 ]
  have rd1623 := RD.erc6909Log4 0 (UInt256.ofNat 6) rd1622 (by decide) hperm
    mem_cost (by decide) (by evm_ov)
  have rd760 := evm_run rd1623 with [
    pop, pop, pop, pop, pop, jump (by jump_dest) ]
  have rd649 := evm_run rd760 with [
    jumpdest, pop, pop, pop, pop, jump (by jump_dest) ]
  have rd651 := evm_run rd649 with [jumpdest, pop, push1 ⟨1⟩]
  have rd654 := RD.erc6909Swap6 rd651 (by decide) (by evm_ov)
  have rd655 := RD.erc6909Swap5 rd654 (by decide) (by evm_ov)
  have rd193 := evm_run rd655 with [
    pop, pop, pop, pop, pop, jump (by jump_dest) ]
  have rd165 := evm_run rd193 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide)
      mem_cost
      (transferEventBaseMem_mload64 (transferFromCallerWord I) (transferFromAmountWord I)
        hcreditMemSize hcreditMemRead64)
      (by decide) (by evm_ov),
    swap1, iszero, iszero, dup2,
    raw mstore 0 (transferReturnBaseMem creditMem (transferFromCallerWord I)
        (transferFromAmountWord I))
      (UInt256.ofNat 6) (by decide) mem_cost
      (by
        rw [show UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256)) = ⟨1⟩ from by decide]
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨32⟩, add, push2 ⟨165⟩, jump (by jump_dest) ]
  exact evm_run rd165 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide)
      mem_cost
      (transferReturnBaseMem_mload64 (transferFromCallerWord I) (transferFromAmountWord I)
        hcreditMemSize hcreditMemRead64)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray (⟨1⟩ : UInt256)) (by decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show (UInt256.sub ((⟨32⟩ : UInt256) + ⟨128⟩) ⟨128⟩).toNat = 32
            from by decide]
        exact transferReturnBaseMem_read128 (transferFromCallerWord I)
          (transferFromAmountWord I) hcreditMemSize)
      (by evm_ov) ]

theorem erc6909TransferFromX_from1545_successCaller {cA gh bl σ σ₀ σcur A I}
    {g : Sat256} {sel : UInt256} {k C : ℕ}
    (hperm : I.perm = true)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (rd1545 : RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1545⟩
      [transferFromCallerWord I, transferFromAmountWord I, transferFromIdWord I,
        transferFromReceiverWord I, transferFromSenderWord I, ⟨760⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨649⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      (transferMapScratchMem
        (transferMapScratchMem
          (transferOuterHashMem (transferFromSenderWord I) (transferFromIdWord I))
          (transferFromSenderWord I) (transferFromIdWord I))
        (transferFromReceiverWord I) (transferFromIdWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C) :
    RDret erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σcur)
      (UInt256.toByteArray (⟨1⟩ : UInt256)) := by
  let debitMem :=
    transferMapScratchMem (transferOuterHashMem (transferFromSenderWord I) (transferFromIdWord I))
      (transferFromSenderWord I) (transferFromIdWord I)
  let creditMem := transferMapScratchMem debitMem (transferFromReceiverWord I)
    (transferFromIdWord I)
  have hdebitMemSize : debitMem.size = 96 := by
    dsimp [debitMem]
    exact transferMapScratchMem_size (transferFromSenderWord I) (transferFromIdWord I)
      (transferOuterHashMem_size (transferFromSenderWord I) (transferFromIdWord I))
  have hdebitMemRead64 :
      debitMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [debitMem]
    exact transferMapScratchMem_read64 (transferFromSenderWord I) (transferFromIdWord I)
      (transferOuterHashMem_size (transferFromSenderWord I) (transferFromIdWord I))
      (transferOuterHashMem_read64 (transferFromSenderWord I) (transferFromIdWord I))
  have hcreditMemSize : creditMem.size = 96 := by
    dsimp [creditMem]
    exact transferMapScratchMem_size (transferFromReceiverWord I) (transferFromIdWord I)
      hdebitMemSize
  have hcreditMemRead64 :
      creditMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [creditMem]
    exact transferMapScratchMem_read64 (transferFromReceiverWord I) (transferFromIdWord I)
      hdebitMemSize hdebitMemRead64
  exact erc6909TransferFromX_from1545_successCaller_mem
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    (sel := sel) (mem := creditMem) hcreditMemSize hcreditMemRead64 hperm hcanonSender
    hcanonReceiver (by simpa [debitMem, creditMem] using rd1545)

theorem erc6909TransferFromX_from1323_afterCredit {cA gh bl σ σ₀ σcur A I}
    {g : Sat256} {sel : UInt256} {k C : ℕ}
    (hperm : I.perm = true)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (hreceiverNZ : transferFromReceiverWord I ≠ ⟨0⟩)
    (henough : (transferFromAmountWord I).toNat ≤
      (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I).toNat)
    (hfit : transferFromTailReceiverCreditNat (initState cA gh bl σcur σ₀ g A I) I <
      UInt256.size)
    (rd1323 : RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1323⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨760⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨649⟩, transferFromCallerWord I, ⟨0⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨193⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1545⟩
      [transferFromCallerWord I, transferFromAmountWord I, transferFromIdWord I,
        transferFromReceiverWord I, transferFromSenderWord I, ⟨760⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨649⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      (transferMapScratchMem
        (transferMapScratchMem
          (transferOuterHashMem (transferFromSenderWord I) (transferFromIdWord I))
          (transferFromSenderWord I) (transferFromIdWord I))
        (transferFromReceiverWord I) (transferFromIdWord I))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σcur (transferFromSenderBalanceSlot I)
          (transferFromTailSenderDebitWord (initState cA gh bl σcur σ₀ g A I) I))
        (transferFromReceiverBalanceSlot I)
        (transferFromTailReceiverCreditWord (initState cA gh bl σcur σ₀ g A I) I)) k C := by
  obtain ⟨_, _, rd2017⟩ := erc6909TransferFromX_from1323_toCheckedAdd
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (σcur := σcur)
    (A := A) (g := g) (sel := sel) hperm hcanonSender hcanonReceiver
    hsenderNZ hreceiverNZ henough rd1323
  obtain ⟨_, _, rd1539₀⟩ := erc6909RoutineCheckedAdd rd2017
    (by simpa [transferFromTailReceiverCreditNat] using hfit)
    (by jump_dest) (by evm_ov)
  have hnew :
      transferFromTailReceiverBalanceWord (initState cA gh bl σcur σ₀ g A I) I +
          transferFromAmountWord I =
        transferFromTailReceiverCreditWord (initState cA gh bl σcur σ₀ g A I) I := by
    apply u256_inj
    rw [uadd_toNat, Nat.mod_eq_of_lt (by
      simpa [transferFromTailReceiverCreditNat] using hfit)]
    unfold transferFromTailReceiverCreditWord
    rw [ulit_toNat' _ hfit]
    rfl
  have rd1539 := rd1539₀
  rw [hnew] at rd1539
  have rd1542 := evm_run rd1539 with [
    jumpdest, swap1, swap2 ]
  obtain ⟨_, _, rd1543⟩ := rd1542.sstore hperm (by decide) (by evm_ov)
  exact ⟨_, _, evm_run rd1543 with [ pop, pop ]⟩

theorem erc6909TransferFromX_from1323_overflow {cA gh bl σ σ₀ σcur A I}
    {g : Sat256} {sel : UInt256} {k C : ℕ}
    (hperm : I.perm = true)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (hreceiverNZ : transferFromReceiverWord I ≠ ⟨0⟩)
    (henough : (transferFromAmountWord I).toNat ≤
      (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I).toNat)
    (hover : UInt256.size ≤
      transferFromTailReceiverCreditNat (initState cA gh bl σcur σ₀ g A I) I)
    (rd1323 : RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1323⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨760⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨649⟩, transferFromCallerWord I, ⟨0⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨193⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2017⟩ := erc6909TransferFromX_from1323_toCheckedAdd
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (σcur := σcur)
    (A := A) (g := g) (sel := sel) hperm hcanonSender hcanonReceiver
    hsenderNZ hreceiverNZ henough rd1323
  exact erc6909RoutineCheckedAdd_overflow rd2017
    (by simpa [transferFromTailReceiverCreditNat] using hover) (by evm_ov)

theorem erc6909TransferFromX_from1323_successCaller {cA gh bl σ σ₀ σcur A I}
    {g : Sat256} {sel : UInt256} {k C : ℕ}
    (hperm : I.perm = true)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (hreceiverNZ : transferFromReceiverWord I ≠ ⟨0⟩)
    (henough : (transferFromAmountWord I).toNat ≤
      (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I).toNat)
    (hfit : transferFromTailReceiverCreditNat (initState cA gh bl σcur σ₀ g A I) I <
      UInt256.size)
    (rd1323 : RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1323⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨760⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨649⟩, transferFromCallerWord I, ⟨0⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨193⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C) :
    RDret erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σcur (transferFromSenderBalanceSlot I)
          (transferFromTailSenderDebitWord (initState cA gh bl σcur σ₀ g A I) I))
        (transferFromReceiverBalanceSlot I)
        (transferFromTailReceiverCreditWord (initState cA gh bl σcur σ₀ g A I) I))
      (UInt256.toByteArray (⟨1⟩ : UInt256)) := by
  obtain ⟨_, _, rd1545⟩ := erc6909TransferFromX_from1323_afterCredit
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (σcur := σcur)
    (A := A) (g := g) (sel := sel) hperm hcanonSender hcanonReceiver
    hsenderNZ hreceiverNZ henough hfit rd1323
  exact erc6909TransferFromX_from1545_successCaller hperm hcanonSender hcanonReceiver rd1545

theorem erc6909TransferFromX_from1323_afterDebit_base
    {cA gh bl σ σ₀ σcur A I} {g : Sat256} {sel : UInt256} {k C : ℕ}
    {base : ByteArray}
    (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hperm : I.perm = true)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (henough : (transferFromAmountWord I).toNat ≤
      (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I).toNat)
    (rd1323 : RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1323⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨760⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨649⟩, transferFromCallerWord I, ⟨0⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨193⟩, sel]
      base (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1476⟩
      [transferFromCallerWord I, transferFromAmountWord I, transferFromIdWord I,
        transferFromReceiverWord I, transferFromSenderWord I, ⟨760⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨649⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      (transferMapScratchMem
        (transferMapScratchMem base (transferFromSenderWord I) (transferFromIdWord I))
        (transferFromSenderWord I) (transferFromIdWord I))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σcur (transferFromSenderBalanceSlot I)
        (transferFromTailSenderDebitWord (initState cA gh bl σcur σ₀ g A I) I)) k C := by
  obtain ⟨_, _, rd1437⟩ := erc6909TransferFromX_from1323_afterRequire_base
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (σcur := σcur)
    (A := A) (g := g) (sel := sel) hbase hcanonSender hsenderNZ henough rd1323
  let senderMem := transferMapScratchMem base (transferFromSenderWord I) (transferFromIdWord I)
  have hsenderMemSize : senderMem.size = 96 := by
    dsimp [senderMem]
    exact transferMapScratchMem_size (transferFromSenderWord I) (transferFromIdWord I) hbase
  have hslot := transferFromSenderBalanceKeccakSlot I hcanonSender
  have rd1451 := evm_run rd1437 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup7, and,
    push0, swap1, dup2,
    raw mstore 0 (approveWordAt0Mem (transferFromSenderWord I) senderMem)
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rw [solcAddrMask_clean hcanonSender]
        rfl)
      (by decide) (by evm_ov) ]
  have rd1456 := evm_run rd1451 with [
    push1 ⟨32⟩, dup2, dup2,
    raw mstore 0 (approveTwoWordHashMem (transferFromSenderWord I) ⟨0⟩ senderMem)
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov) ]
  have rd1461 := evm_run rd1456 with [
    push1 ⟨64⟩, dup1, dup4,
    raw keccak256 0 (transferInnerSlot (transferFromSenderWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        unfold transferInnerSlot
        change UInt256.ofNat
            (fromByteArrayBigEndian
              (ffi.KEC
                ((approveTwoWordHashMem (transferFromSenderWord I) ⟨0⟩ senderMem
                  ).readWithPadding 0 64))) =
          UInt256.ofNat
            (fromByteArrayBigEndian
              (ffi.KEC ((transferInnerHashMem (transferFromSenderWord I)).readWithPadding 0 64)))
        rw [approveTwoWordHashMem_read0_64 (transferFromSenderWord I) ⟨0⟩
          hsenderMemSize, transferInnerHashMem_read0_64])
      (by decide) (by evm_ov) ]
  have rd1468 := evm_run rd1461 with [
    dup8, dup5,
    raw mstore 0 (approveWordAt0Mem (transferFromIdWord I)
        (approveTwoWordHashMem (transferFromSenderWord I) ⟨0⟩ senderMem))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    swap1, swap2,
    raw mstore 0
      (transferMapScratchMem senderMem (transferFromSenderWord I) (transferFromIdWord I))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov) ]
  have rd1470 := evm_run rd1468 with [
    swap1,
    raw keccak256 0 (transferOuterSlot (transferFromSenderWord I) (transferFromIdWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        unfold transferOuterSlot
        change UInt256.ofNat
            (fromByteArrayBigEndian
              (ffi.KEC
                ((transferMapScratchMem senderMem (transferFromSenderWord I)
                    (transferFromIdWord I)).readWithPadding 0 64))) =
          UInt256.ofNat
            (fromByteArrayBigEndian
              (ffi.KEC
                ((transferOuterHashMem (transferFromSenderWord I) (transferFromIdWord I)
                  ).readWithPadding 0 64)))
        rw [transferMapScratchMem_read0_64 (transferFromSenderWord I) (transferFromIdWord I)
          hsenderMemSize, transferOuterHashMem_read0_64])
      (by decide) (by evm_ov) ]
  have hdebit :
      UInt256.sub
          (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I)
          (transferFromAmountWord I) =
        transferFromTailSenderDebitWord (initState cA gh bl σcur σ₀ g A I) I := by
    apply u256_inj
    rw [usub_toNat henough]
    unfold transferFromTailSenderDebitWord
    rw [ulit_toNat' _ (lt_of_le_of_lt
      (Nat.sub_le
        (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I).toNat
        (transferFromAmountWord I).toNat)
      (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I).val.isLt)]
  have rd1475₀ := evm_run rd1470 with [
    swap1, dup4, swap1, sub, swap1 ]
  have rd1475 := rd1475₀
  rw [hdebit, hslot] at rd1475
  obtain ⟨_, _, rd1476⟩ := rd1475.sstore hperm (by decide) (by evm_ov)
  exact ⟨_, _, by simpa [senderMem] using rd1476⟩

theorem erc6909TransferFromX_from1323_toCheckedAdd_base
    {cA gh bl σ σ₀ σcur A I} {g : Sat256} {sel : UInt256} {k C : ℕ}
    {base : ByteArray}
    (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hperm : I.perm = true)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (hreceiverNZ : transferFromReceiverWord I ≠ ⟨0⟩)
    (henough : (transferFromAmountWord I).toNat ≤
      (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I).toNat)
    (rd1323 : RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1323⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨760⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨649⟩, transferFromCallerWord I, ⟨0⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨193⟩, sel]
      base (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2017⟩
      [transferFromTailReceiverBalanceWord (initState cA gh bl σcur σ₀ g A I) I,
        transferFromAmountWord I, ⟨1539⟩, ⟨0⟩, transferFromReceiverBalanceSlot I,
        transferFromAmountWord I, transferFromCallerWord I, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨760⟩, transferFromAmountWord I, transferFromIdWord I,
        transferFromReceiverWord I, transferFromSenderWord I, ⟨649⟩,
        transferFromCallerWord I, ⟨0⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨193⟩, sel]
      (transferMapScratchMem
        (transferMapScratchMem
          (transferMapScratchMem base (transferFromSenderWord I) (transferFromIdWord I))
          (transferFromSenderWord I) (transferFromIdWord I))
        (transferFromReceiverWord I) (transferFromIdWord I))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σcur (transferFromSenderBalanceSlot I)
        (transferFromTailSenderDebitWord (initState cA gh bl σcur σ₀ g A I) I)) k C := by
  obtain ⟨_, _, rd1476⟩ := erc6909TransferFromX_from1323_afterDebit_base
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (σcur := σcur)
    (A := A) (g := g) (sel := sel) hbase hread64 hperm hcanonSender hsenderNZ
    henough rd1323
  let senderMem := transferMapScratchMem base (transferFromSenderWord I) (transferFromIdWord I)
  let debitMem := transferMapScratchMem senderMem (transferFromSenderWord I)
    (transferFromIdWord I)
  have hsenderMemSize : senderMem.size = 96 := by
    dsimp [senderMem]
    exact transferMapScratchMem_size (transferFromSenderWord I) (transferFromIdWord I) hbase
  have hsenderMemRead64 :
      senderMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [senderMem]
    exact transferMapScratchMem_read64 (transferFromSenderWord I) (transferFromIdWord I)
      hbase hread64
  have hdebitMemSize : debitMem.size = 96 := by
    dsimp [debitMem]
    exact transferMapScratchMem_size (transferFromSenderWord I) (transferFromIdWord I)
      hsenderMemSize
  have hdebitMemRead64 :
      debitMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [debitMem]
    exact transferMapScratchMem_read64 (transferFromSenderWord I) (transferFromIdWord I)
      hsenderMemSize hsenderMemRead64
  have hslot := transferFromReceiverBalanceKeccakSlot I hcanonReceiver
  have rd1492 := evm_run rd1476 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup5, and,
    iszero, push2 ⟨1545⟩,
    jumpiNT (by
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      rw [solcAddrMask_clean hcanonReceiver]
      exact isZero_eq_zero_of_ne hreceiverNZ) ]
  have rd1505 := evm_run rd1492 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup5, and, push0, swap1,
    dup2,
    raw mstore 0 (approveWordAt0Mem (transferFromReceiverWord I) debitMem)
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rw [solcAddrMask_clean hcanonReceiver]
        rfl)
      (by decide) (by evm_ov) ]
  have rd1510 := evm_run rd1505 with [
    push1 ⟨32⟩, dup2, dup2,
    raw mstore 0 (approveTwoWordHashMem (transferFromReceiverWord I) ⟨0⟩ debitMem)
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov) ]
  have rd1515 := evm_run rd1510 with [
    push1 ⟨64⟩, dup1, dup4,
    raw keccak256 0 (transferInnerSlot (transferFromReceiverWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        unfold transferInnerSlot
        change UInt256.ofNat
            (fromByteArrayBigEndian
              (ffi.KEC
                ((approveTwoWordHashMem (transferFromReceiverWord I) ⟨0⟩ debitMem
                  ).readWithPadding 0 64))) =
          UInt256.ofNat
            (fromByteArrayBigEndian
              (ffi.KEC
                ((transferInnerHashMem (transferFromReceiverWord I)).readWithPadding 0 64)))
        rw [approveTwoWordHashMem_read0_64 (transferFromReceiverWord I) ⟨0⟩
          hdebitMemSize, transferInnerHashMem_read0_64])
      (by decide) (by evm_ov) ]
  have rd1522 := evm_run rd1515 with [
    dup7, dup5,
    raw mstore 0 (approveWordAt0Mem (transferFromIdWord I)
        (approveTwoWordHashMem (transferFromReceiverWord I) ⟨0⟩ debitMem))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    swap1, swap2,
    raw mstore 0 (transferMapScratchMem debitMem (transferFromReceiverWord I)
        (transferFromIdWord I))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    dup2 ]
  have rd1524 := evm_run rd1522 with [
    raw keccak256 0 (transferOuterSlot (transferFromReceiverWord I) (transferFromIdWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        unfold transferOuterSlot
        change UInt256.ofNat
            (fromByteArrayBigEndian
              (ffi.KEC
                ((transferMapScratchMem debitMem (transferFromReceiverWord I)
                    (transferFromIdWord I)).readWithPadding 0 64))) =
          UInt256.ofNat
            (fromByteArrayBigEndian
              (ffi.KEC
                ((transferOuterHashMem (transferFromReceiverWord I) (transferFromIdWord I)
                  ).readWithPadding 0 64)))
        rw [transferMapScratchMem_read0_64 (transferFromReceiverWord I)
          (transferFromIdWord I) hdebitMemSize, transferOuterHashMem_read0_64])
      (by decide) (by evm_ov),
    dup1 ]
  obtain ⟨k1, C1, rd1526₀⟩ := rd1524.sload (by decide) (by evm_ov)
  have rd1526 : RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1526⟩
      [transferFromTailReceiverBalanceWord (initState cA gh bl σcur σ₀ g A I) I,
        transferFromReceiverBalanceSlot I, ⟨0⟩, transferFromCallerWord I,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨760⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨649⟩, transferFromCallerWord I, ⟨0⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨193⟩, sel]
      (transferMapScratchMem debitMem (transferFromReceiverWord I) (transferFromIdWord I))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σcur (transferFromSenderBalanceSlot I)
        (transferFromTailSenderDebitWord (initState cA gh bl σcur σ₀ g A I) I)) k1 C1 := by
    simpa [transferFromTailReceiverBalanceWord, transferFromTailAfterSenderBalanceState,
      transferFromSenderBalanceSlot, hslot, initState, Solm.EVM.storageLoad,
      State.lookupAccount, Account.lookupStorage, storageStore_accountMap, debitMem]
      using rd1526₀
  exact ⟨_, _, by
    simpa [senderMem, debitMem] using
      evm_run rd1526 with [
        dup5, swap3, swap1, push2 ⟨1539⟩, swap1, dup5, swap1, push2 ⟨2017⟩,
        jump (by jump_dest) ]⟩

theorem erc6909TransferFromX_from1545_successCaller_base
    {cA gh bl σ σ₀ σcur A I} {g : Sat256} {sel : UInt256} {k C : ℕ}
    {base : ByteArray}
    (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hperm : I.perm = true)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (rd1545 : RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1545⟩
      [transferFromCallerWord I, transferFromAmountWord I, transferFromIdWord I,
        transferFromReceiverWord I, transferFromSenderWord I, ⟨760⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨649⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      (transferMapScratchMem
        (transferMapScratchMem
          (transferMapScratchMem base (transferFromSenderWord I) (transferFromIdWord I))
          (transferFromSenderWord I) (transferFromIdWord I))
        (transferFromReceiverWord I) (transferFromIdWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C) :
    RDret erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σcur)
      (UInt256.toByteArray (⟨1⟩ : UInt256)) := by
  let senderMem := transferMapScratchMem base (transferFromSenderWord I) (transferFromIdWord I)
  let debitMem := transferMapScratchMem senderMem (transferFromSenderWord I)
    (transferFromIdWord I)
  let creditMem := transferMapScratchMem debitMem (transferFromReceiverWord I)
    (transferFromIdWord I)
  have hsenderMemSize : senderMem.size = 96 := by
    dsimp [senderMem]
    exact transferMapScratchMem_size (transferFromSenderWord I) (transferFromIdWord I) hbase
  have hsenderMemRead64 :
      senderMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [senderMem]
    exact transferMapScratchMem_read64 (transferFromSenderWord I) (transferFromIdWord I)
      hbase hread64
  have hdebitMemSize : debitMem.size = 96 := by
    dsimp [debitMem]
    exact transferMapScratchMem_size (transferFromSenderWord I) (transferFromIdWord I)
      hsenderMemSize
  have hdebitMemRead64 :
      debitMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [debitMem]
    exact transferMapScratchMem_read64 (transferFromSenderWord I) (transferFromIdWord I)
      hsenderMemSize hsenderMemRead64
  have hcreditMemSize : creditMem.size = 96 := by
    dsimp [creditMem]
    exact transferMapScratchMem_size (transferFromReceiverWord I) (transferFromIdWord I)
      hdebitMemSize
  have hcreditMemRead64 :
      creditMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [creditMem]
    exact transferMapScratchMem_read64 (transferFromReceiverWord I) (transferFromIdWord I)
      hdebitMemSize hdebitMemRead64
  exact erc6909TransferFromX_from1545_successCaller_mem
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    (sel := sel) (mem := creditMem) hcreditMemSize hcreditMemRead64 hperm hcanonSender
    hcanonReceiver (by simpa [senderMem, debitMem, creditMem] using rd1545)
/-
  have rd1563 := evm_run rd1545 with [
    jumpdest, push1 ⟨64⟩, dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost
      (transferMapScratchMem_mload64 (transferFromReceiverWord I) (transferFromIdWord I)
        hdebitMemSize hdebitMemRead64)
      (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup4, dup2, and, dup3,
    raw mstore 6 (transferEventFromBaseMem creditMem (transferFromCallerWord I))
      (UInt256.ofNat 5) (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        change (UInt256.toByteArray (UInt256.land solcAddrMask (transferFromCallerWord I))).write 0
          creditMem 128 32 = transferEventFromBaseMem creditMem (transferFromCallerWord I)
        rw [solcAddrMask_clean_left (transferFromCallerWord_canonical I)]
        rfl)
      (by decide) (by evm_ov) ]
  have rd1570 := evm_run rd1563 with [
    push1 ⟨32⟩, dup3, add, dup6, swap1,
    raw mstore 3 (transferEventBaseMem creditMem (transferFromCallerWord I)
        (transferFromAmountWord I))
      (UInt256.ofNat 6) (by decide) mem_cost (by rfl) (by decide) (by evm_ov) ]
  have rd1573 := evm_run rd1570 with [dup6, swap3, dup2]
  have rd1574 := RD.erc6909Dup9 rd1573 (by decide) (by evm_ov)
  have rd1577 := evm_run rd1574 with [and, swap3, swap2]
  have rd1578 := RD.erc6909Dup10 rd1577 (by decide) (by evm_ov)
  have rd1580₀ := evm_run rd1578 with [and, swap2]
  have rd1580 := rd1580₀
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide,
    solcAddrMask_clean hcanonSender,
    solcAddrMask_clean hcanonReceiver] at rd1580
  have rd1613 := rd1580.pushConst transferTransferTopic (width := 32) (op := .PUSH32)
    (by decide) (by decide) (by evm_ov)
  have rd1622 := evm_run rd1613 with [
    swap2, add, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide)
      mem_cost
      (transferEventBaseMem_mload64 (transferFromCallerWord I) (transferFromAmountWord I)
        hcreditMemSize hcreditMemRead64)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1 ]
  have rd1623 := RD.erc6909Log4 0 (UInt256.ofNat 6) rd1622 (by decide) hperm
    mem_cost (by decide) (by evm_ov)
  have rd760 := evm_run rd1623 with [
    pop, pop, pop, pop, pop, jump (by jump_dest) ]
  have rd649 := evm_run rd760 with [
    jumpdest, pop, pop, pop, pop, jump (by jump_dest) ]
  have rd651 := evm_run rd649 with [jumpdest, pop, push1 ⟨1⟩]
  have rd654 := RD.erc6909Swap6 rd651 (by decide) (by evm_ov)
  have rd655 := RD.erc6909Swap5 rd654 (by decide) (by evm_ov)
  have rd193 := evm_run rd655 with [
    pop, pop, pop, pop, pop, jump (by jump_dest) ]
  have rd165 := evm_run rd193 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide)
      mem_cost
      (transferEventBaseMem_mload64 (transferFromCallerWord I) (transferFromAmountWord I)
        hcreditMemSize hcreditMemRead64)
      (by decide) (by evm_ov),
    swap1, iszero, iszero, dup2,
    raw mstore 0 (transferReturnBaseMem creditMem (transferFromCallerWord I)
        (transferFromAmountWord I))
      (UInt256.ofNat 6) (by decide) mem_cost
      (by
        rw [show UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256)) = ⟨1⟩ from by decide]
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨32⟩, add, push2 ⟨165⟩, jump (by jump_dest) ]
  exact evm_run rd165 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide)
      mem_cost
      (transferReturnBaseMem_mload64 (transferFromCallerWord I) (transferFromAmountWord I)
        hcreditMemSize hcreditMemRead64)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray (⟨1⟩ : UInt256)) (by decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show (UInt256.sub ((⟨32⟩ : UInt256) + ⟨128⟩) ⟨128⟩).toNat = 32
            from by decide]
        exact transferReturnBaseMem_read128 (transferFromCallerWord I)
          (transferFromAmountWord I) hcreditMemSize)
      (by evm_ov) ]
-/

theorem erc6909TransferFromX_from1323_afterCredit_base
    {cA gh bl σ σ₀ σcur A I} {g : Sat256} {sel : UInt256} {k C : ℕ}
    {base : ByteArray}
    (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hperm : I.perm = true)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (hreceiverNZ : transferFromReceiverWord I ≠ ⟨0⟩)
    (henough : (transferFromAmountWord I).toNat ≤
      (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I).toNat)
    (hfit : transferFromTailReceiverCreditNat (initState cA gh bl σcur σ₀ g A I) I <
      UInt256.size)
    (rd1323 : RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1323⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨760⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨649⟩, transferFromCallerWord I, ⟨0⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨193⟩, sel]
      base (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1545⟩
      [transferFromCallerWord I, transferFromAmountWord I, transferFromIdWord I,
        transferFromReceiverWord I, transferFromSenderWord I, ⟨760⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨649⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      (transferMapScratchMem
        (transferMapScratchMem
          (transferMapScratchMem base (transferFromSenderWord I) (transferFromIdWord I))
          (transferFromSenderWord I) (transferFromIdWord I))
        (transferFromReceiverWord I) (transferFromIdWord I))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σcur (transferFromSenderBalanceSlot I)
          (transferFromTailSenderDebitWord (initState cA gh bl σcur σ₀ g A I) I))
        (transferFromReceiverBalanceSlot I)
        (transferFromTailReceiverCreditWord (initState cA gh bl σcur σ₀ g A I) I)) k C := by
  obtain ⟨_, _, rd2017⟩ := erc6909TransferFromX_from1323_toCheckedAdd_base
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (σcur := σcur)
    (A := A) (g := g) (sel := sel) hbase hread64 hperm hcanonSender hcanonReceiver
    hsenderNZ hreceiverNZ henough rd1323
  obtain ⟨_, _, rd1539₀⟩ := erc6909RoutineCheckedAdd rd2017
    (by simpa [transferFromTailReceiverCreditNat] using hfit)
    (by jump_dest) (by evm_ov)
  have hnew :
      transferFromTailReceiverBalanceWord (initState cA gh bl σcur σ₀ g A I) I +
          transferFromAmountWord I =
        transferFromTailReceiverCreditWord (initState cA gh bl σcur σ₀ g A I) I := by
    apply u256_inj
    rw [uadd_toNat, Nat.mod_eq_of_lt (by
      simpa [transferFromTailReceiverCreditNat] using hfit)]
    unfold transferFromTailReceiverCreditWord
    rw [ulit_toNat' _ hfit]
    rfl
  have rd1539 := rd1539₀
  rw [hnew] at rd1539
  have rd1542 := evm_run rd1539 with [
    jumpdest, swap1, swap2 ]
  obtain ⟨_, _, rd1543⟩ := rd1542.sstore hperm (by decide) (by evm_ov)
  exact ⟨_, _, evm_run rd1543 with [ pop, pop ]⟩

theorem erc6909TransferFromX_from1323_overflow_base
    {cA gh bl σ σ₀ σcur A I} {g : Sat256} {sel : UInt256} {k C : ℕ}
    {base : ByteArray}
    (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hperm : I.perm = true)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (hreceiverNZ : transferFromReceiverWord I ≠ ⟨0⟩)
    (henough : (transferFromAmountWord I).toNat ≤
      (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I).toNat)
    (hover : UInt256.size ≤
      transferFromTailReceiverCreditNat (initState cA gh bl σcur σ₀ g A I) I)
    (rd1323 : RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1323⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨760⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨649⟩, transferFromCallerWord I, ⟨0⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨193⟩, sel]
      base (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2017⟩ := erc6909TransferFromX_from1323_toCheckedAdd_base
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (σcur := σcur)
    (A := A) (g := g) (sel := sel) hbase hread64 hperm hcanonSender hcanonReceiver
    hsenderNZ hreceiverNZ henough rd1323
  exact erc6909RoutineCheckedAdd_overflow rd2017
    (by simpa [transferFromTailReceiverCreditNat] using hover) (by evm_ov)

theorem erc6909TransferFromX_from1323_successCaller_base
    {cA gh bl σ σ₀ σcur A I} {g : Sat256} {sel : UInt256} {k C : ℕ}
    {base : ByteArray}
    (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hperm : I.perm = true)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (hreceiverNZ : transferFromReceiverWord I ≠ ⟨0⟩)
    (henough : (transferFromAmountWord I).toNat ≤
      (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I).toNat)
    (hfit : transferFromTailReceiverCreditNat (initState cA gh bl σcur σ₀ g A I) I <
      UInt256.size)
    (rd1323 : RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1323⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨760⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨649⟩, transferFromCallerWord I, ⟨0⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨193⟩, sel]
      base (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C) :
    RDret erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σcur (transferFromSenderBalanceSlot I)
          (transferFromTailSenderDebitWord (initState cA gh bl σcur σ₀ g A I) I))
        (transferFromReceiverBalanceSlot I)
        (transferFromTailReceiverCreditWord (initState cA gh bl σcur σ₀ g A I) I))
      (UInt256.toByteArray (⟨1⟩ : UInt256)) := by
  obtain ⟨_, _, rd1545⟩ := erc6909TransferFromX_from1323_afterCredit_base
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (σcur := σcur)
    (A := A) (g := g) (sel := sel) hbase hread64 hperm hcanonSender hcanonReceiver
    hsenderNZ hreceiverNZ henough hfit rd1323
  exact erc6909TransferFromX_from1545_successCaller_base
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    (sel := sel) hbase hread64 hperm hcanonSender hcanonReceiver rd1545


end OpenZeppelinBench.ERC6909
