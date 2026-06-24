import Examples.OpenZeppelinBench.ERC6909.TransferFrom.Traces.Memory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unnecessarySimpa false

namespace OpenZeppelinBench.ERC6909

theorem erc6909TransferFromX_toDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1954⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨402⟩, ⟨193⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, push2 ⟨193⟩, push2 ⟨402⟩, calldatasize, push1 ⟨4⟩,
    push2 ⟨1954⟩, jump (by jump_dest) ]⟩

theorem erc6909TransferFromX_dec1629_sender {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1629⟩
      [⟨4⟩, ⟨1982⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨402⟩, ⟨193⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨128⟩ = ⟨0⟩ := by
    simpa using solcCalldataStaticLenCheckOk (words := 4) hsz132 hszhi hsize
  obtain ⟨_, _, rd⟩ := erc6909TransferFromX_toDecoder (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, push0, push0, push0, push0, push1 ⟨128⟩, dup6, dup8, sub, slt, iszero,
    push2 ⟨1973⟩, jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, push2 ⟨1982⟩, dup6, push2 ⟨1629⟩, jump (by jump_dest) ]⟩

theorem erc6909TransferFromX_dec1982 {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1982⟩
      [transferFromSenderWord I, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨402⟩, ⟨193⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := erc6909TransferFromX_dec1629_sender (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz132 hsize hszhi hreach
  simpa [transferFromSenderWord, calldataWord] using
    erc6909DecodeAddrOk rd hcanonSender (by jump_dest) (by evm_ov)

theorem erc6909TransferFromX_dec1629_receiver {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1629⟩
      [⟨4⟩ + ⟨32⟩, ⟨1996⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, transferFromSenderWord I,
        ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨402⟩, ⟨193⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := erc6909TransferFromX_dec1982 (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz132 hsize hszhi hcanonSender hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, swap4, pop, push2 ⟨1996⟩, push1 ⟨32⟩, dup7, add,
    push2 ⟨1629⟩, jump (by jump_dest) ]⟩

theorem erc6909TransferFromX_dec1996 {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1996⟩
      [transferFromReceiverWord I, ⟨0⟩, ⟨0⟩, ⟨0⟩, transferFromSenderWord I,
        ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨402⟩, ⟨193⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := erc6909TransferFromX_dec1629_receiver (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz132 hsize hszhi hcanonSender hreach
  simpa [transferFromReceiverWord, calldataWord] using
    erc6909DecodeAddrOk rd hcanonReceiver (by jump_dest) (by evm_ov)

theorem erc6909TransferFromX_decoded {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨556⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := erc6909TransferFromX_dec1996 (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz132 hsize hszhi hcanonSender hcanonReceiver hreach
  have rd1997 := evm_run rd with [jumpdest, swap4]
  have rd1998 := RD.swap7 rd1997 (by decide) (by evm_ov)
  have rd1999 := evm_run rd1998 with [swap4]
  have rd2000 := RD.swap6 rd1999 (by decide) (by evm_ov)
  have rd402 := evm_run rd2000 with [
    pop, pop, pop, pop, push1 ⟨64⟩, dup3, add, calldataload, swap2,
    push1 ⟨96⟩, add, calldataload, swap1, jump (by jump_dest) ]
  have rd556 := evm_run rd402 with [jumpdest, push2 ⟨556⟩, jump (by jump_dest)]
  exact ⟨_, _, by
    simpa [transferFromIdWord, transferFromAmountWord, calldataWord] using rd556⟩

theorem erc6909TransferFromX_skipCaller_toUpdate {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderCaller : transferFromSenderWord I = transferFromCallerWord I)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨661⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨649⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd556⟩ := erc6909TransferFromX_decoded (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz132 hsize hszhi hcanonSender hcanonReceiver hreach
  have hsenderClean :
      UInt256.land (transferFromSenderWord I) solcAddrMask = transferFromSenderWord I :=
    solcAddrMask_clean hcanonSender
  exact ⟨_, _, by
    simpa [transferFromCallerWord] using evm_run rd556 with [
      jumpdest, push0, caller, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub,
      dup7, and, dup2, eq, dup1, iszero, swap1, push2 ⟨620⟩,
      jumpiT (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rw [hsenderClean, hsenderCaller]
        rw [transferFromCallerWord, approveOwnerWord, uInt256_eq_self]
        exact one_ne_zero_uint)
        (by jump_dest),
      jumpdest, iszero, push2 ⟨637⟩,
      jumpiT (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rw [hsenderClean, hsenderCaller]
        rw [transferFromCallerWord, approveOwnerWord, uInt256_eq_self]
        decide)
        (by jump_dest),
      jumpdest, push2 ⟨649⟩, dup7, dup7, dup7, dup7, push2 ⟨661⟩,
      jump (by jump_dest) ]⟩

theorem erc6909TransferFromX_skipCaller_toUpdateHelper {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderCaller : transferFromSenderWord I = transferFromCallerWord I)
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
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd661⟩ := erc6909TransferFromX_skipCaller_toUpdate (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz132 hsize hszhi hcanonSender hcanonReceiver hsenderCaller hreach
  exact ⟨_, _, evm_run rd661 with [
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
    jumpiT (by
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      rw [solcAddrMask_clean hcanonReceiver]
      exact hreceiverNZ)
      (by jump_dest),
    jumpdest, push2 ⟨760⟩, dup5, dup5, dup5, dup5, push2 ⟨1323⟩,
    jump (by jump_dest) ]⟩

theorem erc6909TransferFromX_skipCaller_revert_sender_zero {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderCaller : transferFromSenderWord I = transferFromCallerWord I)
    (hsenderZero : transferFromSenderWord I = ⟨0⟩)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd661⟩ := erc6909TransferFromX_skipCaller_toUpdate (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz132 hsize hszhi hcanonSender hcanonReceiver hsenderCaller hreach
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
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    push4 ⟨0x01486a41⟩, push1 ⟨231⟩, shl, dup2,
    raw mstore 6 (solcReturnMem transferFromInvalidSenderSelectorWord)
      (UInt256.ofNat 5) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push0, push1 ⟨4⟩, dup3, add,
    raw mstore 3 (approveErrorMem transferFromInvalidSenderSelectorWord ⟨0⟩)
      (UInt256.ofNat 6) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨36⟩, add,
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide)
      mem_cost (approveErrorMem_mload64 transferFromInvalidSenderSelectorWord ⟨0⟩)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw rev 0 (by decide) mem_cost (by evm_ov) ]

theorem erc6909TransferFromX_skipCaller_revert_receiver_zero {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderCaller : transferFromSenderWord I = transferFromCallerWord I)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (hreceiverZero : transferFromReceiverWord I = ⟨0⟩)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd661⟩ := erc6909TransferFromX_skipCaller_toUpdate (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz132 hsize hszhi hcanonSender hcanonReceiver hsenderCaller hreach
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
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    push4 ⟨0x0b8bbd61⟩, push1 ⟨228⟩, shl, dup2,
    raw mstore 6 (solcReturnMem transferFromInvalidReceiverSelectorWord)
      (UInt256.ofNat 5) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push0, push1 ⟨4⟩, dup3, add,
    raw mstore 3 (approveErrorMem transferFromInvalidReceiverSelectorWord ⟨0⟩)
      (UInt256.ofNat 6) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨36⟩, add, push2 ⟨698⟩, jump (by jump_dest),
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide)
      mem_cost (approveErrorMem_mload64 transferFromInvalidReceiverSelectorWord ⟨0⟩)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw rev 0 (by decide) mem_cost (by evm_ov) ]

theorem erc6909TransferFromX_skipCaller_afterLoad {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderCaller : transferFromSenderWord I = transferFromCallerWord I)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (hreceiverNZ : transferFromReceiverWord I ≠ ⟨0⟩)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1373⟩
      [transferFromSenderBalanceWord (initState cA gh bl σ σ₀ g A I) I,
        transferFromSenderWord I, transferFromAmountWord I, transferFromIdWord I,
        transferFromReceiverWord I, transferFromSenderWord I, ⟨760⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨649⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      (transferOuterHashMem (transferFromSenderWord I) (transferFromIdWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1323⟩ := erc6909TransferFromX_skipCaller_toUpdateHelper
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := g) (sel := sel) hsz132 hsize hszhi hcanonSender hcanonReceiver
    hsenderCaller hsenderNZ hreceiverNZ hreach
  have hslot := transferFromSenderBalanceKeccakSlot I hcanonSender
  have hcallerWord : UInt256.ofNat ↑I.source = transferFromSenderWord I := by
    simpa [transferFromCallerWord, approveOwnerWord] using hsenderCaller.symm
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
      hslot, hcallerWord, initState,
      Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
      using rd1373₀⟩

theorem erc6909TransferFromX_skipCaller_afterRequire {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderCaller : transferFromSenderWord I = transferFromCallerWord I)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (hreceiverNZ : transferFromReceiverWord I ≠ ⟨0⟩)
    (henough : (transferFromAmountWord I).toNat ≤
      (transferFromSenderBalanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1437⟩
      [transferFromSenderBalanceWord (initState cA gh bl σ σ₀ g A I) I,
        transferFromSenderWord I, transferFromAmountWord I, transferFromIdWord I,
        transferFromReceiverWord I, transferFromSenderWord I, ⟨760⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨649⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      (transferOuterHashMem (transferFromSenderWord I) (transferFromIdWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1373⟩ := erc6909TransferFromX_skipCaller_afterLoad
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := g) (sel := sel) hsz132 hsize hszhi hcanonSender hcanonReceiver
    hsenderCaller hsenderNZ hreceiverNZ hreach
  have hlt : UInt256.lt
      (transferFromSenderBalanceWord (initState cA gh bl σ σ₀ g A I) I)
      (transferFromAmountWord I) = ⟨0⟩ := ult_zero henough
  exact ⟨_, _, evm_run rd1373 with [
    dup3, dup2, lt, iszero, push2 ⟨1437⟩,
    jumpiT (by rw [hlt]; decide) (by jump_dest) ]⟩

theorem erc6909TransferFromX_skipCaller_insufficientTail {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256} {k C : ℕ}
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hlt : (transferFromSenderBalanceWord (initState cA gh bl σ σ₀ g A I) I).toNat <
      (transferFromAmountWord I).toNat)
    (rd1373 : RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1373⟩
      [transferFromSenderBalanceWord (initState cA gh bl σ σ₀ g A I) I,
        transferFromSenderWord I, transferFromAmountWord I, transferFromIdWord I,
        transferFromReceiverWord I, transferFromSenderWord I, ⟨760⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨649⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      (transferOuterHashMem (transferFromSenderWord I) (transferFromIdWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hltw : UInt256.lt
      (transferFromSenderBalanceWord (initState cA gh bl σ σ₀ g A I) I)
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
        (transferFromSenderBalanceWord (initState cA gh bl σ σ₀ g A I) I))
      (UInt256.ofNat 7) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨68⟩, dup2, add, dup5, swap1,
    raw mstore 3 (transferInsufficientBalanceAmountMem (transferFromSenderWord I)
        (transferFromIdWord I)
        (transferFromSenderBalanceWord (initState cA gh bl σ σ₀ g A I) I)
        (transferFromAmountWord I))
      (UInt256.ofNat 8) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨100⟩, dup2, add, dup6, swap1,
    raw mstore 3 (transferInsufficientBalanceIdMem (transferFromSenderWord I)
        (transferFromIdWord I)
        (transferFromSenderBalanceWord (initState cA gh bl σ σ₀ g A I) I)
        (transferFromAmountWord I))
      (UInt256.ofNat 9) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨132⟩, add, push2 ⟨698⟩, jump (by jump_dest),
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 9) (by decide) mem_cost
      (transferInsufficientBalanceIdMem_mload64 (transferFromSenderWord I)
        (transferFromIdWord I)
        (transferFromSenderBalanceWord (initState cA gh bl σ σ₀ g A I) I)
        (transferFromAmountWord I))
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw rev 0 (by decide) mem_cost (by evm_ov) ]

theorem erc6909TransferFromX_skipCaller_insufficient {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderCaller : transferFromSenderWord I = transferFromCallerWord I)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (hreceiverNZ : transferFromReceiverWord I ≠ ⟨0⟩)
    (hlt : (transferFromSenderBalanceWord (initState cA gh bl σ σ₀ g A I) I).toNat <
      (transferFromAmountWord I).toNat)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd1373⟩ := erc6909TransferFromX_skipCaller_afterLoad
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := g) (sel := sel) hsz132 hsize hszhi hcanonSender hcanonReceiver
    hsenderCaller hsenderNZ hreceiverNZ hreach
  exact erc6909TransferFromX_skipCaller_insufficientTail hcanonSender hlt rd1373

theorem erc6909TransferFromX_skipCaller_afterDebit {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4) (hperm : I.perm = true)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderCaller : transferFromSenderWord I = transferFromCallerWord I)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (hreceiverNZ : transferFromReceiverWord I ≠ ⟨0⟩)
    (henough : (transferFromAmountWord I).toNat ≤
      (transferFromSenderBalanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1476⟩
      [transferFromSenderWord I, transferFromAmountWord I, transferFromIdWord I,
        transferFromReceiverWord I, transferFromSenderWord I, ⟨760⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨649⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      (transferMapScratchMem
        (transferOuterHashMem (transferFromSenderWord I) (transferFromIdWord I))
        (transferFromSenderWord I) (transferFromIdWord I))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (transferFromSenderBalanceSlot I)
        (transferFromTailSenderDebitWord (initState cA gh bl σ σ₀ g A I) I)) k C := by
  obtain ⟨_, _, rd1437⟩ := erc6909TransferFromX_skipCaller_afterRequire
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := g) (sel := sel) hsz132 hsize hszhi hcanonSender hcanonReceiver
    hsenderCaller hsenderNZ hreceiverNZ henough hreach
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
          (transferFromSenderBalanceWord (initState cA gh bl σ σ₀ g A I) I)
          (transferFromAmountWord I) =
        transferFromTailSenderDebitWord (initState cA gh bl σ σ₀ g A I) I := by
    apply u256_inj
    rw [usub_toNat henough]
    unfold transferFromTailSenderDebitWord
    rw [ulit_toNat' _ (lt_of_le_of_lt
      (Nat.sub_le
        (transferFromSenderBalanceWord (initState cA gh bl σ σ₀ g A I) I).toNat
        (transferFromAmountWord I).toNat)
      (transferFromSenderBalanceWord (initState cA gh bl σ σ₀ g A I) I).val.isLt)]
  have rd1475₀ := evm_run rd1470 with [
    swap1, dup4, swap1, sub, swap1 ]
  have rd1475 := rd1475₀
  rw [hdebit, hslot] at rd1475
  obtain ⟨_, _, rd1476⟩ := rd1475.sstore hperm (by decide) (by evm_ov)
  exact ⟨_, _, rd1476⟩

theorem erc6909TransferFromX_skipCaller_toCheckedAdd {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4) (hperm : I.perm = true)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderCaller : transferFromSenderWord I = transferFromCallerWord I)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (hreceiverNZ : transferFromReceiverWord I ≠ ⟨0⟩)
    (henough : (transferFromAmountWord I).toNat ≤
      (transferFromSenderBalanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2017⟩
      [transferFromTailReceiverBalanceWord (initState cA gh bl σ σ₀ g A I) I,
        transferFromAmountWord I, ⟨1539⟩, ⟨0⟩, transferFromReceiverBalanceSlot I,
        transferFromAmountWord I, transferFromSenderWord I, transferFromAmountWord I,
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
      (cA, sstoreAccountMap I.codeOwner σ (transferFromSenderBalanceSlot I)
        (transferFromTailSenderDebitWord (initState cA gh bl σ σ₀ g A I) I)) k C := by
  obtain ⟨_, _, rd1476⟩ := erc6909TransferFromX_skipCaller_afterDebit
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := g) (sel := sel) hsz132 hsize hszhi hperm hcanonSender hcanonReceiver
    hsenderCaller hsenderNZ hreceiverNZ henough hreach
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
      [transferFromTailReceiverBalanceWord (initState cA gh bl σ σ₀ g A I) I,
        transferFromReceiverBalanceSlot I, ⟨0⟩, transferFromSenderWord I,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨760⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨649⟩, transferFromCallerWord I, ⟨0⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨193⟩, sel]
      (transferMapScratchMem debitMem (transferFromReceiverWord I) (transferFromIdWord I))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (transferFromSenderBalanceSlot I)
        (transferFromTailSenderDebitWord (initState cA gh bl σ σ₀ g A I) I)) k1 C1 := by
    simpa [transferFromTailReceiverBalanceWord, transferFromTailAfterSenderBalanceState,
      transferFromSenderBalanceSlot, hslot, initState, Solm.EVM.storageLoad,
      State.lookupAccount, Account.lookupStorage, storageStore_accountMap, debitMem]
      using rd1526₀
  exact ⟨_, _, evm_run rd1526 with [
    dup5, swap3, swap1, push2 ⟨1539⟩, swap1, dup5, swap1, push2 ⟨2017⟩,
    jump (by jump_dest) ]⟩

theorem erc6909TransferFromX_skipCaller_afterCredit {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4) (hperm : I.perm = true)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderCaller : transferFromSenderWord I = transferFromCallerWord I)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (hreceiverNZ : transferFromReceiverWord I ≠ ⟨0⟩)
    (henough : (transferFromAmountWord I).toNat ≤
      (transferFromSenderBalanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hfit : transferFromTailReceiverCreditNat (initState cA gh bl σ σ₀ g A I) I <
      UInt256.size)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1545⟩
      [transferFromSenderWord I, transferFromAmountWord I, transferFromIdWord I,
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
        (sstoreAccountMap I.codeOwner σ (transferFromSenderBalanceSlot I)
          (transferFromTailSenderDebitWord (initState cA gh bl σ σ₀ g A I) I))
        (transferFromReceiverBalanceSlot I)
        (transferFromTailReceiverCreditWord (initState cA gh bl σ σ₀ g A I) I)) k C := by
  obtain ⟨_, _, rd2017⟩ := erc6909TransferFromX_skipCaller_toCheckedAdd
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := g) (sel := sel) hsz132 hsize hszhi hperm hcanonSender hcanonReceiver
    hsenderCaller hsenderNZ hreceiverNZ henough hreach
  obtain ⟨_, _, rd1539₀⟩ := erc6909RoutineCheckedAdd rd2017
    (by simpa [transferFromTailReceiverCreditNat] using hfit)
    (by jump_dest) (by evm_ov)
  have hnew :
      transferFromTailReceiverBalanceWord (initState cA gh bl σ σ₀ g A I) I +
          transferFromAmountWord I =
        transferFromTailReceiverCreditWord (initState cA gh bl σ σ₀ g A I) I := by
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

theorem erc6909TransferFromX_skipCaller_overflow {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4) (hperm : I.perm = true)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderCaller : transferFromSenderWord I = transferFromCallerWord I)
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
  obtain ⟨_, _, rd2017⟩ := erc6909TransferFromX_skipCaller_toCheckedAdd
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := g) (sel := sel) hsz132 hsize hszhi hperm hcanonSender hcanonReceiver
    hsenderCaller hsenderNZ hreceiverNZ henough hreach
  exact erc6909RoutineCheckedAdd_overflow rd2017
    (by simpa [transferFromTailReceiverCreditNat] using hover) (by evm_ov)

theorem erc6909TransferFromX_skipCaller_success {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4) (hperm : I.perm = true)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderCaller : transferFromSenderWord I = transferFromCallerWord I)
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
  obtain ⟨_, _, rd1545⟩ := erc6909TransferFromX_skipCaller_afterCredit
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := g) (sel := sel) hsz132 hsize hszhi hperm hcanonSender hcanonReceiver
    hsenderCaller hsenderNZ hreceiverNZ henough hfit hreach
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
  have rd1563 := evm_run rd1545 with [
    jumpdest, push1 ⟨64⟩, dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost
      (transferMapScratchMem_mload64 (transferFromReceiverWord I) (transferFromIdWord I)
        hdebitMemSize hdebitMemRead64)
      (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup4, dup2, and, dup3,
    raw mstore 6 (transferEventFromBaseMem creditMem (transferFromSenderWord I))
      (UInt256.ofNat 5) (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        change (UInt256.toByteArray (UInt256.land solcAddrMask (transferFromSenderWord I))).write 0
          creditMem 128 32 = transferEventFromBaseMem creditMem (transferFromSenderWord I)
        rw [solcAddrMask_clean_left hcanonSender]
        rfl)
      (by decide) (by evm_ov) ]
  have rd1570 := evm_run rd1563 with [
    push1 ⟨32⟩, dup3, add, dup6, swap1,
    raw mstore 3 (transferEventBaseMem creditMem (transferFromSenderWord I)
        (transferFromAmountWord I))
      (UInt256.ofNat 6) (by decide) mem_cost (by rfl) (by decide) (by evm_ov) ]
  have rd1573 := evm_run rd1570 with [dup6, swap3, dup2]
  have rd1574 := RD.dup9 rd1573 (by decide) (by evm_ov)
  have rd1577 := evm_run rd1574 with [and, swap3, swap2]
  have rd1578 := RD.dup10 rd1577 (by decide) (by evm_ov)
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
      (transferEventBaseMem_mload64 (transferFromSenderWord I) (transferFromAmountWord I)
        hcreditMemSize hcreditMemRead64)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1 ]
  have rd1623 := RD.log4 0 (UInt256.ofNat 6) rd1622 (by decide) hperm
    mem_cost (by decide) (by evm_ov)
  have rd760 := evm_run rd1623 with [
    pop, pop, pop, pop, pop, jump (by jump_dest) ]
  have rd649 := evm_run rd760 with [
    jumpdest, pop, pop, pop, pop, jump (by jump_dest) ]
  have rd651 := evm_run rd649 with [jumpdest, pop, push1 ⟨1⟩]
  have rd654 := RD.swap6 rd651 (by decide) (by evm_ov)
  have rd655 := RD.swap5 rd654 (by decide) (by evm_ov)
  have rd193 := evm_run rd655 with [
    pop, pop, pop, pop, pop, jump (by jump_dest) ]
  have rd165 := evm_run rd193 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide)
      mem_cost
      (transferEventBaseMem_mload64 (transferFromSenderWord I) (transferFromAmountWord I)
        hcreditMemSize hcreditMemRead64)
      (by decide) (by evm_ov),
    swap1, iszero, iszero, dup2,
    raw mstore 0 (transferReturnBaseMem creditMem (transferFromSenderWord I)
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
      (transferReturnBaseMem_mload64 (transferFromSenderWord I) (transferFromAmountWord I)
        hcreditMemSize hcreditMemRead64)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray (⟨1⟩ : UInt256)) (by decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show (UInt256.sub ((⟨32⟩ : UInt256) + ⟨128⟩) ⟨128⟩).toNat = 32
            from by decide]
        exact transferReturnBaseMem_read128 (transferFromSenderWord I)
          (transferFromAmountWord I) hcreditMemSize)
      (by evm_ov) ]


end OpenZeppelinBench.ERC6909
