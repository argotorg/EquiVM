import Examples.OpenZeppelinBench.ERC6909.TransferFrom.Traces.SkipCaller

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unnecessarySimpa false

namespace OpenZeppelinBench.ERC6909

theorem erc6909TransferFromX_operatorApproved_toUpdate {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderNe : transferFromSenderWord I ≠ transferFromCallerWord I)
    (hop : transferFromOperatorWord (initState cA gh bl σ σ₀ g A I) I ≠ ⟨0⟩)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨661⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨649⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      (isOperatorOuterHashMem (transferFromSenderWord I) (transferFromCallerWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd556⟩ := erc6909TransferFromX_decoded (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz132 hsize hszhi hcanonSender hcanonReceiver hreach
  have hslot := transferFromOperatorKeccakSlot I hcanonSender
  have hsenderNeEq :
      ¬ UInt256.eq (transferFromSenderWord I) (transferFromCallerWord I) = ⟨1⟩ := by
    intro heq
    apply hsenderNe
    by_contra hne
    simp only [UInt256.eq, UInt256.fromBool, Bool.toUInt256, hne, decide_false,
      Bool.false_eq_true, ↓reduceIte] at heq
    exact absurd heq (by decide)
  have hcallerNeEq :
      ¬ UInt256.eq (transferFromCallerWord I) (transferFromSenderWord I) = ⟨1⟩ := by
    intro heq
    apply hsenderNe
    symm
    by_contra hne
    simp only [UInt256.eq, UInt256.fromBool, Bool.toUInt256, hne, decide_false,
      Bool.false_eq_true, ↓reduceIte] at heq
    exact absurd heq (by decide)
  have heq0 : UInt256.eq (transferFromSenderWord I) (transferFromCallerWord I) = ⟨0⟩ :=
    uInt256_eq_zero_of_ne hsenderNeEq
  have heq0Caller : UInt256.eq (transferFromCallerWord I) (transferFromSenderWord I) = ⟨0⟩ :=
    uInt256_eq_zero_of_ne hcallerNeEq
  have rd615pre := evm_run rd556 with [
    jumpdest, push0, caller, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub,
    dup7, and, dup2, eq, dup1, iszero, swap1, push2 ⟨620⟩,
    jumpiNT (by
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      rw [solcAddrMask_clean hcanonSender]
      simpa [transferFromCallerWord, approveOwnerWord] using heq0Caller),
    pop, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub,
    dup1, dup8, and, push0, swap1, dup2,
    raw mstore 0 (isOperatorOwnerMem (transferFromSenderWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rw [solcAddrMask_clean hcanonSender]
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨32⟩, swap1, dup2,
    raw mstore 0 (isOperatorInnerHashMem (transferFromSenderWord I))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, dup1, dup4,
    raw keccak256 0 (isOperatorInnerSlot (transferFromSenderWord I))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    swap4, dup6, and, dup4,
    raw mstore 0 (isOperatorSpenderMem (transferFromSenderWord I)
        (transferFromCallerWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rw [solcAddrMask_clean (transferFromCallerWord_canonical I)]
        rfl)
      (by decide) (by evm_ov),
    swap3, swap1,
    raw mstore 0 (isOperatorOuterHashMem (transferFromSenderWord I)
        (transferFromCallerWord I))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw keccak256 0 (transferFromOperatorSlotI I)
      (UInt256.ofNat 3) (by decide) mem_cost hslot (by decide) (by evm_ov) ]
  obtain ⟨_, _, rd615⟩ := rd615pre.sload (by decide) (by evm_ov)
  have hopMaskRaw :
      UInt256.land ⟨255⟩
        (Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I)
          (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner
          (transferFromOperatorSlot (initState cA gh bl σ σ₀ g A I) I)) ≠ ⟨0⟩ := by
    rw [SimpleAuction.simpleAuctionU256_land_comm]
    exact hop
  have hopMask :
      UInt256.land ⟨255⟩
        (Option.option ⟨0⟩
          (fun ac => Batteries.RBMap.findD ac.storage (transferFromOperatorSlotI I) ⟨0⟩)
          (Batteries.RBMap.find? σ I.codeOwner)) ≠ ⟨0⟩ := by
    simpa [transferFromOperatorSlot_init, initState, Solm.EVM.storageLoad,
      State.lookupAccount, Account.lookupStorage] using hopMaskRaw
  exact ⟨_, _, by
    simpa [transferFromOperatorWord, transferFromOperatorSlot_init, initState,
      Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage] using
      evm_run rd615 with [
        push1 ⟨255⟩, and, iszero,
        jumpdest, iszero, push2 ⟨637⟩,
        jumpiT (by rw [isZero_eq_zero_of_ne hopMask]; decide) (by jump_dest),
        jumpdest, push2 ⟨649⟩, dup7, dup7, dup7, dup7, push2 ⟨661⟩,
        jump (by jump_dest) ]⟩

theorem erc6909TransferFromX_operatorFalse_toAllowanceHelper {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderNe : transferFromSenderWord I ≠ transferFromCallerWord I)
    (hopZero : transferFromOperatorWord (initState cA gh bl σ σ₀ g A I) I = ⟨0⟩)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1147⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromCallerWord I,
        transferFromSenderWord I, ⟨637⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      (isOperatorOuterHashMem (transferFromSenderWord I) (transferFromCallerWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd556⟩ := erc6909TransferFromX_decoded (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz132 hsize hszhi hcanonSender hcanonReceiver hreach
  have hslot := transferFromOperatorKeccakSlot I hcanonSender
  have hsenderNeEq :
      ¬ UInt256.eq (transferFromSenderWord I) (transferFromCallerWord I) = ⟨1⟩ := by
    intro heq
    apply hsenderNe
    by_contra hne
    simp only [UInt256.eq, UInt256.fromBool, Bool.toUInt256, hne, decide_false,
      Bool.false_eq_true, ↓reduceIte] at heq
    exact absurd heq (by decide)
  have hcallerNeEq :
      ¬ UInt256.eq (transferFromCallerWord I) (transferFromSenderWord I) = ⟨1⟩ := by
    intro heq
    apply hsenderNe
    symm
    by_contra hne
    simp only [UInt256.eq, UInt256.fromBool, Bool.toUInt256, hne, decide_false,
      Bool.false_eq_true, ↓reduceIte] at heq
    exact absurd heq (by decide)
  have heq0Caller : UInt256.eq (transferFromCallerWord I) (transferFromSenderWord I) = ⟨0⟩ :=
    uInt256_eq_zero_of_ne hcallerNeEq
  have rd615pre := evm_run rd556 with [
    jumpdest, push0, caller, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub,
    dup7, and, dup2, eq, dup1, iszero, swap1, push2 ⟨620⟩,
    jumpiNT (by
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      rw [solcAddrMask_clean hcanonSender]
      simpa [transferFromCallerWord, approveOwnerWord] using heq0Caller),
    pop, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub,
    dup1, dup8, and, push0, swap1, dup2,
    raw mstore 0 (isOperatorOwnerMem (transferFromSenderWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rw [solcAddrMask_clean hcanonSender]
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨32⟩, swap1, dup2,
    raw mstore 0 (isOperatorInnerHashMem (transferFromSenderWord I))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, dup1, dup4,
    raw keccak256 0 (isOperatorInnerSlot (transferFromSenderWord I))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    swap4, dup6, and, dup4,
    raw mstore 0 (isOperatorSpenderMem (transferFromSenderWord I)
        (transferFromCallerWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rw [solcAddrMask_clean (transferFromCallerWord_canonical I)]
        rfl)
      (by decide) (by evm_ov),
    swap3, swap1,
    raw mstore 0 (isOperatorOuterHashMem (transferFromSenderWord I)
        (transferFromCallerWord I))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw keccak256 0 (transferFromOperatorSlotI I)
      (UInt256.ofNat 3) (by decide) mem_cost hslot (by decide) (by evm_ov) ]
  obtain ⟨_, _, rd615⟩ := rd615pre.sload (by decide) (by evm_ov)
  have hopMaskRaw :
      UInt256.land ⟨255⟩
        (Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I)
          (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner
          (transferFromOperatorSlot (initState cA gh bl σ σ₀ g A I) I)) = ⟨0⟩ := by
    rw [SimpleAuction.simpleAuctionU256_land_comm]
    exact hopZero
  have hopMask :
      UInt256.land ⟨255⟩
        (Option.option ⟨0⟩
          (fun ac => Batteries.RBMap.findD ac.storage (transferFromOperatorSlotI I) ⟨0⟩)
          (Batteries.RBMap.find? σ I.codeOwner)) = ⟨0⟩ := by
    simpa [transferFromOperatorSlot_init, initState, Solm.EVM.storageLoad,
      State.lookupAccount, Account.lookupStorage] using hopMaskRaw
  exact ⟨_, _, by
    simpa [transferFromOperatorWord, transferFromOperatorSlot_init, initState,
      Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage] using
      evm_run rd615 with [
        push1 ⟨255⟩, and, iszero,
        jumpdest, iszero, push2 ⟨637⟩,
        jumpiNT (by rw [hopMask]; decide),
        push2 ⟨637⟩, dup7, dup3, dup7, dup7, push2 ⟨1147⟩,
        jump (by jump_dest) ]⟩

theorem erc6909TransferFromX_from1147_afterAllowanceLoad
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256} {k C : ℕ}
    {base : ByteArray}
    (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (rd1147 : RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1147⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromCallerWord I,
        transferFromSenderWord I, ⟨637⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      base (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1193⟩
      [transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I,
        transferFromAmountWord I, transferFromIdWord I, transferFromCallerWord I,
        transferFromSenderWord I, ⟨637⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      (approveTwoWordHashMem (transferFromIdWord I)
        (approveSpenderSlot (transferFromSenderWord I) (transferFromCallerWord I))
        (approveTwoWordHashMem (transferFromCallerWord I)
          (approveOwnerSlot (transferFromSenderWord I))
          (approveTwoWordHashMem (transferFromSenderWord I) ⟨2⟩ base)))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  let ownerMem := approveTwoWordHashMem (transferFromSenderWord I) ⟨2⟩ base
  let ownerKeyMem := approveWordAt0Mem (transferFromSenderWord I) base
  let spenderMem := approveTwoWordHashMem (transferFromCallerWord I)
    (approveOwnerSlot (transferFromSenderWord I)) ownerMem
  let spenderKeyMem := approveWordAt0Mem (transferFromCallerWord I) ownerMem
  let idMem := approveTwoWordHashMem (transferFromIdWord I)
    (approveSpenderSlot (transferFromSenderWord I) (transferFromCallerWord I)) spenderMem
  let idKeyMem := approveWordAt0Mem (transferFromIdWord I) spenderMem
  have hownerMemSize : ownerMem.size = 96 := by
    dsimp [ownerMem]
    exact approveTwoWordHashMem_size (transferFromSenderWord I) ⟨2⟩ hbase
  have hownerMemRead64 :
      ownerMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [ownerMem]
    exact approveTwoWordHashMem_read64 (transferFromSenderWord I) ⟨2⟩ hbase hread64
  have hspenderMemSize : spenderMem.size = 96 := by
    dsimp [spenderMem]
    exact approveTwoWordHashMem_size (transferFromCallerWord I)
      (approveOwnerSlot (transferFromSenderWord I)) hownerMemSize
  have hspenderMemRead64 :
      spenderMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [spenderMem]
    exact approveTwoWordHashMem_read64 (transferFromCallerWord I)
      (approveOwnerSlot (transferFromSenderWord I)) hownerMemSize hownerMemRead64
  have hidMemSize : idMem.size = 96 := by
    dsimp [idMem]
    exact approveTwoWordHashMem_size (transferFromIdWord I)
      (approveSpenderSlot (transferFromSenderWord I) (transferFromCallerWord I))
      hspenderMemSize
  have hslot := transferFromAllowanceKeccakSlot I hcanonSender
  have rd1175 := evm_run rd1147 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup5, dup2, and,
    push0, swap1, dup2,
    raw mstore 0 ownerKeyMem (UInt256.ofNat 3) (by decide) mem_cost
      (by
        dsimp [ownerKeyMem]
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rw [solcAddrMask_clean_left hcanonSender]
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨2⟩, push1 ⟨32⟩, swap1, dup2,
    raw mstore 0 ownerMem (UInt256.ofNat 3) (by decide) mem_cost (by rfl)
      (by decide) (by evm_ov),
    push1 ⟨64⟩, dup1, dup4,
    raw keccak256 0 (approveOwnerSlot (transferFromSenderWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        unfold approveOwnerSlot
        change UInt256.ofNat
            (fromByteArrayBigEndian (ffi.KEC (ownerMem.readWithPadding 0 64))) =
          UInt256.ofNat
            (fromByteArrayBigEndian
              (ffi.KEC ((approveOwnerHashMem (transferFromSenderWord I)).readWithPadding 0 64)))
        rw [show ownerMem.readWithPadding 0 64 =
            UInt256.toByteArray (transferFromSenderWord I) ++ UInt256.toByteArray ⟨2⟩ by
          dsimp [ownerMem]
          exact approveTwoWordHashMem_read0_64 (transferFromSenderWord I) ⟨2⟩ hbase]
        rw [approveOwnerHashMem_read0_64])
      (by decide) (by evm_ov) ]
  have rd1191 := evm_run rd1175 with [
    swap4, dup8, and, dup4,
    raw mstore 0 spenderKeyMem (UInt256.ofNat 3) (by decide) mem_cost
      (by
        dsimp [spenderKeyMem]
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rw [solcAddrMask_clean (transferFromCallerWord_canonical I)]
        rfl)
      (by decide) (by evm_ov),
    swap3, dup2,
    raw mstore 0 spenderMem (UInt256.ofNat 3) (by decide) mem_cost (by rfl)
      (by decide) (by evm_ov),
    dup3, dup3,
    raw keccak256 0 (approveSpenderSlot (transferFromSenderWord I) (transferFromCallerWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        unfold approveSpenderSlot
        change UInt256.ofNat
            (fromByteArrayBigEndian (ffi.KEC (spenderMem.readWithPadding 0 64))) =
          UInt256.ofNat
            (fromByteArrayBigEndian
              (ffi.KEC ((approveSpenderHashMem (transferFromSenderWord I)
                (transferFromCallerWord I)).readWithPadding 0 64)))
        rw [show spenderMem.readWithPadding 0 64 =
            UInt256.toByteArray (transferFromCallerWord I) ++
              UInt256.toByteArray (approveOwnerSlot (transferFromSenderWord I)) by
          dsimp [spenderMem]
          exact approveTwoWordHashMem_read0_64 (transferFromCallerWord I)
            (approveOwnerSlot (transferFromSenderWord I)) hownerMemSize]
        rw [approveSpenderHashMem_read0_64])
      (by decide) (by evm_ov),
    dup6, dup4,
    raw mstore 0 idKeyMem (UInt256.ofNat 3) (by decide) mem_cost (by rfl)
      (by decide) (by evm_ov),
    swap1,
    raw mstore 0 idMem (UInt256.ofNat 3) (by decide) mem_cost (by rfl)
      (by decide) (by evm_ov),
    raw keccak256 0 (transferFromAllowanceSlotI I)
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        change UInt256.ofNat
            (fromByteArrayBigEndian (ffi.KEC (idMem.readWithPadding 0 64))) =
          transferFromAllowanceSlotI I
        rw [show idMem.readWithPadding 0 64 =
            UInt256.toByteArray (transferFromIdWord I) ++
              UInt256.toByteArray
                (approveSpenderSlot (transferFromSenderWord I) (transferFromCallerWord I)) by
          dsimp [idMem]
          exact approveTwoWordHashMem_read0_64 (transferFromIdWord I)
            (approveSpenderSlot (transferFromSenderWord I) (transferFromCallerWord I))
            hspenderMemSize]
        rw [← approveIdHashMem_read0_64 (transferFromSenderWord I) (transferFromCallerWord I)
          (transferFromIdWord I)]
        exact hslot)
      (by decide) (by evm_ov) ]
  obtain ⟨k1, C1, rd1193₀⟩ := rd1191.sload (by decide) (by evm_ov)
  exact ⟨k1, C1, by
    simpa [transferFromCurrentAllowanceWord, transferFromAllowanceSlot_init, initState,
      Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage, idMem, idKeyMem,
      spenderMem, spenderKeyMem, ownerMem, ownerKeyMem]
      using rd1193₀⟩

noncomputable def transferFromAllowanceScratchMem (base : ByteArray)
    (I : ExecutionEnv) : ByteArray :=
  approveTwoWordHashMem (transferFromIdWord I)
    (approveSpenderSlot (transferFromSenderWord I) (transferFromCallerWord I))
    (approveTwoWordHashMem (transferFromCallerWord I)
      (approveOwnerSlot (transferFromSenderWord I))
      (approveTwoWordHashMem (transferFromSenderWord I) ⟨2⟩ base))

theorem transferFromAllowanceScratchMem_size {base : ByteArray} (I : ExecutionEnv)
    (hbase : base.size = 96) :
    (transferFromAllowanceScratchMem base I).size = 96 := by
  unfold transferFromAllowanceScratchMem
  exact approveTwoWordHashMem_size (transferFromIdWord I)
    (approveSpenderSlot (transferFromSenderWord I) (transferFromCallerWord I))
    (approveTwoWordHashMem_size (transferFromCallerWord I)
      (approveOwnerSlot (transferFromSenderWord I))
      (approveTwoWordHashMem_size (transferFromSenderWord I) ⟨2⟩ hbase))

theorem transferFromAllowanceScratchMem_read64 {base : ByteArray} (I : ExecutionEnv)
    (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (transferFromAllowanceScratchMem base I).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold transferFromAllowanceScratchMem
  exact approveTwoWordHashMem_read64 (transferFromIdWord I)
    (approveSpenderSlot (transferFromSenderWord I) (transferFromCallerWord I))
    (approveTwoWordHashMem_size (transferFromCallerWord I)
      (approveOwnerSlot (transferFromSenderWord I))
      (approveTwoWordHashMem_size (transferFromSenderWord I) ⟨2⟩ hbase))
    (approveTwoWordHashMem_read64 (transferFromCallerWord I)
      (approveOwnerSlot (transferFromSenderWord I))
      (approveTwoWordHashMem_size (transferFromSenderWord I) ⟨2⟩ hbase)
      (approveTwoWordHashMem_read64 (transferFromSenderWord I) ⟨2⟩ hbase hread64))

noncomputable def transferFromOperatorAllowanceScratchMem (I : ExecutionEnv) : ByteArray :=
  transferFromAllowanceScratchMem
    (isOperatorOuterHashMem (transferFromSenderWord I) (transferFromCallerWord I)) I

theorem transferFromOperatorAllowanceScratchMem_size (I : ExecutionEnv) :
    (transferFromOperatorAllowanceScratchMem I).size = 96 := by
  unfold transferFromOperatorAllowanceScratchMem
  exact transferFromAllowanceScratchMem_size I
    (isOperatorOuterHashMem_size (transferFromSenderWord I) (transferFromCallerWord I))

theorem transferFromOperatorAllowanceScratchMem_read64 (I : ExecutionEnv) :
    (transferFromOperatorAllowanceScratchMem I).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold transferFromOperatorAllowanceScratchMem
  exact transferFromAllowanceScratchMem_read64 I
    (isOperatorOuterHashMem_size (transferFromSenderWord I) (transferFromCallerWord I))
    (isOperatorOuterHashMem_read64 (transferFromSenderWord I) (transferFromCallerWord I))

theorem erc6909TransferFromX_from637_to661_base
    {cA gh bl σ σ₀ σcur A I} {g : Sat256} {sel : UInt256} {k C : ℕ}
    {base : ByteArray}
    (rd637 : RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨637⟩
      [transferFromCallerWord I, ⟨0⟩, transferFromAmountWord I, transferFromIdWord I,
        transferFromReceiverWord I, transferFromSenderWord I, ⟨193⟩, sel]
      base (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨661⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨649⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      base (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C := by
  exact ⟨_, _, evm_run rd637 with [
    jumpdest, push2 ⟨649⟩, dup7, dup7, dup7, dup7, push2 ⟨661⟩,
    jump (by jump_dest) ]⟩

theorem erc6909TransferFromX_from1193_allowanceMax_to661_base
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256} {k C : ℕ}
    {base : ByteArray}
    (hallowanceMax : UInt256.size - 1 ≤
      (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (rd1193 : RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1193⟩
      [transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I,
        transferFromAmountWord I, transferFromIdWord I, transferFromCallerWord I,
        transferFromSenderWord I, ⟨637⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      base (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨661⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨649⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      base (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hmaxToNat :
      (UInt256.ofNat (UInt256.size - 1)).toNat = UInt256.size - 1 := by
    exact ulit_toNat' _ (by
      have hpos : 0 < UInt256.size := by norm_num [UInt256.size]
      exact Nat.sub_lt hpos (by decide))
  have hltMax :
      UInt256.lt
        (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I)
        (UInt256.lnot (⟨0⟩ : UInt256)) = ⟨0⟩ := by
    rw [uint256_lnot_zero_max]
    exact ult_zero (by simpa [hmaxToNat] using hallowanceMax)
  have rd637 := evm_run rd1193 with [
    push0, not, dup2, lt, iszero, push2 ⟨1316⟩,
    jumpiT (by rw [hltMax]; decide) (by jump_dest),
    jumpdest, pop, pop, pop, pop, pop, jump (by jump_dest) ]
  exact erc6909TransferFromX_from637_to661_base
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (σcur := σ)
    (A := A) (g := g) (sel := sel) (base := base) rd637

theorem erc6909TransferFromX_from661_toUpdateHelper {cA gh bl σ σ₀ σcur A I}
    {g : Sat256} {sel : UInt256} {k C : ℕ}
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (hreceiverNZ : transferFromReceiverWord I ≠ ⟨0⟩)
    (rd661 : RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨661⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨649⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1323⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨760⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨649⟩, transferFromCallerWord I, ⟨0⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨193⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C := by
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

theorem erc6909TransferFromX_from661_revert_sender_zero {cA gh bl σ σ₀ σcur A I}
    {g : Sat256} {sel : UInt256} {k C : ℕ}
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hsenderZero : transferFromSenderWord I = ⟨0⟩)
    (rd661 : RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨661⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨649⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C) :
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

theorem erc6909TransferFromX_from661_revert_receiver_zero {cA gh bl σ σ₀ σcur A I}
    {g : Sat256} {sel : UInt256} {k C : ℕ}
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (hreceiverZero : transferFromReceiverWord I = ⟨0⟩)
    (rd661 : RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨661⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨649⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C) :
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

theorem erc6909TransferFromX_from661_toUpdateHelper_base {cA gh bl σ σ₀ σcur A I}
    {g : Sat256} {sel : UInt256} {k C : ℕ} {base : ByteArray}
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (hreceiverNZ : transferFromReceiverWord I ≠ ⟨0⟩)
    (rd661 : RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨661⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨649⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      base (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1323⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨760⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨649⟩, transferFromCallerWord I, ⟨0⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨193⟩, sel]
      base (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C := by
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

theorem erc6909TransferFromX_from1193_allowanceMax_to1323_base
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256} {k C : ℕ}
    {base : ByteArray}
    (hallowanceMax : UInt256.size - 1 ≤
      (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (hreceiverNZ : transferFromReceiverWord I ≠ ⟨0⟩)
    (rd1193 : RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1193⟩
      [transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I,
        transferFromAmountWord I, transferFromIdWord I, transferFromCallerWord I,
        transferFromSenderWord I, ⟨637⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      base (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1323⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨760⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨649⟩, transferFromCallerWord I, ⟨0⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨193⟩, sel]
      base (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd661⟩ := erc6909TransferFromX_from1193_allowanceMax_to661_base
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) (sel := sel) (base := base) hallowanceMax rd1193
  exact erc6909TransferFromX_from661_toUpdateHelper_base
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (σcur := σ)
    (A := A) (g := g) (sel := sel) (base := base) hcanonSender hcanonReceiver
    hsenderNZ hreceiverNZ rd661

set_option maxHeartbeats 2000000 in
theorem erc6909TransferFromX_from1193_allowanceDebit_to661_base
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256} {k C : ℕ}
    {base : ByteArray}
    (hbase : base.size = 96)
    (hperm : I.perm = true)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hallowanceNotMax :
      (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat <
        UInt256.size - 1)
    (hallowanceEnough : (transferFromAmountWord I).toNat ≤
      (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (rd1193 : RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1193⟩
      [transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I,
        transferFromAmountWord I, transferFromIdWord I, transferFromCallerWord I,
        transferFromSenderWord I, ⟨637⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      base (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨661⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨649⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      (transferFromAllowanceScratchMem base I) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (transferFromAllowanceSlotI I)
        (transferFromAllowanceDebitWord (initState cA gh bl σ σ₀ g A I) I)) k C := by
  let ownerMem := approveTwoWordHashMem (transferFromSenderWord I) ⟨2⟩ base
  let ownerKeyMem := approveWordAt0Mem (transferFromSenderWord I) base
  let spenderMem := approveTwoWordHashMem (transferFromCallerWord I)
    (approveOwnerSlot (transferFromSenderWord I)) ownerMem
  let spenderKeyMem := approveWordAt0Mem (transferFromCallerWord I) ownerMem
  let idMem := transferFromAllowanceScratchMem base I
  let idKeyMem := approveWordAt0Mem (transferFromIdWord I) spenderMem
  have hownerMemSize : ownerMem.size = 96 := by
    dsimp [ownerMem]
    exact approveTwoWordHashMem_size (transferFromSenderWord I) ⟨2⟩ hbase
  have hspenderMemSize : spenderMem.size = 96 := by
    dsimp [spenderMem]
    exact approveTwoWordHashMem_size (transferFromCallerWord I)
      (approveOwnerSlot (transferFromSenderWord I)) hownerMemSize
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
        (transferFromAmountWord I) = ⟨0⟩ := ult_zero hallowanceEnough
  have hslot := transferFromAllowanceKeccakSlot I hcanonSender
  have rd1202 := evm_run rd1193 with [
    push0, not, dup2, lt, iszero, push2 ⟨1316⟩,
    jumpiNT (by rw [hltMax]; decide) ]
  have rd1266 := evm_run rd1202 with [
    dup2, dup2, lt, iszero, push2 ⟨1266⟩,
    jumpiT (by rw [hltAmount]; decide) (by jump_dest) ]
  have rd1294 := evm_run rd1266 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup1, dup7, and,
    push0, swap1, dup2,
    raw mstore 0 ownerKeyMem (UInt256.ofNat 3) (by decide) mem_cost
      (by
        dsimp [ownerKeyMem]
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rw [solcAddrMask_clean hcanonSender]
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨2⟩, push1 ⟨32⟩, swap1, dup2,
    raw mstore 0 ownerMem (UInt256.ofNat 3) (by decide) mem_cost (by rfl)
      (by decide) (by evm_ov),
    push1 ⟨64⟩, dup1, dup4,
    raw keccak256 0 (approveOwnerSlot (transferFromSenderWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        unfold approveOwnerSlot
        change UInt256.ofNat
            (fromByteArrayBigEndian (ffi.KEC (ownerMem.readWithPadding 0 64))) =
          UInt256.ofNat
            (fromByteArrayBigEndian
              (ffi.KEC ((approveOwnerHashMem (transferFromSenderWord I)).readWithPadding 0 64)))
        rw [show ownerMem.readWithPadding 0 64 =
            UInt256.toByteArray (transferFromSenderWord I) ++ UInt256.toByteArray ⟨2⟩ by
          dsimp [ownerMem]
          exact approveTwoWordHashMem_read0_64 (transferFromSenderWord I) ⟨2⟩ hbase]
        rw [approveOwnerHashMem_read0_64])
      (by decide) (by evm_ov) ]
  have rd1295 := evm_run rd1294 with [swap4]
  have rd1296 := RD.dup9 rd1295 (by decide) (by evm_ov)
  have rd1310 := evm_run rd1296 with [
    and, dup4,
    raw mstore 0 spenderKeyMem (UInt256.ofNat 3) (by decide) mem_cost
      (by
        dsimp [spenderKeyMem]
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rw [solcAddrMask_clean (transferFromCallerWord_canonical I)]
        rfl)
      (by decide) (by evm_ov),
    swap3, dup2,
    raw mstore 0 spenderMem (UInt256.ofNat 3) (by decide) mem_cost (by rfl)
      (by decide) (by evm_ov),
    dup3, dup3,
    raw keccak256 0 (approveSpenderSlot (transferFromSenderWord I) (transferFromCallerWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        unfold approveSpenderSlot
        change UInt256.ofNat
            (fromByteArrayBigEndian (ffi.KEC (spenderMem.readWithPadding 0 64))) =
          UInt256.ofNat
            (fromByteArrayBigEndian
              (ffi.KEC ((approveSpenderHashMem (transferFromSenderWord I)
                (transferFromCallerWord I)).readWithPadding 0 64)))
        rw [show spenderMem.readWithPadding 0 64 =
            UInt256.toByteArray (transferFromCallerWord I) ++
              UInt256.toByteArray (approveOwnerSlot (transferFromSenderWord I)) by
          dsimp [spenderMem]
          exact approveTwoWordHashMem_read0_64 (transferFromCallerWord I)
            (approveOwnerSlot (transferFromSenderWord I)) hownerMemSize]
        rw [approveSpenderHashMem_read0_64])
      (by decide) (by evm_ov),
    dup7, dup4,
    raw mstore 0 idKeyMem (UInt256.ofNat 3) (by decide) mem_cost (by rfl)
      (by decide) (by evm_ov),
    swap1,
    raw mstore 0 idMem (UInt256.ofNat 3) (by decide) mem_cost
      (by
        dsimp [idMem, transferFromAllowanceScratchMem]
        rfl)
      (by decide) (by evm_ov),
    raw keccak256 0 (transferFromAllowanceSlotI I)
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        change UInt256.ofNat
            (fromByteArrayBigEndian (ffi.KEC (idMem.readWithPadding 0 64))) =
          transferFromAllowanceSlotI I
        rw [show idMem.readWithPadding 0 64 =
            UInt256.toByteArray (transferFromIdWord I) ++
              UInt256.toByteArray
                (approveSpenderSlot (transferFromSenderWord I) (transferFromCallerWord I)) by
          dsimp [idMem, transferFromAllowanceScratchMem]
          exact approveTwoWordHashMem_read0_64 (transferFromIdWord I)
            (approveSpenderSlot (transferFromSenderWord I) (transferFromCallerWord I))
            hspenderMemSize]
        rw [← approveIdHashMem_read0_64 (transferFromSenderWord I) (transferFromCallerWord I)
          (transferFromIdWord I)]
        exact hslot)
      (by decide) (by evm_ov) ]
  have hdebit :
      UInt256.sub
          (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I)
          (transferFromAmountWord I) =
        transferFromAllowanceDebitWord (initState cA gh bl σ σ₀ g A I) I := by
    apply u256_inj
    rw [usub_toNat hallowanceEnough]
    unfold transferFromAllowanceDebitWord
    rw [ulit_toNat' _ (lt_of_le_of_lt
      (Nat.sub_le
        (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat
        (transferFromAmountWord I).toNat)
      (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).val.isLt)]
  have rd1315₀ := evm_run rd1310 with [dup3, dup3, sub, swap1]
  have rd1315 := rd1315₀
  rw [hdebit] at rd1315
  obtain ⟨_, _, rd1316⟩ := rd1315.sstore hperm (by decide) (by evm_ov)
  have rd637 := evm_run rd1316 with [
    jumpdest, pop, pop, pop, pop, pop, jump (by jump_dest) ]
  exact erc6909TransferFromX_from637_to661_base
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (σcur := sstoreAccountMap I.codeOwner σ (transferFromAllowanceSlotI I)
      (transferFromAllowanceDebitWord (initState cA gh bl σ σ₀ g A I) I))
    (A := A) (g := g) (sel := sel) (base := transferFromAllowanceScratchMem base I)
    rd637


end OpenZeppelinBench.ERC6909
