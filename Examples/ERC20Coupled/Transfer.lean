import Examples.ERC20Coupled.SolidityPatterns
import Reasoning.Refinement

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000

namespace ERC20Coupled

open ERC20Standalone

abbrev transferS0 (cA : Batteries.RBSet AccountAddress compare) (gh : BlockHeader)
    (bl : ProcessedBlocks) (σ σ₀ : AccountMap) (g : Sat256) (A : Substate)
    (I : ExecutionEnv) : State :=
  initState cA gh bl σ σ₀ g A I

def TransferDecodedRel {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader}
    {bl : ProcessedBlocks} {σ σ₀ : AccountMap} {A : Substate}
    (I : ExecutionEnv) (g : Sat256) (sel : UInt256) : StateRel :=
  fun cur frame evm =>
    frame = { contract := erc20Contract, locals := transferStore I } ∧
    evm = transferS0 cA gh bl σ σ₀ g A I ∧
    cur.stack = [transferValueWord I, transferToWord I, ⟨300⟩, sel] ∧
    cur.mem = solcFreePtrMem ∧
    cur.aw = UInt256.ofNat 3 ∧
    cur.rdata = ByteArray.empty ∧
    cur.world = (cA, σ)

noncomputable def transferDecodedState {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader}
    {bl : ProcessedBlocks} {σ σ₀ : AccountMap} {A : Substate}
    {I : ExecutionEnv} {g : Sat256} {sel : UInt256} {k C : ℕ}
    (rd1365 : RD erc20Bytecode I g (transferS0 cA gh bl σ σ₀ g A I) ⟨1365⟩
      [transferValueWord I, transferToWord I, ⟨300⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    CoupledState erc20Bytecode I g (transferS0 cA gh bl σ σ₀ g A I)
      (TransferDecodedRel (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) I g sel) ⟨1365⟩ :=
  CoupledState.ofRD
    { contract := erc20Contract, locals := transferStore I }
    (transferS0 cA gh bl σ σ₀ g A I)
    rd1365
    (by simp [worldOf, transferS0, initState])
    (by simp [TransferDecodedRel, cursorOfRD])

/-- Current-cursor segment: transfer's decoded body entry loads `balanceOf[msg.sender]`. -/
theorem transferLoadSenderBalance {cA : Batteries.RBSet AccountAddress compare}
    {gh : BlockHeader} {bl : ProcessedBlocks} {σ σ₀ : AccountMap} {A : Substate}
    {I : ExecutionEnv} {g : Sat256} {sel : UInt256} {k C : ℕ}
    (rd1365 : RD erc20Bytecode I g (transferS0 cA gh bl σ σ₀ g A I) ⟨1365⟩
      [transferValueWord I, transferToWord I, ⟨300⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD erc20Bytecode I g (transferS0 cA gh bl σ σ₀ g A I) ⟨1429⟩
      [transferFromBalanceWord (transferS0 cA gh bl σ σ₀ g A I), transferValueWord I,
        ⟨0⟩, transferValueWord I, transferToWord I, ⟨300⟩, sel]
      (balanceOfHashMem (transferSenderWord I)) (UInt256.ofNat 3) ByteArray.empty (cA, σ)
      k' C' := by
  have hsenderCleanL : UInt256.land erc20AddrMask (transferSenderWord I) = transferSenderWord I :=
    erc20AddrMask_clean_left (approveOwnerWord_canonical I)
  have hslot := transferSenderKeccakSlot I
  have rd1415₀ := evm_run rd1365 with [
    jumpdest, push0, dup2, push0, push0, caller, push20 erc20AddrMask, and,
    push20 erc20AddrMask, and ]
  have rd1415 := rd1415₀
  rw [hsenderCleanL, hsenderCleanL] at rd1415
  have rd1428 := evm_run rd1415 with [
    dup2,
    raw mstore 0 (transferBalanceOwnerMem (transferSenderWord I)) (UInt256.ofNat 3)
      (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, add, swap1, dup2,
    raw mstore 0 (balanceOfHashMem (transferSenderWord I)) (UInt256.ofNat 3)
      (by decide) mem_cost
      (transferBalanceOwnerMem_writeSlot (transferSenderWord I)) (by decide) (by evm_ov),
    push1 ⟨32⟩, add, push0,
    raw keccak256 0 (transferSenderSlotI I) (UInt256.ofNat 3)
      (by decide) mem_cost hslot (by decide) (by evm_ov) ]
  obtain ⟨k1, C1, rd1429₀⟩ := rd1428.sload (by decide) (by evm_ov)
  refine ⟨k1, C1, ?_⟩
  simpa [transferFromBalanceWord, transferSenderSlot, transferSenderSlotI, transferS0, initState]
    using rd1429₀

theorem transferBalanceRequireTrue {cA : Batteries.RBSet AccountAddress compare}
    {gh : BlockHeader} {bl : ProcessedBlocks} {σ σ₀ : AccountMap} {A : Substate}
    {I : ExecutionEnv} {g : Sat256} {sel : UInt256} {k C : ℕ}
    (henough : (transferValueWord I).toNat ≤
      (transferFromBalanceWord (transferS0 cA gh bl σ σ₀ g A I)).toNat)
    (rd1429 : RD erc20Bytecode I g (transferS0 cA gh bl σ σ₀ g A I) ⟨1429⟩
      [transferFromBalanceWord (transferS0 cA gh bl σ σ₀ g A I), transferValueWord I,
        ⟨0⟩, transferValueWord I, transferToWord I, ⟨300⟩, sel]
      (balanceOfHashMem (transferSenderWord I)) (UInt256.ofNat 3) ByteArray.empty (cA, σ)
      k C) :
    ∃ k' C', RD erc20Bytecode I g (transferS0 cA gh bl σ σ₀ g A I) ⟨1493⟩
      [⟨0⟩, transferValueWord I, transferToWord I, ⟨300⟩, sel]
      (balanceOfHashMem (transferSenderWord I)) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k' C' := by
  have hlt : UInt256.lt (transferFromBalanceWord (transferS0 cA gh bl σ σ₀ g A I))
      (transferValueWord I) = ⟨0⟩ := ult_zero henough
  exact ⟨_, _, evm_run rd1429 with [
    lt, iszero, push2 ⟨1493⟩, jumpiT (by rw [hlt]; decide) erc20_jd ]⟩

theorem transferBalanceRequireFalse {cA : Batteries.RBSet AccountAddress compare}
    {gh : BlockHeader} {bl : ProcessedBlocks} {σ σ₀ : AccountMap} {A : Substate}
    {I : ExecutionEnv} {g : Sat256} {sel : UInt256} {k C : ℕ}
    (hlt : (transferFromBalanceWord (transferS0 cA gh bl σ σ₀ g A I)).toNat <
      (transferValueWord I).toNat)
    (rd1429 : RD erc20Bytecode I g (transferS0 cA gh bl σ σ₀ g A I) ⟨1429⟩
      [transferFromBalanceWord (transferS0 cA gh bl σ σ₀ g A I), transferValueWord I,
        ⟨0⟩, transferValueWord I, transferToWord I, ⟨300⟩, sel]
      (balanceOfHashMem (transferSenderWord I)) (UInt256.ofNat 3) ByteArray.empty (cA, σ)
      k C) :
    RDrev erc20Bytecode g (transferS0 cA gh bl σ σ₀ g A I) := by
  have hltw : UInt256.lt (transferFromBalanceWord (transferS0 cA gh bl σ σ₀ g A I))
      (transferValueWord I) = ⟨1⟩ := ult_one hlt
  have rd1430₀ := evm_run rd1429 with [ lt ]
  have rd1430 := rd1430₀
  rw [hltw] at rd1430
  have rd1431₀ := evm_run rd1430 with [ iszero ]
  have rd1431 := rd1431₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd1431
  have rd1435 := evm_run rd1431 with [
    push2 ⟨1493⟩, jumpiNT (by decide) ]
  have rd1438 := evm_run rd1435 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost
      (balanceOfHashMem_mload64 (transferSenderWord I))
      (by decide) (by evm_ov) ]
  have rd1471 := rd1438.pushConst transferErrorSelector (width := 32) (op := .PUSH32)
    (by decide) (by decide) (by evm_ov)
  have rd1473 := evm_run rd1471 with [
    dup2,
    raw mstore 6 (transferInsufficientSelectorMem (transferSenderWord I)) (UInt256.ofNat 5)
      (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov) ]
  have rd2477 := evm_run rd1473 with [
    push1 ⟨4⟩, add, push2 ⟨1484⟩, swap1, push2 ⟨2477⟩, jump erc20_jd ]
  have rd2492 := evm_run rd2477 with [
    jumpdest, push0, push1 ⟨32⟩, dup3, add, swap1, pop, dup2, dup2, sub,
    push0, dup4, add,
    raw mstore 3 (transferInsufficientOffsetMem (transferSenderWord I)) (UInt256.ofNat 6)
      (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov) ]
  have rd2443 := evm_run rd2492 with [
    push2 ⟨2500⟩, dup2, push2 ⟨2443⟩, jump erc20_jd ]
  have rd2283 := evm_run rd2443 with [
    jumpdest, push0, push2 ⟨2455⟩, push1 ⟨27⟩, dup4, push2 ⟨2283⟩,
    jump erc20_jd ]
  have rd2455 := evm_run rd2283 with [
    jumpdest, push0, dup3, dup3,
    raw mstore 3 (transferInsufficientLengthMem (transferSenderWord I)) (UInt256.ofNat 7)
      (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, dup3, add, swap1, pop, swap3, swap2, pop, pop,
    jump erc20_jd ]
  have rd2403 := evm_run rd2455 with [
    jumpdest, swap2, pop, push2 ⟨2466⟩, dup3, push2 ⟨2403⟩, jump erc20_jd ]
  have rd2404 := evm_run rd2403 with [ jumpdest ]
  have rd2437 := rd2404.pushConst transferInsufficientBalanceWord
    (width := 32) (op := .PUSH32) (by decide) (by decide) (by evm_ov)
  have rd2466 := evm_run rd2437 with [
    push0, dup3, add,
    raw mstore 3 (transferInsufficientStringMem (transferSenderWord I)) (UInt256.ofNat 8)
      (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    pop, jump erc20_jd ]
  have rd2500 := evm_run rd2466 with [
    jumpdest, push1 ⟨32⟩, dup3, add, swap1, pop, swap2, swap1, pop,
    jump erc20_jd ]
  have rd1484 := evm_run rd2500 with [
    jumpdest, swap1, pop, swap2, swap1, pop, jump erc20_jd ]
  have rd1492 := evm_run rd1484 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by decide)
      mem_cost
      (transferInsufficientStringMem_mload64 (transferSenderWord I))
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1 ]
  exact rd1492.rev 0 (by decide) mem_cost (by evm_ov)

theorem transferDebitSender {cA : Batteries.RBSet AccountAddress compare}
    {gh : BlockHeader} {bl : ProcessedBlocks} {σ σ₀ : AccountMap} {A : Substate}
    {I : ExecutionEnv} {g : Sat256} {sel : UInt256} {k C : ℕ}
    (hperm : I.perm = true)
    (henough : (transferValueWord I).toNat ≤
      (transferFromBalanceWord (transferS0 cA gh bl σ σ₀ g A I)).toNat)
    (rd1493 : RD erc20Bytecode I g (transferS0 cA gh bl σ σ₀ g A I) ⟨1493⟩
      [⟨0⟩, transferValueWord I, transferToWord I, ⟨300⟩, sel]
      (balanceOfHashMem (transferSenderWord I)) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD erc20Bytecode I g (transferS0 cA gh bl σ σ₀ g A I) ⟨1576⟩
      [⟨0⟩, transferValueWord I, transferToWord I, ⟨300⟩, sel]
      (balanceOfHashMem (transferSenderWord I)) (UInt256.ofNat 3)
      ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (transferSenderSlotI I)
        (transferDebitWord (transferS0 cA gh bl σ σ₀ g A I) I)) k' C' := by
  have hsenderCleanL : UInt256.land erc20AddrMask (transferSenderWord I) = transferSenderWord I :=
    erc20AddrMask_clean_left (approveOwnerWord_canonical I)
  have hslot := transferSenderKeccakSlot I
  have rd1517₀ := evm_run rd1493 with [
    jumpdest, dup2, push0, push0, caller, push20 erc20AddrMask, and,
    push20 erc20AddrMask, and ]
  have rd1517 := rd1517₀
  rw [hsenderCleanL, hsenderCleanL] at rd1517
  have rd1530 := evm_run rd1517 with [
    dup2,
    raw mstore 0 (balanceOfHashMem (transferSenderWord I)) (UInt256.ofNat 3)
      (by decide) mem_cost
      (balanceOfHashMem_writeOwner_self (transferSenderWord I)) (by decide) (by evm_ov),
    push1 ⟨32⟩, add, swap1, dup2,
    raw mstore 0 (balanceOfHashMem (transferSenderWord I)) (UInt256.ofNat 3)
      (by decide) mem_cost
      (balanceOfHashMem_writeSlot_self (transferSenderWord I)) (by decide) (by evm_ov),
    push1 ⟨32⟩, add, push0,
    raw keccak256 0 (transferSenderSlotI I) (UInt256.ofNat 3)
      (by decide) mem_cost hslot (by decide) (by evm_ov),
    push0, dup3, dup3 ]
  obtain ⟨k1, C1, rd1559₀⟩ := rd1530.sload (by decide) (by evm_ov)
  have rd1559 : RD erc20Bytecode I g (transferS0 cA gh bl σ σ₀ g A I) ⟨1559⟩
      [transferFromBalanceWord (transferS0 cA gh bl σ σ₀ g A I), transferValueWord I,
        ⟨0⟩, transferSenderSlotI I, transferValueWord I, ⟨0⟩, transferValueWord I,
        transferToWord I, ⟨300⟩, sel]
      (balanceOfHashMem (transferSenderWord I)) (UInt256.ofNat 3) ByteArray.empty (cA, σ)
      k1 C1 := by
    simpa [transferFromBalanceWord, transferSenderSlot, transferSenderSlotI, transferS0,
      initState, Solm.EVM.storageLoad]
      using rd1559₀
  have rd2552 := evm_run rd1559 with [
    push2 ⟨1568⟩, swap2, swap1, push2 ⟨2552⟩, jump erc20_jd ]
  obtain ⟨k2, C2, rd1568₀⟩ := erc20RoutineCheckedSub rd2552 henough erc20_jd
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hdebit :
      UInt256.sub (transferFromBalanceWord (transferS0 cA gh bl σ σ₀ g A I))
          (transferValueWord I) =
        transferDebitWord (transferS0 cA gh bl σ σ₀ g A I) I := by
    apply u256_inj
    rw [usub_toNat henough]
    unfold transferDebitWord
    rw [ulit_toNat' _ (lt_of_le_of_lt
      (Nat.sub_le (transferFromBalanceWord (transferS0 cA gh bl σ σ₀ g A I)).toNat
        (transferValueWord I).toNat)
      (transferFromBalanceWord (transferS0 cA gh bl σ σ₀ g A I)).val.isLt)]
  have rd1568 := rd1568₀
  rw [hdebit] at rd1568
  have rd1575 := evm_run rd1568 with [
    jumpdest, swap3, pop, pop, dup2, swap1 ]
  obtain ⟨k3, C3, rd1575s⟩ := rd1575.sstore hperm (by decide) (by evm_ov)
  exact ⟨_, _, evm_run rd1575s with [ pop ]⟩

theorem transferLoadRecipientBalance {cA : Batteries.RBSet AccountAddress compare}
    {gh : BlockHeader} {bl : ProcessedBlocks} {σ σ₀ : AccountMap} {A : Substate}
    {I : ExecutionEnv} {g : Sat256} {sel : UInt256} {k C : ℕ}
    (hcanonTo : (transferToWord I).toNat < EVM.addressModulus)
    (_henough : (transferValueWord I).toNat ≤
      (transferFromBalanceWord (transferS0 cA gh bl σ σ₀ g A I)).toNat)
    (rd1576 : RD erc20Bytecode I g (transferS0 cA gh bl σ σ₀ g A I) ⟨1576⟩
      [⟨0⟩, transferValueWord I, transferToWord I, ⟨300⟩, sel]
      (balanceOfHashMem (transferSenderWord I)) (UInt256.ofNat 3)
      ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (transferSenderSlotI I)
        (transferDebitWord (transferS0 cA gh bl σ σ₀ g A I) I)) k C) :
    ∃ k' C', RD erc20Bytecode I g (transferS0 cA gh bl σ σ₀ g A I) ⟨1641⟩
      [transferToBalanceWord (transferS0 cA gh bl σ σ₀ g A I) I, transferValueWord I,
        ⟨0⟩, transferToSlot I, transferValueWord I, ⟨0⟩, transferValueWord I,
        transferToWord I, ⟨300⟩, sel]
      (balanceOfHashMem (transferToWord I)) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (transferSenderSlotI I)
        (transferDebitWord (transferS0 cA gh bl σ σ₀ g A I) I)) k' C' := by
  have htoCleanL : UInt256.land erc20AddrMask (transferToWord I) = transferToWord I :=
    erc20AddrMask_clean_left hcanonTo
  have hslot := transferToKeccakSlot I hcanonTo
  have rd1624₀ := evm_run rd1576 with [
    dup2, push0, push0, dup6, push20 erc20AddrMask, and,
    push20 erc20AddrMask, and ]
  have rd1624 := rd1624₀
  rw [htoCleanL, htoCleanL] at rd1624
  have rd1640 := evm_run rd1624 with [
    dup2,
    raw mstore 0 (balanceOfHashMem (transferToWord I)) (UInt256.ofNat 3)
      (by decide) mem_cost
      (balanceOfHashMem_writeOwner (transferSenderWord I) (transferToWord I))
      (by decide) (by evm_ov),
    push1 ⟨32⟩, add, swap1, dup2,
    raw mstore 0 (balanceOfHashMem (transferToWord I)) (UInt256.ofNat 3)
      (by decide) mem_cost
      (balanceOfHashMem_writeSlot_self (transferToWord I)) (by decide) (by evm_ov),
    push1 ⟨32⟩, add, push0,
    raw keccak256 0 (transferToSlot I) (UInt256.ofNat 3)
      (by decide) mem_cost hslot (by decide) (by evm_ov),
    push0, dup3, dup3 ]
  obtain ⟨k1, C1, rd1641₀⟩ := rd1640.sload (by decide) (by evm_ov)
  refine ⟨k1, C1, ?_⟩
  simpa [transferToBalanceWord, transferAfterDebitState, transferSenderSlot,
    transferSenderSlotI, transferS0, initState, Solm.EVM.storageLoad, State.lookupAccount,
    Account.lookupStorage, erc20StorageStore_accountMap]
    using rd1641₀

theorem transferCheckedAdd {cA : Batteries.RBSet AccountAddress compare}
    {gh : BlockHeader} {bl : ProcessedBlocks} {σ σ₀ : AccountMap} {A : Substate}
    {I : ExecutionEnv} {g : Sat256} {sel : UInt256} {k C : ℕ}
    (hfit : transferNewToNat (transferS0 cA gh bl σ σ₀ g A I) I < UInt256.size)
    (rd1641 : RD erc20Bytecode I g (transferS0 cA gh bl σ σ₀ g A I) ⟨1641⟩
      [transferToBalanceWord (transferS0 cA gh bl σ σ₀ g A I) I, transferValueWord I,
        ⟨0⟩, transferToSlot I, transferValueWord I, ⟨0⟩, transferValueWord I,
        transferToWord I, ⟨300⟩, sel]
      (balanceOfHashMem (transferToWord I)) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (transferSenderSlotI I)
        (transferDebitWord (transferS0 cA gh bl σ σ₀ g A I) I)) k C) :
    ∃ k' C', RD erc20Bytecode I g (transferS0 cA gh bl σ σ₀ g A I) ⟨1650⟩
      [transferNewToWord (transferS0 cA gh bl σ σ₀ g A I) I, ⟨0⟩, transferToSlot I,
        transferValueWord I, ⟨0⟩, transferValueWord I, transferToWord I, ⟨300⟩, sel]
      (balanceOfHashMem (transferToWord I)) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (transferSenderSlotI I)
        (transferDebitWord (transferS0 cA gh bl σ σ₀ g A I) I)) k' C' := by
  have rd2603 := evm_run rd1641 with [
    push2 ⟨1650⟩, swap2, swap1, push2 ⟨2603⟩, jump erc20_jd ]
  obtain ⟨k2, C2, rd1650₀⟩ := erc20RoutineCheckedAdd rd2603
    (by simpa [transferNewToNat] using hfit)
    erc20_jd (by simp only [List.length_cons, List.length_nil]; omega)
  have hnew :
      transferToBalanceWord (transferS0 cA gh bl σ σ₀ g A I) I + transferValueWord I =
        transferNewToWord (transferS0 cA gh bl σ σ₀ g A I) I := by
    apply u256_inj
    rw [uadd_toNat, Nat.mod_eq_of_lt (by simpa [transferNewToNat] using hfit)]
    unfold transferNewToWord
    rw [ulit_toNat' _ hfit]
    rfl
  have rd1650 := rd1650₀
  rw [hnew] at rd1650
  exact ⟨k2, C2, rd1650⟩

theorem transferCheckedAddOverflow {cA : Batteries.RBSet AccountAddress compare}
    {gh : BlockHeader} {bl : ProcessedBlocks} {σ σ₀ : AccountMap} {A : Substate}
    {I : ExecutionEnv} {g : Sat256} {sel : UInt256} {k C : ℕ}
    (hover : UInt256.size ≤ transferNewToNat (transferS0 cA gh bl σ σ₀ g A I) I)
    (rd1641 : RD erc20Bytecode I g (transferS0 cA gh bl σ σ₀ g A I) ⟨1641⟩
      [transferToBalanceWord (transferS0 cA gh bl σ σ₀ g A I) I, transferValueWord I,
        ⟨0⟩, transferToSlot I, transferValueWord I, ⟨0⟩, transferValueWord I,
        transferToWord I, ⟨300⟩, sel]
      (balanceOfHashMem (transferToWord I)) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (transferSenderSlotI I)
        (transferDebitWord (transferS0 cA gh bl σ σ₀ g A I) I)) k C) :
    RDrev erc20Bytecode g (transferS0 cA gh bl σ σ₀ g A I) := by
  have rd2603 := evm_run rd1641 with [
    push2 ⟨1650⟩, swap2, swap1, push2 ⟨2603⟩, jump erc20_jd ]
  exact erc20RoutineCheckedAdd_overflow rd2603
    (by simpa [transferNewToNat] using hover)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem transferCreditRecipient {cA : Batteries.RBSet AccountAddress compare}
    {gh : BlockHeader} {bl : ProcessedBlocks} {σ σ₀ : AccountMap} {A : Substate}
    {I : ExecutionEnv} {g : Sat256} {sel : UInt256} {k C : ℕ}
    (hperm : I.perm = true)
    (rd1650 : RD erc20Bytecode I g (transferS0 cA gh bl σ σ₀ g A I) ⟨1650⟩
      [transferNewToWord (transferS0 cA gh bl σ σ₀ g A I) I, ⟨0⟩, transferToSlot I,
        transferValueWord I, ⟨0⟩, transferValueWord I, transferToWord I, ⟨300⟩, sel]
      (balanceOfHashMem (transferToWord I)) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (transferSenderSlotI I)
        (transferDebitWord (transferS0 cA gh bl σ σ₀ g A I) I)) k C) :
    ∃ k' C', RD erc20Bytecode I g (transferS0 cA gh bl σ σ₀ g A I) ⟨1658⟩
      [⟨0⟩, transferValueWord I, transferToWord I, ⟨300⟩, sel]
      (balanceOfHashMem (transferToWord I)) (UInt256.ofNat 3)
      ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ (transferSenderSlotI I)
          (transferDebitWord (transferS0 cA gh bl σ σ₀ g A I) I))
        (transferToSlot I) (transferNewToWord (transferS0 cA gh bl σ σ₀ g A I) I)) k' C' := by
  have rd1656 := evm_run rd1650 with [
    jumpdest, swap3, pop, pop, dup2, swap1 ]
  obtain ⟨k3, C3, rd1656s⟩ := rd1656.sstore hperm (by decide) (by evm_ov)
  exact ⟨_, _, evm_run rd1656s with [ pop ]⟩

theorem transferReturnTrue {cA : Batteries.RBSet AccountAddress compare}
    {gh : BlockHeader} {bl : ProcessedBlocks} {σ σ₀ : AccountMap} {A : Substate}
    {I : ExecutionEnv} {g : Sat256} {sel : UInt256} {k C : ℕ}
    (hperm : I.perm = true)
    (hcanonTo : (transferToWord I).toNat < EVM.addressModulus)
    (rd1658 : RD erc20Bytecode I g (transferS0 cA gh bl σ σ₀ g A I) ⟨1658⟩
      [⟨0⟩, transferValueWord I, transferToWord I, ⟨300⟩, sel]
      (balanceOfHashMem (transferToWord I)) (UInt256.ofNat 3)
      ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ (transferSenderSlotI I)
          (transferDebitWord (transferS0 cA gh bl σ σ₀ g A I) I))
        (transferToSlot I) (transferNewToWord (transferS0 cA gh bl σ σ₀ g A I) I)) k C) :
    RDret erc20Bytecode g (transferS0 cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ (transferSenderSlotI I)
          (transferDebitWord (transferS0 cA gh bl σ σ₀ g A I) I))
        (transferToSlot I) (transferNewToWord (transferS0 cA gh bl σ σ₀ g A I) I))
      (UInt256.toByteArray (⟨1⟩ : UInt256)) := by
  have hsenderCleanL : UInt256.land erc20AddrMask (transferSenderWord I) = transferSenderWord I :=
    erc20AddrMask_clean_left (approveOwnerWord_canonical I)
  have htoCleanL : UInt256.land erc20AddrMask (transferToWord I) = transferToWord I :=
    erc20AddrMask_clean_left hcanonTo
  have rd1704₀ := evm_run rd1658 with [
    dup3, push20 erc20AddrMask, and, caller, push20 erc20AddrMask, and ]
  have rd1704 := rd1704₀
  rw [htoCleanL, hsenderCleanL] at rd1704
  have rd1737₀ := rd1704.pushConst transferTransferTopic (width := 32) (op := .PUSH32)
    (by decide) (by decide) (by evm_ov)
  have rd2073 := evm_run rd1737₀ with [
    dup5, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost
      (balanceOfHashMem_mload64 (transferToWord I))
      (by decide) (by evm_ov),
    push2 ⟨1750⟩, swap2, swap1, push2 ⟨2073⟩, jump erc20_jd ]
  obtain ⟨k1, C1, rd1750⟩ := erc20RoutineEncodeUint256FromMem
    (val := transferValueWord I) (ret := ⟨1750⟩)
    (R := [transferTransferTopic, transferSenderWord I, transferToWord I, ⟨0⟩,
      transferValueWord I, transferToWord I, ⟨300⟩, sel])
    rd2073 (by rfl) erc20_jd (by simp only [List.length_cons, List.length_nil]; omega)
  have rd1758 := evm_run rd1750 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost
      (balanceOfReturnMem_mload64 (transferToWord I) (transferValueWord I))
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1 ]
  have rd1759 := rd1758.log3 0 (UInt256.ofNat 5) (by decide) hperm mem_cost
    (by decide) (by evm_ov)
  have rd300 := evm_run rd1759 with [
    push1 ⟨1⟩, swap1, pop, swap3, swap2, pop, pop, jump erc20_jd ]
  have rd2033 := evm_run rd300 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost
      (balanceOfReturnMem_mload64 (transferToWord I) (transferValueWord I))
      (by decide) (by evm_ov),
    push2 ⟨313⟩, swap2, swap1, push2 ⟨2033⟩, jump erc20_jd ]
  obtain ⟨k2, C2, rd313⟩ := erc20RoutineEncodeBoolFromMem
    (val := (⟨1⟩ : UInt256)) (ret := ⟨313⟩) (R := [sel])
    rd2033
    (by
      rw [show UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256)) = ⟨1⟩ from by decide])
    erc20_jd (by simp only [List.length_cons, List.length_nil]; omega)
  exact evm_run rd313 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost
      (transferReturnMem_mload64 (transferToWord I) (transferValueWord I))
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray (⟨1⟩ : UInt256)) (by decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide, erc20SubRet32_toNat]
        exact transferReturnMem_read128 (transferToWord I) (transferValueWord I))
      (by evm_ov) ]

theorem erc20TransferBodySuffixCoupled {cA : Batteries.RBSet AccountAddress compare}
    {gh : BlockHeader} {bl : ProcessedBlocks} {σ σ₀ : AccountMap} {A : Substate}
    {I : ExecutionEnv} {g : Sat256} {sel : UInt256}
    (hwv : I.weiValue = ⟨0⟩) (hperm : I.perm = true)
    (hcanonTo : (transferToWord I).toNat < EVM.addressModulus) :
    ∀ st : CoupledState erc20Bytecode I g (transferS0 cA gh bl σ σ₀ g A I)
      (TransferDecodedRel (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) I g sel) ⟨1365⟩,
      CoupledState.refines st erc20Config transferTransition.body
        (transitionPost erc20Bytecode I g (transferS0 cA gh bl σ σ₀ g A I)
          transferTransition.returnType (fun _ _ _ => False)) := by
  intro st
  obtain ⟨hframe, hevm, hstack, hmem, haw, hrdata, hworldRel⟩ := st.hrel
  have rd1365 : RD erc20Bytecode I g (transferS0 cA gh bl σ σ₀ g A I) ⟨1365⟩
      [transferValueWord I, transferToWord I, ⟨300⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) st.k st.C := by
    have hRD := st.toRD hstack hmem haw hrdata
    simpa [hworldRel] using hRD
  obtain ⟨k1429, C1429, rd1429⟩ :=
    transferLoadSenderBalance (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) (sel := sel) rd1365
  let frame1429 : Frame :=
    { contract := erc20Contract,
      locals := transferStoreFromBalance (transferS0 cA gh bl σ σ₀ g A I) I }
  let evm1429 : State := transferS0 cA gh bl σ σ₀ g A I
  let st1429 :=
    st.stepRD frame1429 evm1429 rd1429
      (by simp [evm1429, worldOf, initState])
  change CoupledState.refines st erc20Config
    [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
      .letDecl "fromBalance" (some uint256) (.storage (balanceOfRef sender)),
      .require (.binary .ge (.var "fromBalance") (.var "value")),
      .assign (balanceOfRef sender) (.binary .sub (.var "fromBalance") (.var "value")),
      .letDecl "toBalance" (some uint256) (.storage (balanceOfRef (.var "to"))),
      .letDecl "newToBalance" (some uint256)
        (valueInUInt256 (.binary .add (.var "toBalance") (.var "value"))),
      .assign (balanceOfRef (.var "to")) (.var "newToBalance"),
      .return (.boolLit true) ]
    (transitionPost erc20Bytecode I g (transferS0 cA gh bl σ σ₀ g A I)
      transferTransition.returnType (fun _ _ _ => False))
  refine CoupledState.refines.requireTrue st ?_ ?_
  · rw [hframe, hevm]
    exact evalCallvalueEq_true (by simp [transferS0, initState, hwv])
  refine CoupledState.refines.letDeclAt (st := st) (st' := st1429)
    (value := transferFromBalanceValue (transferS0 cA gh bl σ σ₀ g A I)) ?_ ?_ ?_ ?_
  · rw [hframe, hevm]
    exact evalExpr_transfer_sender_balance (transferS0 cA gh bl σ σ₀ g A I) I
  · change st1429.frame =
      { st.frame with
        locals := st.frame.locals.insert "fromBalance"
          (transferFromBalanceValue (transferS0 cA gh bl σ σ₀ g A I)) }
    simp [st1429, CoupledState.stepRD, CoupledState.ofRD, CoupledState.reached,
      cursorOfRD, frame1429, evm1429, transferStoreFromBalance, hframe]
  · change st1429.evm = st.evm
    simp [st1429, CoupledState.stepRD, CoupledState.ofRD, CoupledState.reached,
      cursorOfRD, frame1429, evm1429, hevm]
  by_cases henough : (transferValueWord I).toNat ≤
      (transferFromBalanceWord (transferS0 cA gh bl σ σ₀ g A I)).toNat
  · by_cases hfit : transferNewToNat (transferS0 cA gh bl σ σ₀ g A I) I < UInt256.size
    · obtain ⟨k1493, C1493, rd1493⟩ :=
        transferBalanceRequireTrue (cA := cA) (gh := gh) (bl := bl) (σ := σ)
          (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel) henough rd1429
      obtain ⟨k1576, C1576, rd1576⟩ :=
        transferDebitSender (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
          (A := A) (I := I) (g := g) (sel := sel) hperm henough rd1493
      obtain ⟨k1641, C1641, rd1641⟩ :=
        transferLoadRecipientBalance (cA := cA) (gh := gh) (bl := bl) (σ := σ)
          (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel) hcanonTo henough rd1576
      obtain ⟨k1650, C1650, rd1650⟩ :=
        transferCheckedAdd (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
          (A := A) (I := I) (g := g) (sel := sel) hfit rd1641
      obtain ⟨k1658, C1658, rd1658⟩ :=
        transferCreditRecipient (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
          (A := A) (I := I) (g := g) (sel := sel) hperm rd1650
      have hret :=
        transferReturnTrue (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
          (A := A) (I := I) (g := g) (sel := sel) hperm hcanonTo rd1658
      let retFrame : Frame :=
        { contract := erc20Contract,
          locals := transferStoreNewToBalance (transferS0 cA gh bl σ σ₀ g A I) I }
      have hblock : ExecBlock erc20Config st1429.frame st1429.evm
          [ .require (.binary .ge (.var "fromBalance") (.var "value")),
            .assign (balanceOfRef sender) (.binary .sub (.var "fromBalance") (.var "value")),
            .letDecl "toBalance" (some uint256) (.storage (balanceOfRef (.var "to"))),
            .letDecl "newToBalance" (some uint256)
              (valueInUInt256 (.binary .add (.var "toBalance") (.var "value"))),
            .assign (balanceOfRef (.var "to")) (.var "newToBalance"),
            .return (.boolLit true) ]
          (ExecResult.returned retFrame
            (transferPostState (transferS0 cA gh bl σ σ₀ g A I) I)
            (some (.bool true))) := by
        simpa [st1429, CoupledState.stepRD, CoupledState.ofRD, CoupledState.reached,
          cursorOfRD, frame1429, evm1429, retFrame, transferS0] using
          transferSourceAfterFromBalanceReturns (transferS0 cA gh bl σ σ₀ g A I) I
            henough hfit
      refine ⟨_, hblock, ?_⟩
      exact ⟨UInt256.toByteArray (⟨1⟩ : UInt256), by
        simpa [worldOf, transferPostState, transferAfterDebitState, transferSenderSlot,
          transferSenderSlotI, transferS0, initState, erc20StorageStore_createdAccounts,
          erc20StorageStore_accountMap] using hret,
        returnEquiv_of_encode erc20BoolTrueReturnEncoding⟩
    · have hover : UInt256.size ≤ transferNewToNat (transferS0 cA gh bl σ σ₀ g A I) I := by
        omega
      obtain ⟨k1493, C1493, rd1493⟩ :=
        transferBalanceRequireTrue (cA := cA) (gh := gh) (bl := bl) (σ := σ)
          (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel) henough rd1429
      obtain ⟨k1576, C1576, rd1576⟩ :=
        transferDebitSender (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
          (A := A) (I := I) (g := g) (sel := sel) hperm henough rd1493
      obtain ⟨k1641, C1641, rd1641⟩ :=
        transferLoadRecipientBalance (cA := cA) (gh := gh) (bl := bl) (σ := σ)
          (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel) hcanonTo henough rd1576
      have hrev :=
        transferCheckedAddOverflow (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
          (A := A) (I := I) (g := g) (sel := sel) hover rd1641
      have hblock : ExecBlock erc20Config st1429.frame st1429.evm
          [ .require (.binary .ge (.var "fromBalance") (.var "value")),
            .assign (balanceOfRef sender) (.binary .sub (.var "fromBalance") (.var "value")),
            .letDecl "toBalance" (some uint256) (.storage (balanceOfRef (.var "to"))),
            .letDecl "newToBalance" (some uint256)
              (valueInUInt256 (.binary .add (.var "toBalance") (.var "value"))),
            .assign (balanceOfRef (.var "to")) (.var "newToBalance"),
          .return (.boolLit true) ] .reverted := by
        simpa [st1429, CoupledState.stepRD, CoupledState.ofRD, CoupledState.reached,
          cursorOfRD, frame1429, evm1429, transferS0] using
          transferSourceAfterFromBalanceReverts_overflow (transferS0 cA gh bl σ σ₀ g A I) I
            henough hover
      exact ⟨_, hblock, hrev⟩
  · have hlt : (transferFromBalanceWord (transferS0 cA gh bl σ σ₀ g A I)).toNat <
        (transferValueWord I).toNat := by
      omega
    have hrev :=
      transferBalanceRequireFalse (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) (sel := sel) hlt rd1429
    have hblock : ExecBlock erc20Config st1429.frame st1429.evm
        [ .require (.binary .ge (.var "fromBalance") (.var "value")),
          .assign (balanceOfRef sender) (.binary .sub (.var "fromBalance") (.var "value")),
          .letDecl "toBalance" (some uint256) (.storage (balanceOfRef (.var "to"))),
          .letDecl "newToBalance" (some uint256)
            (valueInUInt256 (.binary .add (.var "toBalance") (.var "value"))),
          .assign (balanceOfRef (.var "to")) (.var "newToBalance"),
          .return (.boolLit true) ] .reverted := by
      simpa [st1429, CoupledState.stepRD, CoupledState.ofRD, CoupledState.reached,
        cursorOfRD, frame1429, evm1429, transferS0] using
        transferSourceAfterFromBalanceReverts_insufficient (transferS0 cA gh bl σ σ₀ g A I) I
          hlt
    exact ⟨_, hblock, hrev⟩

theorem erc20TransferBodyCoreCoupled {cA gh bl σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = erc20Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : ((⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hreach : ∃ k C, RD erc20Bytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨274⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    runtimeEquivalenceFor erc20Config erc20Contract cA gh bl σ σ₀ g A I := by
  have hsz4 := erc20TransferSelector_size hsel
  have hd := erc20Dispatch_transfer (cd := I.calldata) hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanonTo : (transferToWord I).toNat < EVM.addressModulus
      · have hdec := erc20Decode_transfer_ok (I := I) hsz68 hbig hcanonTo
        obtain ⟨k1365, C1365, rd1365⟩ :=
          erc20TransferX_decoded (cA := cA) (gh := gh) (bl := bl)
            (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) (sel := sel)
            hsz68 hsize hbig hcanonTo hreach
        let st1365 :=
          transferDecodedState (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
            (A := A) (I := I) (g := Sat256.ofUInt256 g) (sel := sel) rd1365
        obtain ⟨result, hblock, hpost⟩ :=
          erc20TransferBodySuffixCoupled (cA := cA) (gh := gh) (bl := bl) (σ := σ)
            (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) (sel := sel)
            hwv hperm hcanonTo st1365
        cases result with
        | ok frame' evm' =>
            obtain ⟨cur', k', C', hRD', hw', hfalse⟩ := hpost
            exact hfalse.elim
        | returned frame' evm' rv =>
            obtain ⟨o, hret, henc⟩ := hpost
            exact hret.reEquivExecutionGen hcode hd hdec
              (ExecFuncBody.execBlockRet hblock) rfl henc
        | reverted =>
            exact hpost.reEquivExecutionRevert hcode hd hdec
              (ExecFuncBody.execBlockRevert hblock)
        | «break» frame' evm' => exact hpost.elim
        | «continue» frame' evm' => exact hpost.elim
      · have hdec := erc20Decode_transfer_none_noncanon (I := I) hsz68 hbig hcanonTo
        have hnc : UInt256.eq (transferToWord I)
            (UInt256.land (transferToWord I) erc20AddrMask) = ⟨0⟩ :=
          erc20Ueq_zero_of_ne (fun he => hcanonTo (erc20Word_canonical_of_clean he))
        exact (erc20TransferX_noncanon_to (g := Sat256.ofUInt256 g)
            hsz68 hsize hbig hnc hreach)
          |>.reEquivDecodingFailed hcode hd hdec
    · have hbigge : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      have hdec := erc20Decode_transfer_none_huge (I := I) hbigge
      exact (erc20TransferX_hugearg (g := Sat256.ofUInt256 g) hsz4 hsize hbigge hreach)
        |>.reEquivDecodingFailed hcode hd hdec
  · have hshort : I.calldata.size < 68 := by omega
    have hdec := erc20Decode_transfer_none_short (I := I) hsz4 hshort
    exact (erc20TransferX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

end ERC20Coupled
