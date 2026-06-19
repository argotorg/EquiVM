import Examples.ERC20Coupled.Standalone.TransferFromBase
import Reasoning.Refinement

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000

namespace ERC20Coupled

open ERC20Standalone

abbrev transferFromS0 (cA : Batteries.RBSet AccountAddress compare) (gh : BlockHeader)
    (bl : ProcessedBlocks) (σ σ₀ : AccountMap) (g : Sat256) (A : Substate)
    (I : ExecutionEnv) : State :=
  initState cA gh bl σ σ₀ g A I

def TransferFromDecodedRel {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader}
    {bl : ProcessedBlocks} {σ σ₀ : AccountMap} {A : Substate}
    (I : ExecutionEnv) (g : Sat256) (sel : UInt256) : StateRel :=
  fun cur frame evm =>
    frame = { contract := erc20Contract, locals := transferFromStore I } ∧
    evm = transferFromS0 cA gh bl σ σ₀ g A I ∧
    cur.stack = [transferFromValueWord I, transferFromToWord I, transferFromFromWord I, ⟨204⟩, sel] ∧
    cur.mem = solcFreePtrMem ∧
    cur.aw = UInt256.ofNat 3 ∧
    cur.rdata = ByteArray.empty ∧
    cur.world = (cA, σ)

/-- Current-cursor segment: decoded `transferFrom` entry loads `allowance[from][msg.sender]`. -/
theorem transferFromLoadAllowance {cA : Batteries.RBSet AccountAddress compare}
    {gh : BlockHeader} {bl : ProcessedBlocks} {σ σ₀ : AccountMap} {A : Substate}
    {I : ExecutionEnv} {g : Sat256} {sel : UInt256} {k C : ℕ}
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (rd613 : RD erc20Bytecode I g (transferFromS0 cA gh bl σ σ₀ g A I) ⟨613⟩
      [transferFromValueWord I, transferFromToWord I, transferFromFromWord I, ⟨204⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD erc20Bytecode I g (transferFromS0 cA gh bl σ σ₀ g A I) ⟨737⟩
      [transferFromCurrentAllowanceWord (transferFromS0 cA gh bl σ σ₀ g A I) I, ⟨0⟩, ⟨0⟩,
        transferFromValueWord I, transferFromToWord I, transferFromFromWord I, ⟨204⟩, sel]
      (allowanceOuterHashMem (transferFromFromWord I) (transferFromSenderWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hfromCleanL : UInt256.land erc20AddrMask (transferFromFromWord I) = transferFromFromWord I :=
    erc20AddrMask_clean_left hcanonFrom
  have hsenderCleanL :
      UInt256.land erc20AddrMask (transferFromSenderWord I) = transferFromSenderWord I :=
    erc20AddrMask_clean_left (transferFromSenderWord_canonical I)
  have hslot := transferFromAllowanceKeccakSlot I hcanonFrom
  have rd663₀ := evm_run rd613 with [
    jumpdest, push0, push0, push1 ⟨1⟩, push0, dup7, push20 erc20AddrMask, and,
    push20 erc20AddrMask, and ]
  have rd663 := rd663₀
  rw [hfromCleanL, hfromCleanL] at rd663
  have rd676 := evm_run rd663 with [
    dup2,
    raw mstore 0 (approveInnerOwnerMem (transferFromFromWord I)) (UInt256.ofNat 3)
      (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, add, swap1, dup2,
    raw mstore 0 (allowanceInnerHashMem (transferFromFromWord I)) (UInt256.ofNat 3)
      (by decide) mem_cost
      (approveInnerOwnerMem_writeSlot (transferFromFromWord I)) (by decide) (by evm_ov),
    push1 ⟨32⟩, add, push0,
    raw keccak256 0 (allowanceInnerSlot (transferFromFromWord I)) (UInt256.ofNat 3)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov) ]
  have rd722₀ := evm_run rd676 with [
    push0, caller, push20 erc20AddrMask, and, push20 erc20AddrMask, and ]
  have rd722 := rd722₀
  rw [hsenderCleanL, hsenderCleanL] at rd722
  have rd735 := evm_run rd722 with [
    dup2,
    raw mstore 0
      (approveOuterSpenderMem (transferFromFromWord I) (transferFromSenderWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, add, swap1, dup2,
    raw mstore 0
      (allowanceOuterHashMem (transferFromFromWord I) (transferFromSenderWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (approveOuterSpenderMem_writeSlot (transferFromFromWord I) (transferFromSenderWord I))
      (by decide) (by evm_ov),
    push1 ⟨32⟩, add, push0,
    raw keccak256 0 (transferFromAllowanceSlotI I) (UInt256.ofNat 3)
      (by decide) mem_cost hslot (by decide) (by evm_ov) ]
  obtain ⟨k1, C1, rd736₀⟩ := rd735.sload (by decide) (by evm_ov)
  refine ⟨k1, C1, ?_⟩
  simpa [transferFromCurrentAllowanceWord, transferFromAllowanceSlot,
    transferFromAllowanceSlotI, transferFromSenderWord, transferFromS0, initState,
    Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage, transferFromSender_ofNat]
    using rd736₀

theorem transferFromAllowanceRequireTrue {cA : Batteries.RBSet AccountAddress compare}
    {gh : BlockHeader} {bl : ProcessedBlocks} {σ σ₀ : AccountMap} {A : Substate}
    {I : ExecutionEnv} {g : Sat256} {sel : UInt256} {k C : ℕ}
    (hallowance : (transferFromValueWord I).toNat ≤
      (transferFromCurrentAllowanceWord (transferFromS0 cA gh bl σ σ₀ g A I) I).toNat)
    (rd737 : RD erc20Bytecode I g (transferFromS0 cA gh bl σ σ₀ g A I) ⟨737⟩
      [transferFromCurrentAllowanceWord (transferFromS0 cA gh bl σ σ₀ g A I) I, ⟨0⟩, ⟨0⟩,
        transferFromValueWord I, transferFromToWord I, transferFromFromWord I, ⟨204⟩, sel]
      (allowanceOuterHashMem (transferFromFromWord I) (transferFromSenderWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD erc20Bytecode I g (transferFromS0 cA gh bl σ σ₀ g A I) ⟨805⟩
      [transferFromCurrentAllowanceWord (transferFromS0 cA gh bl σ σ₀ g A I) I, ⟨0⟩,
        transferFromValueWord I, transferFromToWord I, transferFromFromWord I, ⟨204⟩, sel]
      (allowanceOuterHashMem (transferFromFromWord I) (transferFromSenderWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hlt : UInt256.lt
      (transferFromCurrentAllowanceWord (transferFromS0 cA gh bl σ σ₀ g A I) I)
      (transferFromValueWord I) = ⟨0⟩ := ult_zero hallowance
  exact ⟨_, _, evm_run rd737 with [
    swap1, pop, dup3, dup2, lt, iszero,
    push2 ⟨805⟩, jumpiT (by rw [hlt]; decide) erc20_jd ]⟩

theorem transferFromAllowanceRequireFalse {cA : Batteries.RBSet AccountAddress compare}
    {gh : BlockHeader} {bl : ProcessedBlocks} {σ σ₀ : AccountMap} {A : Substate}
    {I : ExecutionEnv} {g : Sat256} {sel : UInt256} {k C : ℕ}
    (hlt : (transferFromCurrentAllowanceWord (transferFromS0 cA gh bl σ σ₀ g A I) I).toNat <
      (transferFromValueWord I).toNat)
    (rd737 : RD erc20Bytecode I g (transferFromS0 cA gh bl σ σ₀ g A I) ⟨737⟩
      [transferFromCurrentAllowanceWord (transferFromS0 cA gh bl σ σ₀ g A I) I, ⟨0⟩, ⟨0⟩,
        transferFromValueWord I, transferFromToWord I, transferFromFromWord I, ⟨204⟩, sel]
      (allowanceOuterHashMem (transferFromFromWord I) (transferFromSenderWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc20Bytecode g (transferFromS0 cA gh bl σ σ₀ g A I) := by
  have hltw : UInt256.lt
      (transferFromCurrentAllowanceWord (transferFromS0 cA gh bl σ σ₀ g A I) I)
      (transferFromValueWord I) = ⟨1⟩ := ult_one hlt
  have rd742₀ := evm_run rd737 with [ swap1, pop, dup3, dup2, lt ]
  have rd742 := rd742₀
  rw [hltw] at rd742
  have rd743₀ := evm_run rd742 with [ iszero ]
  have rd743 := rd743₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd743
  have rd747 := evm_run rd743 with [
    push2 ⟨805⟩, jumpiNT (by decide) ]
  have rd750 := evm_run rd747 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost
      (allowanceOuterHashMem_mload64 (transferFromFromWord I) (transferFromSenderWord I))
      (by decide) (by evm_ov) ]
  have rd783 := rd750.pushConst transferErrorSelector (width := 32) (op := .PUSH32)
    (by decide) (by decide) (by evm_ov)
  have rd785 := evm_run rd783 with [
    dup2,
    raw mstore 6
      (transferFromInsufficientAllowanceSelectorMem (transferFromFromWord I)
        (transferFromSenderWord I))
      (UInt256.ofNat 5) (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov) ]
  have rd2373 := evm_run rd785 with [
    push1 ⟨4⟩, add, push2 ⟨796⟩, swap1, push2 ⟨2373⟩, jump erc20_jd ]
  have rd2388 := evm_run rd2373 with [
    jumpdest, push0, push1 ⟨32⟩, dup3, add, swap1, pop, dup2, dup2, sub,
    push0, dup4, add,
    raw mstore 3
      (transferFromInsufficientAllowanceOffsetMem (transferFromFromWord I)
        (transferFromSenderWord I))
      (UInt256.ofNat 6) (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov) ]
  have rd2339 := evm_run rd2388 with [
    push2 ⟨2396⟩, dup2, push2 ⟨2339⟩, jump erc20_jd ]
  have rd2283 := evm_run rd2339 with [
    jumpdest, push0, push2 ⟨2351⟩, push1 ⟨29⟩, dup4, push2 ⟨2283⟩,
    jump erc20_jd ]
  have rd2351 := evm_run rd2283 with [
    jumpdest, push0, dup3, dup3,
    raw mstore 3
      (transferFromInsufficientAllowanceLengthMem (transferFromFromWord I)
        (transferFromSenderWord I))
      (UInt256.ofNat 7) (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, dup3, add, swap1, pop, swap3, swap2, pop, pop,
    jump erc20_jd ]
  have rd2299 := evm_run rd2351 with [
    jumpdest, swap2, pop, push2 ⟨2362⟩, dup3, push2 ⟨2299⟩, jump erc20_jd ]
  have rd2300 := evm_run rd2299 with [ jumpdest ]
  have rd2333 := rd2300.pushConst transferFromInsufficientAllowanceWord
    (width := 32) (op := .PUSH32) (by decide) (by decide) (by evm_ov)
  have rd2362 := evm_run rd2333 with [
    push0, dup3, add,
    raw mstore 3
      (transferFromInsufficientAllowanceStringMem (transferFromFromWord I)
        (transferFromSenderWord I))
      (UInt256.ofNat 8) (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    pop, jump erc20_jd ]
  have rd2396 := evm_run rd2362 with [
    jumpdest, push1 ⟨32⟩, dup3, add, swap1, pop, swap2, swap1, pop,
    jump erc20_jd ]
  have rd796ret := evm_run rd2396 with [
    jumpdest, swap1, pop, swap2, swap1, pop, jump erc20_jd ]
  have rd796 := evm_run rd796ret with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by decide)
      mem_cost
      (transferFromInsufficientAllowanceStringMem_mload64 (transferFromFromWord I)
        (transferFromSenderWord I))
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1 ]
  exact rd796.rev 0 (by decide) mem_cost (by evm_ov)

theorem transferFromLoadFromBalance {cA : Batteries.RBSet AccountAddress compare}
    {gh : BlockHeader} {bl : ProcessedBlocks} {σ σ₀ : AccountMap} {A : Substate}
    {I : ExecutionEnv} {g : Sat256} {sel : UInt256} {k C : ℕ}
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (rd805 : RD erc20Bytecode I g (transferFromS0 cA gh bl σ σ₀ g A I) ⟨805⟩
      [transferFromCurrentAllowanceWord (transferFromS0 cA gh bl σ σ₀ g A I) I, ⟨0⟩,
        transferFromValueWord I, transferFromToWord I, transferFromFromWord I, ⟨204⟩, sel]
      (allowanceOuterHashMem (transferFromFromWord I) (transferFromSenderWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD erc20Bytecode I g (transferFromS0 cA gh bl σ σ₀ g A I) ⟨868⟩
      [transferFromFromBalanceWord (transferFromS0 cA gh bl σ σ₀ g A I) I,
        transferFromValueWord I,
        transferFromCurrentAllowanceWord (transferFromS0 cA gh bl σ σ₀ g A I) I, ⟨0⟩,
        transferFromValueWord I, transferFromToWord I, transferFromFromWord I, ⟨204⟩, sel]
      (balanceOfHashMem (transferFromFromWord I)) (UInt256.ofNat 3) ByteArray.empty (cA, σ)
      k' C' := by
  have hfromCleanL : UInt256.land erc20AddrMask (transferFromFromWord I) = transferFromFromWord I :=
    erc20AddrMask_clean_left hcanonFrom
  have hslot := transferFromFromKeccakSlot I hcanonFrom
  have rd854₀ := evm_run rd805 with [
    jumpdest, dup3, push0, push0, dup8, push20 erc20AddrMask, and,
    push20 erc20AddrMask, and ]
  have rd854 := rd854₀
  rw [hfromCleanL, hfromCleanL] at rd854
  have rd867 := evm_run rd854 with [
    dup2,
    raw mstore 0
      ((UInt256.toByteArray (transferFromFromWord I)).write 0
        (allowanceOuterHashMem (transferFromFromWord I) (transferFromSenderWord I)) 0 32)
      (UInt256.ofNat 3) (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, add, swap1, dup2,
    raw mstore 0 (balanceOfHashMem (transferFromFromWord I)) (UInt256.ofNat 3)
      (by decide) mem_cost
      (allowanceOuterHashMem_writeBalanceSlot (transferFromFromWord I) (transferFromSenderWord I))
      (by decide) (by evm_ov),
    push1 ⟨32⟩, add, push0,
    raw keccak256 0 (transferFromFromSlot I) (UInt256.ofNat 3)
      (by decide) mem_cost hslot (by decide) (by evm_ov) ]
  obtain ⟨k1, C1, rd868₀⟩ := rd867.sload (by decide) (by evm_ov)
  refine ⟨k1, C1, ?_⟩
  simpa [transferFromFromBalanceWord, transferFromFromSlot, transferFromS0, initState,
    Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
    using rd868₀

theorem transferFromBalanceRequireTrue {cA : Batteries.RBSet AccountAddress compare}
    {gh : BlockHeader} {bl : ProcessedBlocks} {σ σ₀ : AccountMap} {A : Substate}
    {I : ExecutionEnv} {g : Sat256} {sel : UInt256} {k C : ℕ}
    (hbalance : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord (transferFromS0 cA gh bl σ σ₀ g A I) I).toNat)
    (rd868 : RD erc20Bytecode I g (transferFromS0 cA gh bl σ σ₀ g A I) ⟨868⟩
      [transferFromFromBalanceWord (transferFromS0 cA gh bl σ σ₀ g A I) I,
        transferFromValueWord I,
        transferFromCurrentAllowanceWord (transferFromS0 cA gh bl σ σ₀ g A I) I, ⟨0⟩,
        transferFromValueWord I, transferFromToWord I, transferFromFromWord I, ⟨204⟩, sel]
      (balanceOfHashMem (transferFromFromWord I)) (UInt256.ofNat 3) ByteArray.empty (cA, σ)
      k C) :
    ∃ k' C', RD erc20Bytecode I g (transferFromS0 cA gh bl σ σ₀ g A I) ⟨932⟩
      [transferFromCurrentAllowanceWord (transferFromS0 cA gh bl σ σ₀ g A I) I, ⟨0⟩,
        transferFromValueWord I, transferFromToWord I, transferFromFromWord I, ⟨204⟩, sel]
      (balanceOfHashMem (transferFromFromWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hlt : UInt256.lt
      (transferFromFromBalanceWord (transferFromS0 cA gh bl σ σ₀ g A I) I)
      (transferFromValueWord I) = ⟨0⟩ := ult_zero hbalance
  exact ⟨_, _, evm_run rd868 with [
    lt, iszero, push2 ⟨932⟩, jumpiT (by rw [hlt]; decide) erc20_jd ]⟩

theorem transferFromBalanceRequireFalse {cA : Batteries.RBSet AccountAddress compare}
    {gh : BlockHeader} {bl : ProcessedBlocks} {σ σ₀ : AccountMap} {A : Substate}
    {I : ExecutionEnv} {g : Sat256} {sel : UInt256} {k C : ℕ}
    (hlt : (transferFromFromBalanceWord (transferFromS0 cA gh bl σ σ₀ g A I) I).toNat <
      (transferFromValueWord I).toNat)
    (rd868 : RD erc20Bytecode I g (transferFromS0 cA gh bl σ σ₀ g A I) ⟨868⟩
      [transferFromFromBalanceWord (transferFromS0 cA gh bl σ σ₀ g A I) I,
        transferFromValueWord I,
        transferFromCurrentAllowanceWord (transferFromS0 cA gh bl σ σ₀ g A I) I, ⟨0⟩,
        transferFromValueWord I, transferFromToWord I, transferFromFromWord I, ⟨204⟩, sel]
      (balanceOfHashMem (transferFromFromWord I)) (UInt256.ofNat 3) ByteArray.empty (cA, σ)
      k C) :
    RDrev erc20Bytecode g (transferFromS0 cA gh bl σ σ₀ g A I) := by
  have hltw : UInt256.lt
      (transferFromFromBalanceWord (transferFromS0 cA gh bl σ σ₀ g A I) I)
      (transferFromValueWord I) = ⟨1⟩ := ult_one hlt
  have rd869₀ := evm_run rd868 with [ lt ]
  have rd869 := rd869₀
  rw [hltw] at rd869
  have rd870₀ := evm_run rd869 with [ iszero ]
  have rd870 := rd870₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd870
  have rd874 := evm_run rd870 with [
    push2 ⟨932⟩, jumpiNT (by decide) ]
  have rd877 := evm_run rd874 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost
      (balanceOfHashMem_mload64 (transferFromFromWord I))
      (by decide) (by evm_ov) ]
  have rd910 := rd877.pushConst transferErrorSelector (width := 32) (op := .PUSH32)
    (by decide) (by decide) (by evm_ov)
  have rd912 := evm_run rd910 with [
    dup2,
    raw mstore 6 (transferInsufficientSelectorMem (transferFromFromWord I)) (UInt256.ofNat 5)
      (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov) ]
  have rd2477 := evm_run rd912 with [
    push1 ⟨4⟩, add, push2 ⟨923⟩, swap1, push2 ⟨2477⟩, jump erc20_jd ]
  have rd2492 := evm_run rd2477 with [
    jumpdest, push0, push1 ⟨32⟩, dup3, add, swap1, pop, dup2, dup2, sub,
    push0, dup4, add,
    raw mstore 3 (transferInsufficientOffsetMem (transferFromFromWord I)) (UInt256.ofNat 6)
      (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov) ]
  have rd2443 := evm_run rd2492 with [
    push2 ⟨2500⟩, dup2, push2 ⟨2443⟩, jump erc20_jd ]
  have rd2283 := evm_run rd2443 with [
    jumpdest, push0, push2 ⟨2455⟩, push1 ⟨27⟩, dup4, push2 ⟨2283⟩,
    jump erc20_jd ]
  have rd2455 := evm_run rd2283 with [
    jumpdest, push0, dup3, dup3,
    raw mstore 3 (transferInsufficientLengthMem (transferFromFromWord I)) (UInt256.ofNat 7)
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
    raw mstore 3 (transferInsufficientStringMem (transferFromFromWord I)) (UInt256.ofNat 8)
      (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    pop, jump erc20_jd ]
  have rd2500 := evm_run rd2466 with [
    jumpdest, push1 ⟨32⟩, dup3, add, swap1, pop, swap2, swap1, pop,
    jump erc20_jd ]
  have rd923ret := evm_run rd2500 with [
    jumpdest, swap1, pop, swap2, swap1, pop, jump erc20_jd ]
  have rd923 := evm_run rd923ret with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by decide)
      mem_cost
      (transferInsufficientStringMem_mload64 (transferFromFromWord I))
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1 ]
  exact rd923.rev 0 (by decide) mem_cost (by evm_ov)

theorem transferFromStoreAllowance {cA : Batteries.RBSet AccountAddress compare}
    {gh : BlockHeader} {bl : ProcessedBlocks} {σ σ₀ : AccountMap} {A : Substate}
    {I : ExecutionEnv} {g : Sat256} {sel : UInt256} {k C : ℕ}
    (hperm : I.perm = true)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hallowance : (transferFromValueWord I).toNat ≤
      (transferFromCurrentAllowanceWord (transferFromS0 cA gh bl σ σ₀ g A I) I).toNat)
    (rd932 : RD erc20Bytecode I g (transferFromS0 cA gh bl σ σ₀ g A I) ⟨932⟩
      [transferFromCurrentAllowanceWord (transferFromS0 cA gh bl σ σ₀ g A I) I, ⟨0⟩,
        transferFromValueWord I, transferFromToWord I, transferFromFromWord I, ⟨204⟩, sel]
      (balanceOfHashMem (transferFromFromWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD erc20Bytecode I g (transferFromS0 cA gh bl σ σ₀ g A I) ⟨1069⟩
      [transferFromCurrentAllowanceWord (transferFromS0 cA gh bl σ σ₀ g A I) I, ⟨0⟩,
        transferFromValueWord I, transferFromToWord I, transferFromFromWord I, ⟨204⟩, sel]
      (allowanceOuterHashMem (transferFromFromWord I) (transferFromSenderWord I))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (transferFromAllowanceSlotI I)
        (transferFromAllowanceDebitWord (transferFromS0 cA gh bl σ σ₀ g A I) I)) k' C' := by
  have rd2552 := evm_run rd932 with [
    jumpdest, dup3, dup2, push2 ⟨944⟩, swap2, swap1, push2 ⟨2552⟩, jump erc20_jd ]
  obtain ⟨k1, C1, rd944₀⟩ := erc20RoutineCheckedSub rd2552 hallowance erc20_jd
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hdebit :
      UInt256.sub
          (transferFromCurrentAllowanceWord (transferFromS0 cA gh bl σ σ₀ g A I) I)
          (transferFromValueWord I) =
        transferFromAllowanceDebitWord (transferFromS0 cA gh bl σ σ₀ g A I) I := by
    apply u256_inj
    rw [usub_toNat hallowance]
    unfold transferFromAllowanceDebitWord
    rw [ulit_toNat' _ (lt_of_le_of_lt
      (Nat.sub_le
        (transferFromCurrentAllowanceWord (transferFromS0 cA gh bl σ σ₀ g A I) I).toNat
        (transferFromValueWord I).toNat)
      (transferFromCurrentAllowanceWord (transferFromS0 cA gh bl σ σ₀ g A I) I).val.isLt)]
  have rd944 := rd944₀
  rw [hdebit] at rd944
  have hfromCleanL : UInt256.land erc20AddrMask (transferFromFromWord I) = transferFromFromWord I :=
    erc20AddrMask_clean_left hcanonFrom
  have hsenderCleanL :
      UInt256.land erc20AddrMask (transferFromSenderWord I) = transferFromSenderWord I :=
    erc20AddrMask_clean_left (transferFromSenderWord_canonical I)
  have hslot := transferFromAllowanceKeccakSlot I hcanonFrom
  have rd993₀ := evm_run rd944 with [
    jumpdest, push1 ⟨1⟩, push0, dup8, push20 erc20AddrMask, and,
    push20 erc20AddrMask, and ]
  have rd993 := rd993₀
  rw [hfromCleanL, hfromCleanL] at rd993
  have rd1006 := evm_run rd993 with [
    dup2,
    raw mstore 0 (balanceOfHashMem (transferFromFromWord I)) (UInt256.ofNat 3)
      (by decide) mem_cost
      (balanceOfHashMem_writeOwner_self (transferFromFromWord I)) (by decide) (by evm_ov),
    push1 ⟨32⟩, add, swap1, dup2,
    raw mstore 0 (allowanceInnerHashMem (transferFromFromWord I)) (UInt256.ofNat 3)
      (by decide) mem_cost
      (balanceOfHashMem_writeAllowanceSlot (transferFromFromWord I))
      (by decide) (by evm_ov),
    push1 ⟨32⟩, add, push0,
    raw keccak256 0 (allowanceInnerSlot (transferFromFromWord I)) (UInt256.ofNat 3)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov) ]
  have rd1052₀ := evm_run rd1006 with [
    push0, caller, push20 erc20AddrMask, and, push20 erc20AddrMask, and ]
  have rd1052 := rd1052₀
  rw [hsenderCleanL, hsenderCleanL] at rd1052
  have rd1065 := evm_run rd1052 with [
    dup2,
    raw mstore 0
      (approveOuterSpenderMem (transferFromFromWord I) (transferFromSenderWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, add, swap1, dup2,
    raw mstore 0
      (allowanceOuterHashMem (transferFromFromWord I) (transferFromSenderWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (approveOuterSpenderMem_writeSlot (transferFromFromWord I) (transferFromSenderWord I))
      (by decide) (by evm_ov),
    push1 ⟨32⟩, add, push0,
    raw keccak256 0 (transferFromAllowanceSlotI I) (UInt256.ofNat 3)
      (by decide) mem_cost hslot (by decide) (by evm_ov) ]
  have rd1067 := evm_run rd1065 with [ dup2, swap1 ]
  obtain ⟨k2, C2, rd1067s⟩ := rd1067.sstore hperm (by decide) (by evm_ov)
  exact ⟨_, _, evm_run rd1067s with [ pop ]⟩

theorem transferFromStoreFromBalance {cA : Batteries.RBSet AccountAddress compare}
    {gh : BlockHeader} {bl : ProcessedBlocks} {σ σ₀ : AccountMap} {A : Substate}
    {I : ExecutionEnv} {g : Sat256} {sel : UInt256} {k C : ℕ}
    (hperm : I.perm = true)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hbalance : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord (transferFromS0 cA gh bl σ σ₀ g A I) I).toNat)
    (rd1069 : RD erc20Bytecode I g (transferFromS0 cA gh bl σ σ₀ g A I) ⟨1069⟩
      [transferFromCurrentAllowanceWord (transferFromS0 cA gh bl σ σ₀ g A I) I, ⟨0⟩,
        transferFromValueWord I, transferFromToWord I, transferFromFromWord I, ⟨204⟩, sel]
      (allowanceOuterHashMem (transferFromFromWord I) (transferFromSenderWord I))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (transferFromAllowanceSlotI I)
        (transferFromAllowanceDebitWord (transferFromS0 cA gh bl σ σ₀ g A I) I)) k C) :
    ∃ k' C', RD erc20Bytecode I g (transferFromS0 cA gh bl σ σ₀ g A I) ⟨1151⟩
      [transferFromCurrentAllowanceWord (transferFromS0 cA gh bl σ σ₀ g A I) I, ⟨0⟩,
        transferFromValueWord I, transferFromToWord I, transferFromFromWord I, ⟨204⟩, sel]
      (balanceOfHashMem (transferFromFromWord I))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ (transferFromAllowanceSlotI I)
          (transferFromAllowanceDebitWord (transferFromS0 cA gh bl σ σ₀ g A I) I))
        (transferFromFromSlot I)
        (transferFromBalanceDebitWord (transferFromS0 cA gh bl σ σ₀ g A I) I)) k' C' := by
  have hfromCleanL : UInt256.land erc20AddrMask (transferFromFromWord I) = transferFromFromWord I :=
    erc20AddrMask_clean_left hcanonFrom
  have hslot := transferFromFromKeccakSlot I hcanonFrom
  have rd1117₀ := evm_run rd1069 with [
    dup3, push0, push0, dup8, push20 erc20AddrMask, and,
    push20 erc20AddrMask, and ]
  have rd1117 := rd1117₀
  rw [hfromCleanL, hfromCleanL] at rd1117
  have rd1130 := evm_run rd1117 with [
    dup2,
    raw mstore 0
      ((UInt256.toByteArray (transferFromFromWord I)).write 0
        (allowanceOuterHashMem (transferFromFromWord I) (transferFromSenderWord I)) 0 32)
      (UInt256.ofNat 3) (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, add, swap1, dup2,
    raw mstore 0 (balanceOfHashMem (transferFromFromWord I)) (UInt256.ofNat 3)
      (by decide) mem_cost
      (allowanceOuterHashMem_writeBalanceSlot (transferFromFromWord I) (transferFromSenderWord I))
      (by decide) (by evm_ov),
    push1 ⟨32⟩, add, push0,
    raw keccak256 0 (transferFromFromSlot I) (UInt256.ofNat 3)
      (by decide) mem_cost hslot (by decide) (by evm_ov),
    push0, dup3, dup3 ]
  obtain ⟨k1, C1, rd1134₀⟩ := rd1130.sload (by decide) (by evm_ov)
  have hload := transferFromAllowanceStore_preservesFromBalance σ I
    (transferFromAllowanceDebitWord (transferFromS0 cA gh bl σ σ₀ g A I) I)
  have rd1134 : RD erc20Bytecode I g (transferFromS0 cA gh bl σ σ₀ g A I) ⟨1134⟩
      [transferFromFromBalanceWord (transferFromS0 cA gh bl σ σ₀ g A I) I,
        transferFromValueWord I, ⟨0⟩, transferFromFromSlot I, transferFromValueWord I,
        transferFromCurrentAllowanceWord (transferFromS0 cA gh bl σ σ₀ g A I) I, ⟨0⟩,
        transferFromValueWord I, transferFromToWord I, transferFromFromWord I, ⟨204⟩, sel]
      (balanceOfHashMem (transferFromFromWord I)) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (transferFromAllowanceSlotI I)
        (transferFromAllowanceDebitWord (transferFromS0 cA gh bl σ σ₀ g A I) I)) k1 C1 := by
    have rd1134₁ := rd1134₀
    rw [hload] at rd1134₁
    simpa [transferFromFromBalanceWord, transferFromFromSlot, transferFromS0, initState,
      Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
      using rd1134₁
  have rd2552 := evm_run rd1134 with [
    push2 ⟨1143⟩, swap2, swap1, push2 ⟨2552⟩, jump erc20_jd ]
  obtain ⟨k2, C2, rd1143₀⟩ := erc20RoutineCheckedSub rd2552 hbalance erc20_jd
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hdebit :
      UInt256.sub
          (transferFromFromBalanceWord (transferFromS0 cA gh bl σ σ₀ g A I) I)
          (transferFromValueWord I) =
        transferFromBalanceDebitWord (transferFromS0 cA gh bl σ σ₀ g A I) I := by
    apply u256_inj
    rw [usub_toNat hbalance]
    unfold transferFromBalanceDebitWord
    rw [ulit_toNat' _ (lt_of_le_of_lt
      (Nat.sub_le
        (transferFromFromBalanceWord (transferFromS0 cA gh bl σ σ₀ g A I) I).toNat
        (transferFromValueWord I).toNat)
      (transferFromFromBalanceWord (transferFromS0 cA gh bl σ σ₀ g A I) I).val.isLt)]
  have rd1143 := rd1143₀
  rw [hdebit] at rd1143
  have rd1149 := evm_run rd1143 with [
    jumpdest, swap3, pop, pop, dup2, swap1 ]
  obtain ⟨k3, C3, rd1149s⟩ := rd1149.sstore hperm (by decide) (by evm_ov)
  exact ⟨_, _, evm_run rd1149s with [ pop ]⟩

theorem transferFromStoreToBalance {cA : Batteries.RBSet AccountAddress compare}
    {gh : BlockHeader} {bl : ProcessedBlocks} {σ σ₀ : AccountMap} {A : Substate}
    {I : ExecutionEnv} {g : Sat256} {sel : UInt256} {k C : ℕ}
    (hperm : I.perm = true)
    (hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus)
    (hfit : transferFromNewToNat (transferFromS0 cA gh bl σ σ₀ g A I) I < UInt256.size)
    (rd1151 : RD erc20Bytecode I g (transferFromS0 cA gh bl σ σ₀ g A I) ⟨1151⟩
      [transferFromCurrentAllowanceWord (transferFromS0 cA gh bl σ σ₀ g A I) I, ⟨0⟩,
        transferFromValueWord I, transferFromToWord I, transferFromFromWord I, ⟨204⟩, sel]
      (balanceOfHashMem (transferFromFromWord I))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ (transferFromAllowanceSlotI I)
          (transferFromAllowanceDebitWord (transferFromS0 cA gh bl σ σ₀ g A I) I))
        (transferFromFromSlot I)
        (transferFromBalanceDebitWord (transferFromS0 cA gh bl σ σ₀ g A I) I)) k C) :
    ∃ k' C', RD erc20Bytecode I g (transferFromS0 cA gh bl σ σ₀ g A I) ⟨1233⟩
      [transferFromCurrentAllowanceWord (transferFromS0 cA gh bl σ σ₀ g A I) I, ⟨0⟩,
        transferFromValueWord I, transferFromToWord I, transferFromFromWord I, ⟨204⟩, sel]
      (balanceOfHashMem (transferFromToWord I))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ (transferFromAllowanceSlotI I)
            (transferFromAllowanceDebitWord (transferFromS0 cA gh bl σ σ₀ g A I) I))
          (transferFromFromSlot I)
          (transferFromBalanceDebitWord (transferFromS0 cA gh bl σ σ₀ g A I) I))
        (transferFromToSlot I)
        (transferFromNewToWord (transferFromS0 cA gh bl σ σ₀ g A I) I)) k' C' := by
  have htoCleanL : UInt256.land erc20AddrMask (transferFromToWord I) = transferFromToWord I :=
    erc20AddrMask_clean_left hcanonTo
  have hslot := transferFromToKeccakSlot I hcanonTo
  have rd1199₀ := evm_run rd1151 with [
    dup3, push0, push0, dup7, push20 erc20AddrMask, and,
    push20 erc20AddrMask, and ]
  have rd1199 := rd1199₀
  rw [htoCleanL, htoCleanL] at rd1199
  have rd1215 := evm_run rd1199 with [
    dup2,
    raw mstore 0 (balanceOfHashMem (transferFromToWord I)) (UInt256.ofNat 3)
      (by decide) mem_cost
      (balanceOfHashMem_writeOwner (transferFromFromWord I) (transferFromToWord I))
      (by decide) (by evm_ov),
    push1 ⟨32⟩, add, swap1, dup2,
    raw mstore 0 (balanceOfHashMem (transferFromToWord I)) (UInt256.ofNat 3)
      (by decide) mem_cost
      (balanceOfHashMem_writeSlot_self (transferFromToWord I)) (by decide) (by evm_ov),
    push1 ⟨32⟩, add, push0,
    raw keccak256 0 (transferFromToSlot I) (UInt256.ofNat 3)
      (by decide) mem_cost hslot (by decide) (by evm_ov),
    push0, dup3, dup3 ]
  obtain ⟨k1, C1, rd1216₀⟩ := rd1215.sload (by decide) (by evm_ov)
  have rd1216 : RD erc20Bytecode I g (transferFromS0 cA gh bl σ σ₀ g A I) ⟨1216⟩
      [transferFromToBalanceWord (transferFromS0 cA gh bl σ σ₀ g A I) I,
        transferFromValueWord I, ⟨0⟩, transferFromToSlot I, transferFromValueWord I,
        transferFromCurrentAllowanceWord (transferFromS0 cA gh bl σ σ₀ g A I) I, ⟨0⟩,
        transferFromValueWord I, transferFromToWord I, transferFromFromWord I, ⟨204⟩, sel]
      (balanceOfHashMem (transferFromToWord I)) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ (transferFromAllowanceSlotI I)
          (transferFromAllowanceDebitWord (transferFromS0 cA gh bl σ σ₀ g A I) I))
        (transferFromFromSlot I)
        (transferFromBalanceDebitWord (transferFromS0 cA gh bl σ σ₀ g A I) I)) k1 C1 := by
    simpa [transferFromToBalanceWord, transferFromAfterBalanceState,
      transferFromAfterAllowanceState, transferFromAllowanceSlot, transferFromAllowanceSlotI,
      transferFromS0, initState, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
      erc20StorageStore_accountMap, transferFromAfterAllowance_codeOwner]
      using rd1216₀
  have rd2603 := evm_run rd1216 with [
    push2 ⟨1225⟩, swap2, swap1, push2 ⟨2603⟩, jump erc20_jd ]
  obtain ⟨k2, C2, rd1225₀⟩ := erc20RoutineCheckedAdd rd2603
    (by simpa [transferFromNewToNat] using hfit)
    erc20_jd (by simp only [List.length_cons, List.length_nil]; omega)
  have hnew :
      transferFromToBalanceWord (transferFromS0 cA gh bl σ σ₀ g A I) I +
          transferFromValueWord I =
        transferFromNewToWord (transferFromS0 cA gh bl σ σ₀ g A I) I := by
    apply u256_inj
    rw [uadd_toNat, Nat.mod_eq_of_lt (by simpa [transferFromNewToNat] using hfit)]
    unfold transferFromNewToWord
    rw [ulit_toNat' _ hfit]
    rfl
  have rd1225 := rd1225₀
  rw [hnew] at rd1225
  have rd1231 := evm_run rd1225 with [
    jumpdest, swap3, pop, pop, dup2, swap1 ]
  obtain ⟨k3, C3, rd1231s⟩ := rd1231.sstore hperm (by decide) (by evm_ov)
  exact ⟨_, _, evm_run rd1231s with [ pop ]⟩

theorem transferFromOverflowAfterFromStore {cA : Batteries.RBSet AccountAddress compare}
    {gh : BlockHeader} {bl : ProcessedBlocks} {σ σ₀ : AccountMap} {A : Substate}
    {I : ExecutionEnv} {g : Sat256} {sel : UInt256} {k C : ℕ}
    (hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus)
    (hover : UInt256.size ≤ transferFromNewToNat (transferFromS0 cA gh bl σ σ₀ g A I) I)
    (rd1151 : RD erc20Bytecode I g (transferFromS0 cA gh bl σ σ₀ g A I) ⟨1151⟩
      [transferFromCurrentAllowanceWord (transferFromS0 cA gh bl σ σ₀ g A I) I, ⟨0⟩,
        transferFromValueWord I, transferFromToWord I, transferFromFromWord I, ⟨204⟩, sel]
      (balanceOfHashMem (transferFromFromWord I))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ (transferFromAllowanceSlotI I)
          (transferFromAllowanceDebitWord (transferFromS0 cA gh bl σ σ₀ g A I) I))
        (transferFromFromSlot I)
        (transferFromBalanceDebitWord (transferFromS0 cA gh bl σ σ₀ g A I) I)) k C) :
    RDrev erc20Bytecode g (transferFromS0 cA gh bl σ σ₀ g A I) := by
  have htoCleanL : UInt256.land erc20AddrMask (transferFromToWord I) = transferFromToWord I :=
    erc20AddrMask_clean_left hcanonTo
  have hslot := transferFromToKeccakSlot I hcanonTo
  have rd1199₀ := evm_run rd1151 with [
    dup3, push0, push0, dup7, push20 erc20AddrMask, and,
    push20 erc20AddrMask, and ]
  have rd1199 := rd1199₀
  rw [htoCleanL, htoCleanL] at rd1199
  have rd1215 := evm_run rd1199 with [
    dup2,
    raw mstore 0 (balanceOfHashMem (transferFromToWord I)) (UInt256.ofNat 3)
      (by decide) mem_cost
      (balanceOfHashMem_writeOwner (transferFromFromWord I) (transferFromToWord I))
      (by decide) (by evm_ov),
    push1 ⟨32⟩, add, swap1, dup2,
    raw mstore 0 (balanceOfHashMem (transferFromToWord I)) (UInt256.ofNat 3)
      (by decide) mem_cost
      (balanceOfHashMem_writeSlot_self (transferFromToWord I)) (by decide) (by evm_ov),
    push1 ⟨32⟩, add, push0,
    raw keccak256 0 (transferFromToSlot I) (UInt256.ofNat 3)
      (by decide) mem_cost hslot (by decide) (by evm_ov),
    push0, dup3, dup3 ]
  obtain ⟨k1, C1, rd1216₀⟩ := rd1215.sload (by decide) (by evm_ov)
  have rd1216 : RD erc20Bytecode I g (transferFromS0 cA gh bl σ σ₀ g A I) ⟨1216⟩
      [transferFromToBalanceWord (transferFromS0 cA gh bl σ σ₀ g A I) I,
        transferFromValueWord I, ⟨0⟩, transferFromToSlot I, transferFromValueWord I,
        transferFromCurrentAllowanceWord (transferFromS0 cA gh bl σ σ₀ g A I) I, ⟨0⟩,
        transferFromValueWord I, transferFromToWord I, transferFromFromWord I, ⟨204⟩, sel]
      (balanceOfHashMem (transferFromToWord I)) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ (transferFromAllowanceSlotI I)
          (transferFromAllowanceDebitWord (transferFromS0 cA gh bl σ σ₀ g A I) I))
        (transferFromFromSlot I)
        (transferFromBalanceDebitWord (transferFromS0 cA gh bl σ σ₀ g A I) I)) k1 C1 := by
    simpa [transferFromToBalanceWord, transferFromAfterBalanceState,
      transferFromAfterAllowanceState, transferFromAllowanceSlot, transferFromAllowanceSlotI,
      transferFromS0, initState, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
      erc20StorageStore_accountMap, transferFromAfterAllowance_codeOwner]
      using rd1216₀
  have rd2603 := evm_run rd1216 with [
    push2 ⟨1225⟩, swap2, swap1, push2 ⟨2603⟩, jump erc20_jd ]
  exact erc20RoutineCheckedAdd_overflow rd2603
    (by simpa [transferFromNewToNat] using hover)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem transferFromReturnTrue {cA : Batteries.RBSet AccountAddress compare}
    {gh : BlockHeader} {bl : ProcessedBlocks} {σ σ₀ : AccountMap} {A : Substate}
    {I : ExecutionEnv} {g : Sat256} {sel : UInt256} {k C : ℕ}
    (hperm : I.perm = true)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus)
    (rd1233 : RD erc20Bytecode I g (transferFromS0 cA gh bl σ σ₀ g A I) ⟨1233⟩
      [transferFromCurrentAllowanceWord (transferFromS0 cA gh bl σ σ₀ g A I) I, ⟨0⟩,
        transferFromValueWord I, transferFromToWord I, transferFromFromWord I, ⟨204⟩, sel]
      (balanceOfHashMem (transferFromToWord I)) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ (transferFromAllowanceSlotI I)
            (transferFromAllowanceDebitWord (transferFromS0 cA gh bl σ σ₀ g A I) I))
          (transferFromFromSlot I)
          (transferFromBalanceDebitWord (transferFromS0 cA gh bl σ σ₀ g A I) I))
        (transferFromToSlot I)
        (transferFromNewToWord (transferFromS0 cA gh bl σ σ₀ g A I) I)) k C) :
    RDret erc20Bytecode g (transferFromS0 cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ (transferFromAllowanceSlotI I)
            (transferFromAllowanceDebitWord (transferFromS0 cA gh bl σ σ₀ g A I) I))
          (transferFromFromSlot I)
          (transferFromBalanceDebitWord (transferFromS0 cA gh bl σ σ₀ g A I) I))
        (transferFromToSlot I)
        (transferFromNewToWord (transferFromS0 cA gh bl σ σ₀ g A I) I))
      (UInt256.toByteArray (⟨1⟩ : UInt256)) := by
  have hfromCleanL : UInt256.land erc20AddrMask (transferFromFromWord I) =
      transferFromFromWord I :=
    erc20AddrMask_clean_left hcanonFrom
  have htoCleanL : UInt256.land erc20AddrMask (transferFromToWord I) =
      transferFromToWord I :=
    erc20AddrMask_clean_left hcanonTo
  have rd1279₀ := evm_run rd1233 with [
    dup4, push20 erc20AddrMask, and, dup6, push20 erc20AddrMask, and ]
  have rd1279 := rd1279₀
  rw [htoCleanL, hfromCleanL] at rd1279
  have rd1312₀ := rd1279.pushConst transferTransferTopic (width := 32) (op := .PUSH32)
    (by decide) (by decide) (by evm_ov)
  have rd2073 := evm_run rd1312₀ with [
    dup6, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost
      (balanceOfHashMem_mload64 (transferFromToWord I))
      (by decide) (by evm_ov),
    push2 ⟨1325⟩, swap2, swap1, push2 ⟨2073⟩, jump erc20_jd ]
  obtain ⟨k1, C1, rd1325⟩ := erc20RoutineEncodeUint256FromMem
    (val := transferFromValueWord I) (ret := ⟨1325⟩)
    (R := [transferTransferTopic, transferFromFromWord I, transferFromToWord I,
      transferFromCurrentAllowanceWord (transferFromS0 cA gh bl σ σ₀ g A I) I, ⟨0⟩,
      transferFromValueWord I, transferFromToWord I, transferFromFromWord I, ⟨204⟩, sel])
    rd2073 (by rfl) erc20_jd (by simp only [List.length_cons, List.length_nil]; omega)
  have rd1333 := evm_run rd1325 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost
      (balanceOfReturnMem_mload64 (transferFromToWord I) (transferFromValueWord I))
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1 ]
  have rd1334 := rd1333.log3 0 (UInt256.ofNat 5) (by decide) hperm mem_cost
    (by decide) (by evm_ov)
  have rd204 := evm_run rd1334 with [
    push1 ⟨1⟩, swap2, pop, pop, swap4, swap3, pop, pop, pop, jump erc20_jd ]
  have rd2033 := evm_run rd204 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost
      (balanceOfReturnMem_mload64 (transferFromToWord I) (transferFromValueWord I))
      (by decide) (by evm_ov),
    push2 ⟨217⟩, swap2, swap1, push2 ⟨2033⟩, jump erc20_jd ]
  obtain ⟨k2, C2, rd217⟩ := erc20RoutineEncodeBoolFromMem
    (val := (⟨1⟩ : UInt256)) (ret := ⟨217⟩) (R := [sel])
    rd2033
    (by
      rw [show UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256)) = ⟨1⟩ from by decide])
    erc20_jd (by simp only [List.length_cons, List.length_nil]; omega)
  exact evm_run rd217 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost
      (transferReturnMem_mload64 (transferFromToWord I) (transferFromValueWord I))
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray (⟨1⟩ : UInt256)) (by decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide, erc20SubRet32_toNat]
        exact transferReturnMem_read128 (transferFromToWord I) (transferFromValueWord I))
      (by evm_ov) ]

theorem erc20TransferFromBodySuffixCoupled {cA : Batteries.RBSet AccountAddress compare}
    {gh : BlockHeader} {bl : ProcessedBlocks} {σ σ₀ : AccountMap} {A : Substate}
    {I : ExecutionEnv} {g : Sat256} {sel : UInt256}
    (hwv : I.weiValue = ⟨0⟩) (hperm : I.perm = true)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus) :
    ∀ st : CoupledState erc20Bytecode I g (transferFromS0 cA gh bl σ σ₀ g A I)
      (TransferFromDecodedRel (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) I g sel) ⟨613⟩,
      CoupledState.refines st erc20Config transferFromTransition.body
        (transitionPost erc20Bytecode I g (transferFromS0 cA gh bl σ σ₀ g A I)
          transferFromTransition.returnType (fun _ _ _ => False)) := by
  intro st
  obtain ⟨hframe, hevm, hstack, hmem, haw, hrdata, hworldRel⟩ := st.hrel
  have rd613 : RD erc20Bytecode I g (transferFromS0 cA gh bl σ σ₀ g A I) ⟨613⟩
      [transferFromValueWord I, transferFromToWord I, transferFromFromWord I, ⟨204⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) st.k st.C := by
    have hRD := st.toRD hstack hmem haw hrdata
    simpa [hworldRel] using hRD
  obtain ⟨k737, C737, rd737⟩ :=
    transferFromLoadAllowance (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel) hcanonFrom rd613
  by_cases hallowance : (transferFromValueWord I).toNat ≤
      (transferFromCurrentAllowanceWord (transferFromS0 cA gh bl σ σ₀ g A I) I).toNat
  · obtain ⟨k805, C805, rd805⟩ :=
      transferFromAllowanceRequireTrue (cA := cA) (gh := gh) (bl := bl) (σ := σ)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel) hallowance rd737
    obtain ⟨k868, C868, rd868⟩ :=
      transferFromLoadFromBalance (cA := cA) (gh := gh) (bl := bl) (σ := σ)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel) hcanonFrom rd805
    by_cases hbalance : (transferFromValueWord I).toNat ≤
        (transferFromFromBalanceWord (transferFromS0 cA gh bl σ σ₀ g A I) I).toNat
    · obtain ⟨k932, C932, rd932⟩ :=
        transferFromBalanceRequireTrue (cA := cA) (gh := gh) (bl := bl) (σ := σ)
          (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel) hbalance rd868
      obtain ⟨k1069, C1069, rd1069⟩ :=
        transferFromStoreAllowance (cA := cA) (gh := gh) (bl := bl) (σ := σ)
          (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel)
          hperm hcanonFrom hallowance rd932
      obtain ⟨k1151, C1151, rd1151⟩ :=
        transferFromStoreFromBalance (cA := cA) (gh := gh) (bl := bl) (σ := σ)
          (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel)
          hperm hcanonFrom hbalance rd1069
      by_cases hfit :
          transferFromNewToNat (transferFromS0 cA gh bl σ σ₀ g A I) I < UInt256.size
      · obtain ⟨k1233, C1233, rd1233⟩ :=
          transferFromStoreToBalance (cA := cA) (gh := gh) (bl := bl) (σ := σ)
            (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel)
            hperm hcanonTo hfit rd1151
        have hret :=
          transferFromReturnTrue (cA := cA) (gh := gh) (bl := bl) (σ := σ)
            (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel)
            hperm hcanonFrom hcanonTo rd1233
        let retFrame : Frame :=
          { contract := erc20Contract,
            locals := transferFromStoreNewToBalance
              (transferFromS0 cA gh bl σ σ₀ g A I) I }
        have hblock : ExecBlock erc20Config st.frame st.evm transferFromTransition.body
            (ExecResult.returned retFrame
              (transferFromPostState (transferFromS0 cA gh bl σ σ₀ g A I) I)
              (some (.bool true))) := by
          rw [hframe, hevm]
          change ExecBlock erc20Config { contract := erc20Contract, locals := transferFromStore I }
            (transferFromS0 cA gh bl σ σ₀ g A I)
            [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
              .letDecl "currentAllowance" (some uint256)
                (.storage (allowanceRef (.var "from") sender)),
              .require (.binary .ge (.var "currentAllowance") (.var "value")),
              .letDecl "fromBalance" (some uint256) (.storage (balanceOfRef (.var "from"))),
              .require (.binary .ge (.var "fromBalance") (.var "value")),
              .assign (allowanceRef (.var "from") sender)
                (.binary .sub (.var "currentAllowance") (.var "value")),
              .assign (balanceOfRef (.var "from"))
                (.binary .sub (.var "fromBalance") (.var "value")),
              .letDecl "toBalance" (some uint256) (.storage (balanceOfRef (.var "to"))),
              .letDecl "newToBalance" (some uint256)
                (valueInUInt256 (.binary .add (.var "toBalance") (.var "value"))),
              .assign (balanceOfRef (.var "to")) (.var "newToBalance"),
              .return (.boolLit true) ]
            (ExecResult.returned retFrame
              (transferFromPostState (transferFromS0 cA gh bl σ σ₀ g A I) I)
              (some (.bool true)))
          refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true ?_)) ?_
          · simp [transferFromS0, initState, hwv]
          refine ExecBlock.consNormal
            (ExecStmt.letDecl (evalExpr_transferFrom_currentAllowance
              (transferFromS0 cA gh bl σ σ₀ g A I) I)) ?_
          refine ExecBlock.consNormal
            (ExecStmt.requireTrue (evalExpr_transferFrom_require_allowance_true
              (transferFromS0 cA gh bl σ σ₀ g A I) I hallowance)) ?_
          refine ExecBlock.consNormal
            (ExecStmt.letDecl (evalExpr_transferFrom_from_balance
              (transferFromS0 cA gh bl σ σ₀ g A I) I)) ?_
          refine ExecBlock.consNormal
            (ExecStmt.requireTrue (evalExpr_transferFrom_require_from_true
              (transferFromS0 cA gh bl σ σ₀ g A I) I hbalance)) ?_
          refine ExecBlock.consNormal
            (ExecStmt.assign (evalExpr_transferFrom_allowance_debit
              (transferFromS0 cA gh bl σ σ₀ g A I) I hallowance)
              (transferFromAssignAllowance (transferFromS0 cA gh bl σ σ₀ g A I) I)) ?_
          refine ExecBlock.consNormal
            (ExecStmt.assign
              (evalExpr_transferFrom_balance_debit
                (transferFromS0 cA gh bl σ σ₀ g A I)
                (transferFromAfterAllowanceState (transferFromS0 cA gh bl σ σ₀ g A I) I)
                I hbalance)
              (transferFromAssignFrom (transferFromS0 cA gh bl σ σ₀ g A I) I)) ?_
          refine ExecBlock.consNormal
            (ExecStmt.letDecl (evalExpr_transferFrom_to_balance
              (transferFromS0 cA gh bl σ σ₀ g A I) I)) ?_
          refine ExecBlock.consNormal
            (ExecStmt.letDecl (evalExpr_transferFrom_newToBalance
              (transferFromS0 cA gh bl σ σ₀ g A I) I hfit)) ?_
          refine ExecBlock.consNormal
            (ExecStmt.assign (evalExpr_transferFrom_newToBalance_var
              (transferFromS0 cA gh bl σ σ₀ g A I) I)
              (transferFromAssignTo (transferFromS0 cA gh bl σ σ₀ g A I) I hfit)) ?_
          exact ExecBlock.consReturn (ExecStmt.return (by simp [evalExpr?, pure]))
        refine ⟨_, hblock, ?_⟩
        exact ⟨UInt256.toByteArray (⟨1⟩ : UInt256), by
          simpa [worldOf, transferFromPostState, transferFromAfterBalanceState,
            transferFromAfterAllowanceState, transferFromAllowanceSlot, transferFromAllowanceSlotI,
            transferFromS0, initState, erc20StorageStore_createdAccounts,
            erc20StorageStore_accountMap, transferFromAfterAllowance_codeOwner,
            transferFromAfterBalance_codeOwner] using hret,
          returnEquiv_of_encode erc20BoolTrueReturnEncoding⟩
      · have hover :
            UInt256.size ≤
              transferFromNewToNat (transferFromS0 cA gh bl σ σ₀ g A I) I := by
          omega
        have hrev :=
          transferFromOverflowAfterFromStore (cA := cA) (gh := gh) (bl := bl) (σ := σ)
            (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel)
            hcanonTo hover rd1151
        have hblock : ExecBlock erc20Config st.frame st.evm transferFromTransition.body
            .reverted := by
          rw [hframe, hevm]
          change ExecBlock erc20Config { contract := erc20Contract, locals := transferFromStore I }
            (transferFromS0 cA gh bl σ σ₀ g A I)
            [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
              .letDecl "currentAllowance" (some uint256)
                (.storage (allowanceRef (.var "from") sender)),
              .require (.binary .ge (.var "currentAllowance") (.var "value")),
              .letDecl "fromBalance" (some uint256) (.storage (balanceOfRef (.var "from"))),
              .require (.binary .ge (.var "fromBalance") (.var "value")),
              .assign (allowanceRef (.var "from") sender)
                (.binary .sub (.var "currentAllowance") (.var "value")),
              .assign (balanceOfRef (.var "from"))
                (.binary .sub (.var "fromBalance") (.var "value")),
              .letDecl "toBalance" (some uint256) (.storage (balanceOfRef (.var "to"))),
              .letDecl "newToBalance" (some uint256)
                (valueInUInt256 (.binary .add (.var "toBalance") (.var "value"))),
              .assign (balanceOfRef (.var "to")) (.var "newToBalance"),
              .return (.boolLit true) ] .reverted
          refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true ?_)) ?_
          · simp [transferFromS0, initState, hwv]
          refine ExecBlock.consNormal
            (ExecStmt.letDecl (evalExpr_transferFrom_currentAllowance
              (transferFromS0 cA gh bl σ σ₀ g A I) I)) ?_
          refine ExecBlock.consNormal
            (ExecStmt.requireTrue (evalExpr_transferFrom_require_allowance_true
              (transferFromS0 cA gh bl σ σ₀ g A I) I hallowance)) ?_
          refine ExecBlock.consNormal
            (ExecStmt.letDecl (evalExpr_transferFrom_from_balance
              (transferFromS0 cA gh bl σ σ₀ g A I) I)) ?_
          refine ExecBlock.consNormal
            (ExecStmt.requireTrue (evalExpr_transferFrom_require_from_true
              (transferFromS0 cA gh bl σ σ₀ g A I) I hbalance)) ?_
          refine ExecBlock.consNormal
            (ExecStmt.assign (evalExpr_transferFrom_allowance_debit
              (transferFromS0 cA gh bl σ σ₀ g A I) I hallowance)
              (transferFromAssignAllowance (transferFromS0 cA gh bl σ σ₀ g A I) I)) ?_
          refine ExecBlock.consNormal
            (ExecStmt.assign
              (evalExpr_transferFrom_balance_debit
                (transferFromS0 cA gh bl σ σ₀ g A I)
                (transferFromAfterAllowanceState (transferFromS0 cA gh bl σ σ₀ g A I) I)
                I hbalance)
              (transferFromAssignFrom (transferFromS0 cA gh bl σ σ₀ g A I) I)) ?_
          refine ExecBlock.consNormal
            (ExecStmt.letDecl (evalExpr_transferFrom_to_balance
              (transferFromS0 cA gh bl σ σ₀ g A I) I)) ?_
          exact ExecBlock.consRevert
            (ExecStmt.letDeclRevert (evalExpr_transferFrom_newToBalance_revert
              (transferFromS0 cA gh bl σ σ₀ g A I) I hover))
        exact ⟨_, hblock, hrev⟩
    · have hlt :
          (transferFromFromBalanceWord (transferFromS0 cA gh bl σ σ₀ g A I) I).toNat <
            (transferFromValueWord I).toNat := by
        omega
      have hrev :=
        transferFromBalanceRequireFalse (cA := cA) (gh := gh) (bl := bl) (σ := σ)
          (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel) hlt rd868
      have hblock : ExecBlock erc20Config st.frame st.evm transferFromTransition.body
          .reverted := by
        rw [hframe, hevm]
        change ExecBlock erc20Config { contract := erc20Contract, locals := transferFromStore I }
          (transferFromS0 cA gh bl σ σ₀ g A I)
          [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
            .letDecl "currentAllowance" (some uint256)
              (.storage (allowanceRef (.var "from") sender)),
            .require (.binary .ge (.var "currentAllowance") (.var "value")),
            .letDecl "fromBalance" (some uint256) (.storage (balanceOfRef (.var "from"))),
            .require (.binary .ge (.var "fromBalance") (.var "value")),
            .assign (allowanceRef (.var "from") sender)
              (.binary .sub (.var "currentAllowance") (.var "value")),
            .assign (balanceOfRef (.var "from"))
              (.binary .sub (.var "fromBalance") (.var "value")),
            .letDecl "toBalance" (some uint256) (.storage (balanceOfRef (.var "to"))),
            .letDecl "newToBalance" (some uint256)
              (valueInUInt256 (.binary .add (.var "toBalance") (.var "value"))),
            .assign (balanceOfRef (.var "to")) (.var "newToBalance"),
            .return (.boolLit true) ] .reverted
        refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true ?_)) ?_
        · simp [transferFromS0, initState, hwv]
        refine ExecBlock.consNormal
          (ExecStmt.letDecl (evalExpr_transferFrom_currentAllowance
            (transferFromS0 cA gh bl σ σ₀ g A I) I)) ?_
        refine ExecBlock.consNormal
          (ExecStmt.requireTrue (evalExpr_transferFrom_require_allowance_true
            (transferFromS0 cA gh bl σ σ₀ g A I) I hallowance)) ?_
        refine ExecBlock.consNormal
          (ExecStmt.letDecl (evalExpr_transferFrom_from_balance
            (transferFromS0 cA gh bl σ σ₀ g A I) I)) ?_
        exact ExecBlock.consRevert
          (ExecStmt.requireFalse (evalExpr_transferFrom_require_from_false
            (transferFromS0 cA gh bl σ σ₀ g A I) I hlt))
      exact ⟨_, hblock, hrev⟩
  · have hlt :
        (transferFromCurrentAllowanceWord (transferFromS0 cA gh bl σ σ₀ g A I) I).toNat <
          (transferFromValueWord I).toNat := by
      omega
    have hrev :=
      transferFromAllowanceRequireFalse (cA := cA) (gh := gh) (bl := bl) (σ := σ)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel) hlt rd737
    have hblock : ExecBlock erc20Config st.frame st.evm transferFromTransition.body
        .reverted := by
      rw [hframe, hevm]
      change ExecBlock erc20Config { contract := erc20Contract, locals := transferFromStore I }
        (transferFromS0 cA gh bl σ σ₀ g A I)
        [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
          .letDecl "currentAllowance" (some uint256)
            (.storage (allowanceRef (.var "from") sender)),
          .require (.binary .ge (.var "currentAllowance") (.var "value")),
          .letDecl "fromBalance" (some uint256) (.storage (balanceOfRef (.var "from"))),
          .require (.binary .ge (.var "fromBalance") (.var "value")),
          .assign (allowanceRef (.var "from") sender)
            (.binary .sub (.var "currentAllowance") (.var "value")),
          .assign (balanceOfRef (.var "from"))
            (.binary .sub (.var "fromBalance") (.var "value")),
          .letDecl "toBalance" (some uint256) (.storage (balanceOfRef (.var "to"))),
          .letDecl "newToBalance" (some uint256)
            (valueInUInt256 (.binary .add (.var "toBalance") (.var "value"))),
          .assign (balanceOfRef (.var "to")) (.var "newToBalance"),
          .return (.boolLit true) ] .reverted
      refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true ?_)) ?_
      · simp [transferFromS0, initState, hwv]
      refine ExecBlock.consNormal
        (ExecStmt.letDecl (evalExpr_transferFrom_currentAllowance
          (transferFromS0 cA gh bl σ σ₀ g A I) I)) ?_
      exact ExecBlock.consRevert
        (ExecStmt.requireFalse (evalExpr_transferFrom_require_allowance_false
          (transferFromS0 cA gh bl σ σ₀ g A I) I hlt))
    exact ⟨_, hblock, hrev⟩

theorem erc20TransferFromBodyCoreCoupled {cA gh bl σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = erc20Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : ((⟨#[0x23, 0xb8, 0x72, 0xdd]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hreach : ∃ k C, RD erc20Bytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨178⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    runtimeEquivalenceFor erc20Config erc20Contract cA gh bl σ σ₀ g A I := by
  have hsz4 := erc20TransferFromSelector_size hsel
  have hd := erc20Dispatch_transferFrom (cd := I.calldata) hsel
  by_cases hsz100 : 100 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus
      · by_cases hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus
        · have hdec := erc20Decode_transferFrom_ok (I := I)
            hsz100 hbig hcanonFrom hcanonTo
          obtain ⟨k613, C613, rd613⟩ :=
            standaloneTransferFromX_decoded (cA := cA) (gh := gh) (bl := bl)
              (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) (sel := sel)
              hsz100 hsize hbig hcanonFrom hcanonTo hreach
          let s0 := transferFromS0 cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
          let cur613 : Cursor :=
            { pc := ⟨613⟩,
              stack :=
                [transferFromValueWord I, transferFromToWord I, transferFromFromWord I,
                  ⟨204⟩, sel],
              mem := solcFreePtrMem,
              aw := UInt256.ofNat 3,
              rdata := ByteArray.empty,
              world := (cA, σ) }
          let frame0 : Frame := { contract := erc20Contract, locals := transferFromStore I }
          let evm0 : State := s0
          have hRDc : RDc erc20Bytecode I (Sat256.ofUInt256 g) s0 cur613 k613 C613 := by
            change RD erc20Bytecode I (Sat256.ofUInt256 g) s0 cur613.pc cur613.stack
              cur613.mem cur613.aw cur613.rdata cur613.world k613 C613
            simpa [s0, cur613, transferFromS0] using rd613
          have hworld : cur613.world = worldOf evm0 := by
            simp [cur613, evm0, s0, worldOf, initState]
          have hrel : TransferFromDecodedRel (cA := cA) (gh := gh) (bl := bl) (σ := σ)
              (σ₀ := σ₀) (A := A) I (Sat256.ofUInt256 g) sel cur613 frame0 evm0 := by
            simp [TransferFromDecodedRel, cur613, frame0, evm0, s0, transferFromS0]
          obtain ⟨result, hblock, hpost⟩ :=
            erc20TransferFromBodySuffixCoupled (cA := cA) (gh := gh) (bl := bl)
              (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
              (sel := sel) hwv hperm hcanonFrom hcanonTo
              (CoupledState.mk cur613 k613 C613 frame0 evm0 rfl hRDc hworld hrel)
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
        · have hdec := erc20Decode_transferFrom_none_noncanon_to (I := I)
            hsz100 hbig hcanonFrom hcanonTo
          have hnc : UInt256.eq (transferFromToWord I)
              (UInt256.land (transferFromToWord I) erc20AddrMask) = ⟨0⟩ :=
            erc20Ueq_zero_of_ne (fun he => hcanonTo (erc20Word_canonical_of_clean he))
          exact (standaloneTransferFromX_noncanon_to (g := Sat256.ofUInt256 g)
              hsz100 hsize hbig hcanonFrom hnc hreach)
            |>.reEquivDecodingFailed hcode hd hdec
      · have hdec := erc20Decode_transferFrom_none_noncanon_from (I := I)
          hsz100 hbig hcanonFrom
        have hnc : UInt256.eq (transferFromFromWord I)
            (UInt256.land (transferFromFromWord I) erc20AddrMask) = ⟨0⟩ :=
          erc20Ueq_zero_of_ne (fun he => hcanonFrom (erc20Word_canonical_of_clean he))
        exact (standaloneTransferFromX_noncanon_from (g := Sat256.ofUInt256 g)
            hsz100 hsize hbig hnc hreach)
          |>.reEquivDecodingFailed hcode hd hdec
    · have hbigge : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      have hdec := erc20Decode_transferFrom_none_huge (I := I) hbigge
      exact (standaloneTransferFromX_hugearg (g := Sat256.ofUInt256 g)
          hsz4 hsize hbigge hreach)
        |>.reEquivDecodingFailed hcode hd hdec
  · have hshort : I.calldata.size < 100 := by omega
    have hdec := erc20Decode_transferFrom_none_short (I := I) hsz4 hshort
    exact (standaloneTransferFromX_shortarg (g := Sat256.ofUInt256 g)
        hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

end ERC20Coupled
