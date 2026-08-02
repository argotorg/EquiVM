import Examples.Ripemd160.Dispatch
import Examples.Ripemd160.HashMemory

/-!
# Ripemd160Deployed fallback correctness

The runtime has no selector dispatcher. Every zero-value call enters the hashing body, while a
nonzero-value call is rejected by the compiler-generated nonpayable guard.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Ripemd160

/-- The optimized runtime checks `CALLVALUE` directly and jumps to the empty revert stub. -/
theorem ripemd160X_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = ripemd160RuntimeBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev ripemd160RuntimeBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact evm_run (RD.initState hcode) with [
    push1 ⟨128⟩,
    push1 ⟨64⟩,
    raw mstore 9 solcFreePtrMem (UInt256.ofNat 3) (by decide)
      mem_cost
      (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; rfl)
      (by decide) (by evm_ov),
    callvalue,
    push2 ⟨137⟩,
    jumpiT hwv (by jump_dest),
    jumpdest,
    push0,
    dup1,
    raw rev 0 (by decide) mem_cost (by simp) ]

/-- The macro-added nonpayable guard is the first statement of the fallback body. -/
theorem fallbackBodyReverts_nonPayable (evm : EVM.State) (locals : Store)
    (hwv : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody config contract evm locals fallbackTransition.body .reverted := by
  exact bodyReverts_nonPayable hwv

/-- Runtime equivalence for the nonzero-callvalue branch. -/
theorem fallbackNonPayable {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = ripemd160RuntimeBytecode)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrun := ripemd160X_callvalue_ne
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) hcode hwv
  have hequiv :
      runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀
        (Sat256.ofUInt256 g).toUInt256 A I :=
    hrun.reEquivElim hcode fun _ _ hrev => by
    refine runtimeEquivalenceFor.execution
      (returnConvention := .rawBytes) (solmRes := .reverted) hrev ?_ ?_
    · exact solmExec.fallback
        (selectorDispatch_none I.calldata)
        (receiveDispatch_none I.calldata)
        rfl
        (fallback_callargs I.calldata)
        fallback_returnConvention
        rfl
        (fallbackBodyReverts_nonPayable
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (fallbackLocals I)
          (by simpa [initState] using hwv))
    · exact execResultsEquiv.revert rfl rfl
  simpa using hequiv

/-! ## Zero-value allocator guard -/

/-- The zero-value prologue falls through to the calldata-size allocator check at PC 10. -/
theorem ripemd160X_cvz_prefix {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = ripemd160RuntimeBytecode) (hwv : I.weiValue = ⟨0⟩) :
    ∃ k C, RD ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨10⟩ [] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have rd0 :
      RD ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨0⟩ [] ByteArray.empty (UInt256.ofNat 0) ByteArray.empty (cA, σ) 0 0 :=
    RD.initState hcode
  have rd10 := evm_run rd0 with [
    push1 ⟨128⟩,
    push1 ⟨64⟩,
    raw mstore 9 solcFreePtrMem (UInt256.ofNat 3) (by decide)
      mem_cost
      (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; rfl)
      (by decide) (by evm_ov),
    callvalue,
    push2 ⟨137⟩,
    jumpiNT hwv ]
  exact ⟨_, _, rd10⟩

/-- The shared Solidity panic-0x41 tail reached by either allocator bound check. -/
theorem ripemd160X_panic41 {cA gh bl σ σ₀ A I} {g : Sat256} {stk : List UInt256}
    (hreach : ∃ k C, RD ripemd160RuntimeBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨132⟩ stk
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hov : stk.length + 3 ≤ 1024) :
    RDrev ripemd160RuntimeBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd132⟩ := hreach
  have rd141 := evm_run rd132 with [
    jumpdest,
    push2 ⟨141⟩,
    jump (by jump_dest),
    jumpdest ]
  have rd175 := RD.pushConst rd141 panicSelectorWord
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by omega)
  exact evm_run rd175 with [
    push0,
    raw mstore 0 panic41Mem1 (UInt256.ofNat 3) (by decide)
      mem_cost
      (by unfold panic41Mem1; rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl])
      (by decide) (by omega),
    push1 ⟨65⟩,
    push1 ⟨4⟩,
    raw mstore 0 panic41Mem (UInt256.ofNat 3) (by decide)
      mem_cost
      (by unfold panic41Mem; rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide])
      (by decide) (by omega),
    push1 ⟨36⟩,
    push0,
    raw rev 0 (by decide) mem_cost (by evm_ov) ]

/-- Calldata larger than `uint64` fails the allocator's first check. -/
theorem ripemd160X_calldata_gt_u64 {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = ripemd160RuntimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size)
    (hhuge : 18446744073709551615 < I.calldata.size) :
    RDrev ripemd160RuntimeBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd10⟩ := ripemd160X_cvz_prefix
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hcode hwv
  have hgt :
      UInt256.gt (calldataSizeWord I) ⟨18446744073709551615⟩ = ⟨1⟩ := by
    apply ugt_one
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = 18446744073709551615 by
      native_decide]
    simpa [calldataSizeWord, ulit_toNat' I.calldata.size hsize] using hhuge
  have rd19 := RD.pushConst rd10 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have rd132 := evm_run rd19 with [
    calldatasize,
    gt,
    push2 ⟨132⟩,
    jumpiT (by rw [hgt]; decide) (by jump_dest) ]
  exact ripemd160X_panic41 ⟨_, _, rd132⟩ (by decide)

theorem roundedCalldataSizeWord_toNat (I : ExecutionEnv)
    (hmax : I.calldata.size ≤ 18446744073709551615) :
    (roundedCalldataSizeWord I).toNat = 32 * ((I.calldata.size + 31) / 32) := by
  unfold roundedCalldataSizeWord calldataSizeWord
  rw [uland_toNat, lnot31_toNat, uadd_toNat]
  rw [ulit_toNat' I.calldata.size (lt_of_le_of_lt hmax (by decide))]
  rw [show (⟨31⟩ : UInt256).toNat = 31 from by decide]
  rw [show UInt256.size = 2 ^ 256 from by decide]
  rw [Nat.mod_eq_of_lt (by omega)]
  rw [Nat.and_comm, nat_land_mask _ (by omega)]

theorem fallbackAllocationSize_eq (I : ExecutionEnv)
    (hmax : I.calldata.size ≤ 18446744073709551615) :
    UInt256.land (roundedCalldataSizeWord I + ⟨63⟩) (UInt256.lnot ⟨31⟩) =
      fallbackAllocationSize I := by
  rw [u256_land_comm]
  simpa [fallbackAllocationSize] using
    (alloc_round (roundedCalldataSizeWord I) ((I.calldata.size + 31) / 32)
      (roundedCalldataSizeWord_toNat I hmax)
      (by rw [roundedCalldataSizeWord_toNat I hmax]; omega))

theorem fallbackFreePtr_toNat (I : ExecutionEnv)
    (hmax : I.calldata.size ≤ 18446744073709551615) :
    (fallbackFreePtr I).toNat = 160 + 32 * ((I.calldata.size + 31) / 32) := by
  unfold fallbackFreePtr fallbackAllocationSize
  rw [uadd_toNat, uadd_toNat, roundedCalldataSizeWord_toNat I hmax]
  rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
    show (⟨32⟩ : UInt256).toNat = 32 from by decide,
    show UInt256.size = 2 ^ 256 from by decide]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

theorem fallbackFreePtr_le_u64_of_small (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    UInt256.gt (fallbackFreePtr I) ⟨18446744073709551615⟩ = ⟨0⟩ := by
  apply ugt_zero
  rw [fallbackFreePtr_toNat I (by unfold maxFallbackCalldataSize at hsmall; omega)]
  rw [show (⟨18446744073709551615⟩ : UInt256).toNat = 18446744073709551615 from by
    native_decide]
  unfold maxFallbackCalldataSize at hsmall
  omega

theorem fallbackFreePtr_stack_eq (I : ExecutionEnv)
    (hmax : I.calldata.size ≤ 18446744073709551615) :
    ⟨128⟩ + UInt256.land
        (UInt256.land (calldataSizeWord I + ⟨31⟩) (UInt256.lnot ⟨31⟩) + ⟨63⟩)
        (UInt256.lnot ⟨31⟩) = fallbackFreePtr I := by
  have hrounded :
      UInt256.land (calldataSizeWord I + ⟨31⟩) (UInt256.lnot ⟨31⟩) =
        roundedCalldataSizeWord I := by
    rw [u256_land_comm]
    rfl
  rw [hrounded, fallbackAllocationSize_eq I hmax]
  rfl

theorem fallbackPaddingAddr_toNat (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    ((⟨128⟩ : UInt256) + calldataSizeWord I + ⟨32⟩).toNat =
      160 + I.calldata.size := by
  unfold calldataSizeWord
  rw [uadd_toNat, uadd_toNat,
    ulit_toNat' I.calldata.size
      (lt_of_le_of_lt hsmall (by native_decide : maxFallbackCalldataSize < UInt256.size))]
  rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
    show (⟨32⟩ : UInt256).toNat = 32 from by decide,
    show UInt256.size = 2 ^ 256 from by decide]
  rw [Nat.mod_eq_of_lt (by unfold maxFallbackCalldataSize at hsmall; omega),
    Nat.mod_eq_of_lt (by unfold maxFallbackCalldataSize at hsmall; omega)]
  omega

theorem fallbackFreePtr_gt_u64_of_large (I : ExecutionEnv)
    (hmax : I.calldata.size ≤ 18446744073709551615)
    (hlarge : maxFallbackCalldataSize < I.calldata.size) :
    UInt256.gt (fallbackFreePtr I) ⟨18446744073709551615⟩ = ⟨1⟩ := by
  apply ugt_one
  rw [fallbackFreePtr_toNat I hmax]
  rw [show (⟨18446744073709551615⟩ : UInt256).toNat = 18446744073709551615 from by
    native_decide]
  unfold maxFallbackCalldataSize at hlarge
  omega

theorem fallbackFreePtr_not_lt_128 (I : ExecutionEnv)
    (hmax : I.calldata.size ≤ 18446744073709551615) :
    UInt256.lt (fallbackFreePtr I) ⟨128⟩ = ⟨0⟩ := by
  apply ult_zero
  rw [fallbackFreePtr_toNat I hmax,
    show (⟨128⟩ : UInt256).toNat = 128 from by decide]
  omega

/-- The rounded allocation exceeds `uint64` even though the calldata length itself does not. -/
theorem ripemd160X_calldata_rounding_overflow {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = ripemd160RuntimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size)
    (hmax : I.calldata.size ≤ 18446744073709551615)
    (hlarge : maxFallbackCalldataSize < I.calldata.size) :
    RDrev ripemd160RuntimeBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd10⟩ := ripemd160X_cvz_prefix
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hcode hwv
  have hgt0 :
      UInt256.gt (calldataSizeWord I) ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = 18446744073709551615 from by
      native_decide]
    simpa [calldataSizeWord, ulit_toNat' I.calldata.size hsize] using hmax
  have rd19 := RD.pushConst rd10 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have rd28 := evm_run rd19 with [
    calldatasize,
    gt,
    push2 ⟨132⟩,
    jumpiNT hgt0,
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov) ]
  have rd61 := RD.pushConst rd28 (UInt256.lnot ⟨31⟩)
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have rd77 := evm_run rd61 with [
    push1 ⟨63⟩,
    dup2,
    push1 ⟨31⟩,
    calldatasize,
    add,
    and,
    add,
    and,
    dup2,
    add,
    swap1,
    dup1,
    dup3,
    lt ]
  have hnew := fallbackFreePtr_stack_eq I hmax
  have rd86 := RD.pushConst rd77 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have hbad :
      UInt256.lor
        (UInt256.gt (fallbackFreePtr I) ⟨18446744073709551615⟩)
        (UInt256.lt (fallbackFreePtr I) ⟨128⟩) = ⟨1⟩ := by
    rw [fallbackFreePtr_gt_u64_of_large I hmax hlarge,
      fallbackFreePtr_not_lt_128 I hmax]
    decide
  have rd132 := evm_run rd86 with [
    dup4,
    gt,
    or,
    push2 ⟨132⟩,
    jumpiT (by rw [hnew, hbad]; decide) (by jump_dest) ]
  exact ripemd160X_panic41 ⟨_, _, rd132⟩ (by simp)

/-- Accepted calldata is materialized as Solidity `bytes memory` and reaches the hash routine. -/
theorem ripemd160X_reachHash {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = ripemd160RuntimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    ∃ k C, RD ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨776⟩ [⟨128⟩, ⟨122⟩]
      (fallbackPaddedMem I) (fallbackPaddedAw I) ByteArray.empty (cA, σ) k C := by
  have hmax : I.calldata.size ≤ 18446744073709551615 := by
    unfold maxFallbackCalldataSize at hsmall
    omega
  obtain ⟨_, _, rd10⟩ := ripemd160X_cvz_prefix
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hcode hwv
  have hgt0 :
      UInt256.gt (calldataSizeWord I) ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = 18446744073709551615 from by
      native_decide]
    simpa [calldataSizeWord, ulit_toNat' I.calldata.size hsize] using hmax
  have rd19 := RD.pushConst rd10 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have rd28 := evm_run rd19 with [
    calldatasize,
    gt,
    push2 ⟨132⟩,
    jumpiNT hgt0,
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov) ]
  have rd61 := RD.pushConst rd28 (UInt256.lnot ⟨31⟩)
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have rd77 := evm_run rd61 with [
    push1 ⟨63⟩, dup2, push1 ⟨31⟩, calldatasize, add, and, add, and,
    dup2, add, swap1, dup1, dup3, lt ]
  have rd86 := RD.pushConst rd77 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have hbad0 :
      UInt256.lor
        (UInt256.gt (fallbackFreePtr I) ⟨18446744073709551615⟩)
        (UInt256.lt (fallbackFreePtr I) ⟨128⟩) = ⟨0⟩ := by
    rw [fallbackFreePtr_le_u64_of_small I hsmall,
      fallbackFreePtr_not_lt_128 I hmax]
    decide
  have rd100 := evm_run rd86 with [
    dup4, gt, or, push2 ⟨132⟩,
    jumpiNT (by rw [fallbackFreePtr_stack_eq I hmax, hbad0]),
    push2 ⟨122⟩, swap2, push1 ⟨64⟩,
    raw mstore 0 (fallbackAllocMem I) (UInt256.ofNat 3) (by decide)
      mem_cost
      (by
        unfold fallbackAllocMem
        rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide,
          fallbackFreePtr_stack_eq I hmax])
      (by decide) (by evm_ov) ]
  have rd103 := evm_run rd100 with [
    calldatasize, dup2,
    raw mstore 6 (fallbackLengthMem I) (UInt256.ofNat 5) (by decide)
      mem_cost
      (by unfold fallbackLengthMem; rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide])
      (by decide) (by evm_ov),
    calldatasize, push0, push1 ⟨32⟩, dup4, add ]
  have rd110 := RD.calldatacopy
    (Cₘ (fallbackCopyAw I) - Cₘ (UInt256.ofNat 5))
    (fallbackCalldataMem I) (fallbackCopyAw I)
    rd103 (by decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, fallbackCopyAw]
      rw [show ((⟨128⟩ : UInt256) + ⟨32⟩).toNat = 160 from by decide,
        ulit_toNat' I.calldata.size hsize])
    (by
      unfold fallbackCalldataMem
      rw [show ((⟨128⟩ : UInt256) + ⟨32⟩).toNat = 160 from by decide,
        ulit_toNat' I.calldata.size hsize,
        show (⟨0⟩ : UInt256).toNat = 0 from rfl])
    (by
      unfold fallbackCopyAw
      rw [show ((⟨128⟩ : UInt256) + ⟨32⟩).toNat = 160 from by decide,
        ulit_toNat' I.calldata.size hsize])
    (by evm_ov)
  have rd117 := evm_run rd110 with [
    push0, push1 ⟨32⟩, calldatasize, dup4, add, add ]
  have rd118 := RD.mstore
    (Cₘ (fallbackPaddedAw I) - Cₘ (fallbackCopyAw I))
    (fallbackPaddedMem I) (fallbackPaddedAw I)
    rd117 (by decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, fallbackPaddedAw]
      rw [fallbackPaddingAddr_toNat I hsmall])
    (by
      unfold fallbackPaddedMem
      rw [fallbackPaddingAddr_toNat I hsmall])
    (by
      unfold fallbackPaddedAw
      rw [fallbackPaddingAddr_toNat I hsmall])
    (by evm_ov)
  have rd776 := evm_run rd118 with [push2 ⟨776⟩, jump (by jump_dest)]
  exact ⟨_, _, rd776⟩

/-- Hash entry through padded-buffer allocation and `MCOPY`, at the zero-fill loop header. -/
theorem ripemd160X_reachZeroLoop {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = ripemd160RuntimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    ∃ k C, RD ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨839⟩
      [calldataSizeWord I, hashPaddedLengthWord I, calldataSizeWord I,
        hashNewFreePtr I, hashPadPtr I, calldataSizeWord I + ⟨72⟩, ⟨122⟩]
      (hashCopiedMem I) (hashCopiedAw I) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd776⟩ := ripemd160X_reachHash
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hcode hwv hsize hsmall
  have rd778 := evm_run rd776 with [jumpdest, dup1]
  have rd779 := RD.mload 0 (calldataSizeWord I) (fallbackPaddedAw I)
    rd778 (by native_decide)
    (fallbackPaddedMload128Cost I hsmall)
    (fallbackPaddedMload128Value I hsmall)
    (fallbackPaddedAw_mload128 I hsmall) (by simp)
  have rd784 := evm_run rd779 with [push1 ⟨72⟩, dup2, add, swap2]
  have rd817 := RD.pushConst rd784 (UInt256.lnot ⟨63⟩)
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have rd822 := evm_run rd817 with [dup4, and, swap2, push1 ⟨64⟩]
  have rd823 := RD.mload 0 (hashPadPtr I) (fallbackPaddedAw I)
    rd822 (by native_decide)
    (fallbackPaddedMload64Cost I hsmall)
    (fallbackPaddedMload64Value I hsmall)
    (fallbackPaddedAw_mload64 I hsmall) (by simp)
  have rd834 := evm_run rd823 with [
    swap3, dup2, push1 ⟨32⟩, dup3, dup7, add, swap5, dup6, push1 ⟨64⟩ ]
  have rd835 := RD.mstore 0 (hashAllocatedMem I) (fallbackPaddedAw I)
    rd834 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hstk]
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide,
        haw, fallbackPaddedAw_mload64 I hsmall]
      omega)
    (by
      simp [hashAllocatedMem, hashNewFreePtr, hashPadPtr,
        hashPaddedLengthWord]
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide])
    (fallbackPaddedAw_mload64 I hsmall) (by simp)
  have rd837 := evm_run rd835 with [add, dup6]
  have rd838 := RD.mcopy
    (Cₘ (hashCopiedAw I) - Cₘ (fallbackPaddedAw I))
    (hashCopiedMem I) (hashCopiedAw I) rd837 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, hashCopiedAw]
      rw [show ((⟨128⟩ : UInt256) + ⟨32⟩).toNat = 160 from by decide,
        ulit_toNat' I.calldata.size hsize])
    (by
      unfold hashCopiedMem hashAllocatedMem hashPadPtr
      rw [show ((⟨128⟩ : UInt256) + ⟨32⟩).toNat = 160 from by decide,
        ulit_toNat' I.calldata.size hsize])
    (by
      unfold hashCopiedAw hashPadPtr
      rw [show ((⟨128⟩ : UInt256) + ⟨32⟩).toNat = 160 from by decide,
        ulit_toNat' I.calldata.size hsize])
    (by simp)
  have rd839 := evm_run rd838 with [dup2]
  simpa [hashNewFreePtr, hashPadPtr, hashPaddedLengthWord] using
    (show ∃ k C, RD ripemd160RuntimeBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨839⟩ _
      (hashCopiedMem I) (hashCopiedAw I) ByteArray.empty (cA, σ) k C from ⟨_, _, rd839⟩)

private theorem ripemd160X_zeroLoopBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) {i k C : Nat}
    (hi : i < hashZeroIterations I)
    (h : RD ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨839⟩
      [hashZeroIndexWord I i, hashPaddedLengthWord I, calldataSizeWord I,
        hashNewFreePtr I, hashPadPtr I, calldataSizeWord I + ⟨72⟩, ⟨122⟩]
      (hashZeroMem I i) (hashZeroAw I i) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨839⟩
      [hashZeroIndexWord I (i + 1), hashPaddedLengthWord I, calldataSizeWord I,
        hashNewFreePtr I, hashPadPtr I, calldataSizeWord I + ⟨72⟩, ⟨122⟩]
      (hashZeroMem I (i + 1)) (hashZeroAw I (i + 1))
      ByteArray.empty (cA, σ) k' C' := by
  have hi3 : i < 3 := lt_of_lt_of_le hi (hashZeroIterations_le_three I)
  have hlt : UInt256.lt (hashZeroIndexWord I i) (hashPaddedLengthWord I) = ⟨1⟩ := by
    apply ult_one
    rw [hashZeroIndexWord_toNat I i hsmall (by omega),
      hashPaddedLengthWord_toNat I hsmall]
    exact hashZeroIterations_body I hi
  have rd2187 := evm_run h with [
    jumpdest, dup2, dup2, lt, push2 ⟨2187⟩,
    jumpiT (by rw [hlt]; decide) (by jump_dest) ]
  have rd2193 := evm_run rd2187 with [jumpdest, push0, dup6, dup3, add]
  have rd2194 := RD.mstore
    (Cₘ (hashZeroAw I (i + 1)) - Cₘ (hashZeroAw I i))
    (hashZeroMem I (i + 1)) (hashZeroAw I (i + 1))
    rd2193 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        hashZeroAw, u256_add_comm])
    (by simp [hashZeroMem, u256_add_comm])
    (by simp [hashZeroAw, u256_add_comm])
    (by simp)
  have rd839 := evm_run rd2194 with [
    push1 ⟨32⟩, add, push2 ⟨839⟩, jump (by jump_dest) ]
  have hnext : (⟨32⟩ : UInt256) + hashZeroIndexWord I i =
      hashZeroIndexWord I (i + 1) := by
    rw [u256_add_comm, hashZeroIndexWord_next I i hsmall hi3]
  exact ⟨_, _, by simpa [hnext] using rd839⟩

private theorem ripemd160X_zeroLoopExit {cA gh bl σ σ₀ A I} {g : Sat256}
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) {i k C : Nat}
    (hi : i = hashZeroIterations I)
    (h : RD ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨839⟩
      [hashZeroIndexWord I i, hashPaddedLengthWord I, calldataSizeWord I,
        hashNewFreePtr I, hashPadPtr I, calldataSizeWord I + ⟨72⟩, ⟨122⟩]
      (hashZeroMem I i) (hashZeroAw I i) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨849⟩
      [calldataSizeWord I, hashNewFreePtr I, hashPadPtr I,
        calldataSizeWord I + ⟨72⟩, ⟨122⟩]
      (hashZeroMem I i) (hashZeroAw I i) ByteArray.empty (cA, σ) k' C' := by
  have hi3 : i ≤ 3 := by rw [hi]; exact hashZeroIterations_le_three I
  have hlt : UInt256.lt (hashZeroIndexWord I i) (hashPaddedLengthWord I) = ⟨0⟩ := by
    apply ult_zero
    rw [hashZeroIndexWord_toNat I i hsmall hi3,
      hashPaddedLengthWord_toNat I hsmall]
    rw [hi]
    exact hashZeroIterations_exit I
  exact ⟨_, _, evm_run h with [
    jumpdest, dup2, dup2, lt, push2 ⟨2187⟩,
    jumpiNT (by rw [hlt]), pop, pop ]⟩

/-- Run the complete zero-fill loop and discard its index and bound. -/
theorem ripemd160X_zeroPadding {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = ripemd160RuntimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    ∃ k C, RD ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨849⟩
      [calldataSizeWord I, hashNewFreePtr I, hashPadPtr I,
        calldataSizeWord I + ⟨72⟩, ⟨122⟩]
      (hashZeroMem I (hashZeroIterations I))
      (hashZeroAw I (hashZeroIterations I)) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd839⟩ := ripemd160X_reachZeroLoop
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hcode hwv hsize hsmall
  let Inv : Nat → Nat → Prop := fun v i => i + v = hashZeroIterations I
  let stk : Nat → List UInt256 := fun i =>
    [hashZeroIndexWord I i, hashPaddedLengthWord I, calldataSizeWord I,
      hashNewFreePtr I, hashPadPtr I, calldataSizeWord I + ⟨72⟩, ⟨122⟩]
  let exitStk : Nat → List UInt256 := fun _ =>
    [calldataSizeWord I, hashNewFreePtr I, hashPadPtr I,
      calldataSizeWord I + ⟨72⟩, ⟨122⟩]
  have hexit : ∀ i, Inv 0 i → ∀ k C,
      RD ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨839⟩ (stk i) (hashZeroMem I i) (hashZeroAw I i)
        ByteArray.empty (cA, σ) k C →
      ∃ k' C', RD ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨849⟩ (exitStk i) (hashZeroMem I i) (hashZeroAw I i)
        ByteArray.empty (cA, σ) k' C' := by
    intro i hi k C h
    apply ripemd160X_zeroLoopExit hsmall (by simpa [Inv] using hi)
    simpa [stk] using h
  have hbody : ∀ v i, Inv (v + 1) i → ∀ k C,
      RD ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨839⟩ (stk i) (hashZeroMem I i) (hashZeroAw I i)
        ByteArray.empty (cA, σ) k C →
      ∃ i' k' C', Inv v i' ∧
        RD ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
          ⟨839⟩ (stk i') (hashZeroMem I i') (hashZeroAw I i')
          ByteArray.empty (cA, σ) k' C' := by
    intro v i hi k C h
    have hit : i < hashZeroIterations I := by dsimp [Inv] at hi; omega
    obtain ⟨k', C', h'⟩ := ripemd160X_zeroLoopBody hsmall hit (by simpa [stk] using h)
    exact ⟨i + 1, k', C', by dsimp [Inv]; dsimp [Inv] at hi; omega,
      by simpa [stk] using h'⟩
  obtain ⟨i, k', C', hi, h'⟩ :=
    RD.whileLoopCarry (code := ripemd160RuntimeBytecode) (ee := I) (g := g)
      (s0 := initState cA gh bl σ σ₀ g A I) (rdata := ByteArray.empty)
      (acc := (cA, σ)) (α := Nat) ⟨839⟩ ⟨849⟩ Inv stk
      (hashZeroMem I) (hashZeroAw I) exitStk hexit hbody
      (hashZeroIterations I) 0 (by simp [Inv]) k C (by
        simpa [stk, hashZeroMem, hashZeroAw, hashZeroIndexWord,
          calldataSizeWord, ulit_toNat' I.calldata.size hsize] using rd839)
  have hieq : i = hashZeroIterations I := by dsimp [Inv] at hi; omega
  subst i
  exact ⟨k', C', by simpa [exitStk] using h'⟩

/-- Write the marker and little-endian bit length, then place RIPEMD's five IVs on the stack. -/
theorem ripemd160X_reachHashInit {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = ripemd160RuntimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    ∃ k C, RD ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1014⟩
      [calldataSizeWord I + ⟨72⟩, hashPadPtr I,
        ⟨0x67452301⟩, ⟨0xc3d2e1f0⟩, ⟨0x10325476⟩,
        ⟨0x98badcfe⟩, ⟨0xefcdab89⟩, ⟨122⟩]
      (hashPaddedMessageMem I) (hashPaddedMessageAw I)
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd849⟩ := ripemd160X_zeroPadding
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hcode hwv hsize hsmall
  have rd855 := evm_run rd849 with [push2 ⟨977⟩, dup2, push1 ⟨128⟩]
  have rd888 := RD.pushConst rd855 (UInt256.lnot ⟨7⟩)
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have rd891 := evm_run rd888 with [swap4, dup7, add]
  have rd892 := RD.mstore8
    (Cₘ (hashMarkerAw I) - Cₘ (hashZeroAw I (hashZeroIterations I)))
    (hashMarkerMem I) (hashMarkerAw I) rd891 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        hashMarkerAw, hashMarkerAddr, u256_add_comm])
    (by
      unfold hashMarkerMem hashMarkerAddr
      rw [show UInt8.ofNat (⟨128⟩ : UInt256).toNat = 0x80 from by decide])
    (by simp [hashMarkerAw, hashMarkerAddr, u256_add_comm])
    (by simp)
  have rd895 := evm_run rd892 with [push1 ⟨3⟩, shl]
  have rd904 := RD.pushConst rd895 ⟨0xff00ff00ff00ff00⟩
    (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have rd912 := RD.pushConst rd904 ⟨0x00ff00ff00ff00ff⟩
    (width := 7) (op := .PUSH7) (by decide) (by native_decide) (by evm_ov)
  have rd923 := evm_run rd912 with [
    dup3, push1 ⟨8⟩, shr, and, swap2, push1 ⟨8⟩, shl, and, or ]
  have rd932 := RD.pushConst rd923 ⟨0xffff0000ffff0000⟩
    (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have rd939 := RD.pushConst rd932 ⟨0x0000ffff0000ffff⟩
    (width := 6) (op := .PUSH6) (by decide) (by native_decide) (by evm_ov)
  have rd950 := evm_run rd939 with [
    dup3, push1 ⟨16⟩, shr, and, swap2, push1 ⟨16⟩, shl, and, or ]
  have rd959 := RD.pushConst rd950 ⟨0xffffffff00000000⟩
    (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have rd964 := RD.pushConst rd959 ⟨0x00000000ffffffff⟩
    (width := 4) (op := .PUSH4) (by decide) (by native_decide) (by evm_ov)
  have rd977 := evm_run rd964 with [
    dup3, push1 ⟨32⟩, shr, and, swap2, push1 ⟨32⟩, shl, and, or,
    swap1, jump (by jump_dest) ]
  have rd983 := evm_run rd977 with [jumpdest, push1 ⟨192⟩, shl, swap2, add]
  have rd984 := RD.mstore
    (Cₘ (hashPaddedMessageAw I) - Cₘ (hashMarkerAw I))
    (hashPaddedMessageMem I) (hashPaddedMessageAw I)
    rd983 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        hashPaddedMessageAw, hashLengthAddr, u256_add_comm])
    (by
      simp [hashPaddedMessageMem, hashBitLengthWord, hashSwap64,
        hashSwap64Stage16, hashSwap64Stage8, hashLengthAddr,
        u256_add_comm, u256_land_comm, u256_lor_comm])
    (by simp [hashPaddedMessageAw, hashLengthAddr, u256_add_comm])
    (by simp)
  have rd1014 := evm_run rd984 with [
    push4 ⟨0x67452301⟩, swap1,
    push4 ⟨0xefcdab89⟩, swap3,
    push4 ⟨0x98badcfe⟩, swap3,
    push4 ⟨0x10325476⟩, swap3,
    push4 ⟨0xc3d2e1f0⟩, swap3 ]
  exact ⟨_, _, by simpa using rd1014⟩

/-- Allocate RIPEMD's scratch region and reach the outer 64-byte block loop. -/
theorem ripemd160X_reachBlockLoop {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = ripemd160RuntimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    ∃ k C, RD ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1028⟩
      [hashPadPtr I, calldataSizeWord I + ⟨72⟩, hashScratchPtr I, ⟨0⟩,
        ⟨0x67452301⟩, ⟨0xc3d2e1f0⟩, ⟨0x10325476⟩,
        ⟨0x98badcfe⟩, ⟨0xefcdab89⟩, ⟨122⟩]
      (hashScratchMem I) (hashPaddedMessageAw I)
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1014⟩ := ripemd160X_reachHashInit
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hcode hwv hsize hsmall
  have rd1016 := evm_run rd1014 with [push1 ⟨64⟩]
  have rd1017 := RD.mload 0 (hashScratchPtr I) (hashPaddedMessageAw I)
    rd1016 (by native_decide)
    (hashPaddedMessageMload64Cost I hsmall)
    (hashPaddedMessageMload64Value I hsmall)
    (hashPaddedMessageAw_mload64 I hsmall) (by simp)
  have rd1025 := evm_run rd1017 with [
    swap1, push2 ⟨832⟩, dup3, add, push1 ⟨64⟩ ]
  have rd1026 := RD.mstore 0 (hashScratchMem I) (hashPaddedMessageAw I)
    rd1025 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hstk]
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide,
        haw, hashPaddedMessageAw_mload64 I hsmall]
      omega)
    (by
      simp [hashScratchMem, hashScratchNewFreePtr, hashScratchPtr]
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide])
    (hashPaddedMessageAw_mload64 I hsmall) (by simp)
  have rd1028 := evm_run rd1026 with [push0, swap3]
  exact ⟨_, _, by simpa [hashScratchPtr] using rd1028⟩

theorem fallbackAllocationGuard_false (evm : EVM.State)
    (hlarge : maxFallbackCalldataSize < evm.executionEnv.calldata.size) :
    evalExpr? config
      { contract := contract, locals := fallbackLocals evm.executionEnv }
      evm
      (.binary .le
        (.arrayLength .localVar { base := "data", steps := [] })
        (.intLit maxFallbackCalldataSize)) = .ok (.bool false) := by
  unfold maxFallbackCalldataSize at hlarge ⊢
  simp [fallbackLocals, evalExpr?, readLocalPath?, EvalResult.bind, bind, pure,
    evalBinaryOp?] <;> omega

/-- On oversized calldata the explicit fallback guard models Solidity's failed memory copy. -/
theorem fallbackBodyReverts_allocator (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlarge : maxFallbackCalldataSize < evm.executionEnv.calldata.size) :
    ExecTransitionBody config contract evm (fallbackLocals evm.executionEnv)
      fallbackTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert
    (nonpayableSecondRequireReverts hwv (fallbackAllocationGuard_false evm hlarge))

/-- Runtime equivalence for calldata rejected by Solidity's implicit memory allocator. -/
theorem fallbackOversized {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = ripemd160RuntimeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hlarge : maxFallbackCalldataSize < I.calldata.size) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrun :
      RDrev ripemd160RuntimeBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
    by_cases hmax : I.calldata.size ≤ 18446744073709551615
    · exact ripemd160X_calldata_rounding_overflow hcode hwv hsize hmax hlarge
    · exact ripemd160X_calldata_gt_u64 hcode hwv hsize (by omega)
  have hequiv :
      runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀
        (Sat256.ofUInt256 g).toUInt256 A I :=
    hrun.reEquivElim hcode fun _ _ hrev => by
      refine runtimeEquivalenceFor.execution
        (returnConvention := .rawBytes) (solmRes := .reverted) hrev ?_ ?_
      · exact solmExec.fallback
          (selectorDispatch_none I.calldata)
          (receiveDispatch_none I.calldata)
          rfl
          (fallback_callargs I.calldata)
          fallback_returnConvention
          rfl
          (fallbackBodyReverts_allocator
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (by simpa [initState] using hwv)
            (by simpa [initState] using hlarge))
      · exact execResultsEquiv.revert rfl rfl
  simpa using hequiv

end Ripemd160
