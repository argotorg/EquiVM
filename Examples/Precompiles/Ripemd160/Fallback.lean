import Examples.Precompiles.Ripemd160.HashMemory
import Examples.Precompiles.Ripemd160.ProofSupportExact
import Reasoning.ReachExact

/-!
# Ripemd160Deployed bytecode entry

Every zero-value call enters the hashing body, while a nonzero-value call is rejected by the
compiler-generated nonpayable guard.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Ripemd160

/-! ## Exact gas model for fallback setup and padding -/

/-- Number of calldata words charged by `CALLDATACOPY` and `MCOPY`. -/
def ripemd160CalldataWords (I : ExecutionEnv) : Nat :=
  (I.calldata.size + 31) / 32

/-- Exact gas from bytecode entry through the jump to the hash routine (PC 776). -/
def ripemd160ReachHashGas (I : ExecutionEnv) : Nat :=
  201
    + (Cₘ (fallbackCopyAw I) - Cₘ (UInt256.ofNat 5))
    + 3 * ripemd160CalldataWords I
    + (Cₘ (fallbackPaddedAw I) - Cₘ (fallbackCopyAw I))

/-- Additional gas from PC 776 through the zero-fill loop header at PC 839. -/
def ripemd160ReachZeroLoopGas (I : ExecutionEnv) : Nat :=
  79
    + (Cₘ (hashCopiedAw I) - Cₘ (fallbackPaddedAw I))
    + 3 * ripemd160CalldataWords I

/-- Exact gas for `v` zero-fill iterations starting at iteration `i`, including loop exit. -/
def ripemd160ZeroLoopGas (I : ExecutionEnv) : Nat → Nat → Nat
  | 0, _ => 27
  | v + 1, i =>
      55 + (Cₘ (hashZeroAw I (i + 1)) - Cₘ (hashZeroAw I i))
        + ripemd160ZeroLoopGas I v (i + 1)

/-- Additional gas for writing the marker/length and loading the RIPEMD IV. -/
def ripemd160HashInitGas (I : ExecutionEnv) : Nat :=
  186
    + (Cₘ (hashMarkerAw I) - Cₘ (hashZeroAw I (hashZeroIterations I)))
    + (Cₘ (hashPaddedMessageAw I) - Cₘ (hashMarkerAw I))

/-- Exact gas from bytecode entry to the outer compression-loop header. -/
def ripemd160SetupGas (I : ExecutionEnv) : Nat :=
  ripemd160ReachHashGas I
    + ripemd160ReachZeroLoopGas I
    + ripemd160ZeroLoopGas I (hashZeroIterations I) 0
    + ripemd160HashInitGas I
    + 29

/-- The optimized runtime checks `CALLVALUE` directly and jumps to the empty revert stub. -/
theorem ripemd160X_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = ripemd160RuntimeBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev ripemd160RuntimeBytecode g (initState cA gh bl σ σ₀ g A I) := by
  apply RDxRev.toRDrev
  exact evm_run (RDx.initState hcode) with [
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

/-! ## Zero-value allocator guard -/

/-- The zero-value prologue falls through to the calldata-size allocator check at PC 10. -/
theorem ripemd160X_cvz_prefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = ripemd160RuntimeBytecode) (hwv : I.weiValue = ⟨0⟩) :
    ∃ k, RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨10⟩ [] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k 33 := by
  have rd0 :
      RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨0⟩ [] ByteArray.empty (UInt256.ofNat 0) ByteArray.empty (cA, σ) 0 0 :=
    RDx.initState hcode
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
  exact ⟨_, by convert rd10 using 1 <;> omega⟩

/-- Gas-erasing compatibility wrapper. -/
theorem ripemd160X_cvz_prefix {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = ripemd160RuntimeBytecode) (hwv : I.weiValue = ⟨0⟩) :
    ∃ k C, RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨10⟩ [] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, h⟩ := ripemd160X_cvz_prefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hcode hwv
  exact ⟨k, 33, h⟩

/-- The shared Solidity panic-0x41 tail reached by either allocator bound check. -/
theorem ripemd160X_panic41 {cA gh bl σ σ₀ A I} {g : Sat256} {stk : List UInt256}
    (hreach : ∃ k C, RDx ripemd160RuntimeBytecode I g
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
  have rd175 := RDx.pushConst rd141 panicSelectorWord
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by omega)
  apply RDxRev.toRDrev
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
  have rd19 := RDx.pushConst rd10 ⟨18446744073709551615⟩
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
  have rd19 := RDx.pushConst rd10 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have rd28 := evm_run rd19 with [
    calldatasize,
    gt,
    push2 ⟨132⟩,
    jumpiNT hgt0,
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov) ]
  have rd61 := RDx.pushConst rd28 (UInt256.lnot ⟨31⟩)
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
  have rd86 := RDx.pushConst rd77 ⟨18446744073709551615⟩
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
theorem ripemd160X_reachHashGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = ripemd160RuntimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    ∃ k, RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨776⟩ [⟨128⟩, ⟨122⟩]
      (fallbackPaddedMem I) (fallbackPaddedAw I) ByteArray.empty (cA, σ) k
      (ripemd160ReachHashGas I) := by
  have hmax : I.calldata.size ≤ 18446744073709551615 := by
    unfold maxFallbackCalldataSize at hsmall
    omega
  obtain ⟨k0, rd10⟩ := ripemd160X_cvz_prefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hcode hwv
  have hgt0 :
      UInt256.gt (calldataSizeWord I) ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = 18446744073709551615 from by
      native_decide]
    simpa [calldataSizeWord, ulit_toNat' I.calldata.size hsize] using hmax
  have rd19 := RDx.pushConst rd10 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have rd28 := evm_run rd19 with [
    calldatasize,
    gt,
    push2 ⟨132⟩,
    jumpiNT hgt0,
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov) ]
  have rd61 := RDx.pushConst rd28 (UInt256.lnot ⟨31⟩)
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have rd77 := evm_run rd61 with [
    push1 ⟨63⟩, dup2, push1 ⟨31⟩, calldatasize, add, and, add, and,
    dup2, add, swap1, dup1, dup3, lt ]
  have rd86 := RDx.pushConst rd77 ⟨18446744073709551615⟩
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
  have rd110 := RDx.calldatacopy
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
  have rd118 := RDx.mstore
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
  refine ⟨k0 + 50, ?_⟩
  convert rd776 using 1
  simp only [ripemd160ReachHashGas, ripemd160CalldataWords,
    GasConstants.Gverylow, GasConstants.Gcopy]
  rw [ulit_toNat' I.calldata.size hsize]
  omega

/-- Gas-erasing compatibility wrapper. -/
theorem ripemd160X_reachHash {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = ripemd160RuntimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    ∃ k C, RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨776⟩ [⟨128⟩, ⟨122⟩]
      (fallbackPaddedMem I) (fallbackPaddedAw I) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, h⟩ := ripemd160X_reachHashGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hcode hwv hsize hsmall
  exact ⟨k, ripemd160ReachHashGas I, h⟩

/-- Hash entry through padded-buffer allocation and `MCOPY`, at the zero-fill loop header. -/
theorem ripemd160X_reachZeroLoopGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = ripemd160RuntimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    ∃ k, RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨839⟩
      [calldataSizeWord I, hashPaddedLengthWord I, calldataSizeWord I,
        hashNewFreePtr I, hashPadPtr I, calldataSizeWord I + ⟨72⟩, ⟨122⟩]
      (hashCopiedMem I) (hashCopiedAw I) ByteArray.empty (cA, σ) k
      (ripemd160ReachHashGas I + ripemd160ReachZeroLoopGas I) := by
  obtain ⟨k0, rd776⟩ := ripemd160X_reachHashGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hcode hwv hsize hsmall
  have rd778 := evm_run rd776 with [jumpdest, dup1]
  have rd779 := RDx.mload 0 (calldataSizeWord I) (fallbackPaddedAw I)
    rd778 (by native_decide)
    (fallbackPaddedMload128Cost I hsmall)
    (fallbackPaddedMload128Value I hsmall)
    (fallbackPaddedAw_mload128 I hsmall) (by simp)
  have rd784 := evm_run rd779 with [push1 ⟨72⟩, dup2, add, swap2]
  have rd817 := RDx.pushConst rd784 (UInt256.lnot ⟨63⟩)
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have rd822 := evm_run rd817 with [dup4, and, swap2, push1 ⟨64⟩]
  have rd823 := RDx.mload 0 (hashPadPtr I) (fallbackPaddedAw I)
    rd822 (by native_decide)
    (fallbackPaddedMload64Cost I hsmall)
    (fallbackPaddedMload64Value I hsmall)
    (fallbackPaddedAw_mload64 I hsmall) (by simp)
  have rd834 := evm_run rd823 with [
    swap3, dup2, push1 ⟨32⟩, dup3, dup7, add, swap5, dup6, push1 ⟨64⟩ ]
  have rd835 := RDx.mstore 0 (hashAllocatedMem I) (fallbackPaddedAw I)
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
  have rd838 := RDx.mcopy
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
  refine ⟨k0 + 27, ?_⟩
  simpa only [hashNewFreePtr, hashPadPtr, hashPaddedLengthWord] using
    (show RDx ripemd160RuntimeBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨839⟩ _
      (hashCopiedMem I) (hashCopiedAw I) ByteArray.empty (cA, σ) (k0 + 27)
      (ripemd160ReachHashGas I + ripemd160ReachZeroLoopGas I) from by
        convert rd839 using 1
        simp only [ripemd160ReachZeroLoopGas, ripemd160CalldataWords,
          GasConstants.Gverylow, GasConstants.Gcopy]
        rw [ulit_toNat' I.calldata.size hsize]
        omega)

/-- Gas-erasing compatibility wrapper. -/
theorem ripemd160X_reachZeroLoop {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = ripemd160RuntimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    ∃ k C, RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨839⟩
      [calldataSizeWord I, hashPaddedLengthWord I, calldataSizeWord I,
        hashNewFreePtr I, hashPadPtr I, calldataSizeWord I + ⟨72⟩, ⟨122⟩]
      (hashCopiedMem I) (hashCopiedAw I) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, h⟩ := ripemd160X_reachZeroLoopGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hcode hwv hsize hsmall
  exact ⟨k, ripemd160ReachHashGas I + ripemd160ReachZeroLoopGas I, h⟩

private theorem ripemd160X_zeroLoopBodyGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) {i k C : Nat}
    (hi : i < hashZeroIterations I)
    (h : RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨839⟩
      [hashZeroIndexWord I i, hashPaddedLengthWord I, calldataSizeWord I,
        hashNewFreePtr I, hashPadPtr I, calldataSizeWord I + ⟨72⟩, ⟨122⟩]
      (hashZeroMem I i) (hashZeroAw I i) ByteArray.empty (cA, σ) k C) :
    ∃ k', RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨839⟩
      [hashZeroIndexWord I (i + 1), hashPaddedLengthWord I, calldataSizeWord I,
        hashNewFreePtr I, hashPadPtr I, calldataSizeWord I + ⟨72⟩, ⟨122⟩]
      (hashZeroMem I (i + 1)) (hashZeroAw I (i + 1))
      ByteArray.empty (cA, σ) k'
        (C + (55 + (Cₘ (hashZeroAw I (i + 1)) - Cₘ (hashZeroAw I i)))) := by
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
  have rd2194 := RDx.mstore
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
  refine ⟨k + 16, ?_⟩
  simpa only [hnext] using (show RDx ripemd160RuntimeBytecode I g
    (initState cA gh bl σ σ₀ g A I) ⟨839⟩
    [(⟨32⟩ : UInt256) + hashZeroIndexWord I i, hashPaddedLengthWord I,
      calldataSizeWord I, hashNewFreePtr I, hashPadPtr I,
      calldataSizeWord I + ⟨72⟩, ⟨122⟩]
    (hashZeroMem I (i + 1)) (hashZeroAw I (i + 1))
    ByteArray.empty (cA, σ) (k + 16)
      (C + (55 + (Cₘ (hashZeroAw I (i + 1)) - Cₘ (hashZeroAw I i)))) from by
        convert rd839 using 1 <;> omega)

private theorem ripemd160X_zeroLoopBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) {i k C : Nat}
    (hi : i < hashZeroIterations I)
    (h : RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨839⟩
      [hashZeroIndexWord I i, hashPaddedLengthWord I, calldataSizeWord I,
        hashNewFreePtr I, hashPadPtr I, calldataSizeWord I + ⟨72⟩, ⟨122⟩]
      (hashZeroMem I i) (hashZeroAw I i) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨839⟩
      [hashZeroIndexWord I (i + 1), hashPaddedLengthWord I, calldataSizeWord I,
        hashNewFreePtr I, hashPadPtr I, calldataSizeWord I + ⟨72⟩, ⟨122⟩]
      (hashZeroMem I (i + 1)) (hashZeroAw I (i + 1))
      ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨k', h'⟩ := ripemd160X_zeroLoopBodyGas hsmall hi h
  exact ⟨k', _, h'⟩

private theorem ripemd160X_zeroLoopExitGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) {i k C : Nat}
    (hi : i = hashZeroIterations I)
    (h : RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨839⟩
      [hashZeroIndexWord I i, hashPaddedLengthWord I, calldataSizeWord I,
        hashNewFreePtr I, hashPadPtr I, calldataSizeWord I + ⟨72⟩, ⟨122⟩]
      (hashZeroMem I i) (hashZeroAw I i) ByteArray.empty (cA, σ) k C) :
    ∃ k', RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨849⟩
      [calldataSizeWord I, hashNewFreePtr I, hashPadPtr I,
        calldataSizeWord I + ⟨72⟩, ⟨122⟩]
      (hashZeroMem I i) (hashZeroAw I i) ByteArray.empty (cA, σ) k' (C + 27) := by
  have hi3 : i ≤ 3 := by rw [hi]; exact hashZeroIterations_le_three I
  have hlt : UInt256.lt (hashZeroIndexWord I i) (hashPaddedLengthWord I) = ⟨0⟩ := by
    apply ult_zero
    rw [hashZeroIndexWord_toNat I i hsmall hi3,
      hashPaddedLengthWord_toNat I hsmall]
    rw [hi]
    exact hashZeroIterations_exit I
  have h' := evm_run h with [
    jumpdest, dup2, dup2, lt, push2 ⟨2187⟩,
    jumpiNT (by rw [hlt]), pop, pop ]
  exact ⟨k + 8, by convert h' using 1 <;> omega⟩

private theorem ripemd160X_zeroLoopExit {cA gh bl σ σ₀ A I} {g : Sat256}
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) {i k C : Nat}
    (hi : i = hashZeroIterations I)
    (h : RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨839⟩
      [hashZeroIndexWord I i, hashPaddedLengthWord I, calldataSizeWord I,
        hashNewFreePtr I, hashPadPtr I, calldataSizeWord I + ⟨72⟩, ⟨122⟩]
      (hashZeroMem I i) (hashZeroAw I i) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨849⟩
      [calldataSizeWord I, hashNewFreePtr I, hashPadPtr I,
        calldataSizeWord I + ⟨72⟩, ⟨122⟩]
      (hashZeroMem I i) (hashZeroAw I i) ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨k', h'⟩ := ripemd160X_zeroLoopExitGas hsmall hi h
  exact ⟨k', _, h'⟩

/-- Run the complete zero-fill loop and discard its index and bound. -/
theorem ripemd160X_zeroPaddingGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = ripemd160RuntimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    ∃ k, RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨849⟩
      [calldataSizeWord I, hashNewFreePtr I, hashPadPtr I,
        calldataSizeWord I + ⟨72⟩, ⟨122⟩]
      (hashZeroMem I (hashZeroIterations I))
      (hashZeroAw I (hashZeroIterations I)) ByteArray.empty (cA, σ) k
      (ripemd160ReachHashGas I + ripemd160ReachZeroLoopGas I
        + ripemd160ZeroLoopGas I (hashZeroIterations I) 0) := by
  obtain ⟨k, rd839⟩ := ripemd160X_reachZeroLoopGas
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
      RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨839⟩ (stk i) (hashZeroMem I i) (hashZeroAw I i)
        ByteArray.empty (cA, σ) k C →
      ∃ k', RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨849⟩ (exitStk i) (hashZeroMem I i) (hashZeroAw I i)
        ByteArray.empty (cA, σ) k' (C + ripemd160ZeroLoopGas I 0 i) := by
    intro i hi k C h
    simpa [stk, exitStk, ripemd160ZeroLoopGas] using
      ripemd160X_zeroLoopExitGas hsmall (by simpa [Inv] using hi) (by
        simpa [stk] using h)
  have hbody : ∀ v i, Inv (v + 1) i → ∀ k C,
      RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨839⟩ (stk i) (hashZeroMem I i) (hashZeroAw I i)
        ByteArray.empty (cA, σ) k C →
      ∃ i' k' dC, Inv v i' ∧
        ripemd160ZeroLoopGas I (v + 1) i =
          dC + ripemd160ZeroLoopGas I v i' ∧
        RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
          ⟨839⟩ (stk i') (hashZeroMem I i') (hashZeroAw I i')
          ByteArray.empty (cA, σ) k' (C + dC) := by
    intro v i hi k C h
    have hit : i < hashZeroIterations I := by dsimp [Inv] at hi; omega
    obtain ⟨k', h'⟩ := ripemd160X_zeroLoopBodyGas hsmall hit (by simpa [stk] using h)
    refine ⟨i + 1, k',
      55 + (Cₘ (hashZeroAw I (i + 1)) - Cₘ (hashZeroAw I i)), ?_, ?_, ?_⟩
    · dsimp [Inv] at hi ⊢; omega
    · rfl
    · simpa [stk] using h'
  obtain ⟨i, k', hi, h'⟩ :=
    RDx.whileLoopCarryGas (code := ripemd160RuntimeBytecode) (ee := I) (g := g)
      (s0 := initState cA gh bl σ σ₀ g A I) (rdata := ByteArray.empty)
      (acc := (cA, σ)) (α := Nat) ⟨839⟩ ⟨849⟩ Inv stk
      (hashZeroMem I) (hashZeroAw I) exitStk (ripemd160ZeroLoopGas I) hexit hbody
      (hashZeroIterations I) 0 (by simp [Inv]) k
      (ripemd160ReachHashGas I + ripemd160ReachZeroLoopGas I) (by
        simpa [stk, hashZeroMem, hashZeroAw, hashZeroIndexWord,
          calldataSizeWord, ulit_toNat' I.calldata.size hsize] using rd839)
  have hieq : i = hashZeroIterations I := by dsimp [Inv] at hi; omega
  subst i
  exact ⟨k', by simpa [exitStk] using h'⟩

/-- Gas-erasing compatibility wrapper. -/
theorem ripemd160X_zeroPadding {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = ripemd160RuntimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    ∃ k C, RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨849⟩
      [calldataSizeWord I, hashNewFreePtr I, hashPadPtr I,
        calldataSizeWord I + ⟨72⟩, ⟨122⟩]
      (hashZeroMem I (hashZeroIterations I))
      (hashZeroAw I (hashZeroIterations I)) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, h⟩ := ripemd160X_zeroPaddingGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hcode hwv hsize hsmall
  exact ⟨k, _, h⟩

/-- Write the marker and little-endian bit length, then place RIPEMD's five IVs on the stack. -/
theorem ripemd160X_reachHashInitGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = ripemd160RuntimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    ∃ k, RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1014⟩
      [calldataSizeWord I + ⟨72⟩, hashPadPtr I,
        ⟨0x67452301⟩, ⟨0xc3d2e1f0⟩, ⟨0x10325476⟩,
        ⟨0x98badcfe⟩, ⟨0xefcdab89⟩, ⟨122⟩]
      (hashPaddedMessageMem I) (hashPaddedMessageAw I)
      ByteArray.empty (cA, σ) k
      (ripemd160ReachHashGas I + ripemd160ReachZeroLoopGas I
        + ripemd160ZeroLoopGas I (hashZeroIterations I) 0
        + ripemd160HashInitGas I) := by
  obtain ⟨k0, rd849⟩ := ripemd160X_zeroPaddingGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hcode hwv hsize hsmall
  have rd855 := evm_run rd849 with [push2 ⟨977⟩, dup2, push1 ⟨128⟩]
  have rd888 := RDx.pushConst rd855 (UInt256.lnot ⟨7⟩)
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have rd891 := evm_run rd888 with [swap4, dup7, add]
  have rd892 := RDx.mstore8
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
  have rd904 := RDx.pushConst rd895 ⟨0xff00ff00ff00ff00⟩
    (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have rd912 := RDx.pushConst rd904 ⟨0x00ff00ff00ff00ff⟩
    (width := 7) (op := .PUSH7) (by decide) (by native_decide) (by evm_ov)
  have rd923 := evm_run rd912 with [
    dup3, push1 ⟨8⟩, shr, and, swap2, push1 ⟨8⟩, shl, and, or ]
  have rd932 := RDx.pushConst rd923 ⟨0xffff0000ffff0000⟩
    (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have rd939 := RDx.pushConst rd932 ⟨0x0000ffff0000ffff⟩
    (width := 6) (op := .PUSH6) (by decide) (by native_decide) (by evm_ov)
  have rd950 := evm_run rd939 with [
    dup3, push1 ⟨16⟩, shr, and, swap2, push1 ⟨16⟩, shl, and, or ]
  have rd959 := RDx.pushConst rd950 ⟨0xffffffff00000000⟩
    (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have rd964 := RDx.pushConst rd959 ⟨0x00000000ffffffff⟩
    (width := 4) (op := .PUSH4) (by decide) (by native_decide) (by evm_ov)
  have rd977 := evm_run rd964 with [
    dup3, push1 ⟨32⟩, shr, and, swap2, push1 ⟨32⟩, shl, and, or,
    swap1, jump (by jump_dest) ]
  have rd983 := evm_run rd977 with [jumpdest, push1 ⟨192⟩, shl, swap2, add]
  have rd984 := RDx.mstore
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
  refine ⟨k0 + 61, ?_⟩
  simpa using (show RDx ripemd160RuntimeBytecode I g
    (initState cA gh bl σ σ₀ g A I) ⟨1014⟩ _
    (hashPaddedMessageMem I) (hashPaddedMessageAw I)
    ByteArray.empty (cA, σ) (k0 + 61)
      (ripemd160ReachHashGas I + ripemd160ReachZeroLoopGas I
        + ripemd160ZeroLoopGas I (hashZeroIterations I) 0
        + ripemd160HashInitGas I) from by
          convert rd1014 using 1
          simp only [ripemd160HashInitGas]
          omega)

/-- Gas-erasing compatibility wrapper. -/
theorem ripemd160X_reachHashInit {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = ripemd160RuntimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    ∃ k C, RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1014⟩
      [calldataSizeWord I + ⟨72⟩, hashPadPtr I,
        ⟨0x67452301⟩, ⟨0xc3d2e1f0⟩, ⟨0x10325476⟩,
        ⟨0x98badcfe⟩, ⟨0xefcdab89⟩, ⟨122⟩]
      (hashPaddedMessageMem I) (hashPaddedMessageAw I)
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, h⟩ := ripemd160X_reachHashInitGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hcode hwv hsize hsmall
  exact ⟨k, _, h⟩

/-- Allocate RIPEMD's scratch region and reach the outer 64-byte block loop. -/
theorem ripemd160X_reachBlockLoopGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = ripemd160RuntimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    ∃ k, RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1028⟩
      [hashPadPtr I, calldataSizeWord I + ⟨72⟩, hashScratchPtr I, ⟨0⟩,
        ⟨0x67452301⟩, ⟨0xc3d2e1f0⟩, ⟨0x10325476⟩,
        ⟨0x98badcfe⟩, ⟨0xefcdab89⟩, ⟨122⟩]
      (hashScratchMem I) (hashPaddedMessageAw I)
      ByteArray.empty (cA, σ) k (ripemd160SetupGas I) := by
  obtain ⟨k0, rd1014⟩ := ripemd160X_reachHashInitGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hcode hwv hsize hsmall
  have rd1016 := evm_run rd1014 with [push1 ⟨64⟩]
  have rd1017 := RDx.mload 0 (hashScratchPtr I) (hashPaddedMessageAw I)
    rd1016 (by native_decide)
    (hashPaddedMessageMload64Cost I hsmall)
    (hashPaddedMessageMload64Value I hsmall)
    (hashPaddedMessageAw_mload64 I hsmall) (by simp)
  have rd1025 := evm_run rd1017 with [
    swap1, push2 ⟨832⟩, dup3, add, push1 ⟨64⟩ ]
  have rd1026 := RDx.mstore 0 (hashScratchMem I) (hashPaddedMessageAw I)
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
  refine ⟨k0 + 10, ?_⟩
  simpa [hashScratchPtr] using (show RDx ripemd160RuntimeBytecode I g
    (initState cA gh bl σ σ₀ g A I) ⟨1028⟩ _
    (hashScratchMem I) (hashPaddedMessageAw I)
    ByteArray.empty (cA, σ) (k0 + 10) (ripemd160SetupGas I) from by
      convert rd1028 using 1)

/-- Gas-erasing compatibility wrapper. -/
theorem ripemd160X_reachBlockLoop {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = ripemd160RuntimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    ∃ k C, RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1028⟩
      [hashPadPtr I, calldataSizeWord I + ⟨72⟩, hashScratchPtr I, ⟨0⟩,
        ⟨0x67452301⟩, ⟨0xc3d2e1f0⟩, ⟨0x10325476⟩,
        ⟨0x98badcfe⟩, ⟨0xefcdab89⟩, ⟨122⟩]
      (hashScratchMem I) (hashPaddedMessageAw I)
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, h⟩ := ripemd160X_reachBlockLoopGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hcode hwv hsize hsmall
  exact ⟨k, ripemd160SetupGas I, h⟩

end Ripemd160
