import Examples.Ripemd160Old.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

open Ripemd160

/-- The original unoptimized runtime rejects nonzero call value before entering the fallback. -/
theorem runtime_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev runtimeBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have rd0 : RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨0⟩ [] ByteArray.empty (UInt256.ofNat 0) ByteArray.empty (cA, σ) 0 0 :=
    RD.initState hcode
  exact evm_run_rfl rd0 with [
    push1 ⟨128⟩,
    push1 ⟨64⟩,
    raw mstore 9 solcFreePtrMem (UInt256.ofNat 3) (by old_decode)
      mem_cost
      (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; rfl)
      (by decide) (by evm_ov),
    callvalue,
    iszero,
    push2 ⟨235⟩,
    jumpiNT (isZero_eq_zero_of_ne hwv),
    push2 ⟨21⟩,
    jump jump_21,
    jumpdest,
    push0,
    dup1,
    raw rev 0 (by old_decode) mem_cost (by simp) ]

/-- The zero-value fallback reaches the old compiler's dynamic-bytes allocator. -/
theorem runtime_reachAllocator {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode) (hwv : I.weiValue = ⟨0⟩) :
    ∃ k C, RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨121⟩
      [calldataSizeWord I, ⟨183⟩, ⟨188⟩, calldataSizeWord I, ⟨0⟩,
        ⟨232⟩, calldataSizeWord I, ⟨249⟩, ⟨254⟩]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have rd0 : RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨0⟩ [] ByteArray.empty (UInt256.ofNat 0) ByteArray.empty (cA, σ) 0 0 :=
    RD.initState hcode
  have rd235 := evm_run_rfl rd0 with [
    push1 ⟨128⟩,
    push1 ⟨64⟩,
    raw mstore 9 solcFreePtrMem (UInt256.ofNat 3) (by old_decode)
      mem_cost
      (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; rfl)
      (by decide) (by evm_ov),
    callvalue, iszero, push2 ⟨235⟩,
    jumpiT (by rw [hwv]; decide) jump_235, jumpdest ]
  have rd121 := evm_run_rfl rd235 with [
    push2 ⟨254⟩, push2 ⟨249⟩, push0, calldatasize, swap1,
    push2 ⟨221⟩, jump jump_221,
    jumpdest, push2 ⟨232⟩, swap2, calldatasize, swap2,
    push2 ⟨167⟩, jump jump_167,
    jumpdest, swap1, swap3, swap2, swap3,
    push2 ⟨188⟩, push2 ⟨183⟩, dup3,
    push2 ⟨121⟩, jump jump_121 ]
  exact ⟨_, _, rd121⟩

/-- Runtime equivalence for the nonzero-callvalue branch. -/
theorem fallbackNonPayable {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = runtimeBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    runtimeEquivalenceFor Ripemd160.config Ripemd160.contract
      cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrun := runtime_callvalue_ne
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) hcode hwv
  have hequiv :
      runtimeEquivalenceFor Ripemd160.config Ripemd160.contract
        cA gh bl σ_evm σ_solm σ₀ (Sat256.ofUInt256 g).toUInt256 A I :=
    hrun.reEquivElim hcode fun _ _ hrev => by
      refine runtimeEquivalenceFor.execution
        (returnConvention := .rawBytes) (solmRes := .reverted) hrev ?_ ?_
      · exact solmExec.fallback
          (Ripemd160.selectorDispatch_none I.calldata)
          (Ripemd160.receiveDispatch_none I.calldata)
          rfl
          (Ripemd160.fallback_callargs I.calldata)
          Ripemd160.fallback_returnConvention
          rfl
          (Ripemd160.fallbackBodyReverts_nonPayable
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (Ripemd160.fallbackLocals I)
            (by simpa [initState] using hwv))
      · exact execResultsEquiv.revert rfl rfl
  simpa using hequiv

end Ripemd160Old
