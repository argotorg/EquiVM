import Examples.Ripemd160Old.Equivalence
import Examples.Ripemd160Old.DecodeOversized

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 5000000

namespace Ripemd160Old

open Ripemd160

private theorem runtime_panic41 {cA σ I} {g : Sat256} {s0 : State}
    {t : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {k C : Nat}
    (rd39 : RD runtimeBytecode I g s0 ⟨39⟩ t mem aw rdata (cA, σ) k C)
    (hov : t.length + 4 ≤ 1024) :
    RDrev runtimeBytecode g s0 := by
  have rd48 := evm_run_rfl rd39 with [
    jumpdest, push4 ⟨1313373041⟩, push1 ⟨224⟩, shl, push0 ]
  have rd49 := RD.runtimeMstore rd48 (by old_decode) (by evm_ov)
  have rd54 := evm_run_rfl rd49 with [push1 ⟨65⟩, push1 ⟨4⟩]
  have rd55 := RD.runtimeMstore rd54 (by old_decode) (by evm_ov)
  exact evm_run_rfl rd55 with [
    push1 ⟨36⟩, push0,
    raw rev 0 (by old_decode) (by
      intro s haw hstk
      have hmax1 : max aw.toNat 1 < UInt256.size :=
        max_lt aw.val.isLt (by native_decide)
      have hto1 : (UInt256.ofNat (max aw.toNat 1)).toNat = max aw.toNat 1 :=
        ulit_toNat' _ hmax1
      have hmax2 : max aw.toNat 2 < UInt256.size :=
        max_lt aw.val.isLt (by native_decide)
      have hto2 : (UInt256.ofNat (max aw.toNat 2)).toNat =
          max aw.toNat 2 := ulit_toNat' _ hmax2
      norm_num [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        runtimeMstoreAw, MachineState.M, hto1, hto2,
        show (⟨4⟩ : UInt256).toNat = 4 by decide,
        show (⟨36⟩ : UInt256).toNat = 36 by decide]) (by evm_ov) ]

/-- Calldata larger than `uint64` fails the old allocator's first check. -/
theorem runtime_calldata_gt_u64 {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size)
    (hhuge : 18446744073709551615 < I.calldata.size) :
    RDrev runtimeBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd121⟩ := runtime_reachAllocator
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hcode hwv
  have hgt : UInt256.gt (calldataSizeWord I) ⟨18446744073709551615⟩ = ⟨1⟩ := by
    apply ugt_one
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat =
      18446744073709551615 by native_decide]
    simpa [calldataSizeWord, ulit_toNat' I.calldata.size hsize] using hhuge
  have rd122 := evm_run_rfl rd121 with [jumpdest]
  have rd131 := RD.pushConst rd122 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by decide) (by old_decode) (by evm_ov)
  have rd151 := evm_run_rfl rd131 with [
    dup2, gt, push2 ⟨151⟩, jumpiT (by rw [hgt]; decide) jump_151 ]
  have rd39 := evm_run_rfl rd151 with [
    jumpdest, push2 ⟨39⟩, jump jump_39 ]
  exact runtime_panic41 rd39 (by simp)

/-- The rounded old allocation exceeds `uint64` while the calldata length itself does not. -/
theorem runtime_calldata_rounding_overflow {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size)
    (hmax : I.calldata.size ≤ 18446744073709551615)
    (hlarge : maxFallbackCalldataSize < I.calldata.size) :
    RDrev runtimeBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd121⟩ := runtime_reachAllocator
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hcode hwv
  have hgt0 : UInt256.gt (calldataSizeWord I) ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat =
      18446744073709551615 by native_decide]
    simpa [calldataSizeWord, ulit_toNat' I.calldata.size hsize] using hmax
  have rd122 := evm_run_rfl rd121 with [jumpdest]
  have rd131 := RD.pushConst rd122 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by decide) (by old_decode) (by evm_ov)
  have rd29 := evm_run_rfl rd131 with [
    dup2, gt, push2 ⟨151⟩, jumpiNT hgt0,
    push2 ⟨147⟩, push1 ⟨32⟩, swap2, push2 ⟨29⟩,
    jump jump_29, jumpdest ]
  have rd183 := evm_run_rfl rd29 with [
    push1 ⟨31⟩, dup1, not, swap2, add, and, swap1,
    jump jump_147, jumpdest, add, swap1, jump jump_183,
    jumpdest, push2 ⟨100⟩, jump jump_100, jumpdest ]
  have rd69 := evm_run_rfl rd183 with [
    swap1, push2 ⟨119⟩, push2 ⟨112⟩, push2 ⟨15⟩,
    jump jump_15, jumpdest, push1 ⟨64⟩ ]
  have rd18 := RD.mload 0 ⟨128⟩ (UInt256.ofNat 3)
    rd69 (by old_decode) mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov)
  have rd29' := evm_run_rfl rd18 with [
    swap1, jump jump_112, jumpdest,
    swap3, dup4, push2 ⟨59⟩, jump jump_59, jumpdest,
    swap1, push2 ⟨69⟩, swap1, push2 ⟨29⟩,
    jump jump_29, jumpdest,
    push1 ⟨31⟩, dup1, not, swap2, add, and, swap1,
    jump jump_69, jumpdest ]
  have hfreeStack :
      ⟨128⟩ + UInt256.land
          ((UInt256.land (calldataSizeWord I + ⟨31⟩) (UInt256.lnot ⟨31⟩) +
            ⟨32⟩) + ⟨31⟩)
          (UInt256.lnot ⟨31⟩) = fallbackFreePtr I := by
    simpa [u256_add_assoc] using fallbackFreePtr_stack_eq I hmax
  have hbad : UInt256.lor
      (UInt256.gt (fallbackFreePtr I) ⟨18446744073709551615⟩)
      (UInt256.lt (fallbackFreePtr I) ⟨128⟩) = ⟨1⟩ := by
    rw [fallbackFreePtr_gt_u64_of_large I hmax hlarge,
      fallbackFreePtr_not_lt_128 I hmax]
    decide
  have rd75 := evm_run_rfl rd29' with [dup2, add, swap1, dup2, lt]
  have rd84 := RD.pushConst rd75 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by decide) (by old_decode) (by evm_ov)
  have rd95 := evm_run_rfl rd84 with [
    dup3, gt, or, push2 ⟨95⟩,
    jumpiT (by rw [hfreeStack, hbad]; decide) jump_95 ]
  have rd39 := evm_run_rfl rd95 with [
    jumpdest, push2 ⟨39⟩, jump jump_39 ]
  exact runtime_panic41 rd39 (by simp)

/-- Equivalence for calls rejected by the old compiler's allocator. -/
theorem fallbackOversized {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = runtimeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hlarge : maxFallbackCalldataSize < I.calldata.size) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrun : RDrev runtimeBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
    by_cases hmax : I.calldata.size ≤ 18446744073709551615
    · exact runtime_calldata_rounding_overflow hcode hwv hsize hmax hlarge
    · exact runtime_calldata_gt_u64 hcode hwv hsize (by omega)
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

end Ripemd160Old
