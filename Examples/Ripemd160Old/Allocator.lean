import Examples.Ripemd160Old.Entry

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

open Ripemd160

/-- The old allocator accepts bounded calldata and reaches the calldata-copy helper. -/
theorem runtime_reachCopy {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    ∃ k C, RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨156⟩
      [⟨0⟩, ⟨160⟩, calldataSizeWord I, ⟨214⟩, ⟨232⟩, ⟨128⟩, ⟨249⟩, ⟨254⟩]
      (fallbackLengthMem I) (UInt256.ofNat 5) ByteArray.empty (cA, σ) k C := by
  have hmax : I.calldata.size ≤ 18446744073709551615 := by
    unfold maxFallbackCalldataSize at hsmall
    omega
  obtain ⟨_, _, rd121⟩ := runtime_reachAllocator
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hcode hwv
  have hgt0 :
      UInt256.gt (calldataSizeWord I) ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = 18446744073709551615 from by
      native_decide]
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
  have rd28 := evm_run_rfl rd183 with [
    swap1, push2 ⟨119⟩, push2 ⟨112⟩, push2 ⟨15⟩,
    jump jump_15, jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by old_decode)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    swap1, jump jump_112, jumpdest,
    swap3, dup4, push2 ⟨59⟩, jump jump_59, jumpdest,
    swap1, push2 ⟨69⟩, swap1, push2 ⟨29⟩,
    jump jump_29, jumpdest,
    push1 ⟨31⟩, dup1, not, swap2, add, and, swap1,
    jump jump_69, jumpdest ]
  have hfreeStack :
      ⟨128⟩ + UInt256.land
          ((UInt256.land (calldataSizeWord I + ⟨31⟩) (UInt256.lnot ⟨31⟩) + ⟨32⟩) + ⟨31⟩)
          (UInt256.lnot ⟨31⟩) = fallbackFreePtr I := by
    simpa [u256_add_assoc] using fallbackFreePtr_stack_eq I hmax
  have hbad0 :
      UInt256.lor
        (UInt256.gt (fallbackFreePtr I) ⟨18446744073709551615⟩)
        (UInt256.lt (fallbackFreePtr I) ⟨128⟩) = ⟨0⟩ := by
    rw [fallbackFreePtr_le_u64_of_small I hsmall,
      fallbackFreePtr_not_lt_128 I hmax]
    decide
  have rd91 := evm_run_rfl rd28 with [dup2, add, swap1, dup2, lt]
  have rd84 := RD.pushConst rd91 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by decide) (by old_decode) (by evm_ov)
  have rd100 := evm_run_rfl rd84 with [
    dup3, gt, or, push2 ⟨95⟩,
    jumpiNT (by rw [hfreeStack, hbad0]),
    push1 ⟨64⟩,
    raw mstore 0 (fallbackAllocMem I) (UInt256.ofNat 3) (by old_decode)
      mem_cost
      (by
        unfold fallbackAllocMem
        rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide,
          hfreeStack])
      (by decide) (by evm_ov),
    jump jump_119, jumpdest, jump jump_188, jumpdest ]
  have rd156 := evm_run_rfl rd100 with [
    swap4, dup2, dup6,
    raw mstore 6 (fallbackLengthMem I) (UInt256.ofNat 5) (by old_decode)
      mem_cost
      (by unfold fallbackLengthMem; rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide])
      (by decide) (by evm_ov),
    push1 ⟨32⟩, dup6, add, swap1, dup3, dup5, add, gt,
    push2 ⟨216⟩, jumpiNT (by rw [u256_zero_add]; apply ugt_zero; omega),
    push2 ⟨214⟩, swap3, push2 ⟨156⟩, jump jump_156 ]
  exact ⟨_, _, by simpa [fallbackAllocationSize, roundedCalldataSizeWord,
    u256_land_comm] using rd156⟩

end Ripemd160Old
