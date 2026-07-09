import Benchmarks.OpenZeppelinBench.TimelockController.Dispatch

/-!
# OpenZeppelin TimelockController shared return routines

`tlcReturnWord` is solc 0.8.35's split 32-byte return encoder (store `val` at the free pointer @581,
jump to the return dispatcher @521, `RETURN(0x80, 0x20)`).  Shared by every `uint256` / `bytes32`
getter.  (The library's single-block `RD.solcReturnWordFromMem` does not match this split shape.)

LIBRARY CANDIDATE: `Reasoning.Solc` — split-encoder analogue of `RD.solcReturnWordFromMem`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace OpenZeppelinBench.TimelockController

/-- Shared 32-byte return encoder: from pc 581 with `[val, cont, R]` and the free-pointer memory,
    store `val` at 0x80 (@581), jump to the return dispatcher (@521), and `RETURN(0x80, 0x20)` the
    32 bytes of `val`.  Used by every `uint256` / `bytes32` getter. -/
theorem tlcReturnWord {cA gh bl σ σ₀ A I} {g : Sat256} {val cont : UInt256} {R : List UInt256}
    {k C : ℕ}
    (h : RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨581⟩
      (val :: cont :: R) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hov : R.length + 5 ≤ 1024) :
    RDret timelockControllerBenchBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray val) := by
  have h521 := h.jumpdest (by native_decide) (by simp only [List.length_cons]; omega)
    |>.push1 ⟨64⟩ (by native_decide) (by simp only [List.length_cons]; omega)
    |>.mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide) mem_cost solcFreePtrMem_mload64
        (by decide) (by evm_ov)
    |>.swap1 (by native_decide) (by simp only [List.length_cons]; omega)
    |>.dup2 (by native_decide) (by simp only [List.length_cons]; omega)
    |>.mstore 6 (solcReturnMem val) (UInt256.ofNat 5) (by native_decide) mem_cost
        (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl) (by decide) (by evm_ov)
    |>.push1 ⟨32⟩ (by native_decide) (by simp only [List.length_cons]; omega)
    |>.add (by native_decide) (by simp only [List.length_cons]; omega)
    |>.push2 ⟨521⟩ (by native_decide) (by simp only [List.length_cons]; omega)
    |>.jump (by native_decide) (by jump_dest) (by simp only [List.length_cons]; omega)
  have hret := h521.jumpdest (by native_decide) (by simp only [List.length_cons]; omega)
    |>.push1 ⟨64⟩ (by native_decide) (by simp only [List.length_cons]; omega)
    |>.mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide) mem_cost (solcReturnMem_mload64 val)
        (by decide) (by evm_ov)
    |>.dup1 (by native_decide) (by simp only [List.length_cons]; omega)
    |>.swap2 (by native_decide) (by simp only [List.length_cons]; omega)
    |>.sub (by native_decide) (by simp only [List.length_cons]; omega)
    |>.swap1 (by native_decide) (by simp only [List.length_cons]; omega)
  exact hret.ret 0 (UInt256.toByteArray val) (by native_decide) mem_cost
    (by rw [show ((⟨32⟩ + ⟨128⟩ : UInt256).sub ⟨128⟩).toNat = 32 from by decide,
        show (⟨128⟩ : UInt256).toNat = 128 from by decide]; exact solcReturnMem_read128 val)
    (by simp only [List.length_cons]; omega)

end OpenZeppelinBench.TimelockController
