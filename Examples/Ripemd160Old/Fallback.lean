import Examples.Ripemd160Old.Allocator

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

open Ripemd160

/-- Accepted calldata is materialized as Solidity bytes memory before the old hash routine. -/
theorem runtime_reachHash {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    ∃ k C, RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨8306⟩ [⟨128⟩, ⟨254⟩]
      (fallbackPaddedMem I) (fallbackPaddedAw I) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd156⟩ := runtime_reachCopy
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hcode hsize hwv hsmall
  have hbase : (⟨160⟩ : UInt256).toNat = 160 := by decide
  have hcalldata : (calldataSizeWord I).toNat = I.calldata.size := by
    exact ulit_toNat' I.calldata.size hsize
  have hpadding : ((⟨160⟩ : UInt256) + calldataSizeWord I).toNat =
      160 + I.calldata.size := by
    have hfit : 160 + I.calldata.size < UInt256.size := by
      unfold maxFallbackCalldataSize at hsmall
      unfold UInt256.size
      omega
    rw [uadd_toNat, hbase, hcalldata, Nat.mod_eq_of_lt hfit]
  have rd163 := evm_run_rfl rd156 with [jumpdest, swap1, dup3, push0, swap4, swap3, dup3]
  have rd164 := RD.calldatacopy
    (Cₘ (fallbackCopyAw I) - Cₘ (UInt256.ofNat 5))
    (fallbackCalldataMem I) (fallbackCopyAw I)
    rd163 (by old_decode)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, fallbackCopyAw]
      rw [hbase, hcalldata])
    (by
      unfold fallbackCalldataMem
      rw [hbase, hcalldata,
        show (⟨0⟩ : UInt256).toNat = 0 from rfl])
    (by
      unfold fallbackCopyAw
      rw [hbase, hcalldata])
    (by evm_ov)
  have rd165 := evm_run_rfl rd164 with [add]
  have rd166 := RD.mstore
    (Cₘ (fallbackPaddedAw I) - Cₘ (fallbackCopyAw I))
    (fallbackPaddedMem I) (fallbackPaddedAw I)
    rd165 (by old_decode)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, fallbackPaddedAw]
      rw [hpadding])
    (by
      unfold fallbackPaddedMem
      rw [hpadding])
    (by
      unfold fallbackPaddedAw
      rw [hpadding])
    (by evm_ov)
  have rd8306 := evm_run_rfl rd166 with [
    jump jump_214, jumpdest, jump jump_232, jumpdest,
    swap1, jump jump_249, jumpdest,
    push2 ⟨8306⟩, jump jump_8306 ]
  exact ⟨_, _, rd8306⟩

end Ripemd160Old
