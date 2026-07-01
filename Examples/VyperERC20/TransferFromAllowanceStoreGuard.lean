import Examples.VyperERC20.TransferFromBalanceLoadPhase

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

namespace VyperERC20

theorem erc20X_transferFromAllowanceStoreGuard {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hallowance : (transferFromValueWord I).toNat ≤
      (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨445⟩
      [transferFromSelectorWord]
      (transferFromFromBalanceHashMem
        (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I)
        (transferFromCurrentAllowanceRaw σ I))
      (UInt256.ofNat 5) ByteArray.empty
      (cA, σ) k C) :
    ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨465⟩
      [transferFromAllowanceDebitWord (initState cA gh bl σ σ₀ g A I) I,
        transferFromSelectorWord]
      (transferFromFromBalanceHashMem
        (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I)
        (transferFromCurrentAllowanceRaw σ I))
      (UInt256.ofNat 5) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨k, C, rd445⟩ := hreach
  let evm0 := initState cA gh bl σ σ₀ g A I
  have hallowanceLoadRaw :
      transferFromCurrentAllowanceRaw σ I = transferFromCurrentAllowanceWord evm0 I := by
    simpa [evm0] using
      (transferFromCurrentAllowanceRaw_initState (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g))
  have hallowanceEnoughRaw :
      (transferFromValueWord I).toNat ≤ (transferFromCurrentAllowanceRaw σ I).toNat := by
    rw [hallowanceLoadRaw]
    simpa [evm0] using hallowance
  have hdebitNat :
      (transferFromAllowanceDebitWord evm0 I).toNat =
        (transferFromCurrentAllowanceWord evm0 I).toNat - (transferFromValueWord I).toNat := by
    unfold transferFromAllowanceDebitWord
    exact ulit_toNat' _ (lt_of_le_of_lt (Nat.sub_le _ _)
      (transferFromCurrentAllowanceWord evm0 I).val.isLt)
  have hdebitWordRaw :
      UInt256.sub (transferFromCurrentAllowanceRaw σ I) (transferFromValueWord I) =
        transferFromAllowanceDebitWord evm0 I := by
    apply u256_inj
    rw [usub_toNat hallowanceEnoughRaw, hallowanceLoadRaw, hdebitNat]
  have hdebitGuardRaw :
      UInt256.gt
          (UInt256.sub (transferFromCurrentAllowanceRaw σ I) (transferFromValueWord I))
          (transferFromCurrentAllowanceRaw σ I) = ⟨0⟩ := by
    exact ugt_zero (by
      rw [usub_toNat hallowanceEnoughRaw]
      exact Nat.sub_le _ _)
  have hdebitWordRaw' :
      UInt256.sub (transferFromCurrentAllowanceRaw σ I)
          (uInt256OfByteArray (I.calldata.readBytes (⟨68⟩ : UInt256).toNat 32)) =
        transferFromAllowanceDebitWord evm0 I := by
    simpa [transferFromValueWord] using hdebitWordRaw
  have rd465 := evm_run rd445 with [
    push1 ⟨128⟩,
    raw mload 0 (transferFromCurrentAllowanceRaw σ I) (UInt256.ofNat 5)
      (by vyper_erc20_transferFrom_decode) mem_cost
      (by
        exact mloadWordValue_of_readWithPadding
          (mem := transferFromFromBalanceHashMem
            (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I)
            (transferFromCurrentAllowanceRaw σ I))
          (aw := UInt256.ofNat 5) (off := ⟨128⟩) (v := transferFromCurrentAllowanceRaw σ I)
          (by rw [transferFromFromBalanceHashMem_size]; decide)
          (by decide)
          (transferFromFromBalanceHashMem_read128
            (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I)
            (transferFromCurrentAllowanceRaw σ I)))
      (by decide) (by evm_ov),
    push1 ⟨68⟩, calldataload,
    dup1, dup3, sub, dup3, dup2, gt, push2 ⟨801⟩,
    jumpiNT (by simpa [transferFromValueWord] using hdebitGuardRaw),
    swap1, pop, swap1, pop]
  exact ⟨_, _, by simpa [evm0, hdebitWordRaw'] using rd465⟩

end VyperERC20
