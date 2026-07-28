import Examples.VyperERC20.TransferFromBase

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

namespace VyperERC20

theorem erc20X_transferFromBeforeFromStoreCore {cA gh bl σ σ₀ A I} {g : Sat256}
    (hbalanceDebit : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord
        (transferFromAfterAllowanceState (initState cA gh bl σ σ₀ g A I) I) I).toNat)
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨508⟩
      [transferFromFromBalanceRawAfterAllowance σ I
          (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g),
        transferFromFromSlot I, transferFromSelectorWord]
      (transferFromAfterFromLoadMemI σ I)
      (UInt256.ofNat 5) ByteArray.empty
      (cA, transferFromAccountMapAfterAllowanceI σ I
        (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g)) k C) :
    ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨526⟩
      [transferFromFromSlot I,
        transferFromBalanceDebitWord
          (transferFromAfterAllowanceState (initState cA gh bl σ σ₀ g A I) I) I,
        transferFromFromSlot I, transferFromSelectorWord]
      (transferFromAfterFromLoadMemI σ I)
      (UInt256.ofNat 5) ByteArray.empty
      (cA, transferFromAccountMapAfterAllowanceI σ I
        (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g)) k C := by
  obtain ⟨k, C, rdAfterLoad⟩ := hreach
  let evm0 := initState cA gh bl σ σ₀ g A I
  let evm1 := transferFromAfterAllowanceState evm0 I
  have hfromLoadRaw :
      transferFromFromBalanceRawAfterAllowance σ I
          (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g) =
        transferFromFromBalanceWord evm1 I := by
    simpa [evm0, evm1] using
      (transferFromFromBalanceRawAfterAllowance_initState (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g))
  have hfromEnoughRaw :
      (transferFromValueWord I).toNat ≤
        (transferFromFromBalanceRawAfterAllowance σ I
          (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g)).toNat := by
    rw [hfromLoadRaw]
    simpa [evm0, evm1] using hbalanceDebit
  have hdebitNat :
      (transferFromBalanceDebitWord evm1 I).toNat =
        (transferFromFromBalanceWord evm1 I).toNat - (transferFromValueWord I).toNat := by
    unfold transferFromBalanceDebitWord
    exact ulit_toNat' _ (lt_of_le_of_lt (Nat.sub_le _ _)
      (transferFromFromBalanceWord evm1 I).val.isLt)
  have hdebitWordRaw :
      UInt256.sub
          (transferFromFromBalanceRawAfterAllowance σ I
            (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g))
          (transferFromValueWord I) =
        transferFromBalanceDebitWord evm1 I := by
    apply u256_inj
    rw [usub_toNat hfromEnoughRaw, hfromLoadRaw, hdebitNat]
  have hdebitGuardRaw :
      UInt256.gt
          (UInt256.sub
            (transferFromFromBalanceRawAfterAllowance σ I
              (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g))
            (transferFromValueWord I))
          (transferFromFromBalanceRawAfterAllowance σ I
            (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g))
        = ⟨0⟩ := by
    exact ugt_zero (by
      rw [usub_toNat hfromEnoughRaw]
      exact Nat.sub_le _ _)
  have rdBeforeStore := evm_run rdAfterLoad with [
    push1 ⟨68⟩, calldataload,
    dup1, dup3, sub, dup3, dup2, gt, push2 ⟨801⟩,
    jumpiNT (by simpa [transferFromValueWord] using hdebitGuardRaw),
    swap1, pop, swap1, pop, dup2]
  have hdebitWordRaw' :
      UInt256.sub
          (transferFromFromBalanceRawAfterAllowance σ I
            (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g))
          (uInt256OfByteArray (I.calldata.readBytes (⟨68⟩ : UInt256).toNat 32)) =
        transferFromBalanceDebitWord evm1 I := by
    simpa [transferFromValueWord] using hdebitWordRaw
  have hpc526 :
      (⟨508⟩ : UInt256) + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 3 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ =
        (⟨526⟩ : UInt256) := by
    native_decide
  exact ⟨_, _, by simpa [evm0, evm1, hdebitWordRaw', hpc526] using rdBeforeStore⟩

end VyperERC20
