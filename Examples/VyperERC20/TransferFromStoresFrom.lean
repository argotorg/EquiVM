import Examples.VyperERC20.TransferFromStoresBeforeFromStore

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

namespace VyperERC20

theorem erc20TransferFromX_balanceDebitUnderflow {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hltDebit : (transferFromFromBalanceWord
      (transferFromAfterAllowanceState (initState cA gh bl σ σ₀ g A I) I) I).toNat <
      (transferFromValueWord I).toNat)
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨493⟩
      [transferFromSelectorWord]
      (transferFromAllowanceScratchMem
        (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I)
        (transferFromCurrentAllowanceRaw σ I))
      (UInt256.ofNat 5) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (transferFromAllowanceSlotI I)
        (transferFromAllowanceDebitWord (initState cA gh bl σ σ₀ g A I) I)) k C) :
    RDrev vyperERC20Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  let evm0 := initState cA gh bl σ σ₀ g A I
  let evm1 := transferFromAfterAllowanceState evm0 I
  have hreach493 :
      ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨493⟩
        [transferFromSelectorWord]
        (transferFromAllowanceScratchMem
          (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I)
          (transferFromCurrentAllowanceRaw σ I))
        (UInt256.ofNat 5) ByteArray.empty
        (cA, transferFromAccountMapAfterAllowanceI σ I
          (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g)) k C := by
    simpa [transferFromAccountMapAfterAllowanceI, transferFromAllowanceDebitI] using hreach
  obtain ⟨k497, C497, rd497⟩ := erc20X_transferFromAfterFromLoadSetup
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hreach493
  have hreach497 :
      ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨497⟩
        [transferFromFromWord I, ⟨0⟩, transferFromSelectorWord]
        (transferFromAllowanceScratchMemI σ I)
        (UInt256.ofNat 5) ByteArray.empty
        (cA, transferFromAccountMapAfterAllowanceI σ I
          (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g)) k C := by
    exact ⟨k497, C497, by simpa [transferFromAllowanceScratchMemI] using rd497⟩
  obtain ⟨k499, C499, rd499⟩ := erc20X_transferFromAfterFromLoadKeyReady
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hreach497
  obtain ⟨k500, C500, rd500⟩ := erc20X_transferFromAfterFromLoadKeyStore
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    ⟨k499, C499, rd499⟩
  have hreach500 :
      ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨500⟩
        [⟨0⟩, transferFromSelectorWord]
        (wordAt32Mem (transferFromFromWord I) (transferFromAllowanceScratchMemI σ I))
        (UInt256.ofNat 5) ByteArray.empty
        (cA, transferFromAccountMapAfterAllowanceI σ I
          (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g)) k C := ⟨k500, C500, rd500⟩
  obtain ⟨k502, C502, rd502⟩ := erc20X_transferFromAfterFromLoadHashStore
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hreach500
  have hreach502 :
      ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨502⟩
        [transferFromSelectorWord]
        (wordAt0Mem ⟨0⟩
          (wordAt32Mem (transferFromFromWord I) (transferFromAllowanceScratchMemI σ I)))
        (UInt256.ofNat 5) ByteArray.empty
        (cA, transferFromAccountMapAfterAllowanceI σ I
          (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g)) k C := ⟨k502, C502, rd502⟩
  obtain ⟨k508, C508, rd508⟩ := erc20X_transferFromAfterFromLoadSlot
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcanonFrom hreach502
  have hltDebitRaw :
      (transferFromFromBalanceRawAfterAllowance σ I
        (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g)).toNat <
        (transferFromValueWord I).toNat := by
    rw [transferFromAllowanceDebitI]
    rw [transferFromFromBalanceRawAfterAllowance_initState (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)]
    simpa [evm0, evm1] using hltDebit
  have hsubNat :
      (UInt256.sub
        (transferFromFromBalanceRawAfterAllowance σ I
          (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g))
        (transferFromValueWord I)).toNat =
          UInt256.size +
            (transferFromFromBalanceRawAfterAllowance σ I
              (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g)).toNat -
            (transferFromValueWord I).toNat := by
    exact usub_toNat_underflow hltDebitRaw
  have hdebitGuardRaw :
      UInt256.gt
        (UInt256.sub
          (transferFromFromBalanceRawAfterAllowance σ I
            (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g))
          (transferFromValueWord I))
        (transferFromFromBalanceRawAfterAllowance σ I
          (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g)) = ⟨1⟩ := by
    apply ugt_one
    rw [hsubNat]
    have hv : (transferFromValueWord I).toNat < UInt256.size := (transferFromValueWord I).val.isLt
    omega
  have rd801 := evm_run rd508 with [
    push1 ⟨68⟩, calldataload,
    dup1, dup3, sub, dup3, dup2, gt, push2 ⟨801⟩,
    jumpiT (by rw [show
        UInt256.gt
          (UInt256.sub
            (transferFromFromBalanceRawAfterAllowance σ I
              (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g))
            (uInt256OfByteArray (I.calldata.readBytes (⟨68⟩ : UInt256).toNat 32)))
          (transferFromFromBalanceRawAfterAllowance σ I
            (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g)) = ⟨1⟩ by
          simpa [transferFromValueWord] using hdebitGuardRaw]; decide)
      (by vyper_erc20_transferFrom_decode)]
  exact vyperRuntimeRevert801 (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) rd801 rfl (by
      simp only [List.length_cons, List.length_nil]
      omega)

end VyperERC20
