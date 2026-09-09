import Examples.VyperERC20.TransferFromStoresAfterFromLoadHashStore

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

namespace VyperERC20

theorem erc20X_transferFromAfterFromLoadSlot {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨502⟩
      [transferFromSelectorWord]
      (wordAt0Mem ⟨0⟩
        (wordAt32Mem (transferFromFromWord I) (transferFromAllowanceScratchMemI σ I)))
      (UInt256.ofNat 5) ByteArray.empty
      (cA, transferFromAccountMapAfterAllowanceI σ I
        (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g)) k C) :
    ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨508⟩
      [transferFromFromBalanceRawAfterAllowance σ I
          (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g),
        transferFromFromSlot I, transferFromSelectorWord]
      (transferFromAfterFromLoadMemI σ I)
      (UInt256.ofNat 5) ByteArray.empty
      (cA, transferFromAccountMapAfterAllowanceI σ I
        (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g)) k C := by
  obtain ⟨k, C, rd502⟩ := hreach
  let evm0 := initState cA gh bl σ σ₀ g A I
  let evm1 := transferFromAfterAllowanceState evm0 I
  have hread0_64 :
      ((wordAt0Mem ⟨0⟩
        (wordAt32Mem (transferFromFromWord I) (transferFromAllowanceScratchMemI σ I))).readWithPadding 0 64) =
        UInt256.toByteArray (⟨0⟩ : UInt256) ++ UInt256.toByteArray (transferFromFromWord I) := by
    simpa [transferFromAllowanceScratchMemI] using
      transferFromAfterFromLoadMem_read0_64
        (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I)
        (transferFromCurrentAllowanceRaw σ I)
  have hslot :
      UInt256.ofNat
          (fromByteArrayBigEndian
            (ffi.KEC
              (((wordAt0Mem ⟨0⟩
                (wordAt32Mem (transferFromFromWord I) (transferFromAllowanceScratchMemI σ I))).readWithPadding 0 64)))) =
        transferFromFromSlot I := by
    rw [hread0_64]
    unfold transferFromFromSlot erc20BalanceOfSlot vyperMappingSlot
    rw [keyValueToWord_address_of_canonical _ hcanonFrom]
    exact keccakSlot_eq _
  have hfromLoadRaw :
      transferFromFromBalanceRawAfterAllowance σ I
          (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g) =
        transferFromFromBalanceWord evm1 I := by
    simpa [evm0, evm1] using
      (transferFromFromBalanceRawAfterAllowance_initState (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g))
  have hpc508 :
      (⟨502⟩ : UInt256) + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ =
        (⟨508⟩ : UInt256) := by
    decide +native
  have rd504 := rd502.push1 ⟨64⟩ (by decide +native) (by evm_ov)
  have rd505 := rd504.push0 (by decide +native) (by evm_ov)
  have rd506 := rd505.keccak256 0
    (transferFromFromSlot I)
    (UInt256.ofNat 5)
    (by decide +native) mem_cost hslot (by decide) (by evm_ov)
  have rd507 := rd506.dup1 (by decide +native) (by evm_ov)
  obtain ⟨k1, C1, rd508⟩ := rd507.sload
    (by vyper_erc20_transferFrom_decode) (by evm_ov)
  exact ⟨_, _, by
    simpa [evm0, evm1, hpc508, hfromLoadRaw.symm, transferFromAfterFromLoadMemI] using rd508⟩

end VyperERC20
