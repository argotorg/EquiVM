import Examples.VyperERC20.TransferFromStoresAfterFromLoadKeyStore

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

namespace VyperERC20

theorem erc20X_transferFromAfterFromLoadHashStore {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨500⟩
      [⟨0⟩, transferFromSelectorWord]
      (wordAt32Mem (transferFromFromWord I) (transferFromAllowanceScratchMemI σ I))
      (UInt256.ofNat 5) ByteArray.empty
      (cA, transferFromAccountMapAfterAllowanceI σ I
        (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g)) k C) :
    ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨502⟩
      [transferFromSelectorWord]
      (wordAt0Mem ⟨0⟩
        (wordAt32Mem (transferFromFromWord I) (transferFromAllowanceScratchMemI σ I)))
      (UInt256.ofNat 5) ByteArray.empty
      (cA, transferFromAccountMapAfterAllowanceI σ I
        (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g)) k C := by
  obtain ⟨k, C, rd500⟩ := hreach
  have rd501 := rd500.push0 (by decide +native) (by evm_ov)
  have rd502 := rd501.mstore 0
    (wordAt0Mem ⟨0⟩
      (wordAt32Mem (transferFromFromWord I) (transferFromAllowanceScratchMemI σ I)))
    (UInt256.ofNat 5)
    (by decide +native) mem_cost rfl (by decide) (by evm_ov)
  exact ⟨_, _, rd502⟩

end VyperERC20
