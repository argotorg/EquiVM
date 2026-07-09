import Examples.VyperERC20.TransferFromAllowanceStoreOuterKeyStore

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

namespace VyperERC20

theorem erc20X_transferFromAllowanceStoreAfterOuterHashStore {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨484⟩
      [transferFromAllowanceInnerSlotI I,
        transferFromAllowanceInnerSlotI I,
        transferFromAllowanceDebitI cA gh bl σ σ₀ A I g,
        transferFromSelectorWord]
      (wordAt32Mem (approveOwnerWord I) (transferFromAllowanceInnerScratchMemI σ I))
      (UInt256.ofNat 5) ByteArray.empty
      (cA, σ) k C) :
    ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨486⟩
      [transferFromAllowanceInnerSlotI I,
        transferFromAllowanceDebitI cA gh bl σ σ₀ A I g,
        transferFromSelectorWord]
      (transferFromAllowanceScratchMemI σ I)
      (UInt256.ofNat 5) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨k, C, rd484⟩ := hreach
  have rd485 := rd484.push0 (by native_decide) (by evm_ov)
  have rd486 := rd485.mstore 0
    (transferFromAllowanceScratchMemI σ I)
    (UInt256.ofNat 5)
    (by native_decide) mem_cost rfl (by decide) (by evm_ov)
  exact ⟨_, _, rd486⟩

end VyperERC20
