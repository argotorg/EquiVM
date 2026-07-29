import Examples.VyperERC20.TransferFromAllowanceStoreOuterKeyReady

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

namespace VyperERC20

theorem erc20X_transferFromAllowanceStoreAfterOuterKeyStore {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨483⟩
      [⟨32⟩, approveOwnerWord I,
        transferFromAllowanceInnerSlotI I,
        transferFromAllowanceInnerSlotI I,
        transferFromAllowanceDebitI cA gh bl σ σ₀ A I g,
        transferFromSelectorWord]
      (transferFromAllowanceInnerScratchMemI σ I)
      (UInt256.ofNat 5) ByteArray.empty
      (cA, σ) k C) :
    ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨484⟩
      [transferFromAllowanceInnerSlotI I,
        transferFromAllowanceInnerSlotI I,
        transferFromAllowanceDebitI cA gh bl σ σ₀ A I g,
        transferFromSelectorWord]
      (wordAt32Mem (approveOwnerWord I) (transferFromAllowanceInnerScratchMemI σ I))
      (UInt256.ofNat 5) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨k, C, rd483⟩ := hreach
  have rd484 := rd483.mstore 0
    (wordAt32Mem (approveOwnerWord I) (transferFromAllowanceInnerScratchMemI σ I))
    (UInt256.ofNat 5)
    (by native_decide) mem_cost rfl (by decide) (by evm_ov)
  exact ⟨_, _, rd484⟩

end VyperERC20
