import Examples.VyperERC20.TransferFromStoresAfterFromLoadKeyReady

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

namespace VyperERC20

theorem erc20X_transferFromAfterFromLoadKeyStore {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨499⟩
      [⟨32⟩, transferFromFromWord I, ⟨0⟩, transferFromSelectorWord]
      (transferFromAllowanceScratchMemI σ I)
      (UInt256.ofNat 5) ByteArray.empty
      (cA, transferFromAccountMapAfterAllowanceI σ I
        (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g)) k C) :
    ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨500⟩
      [⟨0⟩, transferFromSelectorWord]
      (wordAt32Mem (transferFromFromWord I) (transferFromAllowanceScratchMemI σ I))
      (UInt256.ofNat 5) ByteArray.empty
      (cA, transferFromAccountMapAfterAllowanceI σ I
        (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g)) k C := by
  obtain ⟨k, C, rd499⟩ := hreach
  have rd500 := rd499.mstore 0
    (wordAt32Mem (transferFromFromWord I) (transferFromAllowanceScratchMemI σ I))
    (UInt256.ofNat 5)
    (by native_decide) mem_cost rfl (by decide) (by evm_ov)
  exact ⟨_, _, rd500⟩

end VyperERC20
