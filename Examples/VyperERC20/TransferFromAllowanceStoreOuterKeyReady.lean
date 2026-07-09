import Examples.VyperERC20.TransferFromAllowanceStorePrep

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

namespace VyperERC20

theorem erc20X_transferFromAllowanceStoreAfterOuterKeyReady {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨479⟩
      [transferFromAllowanceInnerSlotI I,
        transferFromAllowanceDebitI cA gh bl σ σ₀ A I g,
        transferFromSelectorWord]
      (transferFromAllowanceInnerScratchMemI σ I)
      (UInt256.ofNat 5) ByteArray.empty
      (cA, σ) k C) :
    ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨483⟩
      [⟨32⟩, approveOwnerWord I,
        transferFromAllowanceInnerSlotI I,
        transferFromAllowanceInnerSlotI I,
        transferFromAllowanceDebitI cA gh bl σ σ₀ A I g,
        transferFromSelectorWord]
      (transferFromAllowanceInnerScratchMemI σ I)
      (UInt256.ofNat 5) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨k, C, rd479⟩ := hreach
  have rd483 := evm_run rd479 with [dup1, caller, push1 ⟨32⟩]
  exact ⟨_, _, rd483⟩

end VyperERC20
