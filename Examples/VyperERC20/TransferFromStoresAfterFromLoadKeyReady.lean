import Examples.VyperERC20.TransferFromStoresAfterFromLoadSetup

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

namespace VyperERC20

theorem erc20X_transferFromAfterFromLoadKeyReady {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨497⟩
      [transferFromFromWord I, ⟨0⟩, transferFromSelectorWord]
      (transferFromAllowanceScratchMemI σ I)
      (UInt256.ofNat 5) ByteArray.empty
      (cA, transferFromAccountMapAfterAllowanceI σ I
        (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g)) k C) :
    ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨499⟩
      [⟨32⟩, transferFromFromWord I, ⟨0⟩, transferFromSelectorWord]
      (transferFromAllowanceScratchMemI σ I)
      (UInt256.ofNat 5) ByteArray.empty
      (cA, transferFromAccountMapAfterAllowanceI σ I
        (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g)) k C := by
  obtain ⟨k, C, rd497⟩ := hreach
  have rd499 := rd497.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, rd499⟩

end VyperERC20
