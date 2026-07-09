import Examples.VyperERC20.TransferFromAllowanceStoreInnerLoad

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

namespace VyperERC20

theorem erc20X_transferFromAllowanceStoreAfterInnerKeyReady {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨470⟩
      [transferFromFromWord I, ⟨1⟩,
        transferFromAllowanceDebitWord (initState cA gh bl σ σ₀ g A I) I, transferFromSelectorWord]
      (transferFromFromBalanceHashMem
        (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I)
        (transferFromCurrentAllowanceRaw σ I))
      (UInt256.ofNat 5) ByteArray.empty
      (cA, σ) k C) :
    ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨472⟩
      [⟨32⟩, transferFromFromWord I, ⟨1⟩,
        transferFromAllowanceDebitWord (initState cA gh bl σ σ₀ g A I) I, transferFromSelectorWord]
      (transferFromFromBalanceHashMem
        (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I)
        (transferFromCurrentAllowanceRaw σ I))
      (UInt256.ofNat 5) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨k, C, rd470⟩ := hreach
  have rd472 := evm_run rd470 with [push1 ⟨32⟩]
  exact ⟨_, _, rd472⟩

end VyperERC20
