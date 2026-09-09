import Examples.VyperERC20.TransferFromAllowanceStoreInnerKeyReady

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

namespace VyperERC20

theorem erc20X_transferFromAllowanceStoreAfterInnerKeyStore {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨472⟩
      [⟨32⟩, transferFromFromWord I, ⟨1⟩,
        transferFromAllowanceDebitWord (initState cA gh bl σ σ₀ g A I) I, transferFromSelectorWord]
      (transferFromFromBalanceHashMem
        (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I)
        (transferFromCurrentAllowanceRaw σ I))
      (UInt256.ofNat 5) ByteArray.empty
      (cA, σ) k C) :
    ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨473⟩
      [⟨1⟩,
        transferFromAllowanceDebitWord (initState cA gh bl σ σ₀ g A I) I,
        transferFromSelectorWord]
      (wordAt32Mem (transferFromFromWord I)
        (transferFromFromBalanceHashMem
          (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I)
          (transferFromCurrentAllowanceRaw σ I)))
      (UInt256.ofNat 5) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨k, C, rd472⟩ := hreach
  have rd473 := rd472.mstore 0
    (wordAt32Mem (transferFromFromWord I)
      (transferFromFromBalanceHashMem
        (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I)
        (transferFromCurrentAllowanceRaw σ I)))
    (UInt256.ofNat 5)
    (by decide +native) mem_cost
    rfl
    (by decide) (by evm_ov)
  exact ⟨_, _, rd473⟩

end VyperERC20
