import Examples.VyperERC20.TransferFromAllowanceStoreInnerKeyStore

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

namespace VyperERC20

theorem erc20X_transferFromAllowanceStoreAfterInnerHashStore {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨473⟩
      [⟨1⟩,
        transferFromAllowanceDebitWord (initState cA gh bl σ σ₀ g A I) I,
        transferFromSelectorWord]
      (wordAt32Mem (transferFromFromWord I)
        (transferFromFromBalanceHashMem
          (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I)
          (transferFromCurrentAllowanceRaw σ I)))
      (UInt256.ofNat 5) ByteArray.empty
      (cA, σ) k C) :
    ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨475⟩
      [transferFromAllowanceDebitWord (initState cA gh bl σ σ₀ g A I) I,
        transferFromSelectorWord]
      (transferFromAllowanceInnerScratchMem
        (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I)
        (transferFromCurrentAllowanceRaw σ I))
      (UInt256.ofNat 5) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨k, C, rd473⟩ := hreach
  have rd474 := rd473.push0 (by native_decide) (by evm_ov)
  have rd475 := rd474.mstore 0
    (transferFromAllowanceInnerScratchMem
      (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I)
      (transferFromCurrentAllowanceRaw σ I))
    (UInt256.ofNat 5)
    (by native_decide) mem_cost
    rfl
    (by decide) (by evm_ov)
  exact ⟨_, _, rd475⟩

end VyperERC20
