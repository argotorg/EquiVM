import Examples.VyperERC20.TransferFromAllowanceStoreGuard

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

namespace VyperERC20

theorem erc20X_transferFromAllowanceStoreAfterInnerLoad {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨465⟩
      [transferFromAllowanceDebitWord (initState cA gh bl σ σ₀ g A I) I, transferFromSelectorWord]
      (transferFromFromBalanceHashMem
        (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I)
        (transferFromCurrentAllowanceRaw σ I))
      (UInt256.ofNat 5) ByteArray.empty
      (cA, σ) k C) :
    ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨470⟩
      [transferFromFromWord I, ⟨1⟩,
        transferFromAllowanceDebitWord (initState cA gh bl σ σ₀ g A I) I,
        transferFromSelectorWord]
      (transferFromFromBalanceHashMem
        (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I)
        (transferFromCurrentAllowanceRaw σ I))
      (UInt256.ofNat 5) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨k, C, rd465⟩ := hreach
  have rd470 := evm_run rd465 with [
    push1 ⟨1⟩, push1 ⟨64⟩,
    raw mload 0 (transferFromFromWord I) (UInt256.ofNat 5)
      (by vyper_erc20_transferFrom_decode) mem_cost
      (by
        exact mloadWordValue_of_readWithPadding
          (mem := transferFromFromBalanceHashMem
            (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I)
            (transferFromCurrentAllowanceRaw σ I))
          (aw := UInt256.ofNat 5) (off := ⟨64⟩) (v := transferFromFromWord I)
          (by rw [transferFromFromBalanceHashMem_size]; decide)
          (by decide)
          (transferFromFromBalanceHashMem_read64
            (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I)
            (transferFromCurrentAllowanceRaw σ I)))
      (by decide) (by evm_ov)]
  exact ⟨_, _, rd470⟩

end VyperERC20
