import Examples.VyperERC20.TransferFromAllowance

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

namespace VyperERC20

theorem erc20X_transferFromAfterFromLoadSetup {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨493⟩
      [transferFromSelectorWord]
      (transferFromAllowanceScratchMem
        (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I)
        (transferFromCurrentAllowanceRaw σ I))
      (UInt256.ofNat 5) ByteArray.empty
      (cA, transferFromAccountMapAfterAllowanceI σ I
        (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g)) k C) :
    ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨497⟩
      [transferFromFromWord I, ⟨0⟩, transferFromSelectorWord]
      (transferFromAllowanceScratchMem
        (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I)
        (transferFromCurrentAllowanceRaw σ I))
      (UInt256.ofNat 5) ByteArray.empty
      (cA, transferFromAccountMapAfterAllowanceI σ I
        (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g)) k C := by
  obtain ⟨k, C, rd493⟩ := hreach
  have rd496 := evm_run rd493 with [
    push0, push1 ⟨64⟩,
    raw mload 0 (transferFromFromWord I) (UInt256.ofNat 5)
      (by vyper_erc20_transferFrom_decode) mem_cost
      (by
        exact mloadWordValue_of_readWithPadding
          (mem := transferFromAllowanceScratchMem
            (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I)
            (transferFromCurrentAllowanceRaw σ I))
          (aw := UInt256.ofNat 5) (off := ⟨64⟩) (v := transferFromFromWord I)
          (by rw [transferFromAllowanceScratchMem_size]; decide)
          (by decide)
          (transferFromAllowanceScratchMem_read64
            (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I)
            (transferFromCurrentAllowanceRaw σ I)))
      (by decide) (by evm_ov)]
  have hpc496 :
      (⟨493⟩ : UInt256) + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ = (⟨497⟩ : UInt256) := by
    native_decide
  exact ⟨_, _, by simpa [hpc496] using rd496⟩

end VyperERC20
