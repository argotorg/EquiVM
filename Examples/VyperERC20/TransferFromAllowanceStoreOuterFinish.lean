import Examples.VyperERC20.TransferFromAllowanceStoreOuterHashStore

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

namespace VyperERC20

theorem erc20X_transferFromAllowanceStoreAfterOuterFinish {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨486⟩
      [transferFromAllowanceInnerSlotI I,
        transferFromAllowanceDebitI cA gh bl σ σ₀ A I g,
        transferFromSelectorWord]
      (transferFromAllowanceScratchMemI σ I)
      (UInt256.ofNat 5) ByteArray.empty
      (cA, σ) k C) :
    ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨492⟩
      [transferFromAllowanceSlotI I,
        transferFromAllowanceDebitI cA gh bl σ σ₀ A I g,
        transferFromSelectorWord]
      (transferFromAllowanceScratchMemI σ I)
      (UInt256.ofNat 5) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨k, C, rd486⟩ := hreach
  have hslotScratch :
      UInt256.ofNat
          (fromByteArrayBigEndian
            (ffi.KEC ((transferFromAllowanceScratchMemI σ I).readWithPadding 0 64))) =
        transferFromAllowanceSlotI I := by
    unfold transferFromAllowanceScratchMemI
    rw [transferFromAllowanceScratchMem_read0_64]
    unfold transferFromAllowanceSlotI erc20AllowanceSlot vyperMappingSlot
    rw [transferFromAllowanceInnerKeccakSlot (I := I) hcanonFrom, keyValueToWord_address]
    exact keccakSlot_eq _
  have rd492 := evm_run rd486 with [
    push1 ⟨64⟩, push0,
    raw keccak256 0 (transferFromAllowanceSlotI I)
      (UInt256.ofNat 5)
      (by vyper_erc20_transferFrom_decode) mem_cost hslotScratch (by decide) (by evm_ov),
    swap1, pop]
  exact ⟨_, _, rd492⟩

end VyperERC20
