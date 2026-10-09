import Examples.VyperERC20.TransferFromAllowanceStoreOuterPhase

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

namespace VyperERC20

/-- The allowance `SSTORE` (the first forbidden opcode on the success path): with write
    permission the store happens; in static mode the run halts there. -/
theorem erc20X_transferFromAfterAllowanceStore {σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState σ σ₀ g A I) ⟨492⟩
      [transferFromAllowanceSlotI I,
        transferFromAllowanceDebitWord (initState σ σ₀ g A I) I,
        transferFromSelectorWord]
      (transferFromAllowanceScratchMem
        (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I)
        (transferFromCurrentAllowanceRaw σ I))
      (UInt256.ofNat 5) ByteArray.empty
      σ k C) :
    (I.perm = true ∧ ∃ k C, RD vyperERC20Bytecode I g (initState σ σ₀ g A I) ⟨493⟩
      [transferFromSelectorWord]
      (transferFromAllowanceScratchMem
        (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I)
        (transferFromCurrentAllowanceRaw σ I))
      (UInt256.ofNat 5) ByteArray.empty
      (sstoreAccountMap I.codeOwner σ (transferFromAllowanceSlotI I)
        (transferFromAllowanceDebitWord (initState σ σ₀ g A I) I)) k C)
    ∨ (I.perm = false ∧ RDstatic vyperERC20Bytecode g (initState σ σ₀ g A I)) := by
  obtain ⟨k, C, rd492⟩ := hreach
  by_cases hp : I.perm = true
  · obtain ⟨k1, C1, rdAfterStore⟩ := rd492.sstore hp
      (by vyper_erc20_transferFrom_decode) (by evm_ov)
    exact Or.inl ⟨hp, _, _, rdAfterStore⟩
  · have hpf : I.perm = false := by simpa using hp
    exact Or.inr ⟨hpf, rd492.sstoreStatic hpf (by vyper_erc20_transferFrom_decode) (by evm_ov)⟩



end VyperERC20
