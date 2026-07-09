import Examples.VyperERC20.TransferFromStoresAfterFromLoadSlot

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

namespace VyperERC20

theorem erc20X_transferFromAfterFromLoadTail {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨499⟩
      [⟨32⟩, transferFromFromWord I, ⟨0⟩, transferFromSelectorWord]
      (transferFromAllowanceScratchMemI σ I)
      (UInt256.ofNat 5) ByteArray.empty
      (cA, transferFromAccountMapAfterAllowanceI σ I
        (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g)) k C) :
    ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨508⟩
      [transferFromFromBalanceRawAfterAllowance σ I
          (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g),
        transferFromFromSlot I, transferFromSelectorWord]
      (transferFromFromBalanceHashMemI σ I)
      (UInt256.ofNat 5) ByteArray.empty
      (cA, transferFromAccountMapAfterAllowanceI σ I
        (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g)) k C := by
  obtain ⟨k500, C500, rd500⟩ := erc20X_transferFromAfterFromLoadKeyStore
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hreach
  have hreach500 :
      ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨500⟩
        [⟨0⟩, transferFromSelectorWord]
        (wordAt32Mem (transferFromFromWord I) (transferFromAllowanceScratchMemI σ I))
        (UInt256.ofNat 5) ByteArray.empty
        (cA, transferFromAccountMapAfterAllowanceI σ I
          (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g)) k C := ⟨k500, C500, rd500⟩
  obtain ⟨k502, C502, rd502⟩ := erc20X_transferFromAfterFromLoadHashStore
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hreach500
  obtain ⟨k508, C508, rd508⟩ := erc20X_transferFromAfterFromLoadSlot
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcanonFrom ⟨k502, C502, rd502⟩
  exact ⟨k508, C508, rd508⟩

end VyperERC20
