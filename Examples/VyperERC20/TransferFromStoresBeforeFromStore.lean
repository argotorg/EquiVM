import Examples.VyperERC20.TransferFromStoresAfterFromLoadSlot
import Examples.VyperERC20.TransferFromStoresBeforeFromStoreCore

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

namespace VyperERC20

theorem erc20X_transferFromBeforeFromStore {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hbalanceDebit : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord
        (transferFromAfterAllowanceState (initState cA gh bl σ σ₀ g A I) I) I).toNat)
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨493⟩
      [transferFromSelectorWord]
      (transferFromAllowanceScratchMem
        (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I)
        (transferFromCurrentAllowanceRaw σ I))
      (UInt256.ofNat 5) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (transferFromAllowanceSlotI I)
        (transferFromAllowanceDebitWord (initState cA gh bl σ σ₀ g A I) I)) k C) :
    ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨526⟩
      [transferFromFromSlot I,
        transferFromBalanceDebitWord
          (transferFromAfterAllowanceState (initState cA gh bl σ σ₀ g A I) I) I,
        transferFromFromSlot I, transferFromSelectorWord]
      (transferFromAfterFromLoadMemI σ I)
      (UInt256.ofNat 5) ByteArray.empty
      (cA, transferFromAccountMapAfterAllowanceI σ I
        (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g)) k C := by
  have hreach493 :
      ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨493⟩
        [transferFromSelectorWord]
        (transferFromAllowanceScratchMem
          (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I)
          (transferFromCurrentAllowanceRaw σ I))
        (UInt256.ofNat 5) ByteArray.empty
        (cA, transferFromAccountMapAfterAllowanceI σ I
          (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g)) k C := by
    simpa [transferFromAccountMapAfterAllowanceI, transferFromAllowanceDebitI] using hreach
  obtain ⟨k497, C497, rd497⟩ := erc20X_transferFromAfterFromLoadSetup
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hreach493
  have hreach497 :
      ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨497⟩
        [transferFromFromWord I, ⟨0⟩, transferFromSelectorWord]
        (transferFromAllowanceScratchMemI σ I)
        (UInt256.ofNat 5) ByteArray.empty
        (cA, transferFromAccountMapAfterAllowanceI σ I
          (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g)) k C := by
    exact ⟨k497, C497, by simpa [transferFromAllowanceScratchMemI] using rd497⟩
  obtain ⟨k499, C499, rd499⟩ := erc20X_transferFromAfterFromLoadKeyReady
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hreach497
  obtain ⟨k500, C500, rd500⟩ := erc20X_transferFromAfterFromLoadKeyStore
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    ⟨k499, C499, rd499⟩
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
  have hreach502 :
      ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨502⟩
        [transferFromSelectorWord]
        (wordAt0Mem ⟨0⟩
          (wordAt32Mem (transferFromFromWord I) (transferFromAllowanceScratchMemI σ I)))
        (UInt256.ofNat 5) ByteArray.empty
        (cA, transferFromAccountMapAfterAllowanceI σ I
          (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g)) k C := ⟨k502, C502, rd502⟩
  obtain ⟨k508, C508, rd508⟩ := erc20X_transferFromAfterFromLoadSlot
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcanonFrom hreach502
  exact erc20X_transferFromBeforeFromStoreCore
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hbalanceDebit ⟨k508, C508, rd508⟩

end VyperERC20
