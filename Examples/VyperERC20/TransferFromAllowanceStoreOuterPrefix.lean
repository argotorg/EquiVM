import Examples.VyperERC20.TransferFromAllowanceStoreOuterHashStore

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

namespace VyperERC20

theorem erc20X_transferFromAllowanceStoreBeforeOuterFinish {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hallowance : (transferFromValueWord I).toNat ≤
      (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨445⟩
      [transferFromSelectorWord]
      (transferFromFromBalanceHashMem
        (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I)
        (transferFromCurrentAllowanceRaw σ I))
      (UInt256.ofNat 5) ByteArray.empty
      (cA, σ) k C) :
    ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨486⟩
      [transferFromAllowanceInnerSlotI I,
        transferFromAllowanceDebitI cA gh bl σ σ₀ A I g,
        transferFromSelectorWord]
      (transferFromAllowanceScratchMemI σ I)
      (UInt256.ofNat 5) ByteArray.empty
      (cA, σ) k C := by
  have h465 := erc20X_transferFromAllowanceStoreGuard
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcanonFrom hallowance hreach
  have h470 := erc20X_transferFromAllowanceStoreAfterInnerLoad
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    h465
  have h472 := erc20X_transferFromAllowanceStoreAfterInnerKeyReady
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    h470
  have h473 := erc20X_transferFromAllowanceStoreAfterInnerKeyStore
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    h472
  have h475 := erc20X_transferFromAllowanceStoreAfterInnerHashStore
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    h473
  have h479 := erc20X_transferFromAllowanceStoreInnerSlot
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    h475
  have h483 := erc20X_transferFromAllowanceStoreAfterOuterKeyReady
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    h479
  have h484 := erc20X_transferFromAllowanceStoreAfterOuterKeyStore
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    h483
  exact erc20X_transferFromAllowanceStoreAfterOuterHashStore
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    h484

end VyperERC20
