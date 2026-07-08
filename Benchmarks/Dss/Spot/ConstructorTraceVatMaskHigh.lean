import Benchmarks.Dss.Spot.ConstructorTraceVatMaskLow

/-!
# MakerDAO/Sky DSS Spotter constructor vat high-word mask trace
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Spot

set_option maxRecDepth 2000000

theorem spotCtorVatMaskHighReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σWards σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat : AccountAddress) {k C : ℕ}
    (rd90 :
      RD (spotCtorCode vat) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨90⟩
        [UInt256.land (EVM.word vat.val) solcAddrMask, ⟨2⟩, ⟨1⟩,
          solcSlotWord σWards I ⟨2⟩]
        (spotCtorWardsHashMem I vat) (UInt256.ofNat 5) ByteArray.empty
        (createdAccounts, σWards) k C) :
    ∃ k' C', RD (spotCtorCode vat) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨102⟩
      [UInt256.land (solcSlotWord σWards I ⟨2⟩) (UInt256.lnot solcAddrMask), ⟨2⟩,
        ⟨1⟩, UInt256.land (EVM.word vat.val) solcAddrMask]
      (spotCtorWardsHashMem I vat) (UInt256.ofNat 5) ByteArray.empty
      (createdAccounts, σWards) k' C' := by
  have rd102 := spot_ctor_run rd90 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, not, swap1, swap4,
    raw and (by spot_ctor_decode) (by evm_ov)]
  have hpc102 :
      (⟨90⟩ : UInt256) + UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 2 +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ =
        ⟨102⟩ := by
    native_decide
  rw [hpc102] at rd102
  exact ⟨_, _, by
    simpa [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide] using rd102⟩

end Benchmarks.Dss.Spot
