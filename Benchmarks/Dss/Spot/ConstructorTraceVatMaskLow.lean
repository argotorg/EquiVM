import Benchmarks.Dss.Spot.ConstructorTraceVatSload

/-!
# MakerDAO/Sky DSS Spotter constructor vat low-address mask trace
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Spot

set_option maxRecDepth 2000000

theorem spotCtorVatMaskLowReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σWards σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat : AccountAddress) {k C : ℕ}
    (rd79 :
      RD (spotCtorCode vat) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨79⟩
        [solcSlotWord σWards I ⟨2⟩, ⟨2⟩, ⟨1⟩, EVM.word vat.val]
        (spotCtorWardsHashMem I vat) (UInt256.ofNat 5) ByteArray.empty
        (createdAccounts, σWards) k C) :
    ∃ k' C', RD (spotCtorCode vat) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨90⟩
      [UInt256.land (EVM.word vat.val) solcAddrMask, ⟨2⟩, ⟨1⟩,
        solcSlotWord σWards I ⟨2⟩]
      (spotCtorWardsHashMem I vat) (UInt256.ofNat 5) ByteArray.empty
      (createdAccounts, σWards) k' C' := by
  have rd90 := spot_ctor_run rd79 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, swap1, swap4,
    raw and (by spot_ctor_decode) (by evm_ov)]
  have hpc90 :
      (⟨79⟩ : UInt256) + UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 2 +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ =
        ⟨90⟩ := by
    decide +native
  rw [hpc90] at rd90
  exact ⟨_, _, by
    simpa [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide] using rd90⟩

end Benchmarks.Dss.Spot
