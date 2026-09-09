import Benchmarks.Dss.Jug.ConstructorTraceVatMaskLow

/-!
# MakerDAO/Sky DSS Jug constructor vat high-word mask trace
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Jug

set_option maxRecDepth 2000000

theorem jugCtorVatMaskHighReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σWards σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat : AccountAddress) {k C : ℕ}
    (rd88 :
      RD (jugCtorCode vat) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨88⟩
        [UInt256.land (EVM.word vat.val) solcAddrMask, ⟨2⟩, solcSlotWord σWards I ⟨2⟩]
        (jugCtorWardsHashMem I vat) (UInt256.ofNat 5) ByteArray.empty
        (createdAccounts, σWards) k C) :
    ∃ k' C', RD (jugCtorCode vat) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨100⟩
      [UInt256.land (solcSlotWord σWards I ⟨2⟩) (UInt256.lnot solcAddrMask), ⟨2⟩,
        UInt256.land (EVM.word vat.val) solcAddrMask]
      (jugCtorWardsHashMem I vat) (UInt256.ofNat 5) ByteArray.empty
      (createdAccounts, σWards) k' C' := by
  have rd100 := jug_ctor_run rd88 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, not, swap1, swap3,
    raw and (by jug_ctor_decode) (by evm_ov)]
  have hpc100 :
      (⟨88⟩ : UInt256) + UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 2 +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ =
        ⟨100⟩ := by
    decide +native
  rw [hpc100] at rd100
  exact ⟨_, _, by
    simpa [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide] using rd100⟩

end Benchmarks.Dss.Jug
