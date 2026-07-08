import Benchmarks.Dss.Flopper.ConstructorTraceStores

/-!
# MakerDAO/Sky DSS Flopper constructor return trace
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Flopper

set_option maxRecDepth 2000000

set_option maxHeartbeats 800000 in
theorem flopperCtorReturnTrace
    {I : ExecutionEnv} {g : Sat256} {s0 : State} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (vat gem : AccountAddress)
    (h : RD (flopperCtorCode vat gem) I g s0 ⟨206⟩ []
      (flopperCtorWardsHashMem I vat gem) (UInt256.ofNat 6) rdata acc k C) :
    RDret (flopperCtorCode vat gem) g s0 acc flopperBytecode := by
  have hcopy : (flopperCtorCode vat gem).write 220 (flopperCtorWardsHashMem I vat gem) 0 4780 =
      flopperCtorReturnMem I vat gem := by
    rfl
  have rdBeforeReturn := flopper_ctor_run h with [
    push2 ⟨4780⟩, dup1, push2 ⟨220⟩, push1 ⟨0⟩,
    raw codecopy
      (Cₘ (UInt256.ofNat (MachineState.M (UInt256.ofNat 6).toNat 0 4780)) -
        Cₘ (UInt256.ofNat 6))
      (flopperCtorReturnMem I vat gem) (UInt256.ofNat 150)
      (by flopper_ctor_decode) mem_cost hcopy (by decide) (by evm_ov),
    push1 ⟨0⟩]
  exact rdBeforeReturn.ret 0 flopperBytecode
    (by flopper_ctor_decode) mem_cost (flopperCtorReturnMem_read I vat gem) (by evm_ov)

theorem flopperInitcodeSuccess
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ : AccountMap} {σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat gem : AccountAddress)
    (hcode : I.code = flopperCtorCode vat gem)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) :
    RDret (flopperCtorCode vat gem) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      (createdAccounts, flopperCtorFinalMap (flopperCtorAfterKicksMap σ I) I vat gem)
      flopperBytecode := by
  obtain ⟨_, _, rd134⟩ :=
    flopperCtorArgsReach
      (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
      (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      vat gem hcode hperm hwv
  obtain ⟨_, _, rd206⟩ := flopperCtorStoresReach vat gem hperm rd134
  exact flopperCtorReturnTrace (I := I) vat gem rd206

end Benchmarks.Dss.Flopper
