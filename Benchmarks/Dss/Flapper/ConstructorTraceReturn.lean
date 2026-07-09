import Benchmarks.Dss.Flapper.ConstructorTraceStores

/-!
# MakerDAO/Sky DSS Flapper constructor return trace
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Flapper

set_option maxRecDepth 2000000

set_option maxHeartbeats 800000 in
theorem flapperCtorReturnTrace
    {I : ExecutionEnv} {g : Sat256} {s0 : State} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (vat gem : AccountAddress)
    (h : RD (flapperCtorCode vat gem) I g s0 ⟨194⟩ []
      (flapperCtorWardsHashMem I vat gem) (UInt256.ofNat 6) rdata acc k C) :
    RDret (flapperCtorCode vat gem) g s0 acc flapperBytecode := by
  have hcopy : (flapperCtorCode vat gem).write 208 (flapperCtorWardsHashMem I vat gem) 0 5008 =
      flapperCtorReturnMem I vat gem := by
    rfl
  have rdBeforeReturn := flapper_ctor_run h with [
    push2 ⟨5008⟩, dup1, push2 ⟨208⟩, push1 ⟨0⟩,
    raw codecopy
      (Cₘ (UInt256.ofNat (MachineState.M (UInt256.ofNat 6).toNat 0 5008)) -
        Cₘ (UInt256.ofNat 6))
      (flapperCtorReturnMem I vat gem) (UInt256.ofNat 157)
      (by flapper_ctor_decode) mem_cost hcopy (by decide) (by evm_ov),
    push1 ⟨0⟩]
  exact rdBeforeReturn.ret 0 flapperBytecode
    (by flapper_ctor_decode) mem_cost (flapperCtorReturnMem_read I vat gem) (by evm_ov)

theorem flapperInitcodeSuccess
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ : AccountMap} {σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat gem : AccountAddress)
    (hcode : I.code = flapperCtorCode vat gem)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) :
    RDret (flapperCtorCode vat gem) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      (createdAccounts, flapperCtorFinalMap (flapperCtorAfterKicksMap σ I) I vat gem)
      flapperBytecode := by
  obtain ⟨_, _, rd122⟩ :=
    flapperCtorArgsReach
      (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
      (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      vat gem hcode hperm hwv
  obtain ⟨_, _, rd194⟩ := flapperCtorStoresReach vat gem hperm rd122
  exact flapperCtorReturnTrace (I := I) vat gem rd194

end Benchmarks.Dss.Flapper
