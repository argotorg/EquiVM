import Benchmarks.Dss.DaiJoin.ConstructorTraceStores

/-!
# MakerDAO/Sky DSS DaiJoin constructor return trace
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.DaiJoin

set_option maxRecDepth 2000000

set_option maxHeartbeats 800000 in
theorem daiJoinCtorReturnTrace
    {I : ExecutionEnv} {g : Sat256} {s0 : State} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (vat dai : AccountAddress)
    (h : RD (daiJoinCtorCode vat dai) I g s0 ⟨129⟩ []
      (daiJoinCtorWardsHashMem I vat dai) (UInt256.ofNat 6) rdata acc k C) :
    RDret (daiJoinCtorCode vat dai) g s0 acc daiJoinBytecode := by
  have hcopy : (daiJoinCtorCode vat dai).write 143
      (daiJoinCtorWardsHashMem I vat dai) 0 1733 =
      daiJoinCtorReturnMem I vat dai := by
    rfl
  have rdBeforeReturn := daiJoin_ctor_run h with [
    push2 ⟨1733⟩, dup1, push2 ⟨143⟩, push1 ⟨0⟩,
    raw codecopy
      (Cₘ (UInt256.ofNat (MachineState.M (UInt256.ofNat 6).toNat 0 1733)) -
        Cₘ (UInt256.ofNat 6))
      (daiJoinCtorReturnMem I vat dai) (UInt256.ofNat 55)
      (by daiJoin_ctor_decode) mem_cost hcopy (by decide) (by evm_ov),
    push1 ⟨0⟩]
  exact rdBeforeReturn.ret 0 daiJoinBytecode
    (by daiJoin_ctor_decode) mem_cost (daiJoinCtorReturnMem_read I vat dai) (by evm_ov)

theorem daiJoinInitcodeSuccess
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ : AccountMap} {σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat dai : AccountAddress)
    (hcode : I.code = daiJoinCtorCode vat dai)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) :
    RDret (daiJoinCtorCode vat dai) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      (createdAccounts,
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner σ (daiJoinCtorCallerWardsSlot I) ⟨1⟩)
              ⟨3⟩ ⟨1⟩)
            ⟨1⟩
            (daiJoinCtorVatStored
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner σ (daiJoinCtorCallerWardsSlot I) ⟨1⟩)
                ⟨3⟩ ⟨1⟩) I vat))
          ⟨2⟩
          (daiJoinCtorDaiStored
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner σ (daiJoinCtorCallerWardsSlot I) ⟨1⟩)
                ⟨3⟩ ⟨1⟩)
              ⟨1⟩
              (daiJoinCtorVatStored
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner σ (daiJoinCtorCallerWardsSlot I) ⟨1⟩)
                  ⟨3⟩ ⟨1⟩) I vat))
            I dai))
      daiJoinBytecode := by
  obtain ⟨_, _, rd61⟩ :=
    daiJoinCtorArgsReach
      (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
      (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      vat dai hcode hwv
  obtain ⟨_, _, rd82⟩ := daiJoinCtorWardsStoreReach vat dai hperm rd61
  obtain ⟨_, _, rd129⟩ := daiJoinCtorStoresReach vat dai hperm rd82
  exact daiJoinCtorReturnTrace (I := I) vat dai rd129

end Benchmarks.Dss.DaiJoin
