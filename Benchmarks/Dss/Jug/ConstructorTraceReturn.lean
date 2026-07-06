import Benchmarks.Dss.Jug.ConstructorTraceStores

/-!
# MakerDAO/Sky DSS Jug constructor return trace
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Jug

set_option maxRecDepth 2000000

set_option maxHeartbeats 800000 in
theorem jugCtorReturnTrace
    {I : ExecutionEnv} {g : Sat256} {s0 : State} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (vat : AccountAddress)
    (h : RD (jugCtorCode vat) I g s0 ⟨106⟩ []
      (jugCtorWardsHashMem I vat) (UInt256.ofNat 5) rdata acc k C) :
    RDret (jugCtorCode vat) g s0 acc jugBytecode := by
  have hcopy : (jugCtorCode vat).write 120 (jugCtorWardsHashMem I vat) 0 2440 =
      jugCtorReturnMem I vat := by
    rfl
  have rdBeforeReturn := jug_ctor_run h with [
    push2 ⟨2440⟩, dup1, push2 ⟨120⟩, push1 ⟨0⟩,
    raw codecopy
      (Cₘ (UInt256.ofNat (MachineState.M (UInt256.ofNat 5).toNat 0 2440)) -
        Cₘ (UInt256.ofNat 5))
      (jugCtorReturnMem I vat) (UInt256.ofNat 77)
      (by jug_ctor_decode) mem_cost hcopy (by decide) (by evm_ov),
    push1 ⟨0⟩]
  exact rdBeforeReturn.ret 0 jugBytecode
    (by jug_ctor_decode) mem_cost (jugCtorReturnMem_read I vat) (by evm_ov)

theorem jugInitcodeSuccess
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ : AccountMap} {σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat : AccountAddress)
    (hcode : I.code = jugCtorCode vat)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) :
    RDret (jugCtorCode vat) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      (createdAccounts,
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ (jugCtorCallerWardsSlot I) ⟨1⟩)
          ⟨2⟩
          (jugCtorVatStored
            (sstoreAccountMap I.codeOwner σ (jugCtorCallerWardsSlot I) ⟨1⟩) I vat))
      jugBytecode := by
  obtain ⟨_, _, rd54⟩ :=
    jugCtorArgsReach
      (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
      (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      vat hcode hwv
  obtain ⟨_, _, rd73⟩ := jugCtorWardsStoreReach vat hperm rd54
  obtain ⟨_, _, rd106⟩ := jugCtorVatStoreReach vat hperm rd73
  exact jugCtorReturnTrace (I := I) vat rd106

end Benchmarks.Dss.Jug
