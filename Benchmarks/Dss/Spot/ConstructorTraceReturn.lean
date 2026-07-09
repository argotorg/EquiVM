import Benchmarks.Dss.Spot.ConstructorTraceStores

/-!
# MakerDAO/Sky DSS Spotter constructor return trace
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Spot

set_option maxRecDepth 2000000

set_option maxHeartbeats 800000 in
theorem spotCtorReturnTrace
    {I : ExecutionEnv} {g : Sat256} {s0 : State} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (vat : AccountAddress)
    (h : RD (spotCtorCode vat) I g s0 ⟨128⟩ []
      (spotCtorWardsHashMem I vat) (UInt256.ofNat 5) rdata acc k C) :
    RDret (spotCtorCode vat) g s0 acc spotBytecode := by
  have hcopy : (spotCtorCode vat).write 142 (spotCtorWardsHashMem I vat) 0 2178 =
      spotCtorReturnMem I vat := by
    rfl
  have rdBeforeReturn := spot_ctor_run h with [
    push2 ⟨2178⟩, dup1, push2 ⟨142⟩, push1 ⟨0⟩,
    raw codecopy
      (Cₘ (UInt256.ofNat (MachineState.M (UInt256.ofNat 5).toNat 0 2178)) -
        Cₘ (UInt256.ofNat 5))
      (spotCtorReturnMem I vat) (UInt256.ofNat 69)
      (by spot_ctor_decode) mem_cost hcopy (by decide) (by evm_ov),
    push1 ⟨0⟩]
  exact rdBeforeReturn.ret 0 spotBytecode
    (by spot_ctor_decode) mem_cost (spotCtorReturnMem_read I vat) (by evm_ov)

theorem spotInitcodeSuccess
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ : AccountMap} {σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat : AccountAddress)
    (hcode : I.code = spotCtorCode vat)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) :
    RDret (spotCtorCode vat) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      (createdAccounts,
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner σ (spotCtorCallerWardsSlot I) ⟨1⟩)
              ⟨2⟩
              (spotCtorVatStored
                (sstoreAccountMap I.codeOwner σ (spotCtorCallerWardsSlot I) ⟨1⟩) I vat))
            ⟨3⟩ spotCtorOneWord)
          ⟨4⟩ ⟨1⟩)
      spotBytecode := by
  obtain ⟨_, _, rd54⟩ :=
    spotCtorArgsReach
      (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
      (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      vat hcode hwv
  obtain ⟨_, _, rd75⟩ := spotCtorWardsStoreReach vat hperm rd54
  obtain ⟨_, _, rd109⟩ := spotCtorVatStoreReach vat hperm rd75
  obtain ⟨_, _, rd128⟩ := spotCtorTailStoresReach vat hperm rd109
  exact spotCtorReturnTrace (I := I) vat rd128

end Benchmarks.Dss.Spot
