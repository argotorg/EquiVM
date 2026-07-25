import Benchmarks.Dss.Cat.ConstructorTraceWards
import Benchmarks.Dss.Cat.ConstructorTraceVat

/-!
# MakerDAO/Sky DSS Cat constructor scalar-store + return trace

From the vat store (`pc 109`, stack `[⟨1⟩]`) the constructor writes the single remaining scalar
(`live = 1` at slot 2 — reusing the stray `1`), then `CODECOPY`s the 3873-byte runtime from creation
offset 126 and `RETURN`s it.  Kept as a single terminal (`RDret`) so no intermediate program counter
needs to be reconciled.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Cat

set_option maxRecDepth 2000000

set_option maxHeartbeats 1000000 in
theorem catCtorReturnTrace
    {I : ExecutionEnv} {g : Sat256} {s0 : State} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σVat : AccountMap} {k C : Nat}
    (vat : AccountAddress) (hperm : I.perm = true)
    (h : RD (catCtorCode vat) I g s0 ⟨109⟩ [⟨1⟩]
      (catCtorWardsHashMem I vat) (UInt256.ofNat 5) rdata (cA, σVat) k C) :
    RDret (catCtorCode vat) g s0
      (cA, sstoreAccountMap I.codeOwner σVat ⟨2⟩ ⟨1⟩)
      catBytecode := by
  have hcopy : (catCtorCode vat).write 126 (catCtorWardsHashMem I vat) 0 3873 =
      catCtorReturnMem I vat := by rfl
  have rd111 := cat_ctor_run h with [push1 ⟨2⟩]
  obtain ⟨_, _, rd112⟩ := rd111.sstore hperm (by cat_ctor_decode) (by evm_ov)
  have rdBeforeReturn := cat_ctor_run rd112 with [
    push2 ⟨3873⟩, dup1, push2 ⟨126⟩, push1 ⟨0⟩,
    raw codecopy
      (Cₘ (UInt256.ofNat (MachineState.M (UInt256.ofNat 5).toNat 0 3873)) -
        Cₘ (UInt256.ofNat 5))
      (catCtorReturnMem I vat) (UInt256.ofNat 122)
      (by cat_ctor_decode) mem_cost hcopy (by decide) (by evm_ov),
    push1 ⟨0⟩]
  exact rdBeforeReturn.ret 0 catBytecode
    (by cat_ctor_decode) mem_cost (catCtorReturnMem_read I vat) (by evm_ov)

theorem catInitcodeSuccess
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ : AccountMap} {σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat : AccountAddress)
    (hcode : I.code = catCtorCode vat)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) :
    RDret (catCtorCode vat) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      (createdAccounts,
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner σ (catCtorCallerWardsSlot I) ⟨1⟩)
            ⟨3⟩
            (catCtorVatStored
              (sstoreAccountMap I.codeOwner σ (catCtorCallerWardsSlot I) ⟨1⟩) I vat))
          ⟨2⟩ ⟨1⟩)
      catBytecode := by
  obtain ⟨_, _, rd54⟩ :=
    catCtorArgsReach
      (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
      (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      vat hcode hwv
  obtain ⟨_, _, rd75⟩ := catCtorWardsStoreReach vat hperm rd54
  obtain ⟨_, _, rd109⟩ := catCtorVatStoreReach vat hperm rd75
  exact catCtorReturnTrace vat hperm rd109

end Benchmarks.Dss.Cat
