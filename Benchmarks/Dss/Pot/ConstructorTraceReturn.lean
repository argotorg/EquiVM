import Benchmarks.Dss.Pot.ConstructorTraceWards
import Benchmarks.Dss.Pot.ConstructorTraceVat

/-!
# MakerDAO/Sky DSS Pot constructor scalar-store + return trace

From the vat store (`pc 109`, stack `[⟨1⟩]`) the constructor writes the four remaining scalars
(`dsr = ONE`, `chi = ONE`, `rho = now`, `live = 1` — reusing the stray `1` for `live`), then
`CODECOPY`s the runtime and `RETURN`s it.  Kept as a single terminal (`RDret`) so no intermediate
program counter needs to be reconciled.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Pot

set_option maxRecDepth 2000000

set_option maxHeartbeats 1000000 in
theorem potCtorReturnTrace
    {I : ExecutionEnv} {g : Sat256} {s0 : State} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σVat : AccountMap} {k C : Nat}
    (vat : AccountAddress) (hperm : I.perm = true)
    (h : RD (potCtorCode vat) I g s0 ⟨109⟩ [⟨1⟩]
      (potCtorWardsHashMem I vat) (UInt256.ofNat 5) rdata (cA, σVat) k C) :
    RDret (potCtorCode vat) g s0
      (cA,
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner σVat ⟨3⟩ potCtorOne) ⟨4⟩ potCtorOne)
            ⟨7⟩ (UInt256.ofNat I.header.timestamp)) ⟨8⟩ ⟨1⟩)
      potBytecode := by
  have hcopy : (potCtorCode vat).write 151 (potCtorWardsHashMem I vat) 0 2595 =
      potCtorReturnMem I vat := by rfl
  have rd122 := h.pushConst potCtorOne (width := 12) (op := .PUSH12)
    (by decide) (by pot_ctor_decode) (by evm_ov)
  have rd126 := pot_ctor_run rd122 with [push1 ⟨3⟩, dup2, swap1]
  obtain ⟨_, _, rd127⟩ := rd126.sstore hperm (by pot_ctor_decode) (by evm_ov)
  have rd129 := pot_ctor_run rd127 with [push1 ⟨4⟩]
  obtain ⟨_, _, rd130⟩ := rd129.sstore hperm (by pot_ctor_decode) (by evm_ov)
  have rd133 := pot_ctor_run rd130 with [timestamp, push1 ⟨7⟩]
  obtain ⟨_, _, rd134⟩ := rd133.sstore hperm (by pot_ctor_decode) (by evm_ov)
  have rd136 := pot_ctor_run rd134 with [push1 ⟨8⟩]
  obtain ⟨_, _, rd137⟩ := rd136.sstore hperm (by pot_ctor_decode) (by evm_ov)
  have rdBeforeReturn := pot_ctor_run rd137 with [
    push2 ⟨2595⟩, dup1, push2 ⟨151⟩, push1 ⟨0⟩,
    raw codecopy
      (Cₘ (UInt256.ofNat (MachineState.M (UInt256.ofNat 5).toNat 0 2595)) -
        Cₘ (UInt256.ofNat 5))
      (potCtorReturnMem I vat) (UInt256.ofNat 82)
      (by pot_ctor_decode) mem_cost hcopy (by decide) (by evm_ov),
    push1 ⟨0⟩]
  exact rdBeforeReturn.ret 0 potBytecode
    (by pot_ctor_decode) mem_cost (potCtorReturnMem_read I vat) (by evm_ov)

theorem potInitcodeSuccess
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ : AccountMap} {σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat : AccountAddress)
    (hcode : I.code = potCtorCode vat)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) :
    RDret (potCtorCode vat) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      (createdAccounts,
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner σ (potCtorCallerWardsSlot I) ⟨1⟩)
                  ⟨5⟩
                  (potCtorVatStored
                    (sstoreAccountMap I.codeOwner σ (potCtorCallerWardsSlot I) ⟨1⟩) I vat))
                ⟨3⟩ potCtorOne)
              ⟨4⟩ potCtorOne)
            ⟨7⟩ (UInt256.ofNat I.header.timestamp))
          ⟨8⟩ ⟨1⟩)
      potBytecode := by
  obtain ⟨_, _, rd54⟩ :=
    potCtorArgsReach
      (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
      (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      vat hcode hwv
  obtain ⟨_, _, rd75⟩ := potCtorWardsStoreReach vat hperm rd54
  obtain ⟨_, _, rd109⟩ := potCtorVatStoreReach vat hperm rd75
  exact potCtorReturnTrace vat hperm rd109

end Benchmarks.Dss.Pot
