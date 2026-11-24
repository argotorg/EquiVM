import Benchmarks.CurveVault.Calls

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch Reasoning.VyperCalls
namespace Benchmarks.CurveVault

-- LIBRARY CANDIDATE: a static call with one copied result word and an explicit
-- success/return-size guard. The typed call remains opaque to the caller.
theorem staticWordCallBridgeExact {cfg : Config} {code : ByteArray}
    {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {pc next gasArg target inOffset outOffset : UInt256} {R : List UInt256}
    {callName : Ident} {nextStack : ByteArray → List UInt256}
    (hs : SourceState s0 I σ evm) (hstack : R.length + 1 ≤ 1024)
    (hpc : decode code pc = some (.STATICCALL, .none))
    (hcd : cfg.externalABI.encode? callName [] = some (mem.readWithPadding inOffset.toNat 4))
    (hbuffer : outOffset.toNat + 32 ≤ mem.size)
    (hpass : ∀ {mem' aw' out σ' k' C'}, 32 ≤ out.size → out.size < UInt256.size →
      RD fork code I g s0 (pc + ⟨1⟩) (⟨1⟩ :: R) mem' aw' out σ' k' C' →
      ∃ k'' C'', RD fork code I g s0 next (nextStack out) mem' aw' out σ' k'' C'')
    (hfail : ∀ {mem' aw' out σ' k' C'},
      RD fork code I g s0 (pc + ⟨1⟩) (⟨0⟩ :: R) mem' aw' out σ' k' C' → RDrev fork code g s0)
    (hshort : ∀ {mem' aw' out σ' k' C'}, out.size < 32 →
      RD fork code I g s0 (pc + ⟨1⟩) (⟨1⟩ :: R) mem' aw' out σ' k' C' → RDrev fork code g s0)
    (h : RD fork code I g s0 pc
      (gasArg :: target :: inOffset :: ⟨4⟩ :: outOffset :: ⟨32⟩ :: R) mem aw rdata σ k C) :
    (∃ (evm' : State) (σ' : AccountMap) (out : ByteArray) (aw' : UInt256) (k' C' : Nat),
      aw' = UInt256.ofNat (MachineState.M (MachineState.M aw.toNat inOffset.toNat 4) outOffset.toNat 32) ∧
      32 ≤ out.size ∧ out.size < UInt256.size ∧
      typedCallViaEVM fork cfg evm (AccountAddress.ofUInt256 target) callName 0 [] (true, evm', out) false ∧
      SourceState s0 I σ' evm' ∧
      RD fork code I g s0 next (nextStack out) ((retWord out).toByteArray.write 0 mem outOffset.toNat 32) aw' out σ' k' C') ∨
    (∃ (evm' : State) (out : ByteArray),
      typedCallViaEVM fork cfg evm (AccountAddress.ofUInt256 target) callName 0 [] (false, evm', out) false ∧ RDrev fork code g s0) ∨
    (∃ (evm' : State) (out : ByteArray),
      typedCallViaEVM fork cfg evm (AccountAddress.ofUInt256 target) callName 0 [] (true, evm', out) false ∧
      out.size < 32 ∧ RDrev fork code g s0) := by
  obtain ⟨evm', σ', z, out, k', C', hcall, hs', rd, hout⟩ :=
    typedStaticCallBridge h hs hpc hcd (by decide +kernel) hstack
  have hout256 : out.size < UInt256.size := lt_trans hout (by decide +kernel)
  cases z with
  | false => exact Or.inr (Or.inl ⟨evm', out, hcall, hfail rd⟩)
  | true =>
    by_cases h32 : 32 ≤ out.size
    · obtain ⟨k'', C'', rdNext⟩ := hpass h32 hout256 rd
      have hmin : (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 32 := min32_toNat _ h32 hout256
      rw [hmin, write_out_eq_word out mem outOffset.toNat h32 hbuffer] at rdNext
      exact Or.inl ⟨evm', σ', out, _, k'', C'', rfl, h32, hout256, hcall, hs', rdNext⟩
    · have hlt : out.size < 32 := by omega
      exact Or.inr (Or.inr ⟨evm', out, hcall, hlt, hshort hlt rd⟩)
theorem staticWordCallBridge {cfg : Config} {code : ByteArray}
    {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {pc next gasArg target inOffset outOffset : UInt256} {R : List UInt256}
    {callName : Ident} {nextStack : ByteArray → List UInt256}
    (hs : SourceState s0 I σ evm) (hstack : R.length + 1 ≤ 1024)
    (hpc : decode code pc = some (.STATICCALL, .none))
    (hcd : cfg.externalABI.encode? callName [] = some (mem.readWithPadding inOffset.toNat 4))
    (hbuffer : outOffset.toNat + 32 ≤ mem.size)
    (hpass : ∀ {mem' aw' out σ' k' C'}, 32 ≤ out.size → out.size < UInt256.size →
      RD fork code I g s0 (pc + ⟨1⟩) (⟨1⟩ :: R) mem' aw' out σ' k' C' →
      ∃ k'' C'', RD fork code I g s0 next (nextStack out) mem' aw' out σ' k'' C'')
    (hfail : ∀ {mem' aw' out σ' k' C'},
      RD fork code I g s0 (pc + ⟨1⟩) (⟨0⟩ :: R) mem' aw' out σ' k' C' → RDrev fork code g s0)
    (hshort : ∀ {mem' aw' out σ' k' C'}, out.size < 32 →
      RD fork code I g s0 (pc + ⟨1⟩) (⟨1⟩ :: R) mem' aw' out σ' k' C' → RDrev fork code g s0)
    (h : RD fork code I g s0 pc
      (gasArg :: target :: inOffset :: ⟨4⟩ :: outOffset :: ⟨32⟩ :: R) mem aw rdata σ k C) :
    (∃ (evm' : State) (σ' : AccountMap) (out : ByteArray) (aw' : UInt256) (k' C' : Nat),
      32 ≤ out.size ∧ out.size < UInt256.size ∧
      typedCallViaEVM fork cfg evm (AccountAddress.ofUInt256 target) callName 0 [] (true, evm', out) false ∧
      SourceState s0 I σ' evm' ∧
      RD fork code I g s0 next (nextStack out) ((retWord out).toByteArray.write 0 mem outOffset.toNat 32) aw' out σ' k' C') ∨
    (∃ (evm' : State) (out : ByteArray),
      typedCallViaEVM fork cfg evm (AccountAddress.ofUInt256 target) callName 0 [] (false, evm', out) false ∧ RDrev fork code g s0) ∨
    (∃ (evm' : State) (out : ByteArray),
      typedCallViaEVM fork cfg evm (AccountAddress.ofUInt256 target) callName 0 [] (true, evm', out) false ∧
      out.size < 32 ∧ RDrev fork code g s0) := by
  rcases staticWordCallBridgeExact hs hstack hpc hcd hbuffer hpass hfail hshort h with
    ⟨evm', σ', out, aw', k', C', _, h32, hwide, hcall, hs', rd⟩ | hfail
  · exact Or.inl ⟨evm', σ', out, aw', k', C', h32, hwide, hcall, hs', rd⟩
  · exact Or.inr hfail

end Benchmarks.CurveVault
