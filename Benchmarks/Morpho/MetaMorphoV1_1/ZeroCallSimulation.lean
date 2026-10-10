import Reasoning.ExternalCall

/-! Couple a zero-value CALL to the source, including static mode and the depth limit. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

-- LIBRARY CANDIDATE: the raw counterpart of typedStaticcallSimulation.
theorem zeroCallSimulation {code : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {mem rdata data : ByteArray} {aw : UInt256} {σ : AccountMap}
    {k C : Nat} {pc gasArg target input inputSize output outputSize : UInt256}
    {R : List UInt256} {address : AccountAddress}
    (hstack : R.length + 1 ≤ 1024) (hdec : decode code pc = some (.CALL, none))
    (hs : SourceState s0 I σ evm) (htarget : address = AccountAddress.ofUInt256 target)
    (hdata : mem.readWithPadding input.toNat inputSize.toNat = data)
    (rd : RD code I g s0 pc
      (gasArg :: target :: ⟨0⟩ :: input :: inputSize :: output :: outputSize :: R)
      mem aw rdata σ k C) :
    ∃ (evm' : State) (ok : Bool) (out : ByteArray) (aw' : UInt256) (k' C' : Nat),
      callViaEVM evm address 0 data (ok, evm', out) ∧
      SourceState s0 I evm'.accountMap evm' ∧ out.size < UInt256.size ∧
      RD code I g s0 (pc + ⟨1⟩) ((if ok then ⟨1⟩ else ⟨0⟩) :: R)
        (out.write 0 mem output.toNat (min outputSize (UInt256.ofNat out.size)).toNat)
        aw' out evm'.accountMap k' C' := by
  by_cases hdepth : I.depth = 1024
  · obtain ⟨k', C', hrd⟩ := rd.callDepthLimit hdec hdepth hstack
    have hcall : callViaEVM evm address 0 data
        (false, { evm with substate := (evm.addAccessedAccount address).substate },
          ByteArray.empty) := by
      apply callViaEVM.callNotMade rfl rfl
      rintro ⟨_, hne⟩
      exact hne (by rw [hs.env]; exact hdepth)
    simp only [hs.accounts] at hrd
    exact ⟨_, false, ByteArray.empty, _, k', C', hcall, ⟨hs.world, hs.env, rfl⟩,
      by decide, hrd⟩
  · have hlt : I.depth.val < 1024 := by
      have hbound := I.depth.isLt
      have hne : I.depth.val ≠ 1024 := fun he ↦ hdepth (Fin.ext he)
      omega
    obtain ⟨σ', ok, out, A_in, callGas, k', C', ⟨g', A', htheta⟩, hrd, hout⟩ :=
      rd.call hdec hlt hstack
    have hcall : callViaEVM evm address 0 data
        (ok, { evm with accountMap := σ', substate := A' }, out) := by
      apply callViaEVM.callMade (perm := true) (g' := g') wordOfInt_zero.symm ?_ rfl
        (Fin.zero_le _) (by rw [hs.env]; exact hdepth)
      refine ⟨callGas, A_in, ?_⟩
      simpa only [hs.accounts, ← hs.world, ← hs.env, Bool.true_and, hdata,
        accountAddress_roundtrip, ← htarget] using htheta
    exact ⟨_, ok, out, _, k', C', hcall, ⟨hs.world, hs.env, rfl⟩, hout, hrd⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
