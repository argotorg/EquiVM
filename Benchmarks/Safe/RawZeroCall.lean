import Benchmarks.Safe.Common
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

-- GENERALIZES rawZeroCall_source_of_theta to static callers and includes depth-limit failure.
theorem rawZeroCallTrace {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    {code mem rdata : ByteArray} {pc aw gasArg target inOffset inSize outOffset outSize : UInt256}
    {k C : Nat} {R : List UInt256}
    (h : RD code I g (initState σ σ₀ g A I) pc
      (gasArg :: target :: ⟨0⟩ :: inOffset :: inSize :: outOffset :: outSize :: R)
      mem aw rdata σ k C)
    (hdec : decode code pc = some (.CALL, .none)) (hov : R.length + 1 ≤ 1024) :
    ∃ (evm' : EVM.State) (σ' : AccountMap) (z : Bool) (out : ByteArray) (aw' : UInt256)
      (k' C' : Nat),
      callViaEVM (initState σ σ₀ g A I) (AccountAddress.ofUInt256 target) 0
        (mem.readWithPadding inOffset.toNat inSize.toNat) (z, evm', out) ∧
      evm'.executionEnv = I ∧ evm'.accountMap = σ' ∧
      RD code I g (initState σ σ₀ g A I) (pc + ⟨1⟩)
        ((if z then ⟨1⟩ else ⟨0⟩) :: R) (callOutputMem mem out outOffset outSize)
        aw' out σ' k' C' ∧ out.size < UInt256.size := by
  by_cases hd : I.depth = 1024
  · obtain ⟨k', C', hr⟩ := RD.callDepthLimit h hdec hd hov
    refine ⟨{ initState σ σ₀ g A I with substate :=
        ((initState σ σ₀ g A I).addAccessedAccount
          (AccountAddress.ofUInt256 target)).substate },
      σ, false, ByteArray.empty, _, k', C', ?_, rfl, rfl, hr, by decide⟩
    exact callViaEVM.callNotMade rfl rfl (fun hgood ↦ hgood.2 hd)
  · have hdl : I.depth.val < 1024 := by
      have hbound := I.depth.isLt
      have hne : I.depth.val ≠ 1024 := fun he ↦ hd (Fin.ext he)
      omega
    obtain ⟨σ', z, out, AIn, gasCall, k', C', ⟨gasLeft, A', hΘ⟩, hr, hout⟩ :=
      RD.call h hdec hdl hov
    refine ⟨{ initState σ σ₀ g A I with accountMap := σ', substate := A' },
      σ', z, out, _, k', C', ?_, rfl, rfl, hr, hout⟩
    apply callViaEVM.callMade (perm := true) (g' := gasLeft) wordOfInt_zero.symm
      ⟨gasCall, AIn, ?_⟩ rfl (Fin.zero_le _) hd
    simpa only [initState, accountAddress_roundtrip, Bool.true_and] using hΘ

end Benchmarks.Safe
