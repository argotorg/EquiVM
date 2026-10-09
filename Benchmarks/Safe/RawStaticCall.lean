import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

-- LIBRARY CANDIDATE: couple STATICCALL with any source state having the same call inputs.
theorem rawStaticCallTraceFrom {σ : AccountMap} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} (evm : EVM.State) {code mem rdata : ByteArray}
    {pc aw gasArg target inOffset inSize outOffset outSize : UInt256}
    {k C : Nat} {R : List UInt256}
    (h : RD code I g s0 pc
      (gasArg :: target :: inOffset :: inSize :: outOffset :: outSize :: R) mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hdec : decode code pc = some (.STATICCALL, .none)) (hov : R.length + 1 ≤ 1024) :
    ∃ (evm' : EVM.State) (σ' : AccountMap) (z : Bool) (out : ByteArray) (aw' : UInt256)
      (k' C' : Nat),
      callViaEVM evm (AccountAddress.ofUInt256 target) 0
        (mem.readWithPadding inOffset.toNat inSize.toNat) (z, evm', out) false ∧
      evm'.executionEnv = I ∧ evm'.accountMap = σ' ∧ evm'.σ₀ = s0.σ₀ ∧
      RD code I g s0 (pc + ⟨1⟩)
        ((if z then ⟨1⟩ else ⟨0⟩) :: R) (callOutputMem mem out outOffset outSize)
        aw' out σ' k' C' ∧ out.size < UInt256.size ∧
      ((mem.readWithPadding inOffset.toNat inSize.toNat).size ≤ maxReturnDataSizeByGas →
        out.size < 2 ^ 138) := by
  by_cases hd : I.depth = 1024
  · obtain ⟨k', C', hr⟩ := RD.solcStaticcallDepthLimit h hdec hd hov
    refine ⟨{ evm with substate :=
        (evm.addAccessedAccount (AccountAddress.ofUInt256 target)).substate },
      σ, false, ByteArray.empty, _, k', C', ?_, hee, hacc, hworld, hr,
      by decide, fun _ ↦ by decide⟩
    exact callViaEVM.callNotMade rfl rfl
      (fun hgood ↦ hgood.2 (by simpa only [hee] using hd))
  · have hdl : I.depth.val < 1024 := by
      have hbound := I.depth.isLt
      have hne : I.depth.val ≠ 1024 := fun he ↦ hd (Fin.ext he)
      omega
    obtain ⟨σ', z, out, AIn, gasCall, k', C', ⟨gasLeft, A', hΘ⟩, hr, hout⟩ :=
      RD.solcStaticcall h hdec hdl hov
    refine ⟨{ evm with accountMap := σ', substate := A' },
      σ', z, out, _, k', C', ?_, hee, rfl, hworld, hr, hout, ?_⟩
    · apply callViaEVM.callMade (perm := false) (g' := gasLeft) wordOfInt_zero.symm
        ⟨gasCall, AIn, ?_⟩ rfl (Fin.zero_le _) (by simpa only [hee] using hd)
      simpa only [hee, hacc, hworld, accountAddress_roundtrip, Bool.false_and] using hΘ
    · exact fun hsmall ↦
        Theta_returnData_size_lt_2pow138_of_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hΘ hsmall

end Benchmarks.Safe
