import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

-- LIBRARY CANDIDATE: couple STATICCALL to the same opaque source call witness.
theorem staticCallBridge {code I g s0 pc R mem aw rdata σ k C evm}
    {gasArg target inOffset inSize outOffset outSize : UInt256} {calldata : ByteArray}
    (h : RD code I g s0 pc
      (gasArg :: target :: inOffset :: inSize :: outOffset :: outSize :: R)
      mem aw rdata σ k C)
    (hs : SourceState s0 I σ evm)
    (hdec : decode code pc = some (.STATICCALL, .none))
    (hcd : mem.readWithPadding inOffset.toNat inSize.toNat = calldata)
    (hsmall : calldata.size ≤ Ethereum.EVM.maxReturnDataSizeByGas)
    (hov : R.length + 1 ≤ 1024) :
    ∃ (evm' : EVM.State) (σ' : AccountMap) (z : Bool) (out : ByteArray) (k' C' : Nat),
      callViaEVM evm (AccountAddress.ofUInt256 target) 0 calldata (z, evm', out) false ∧
      SourceState s0 I σ' evm' ∧
      RD code I g s0 (pc + ⟨1⟩) ((if z then ⟨1⟩ else ⟨0⟩) :: R)
        (callOutputMem mem out outOffset outSize)
        (callActiveWords aw inOffset inSize outOffset outSize) out σ' k' C' ∧
      out.size < 2 ^ 138 := by
  by_cases hd : I.depth = 1024
  · obtain ⟨k', C', rd⟩ := h.solcStaticcallDepthLimit hdec hd hov
    let evm' := { evm with substate := (evm.addAccessedAccount (AccountAddress.ofUInt256 target)).substate }
    have hcall : callViaEVM evm (AccountAddress.ofUInt256 target) 0 calldata (false, evm', ByteArray.empty) false := by
      apply callViaEVM.callNotMade rfl rfl
      simp only [hs.env, hd, ne_eq, not_true_eq_false, and_false, not_false_eq_true]
    exact ⟨evm', σ, false, ByteArray.empty, k', C', hcall, ⟨hs.world, hs.env, hs.accounts⟩, rd, by decide⟩
  · have hdlt : I.depth.val < 1024 := by
      have hb := I.depth.isLt
      have hn : I.depth.val ≠ 1024 := fun hv => hd (Fin.ext hv)
      omega
    obtain ⟨σ', z, out, AIn, callGas, k', C', ⟨gasLeft, AS', hΘ⟩, rd, _⟩ :=
      h.solcStaticcall hdec hdlt hov
    rw [hcd] at hΘ
    have hout : out.size < 2 ^ 138 :=
      Theta_returnData_size_lt_2pow138_of_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hΘ hsmall
    let evm' := { evm with accountMap := σ', substate := AS' }
    have hcall : callViaEVM evm (AccountAddress.ofUInt256 target) 0 calldata (z, evm', out) false := by
      apply callViaEVM.callMade (valueWord := ⟨0⟩) (g' := gasLeft) (A' := AS')
        wordOfInt_zero.symm ?_ rfl ?_ ?_
      · refine ⟨callGas, AIn, ?_⟩
        simp only [hs.env, hs.world, ← hs.accounts, Bool.false_and]
        simpa only [accountAddress_roundtrip] using hΘ
      · exact Fin.zero_le _
      · simpa only [hs.env] using hd
    exact ⟨evm', σ', z, out, k', C', hcall, ⟨hs.world, hs.env, rfl⟩, rd, hout⟩

end Benchmarks.Morpho.MorphoBlue
