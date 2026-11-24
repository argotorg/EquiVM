import Reasoning.ExternalCall

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- GENERALIZES Reasoning.ExternalCall.callStateMade to either caller permission bit.
theorem callStateMadeAny {s0 I σ evm} (hs : SourceState s0 I σ evm)
    {target value : UInt256} {calldata : ByteArray}
    {σ' : AccountMap} {gasLeft callGas : UInt256} {AS' AIn : Substate} {z : Bool} {out : ByteArray}
    (hbalance : value ≤ (σ.get? I.codeOwner |>.elim ⟨0⟩ (·.balance)))
    (hdepth : I.depth.val < 1024)
    (hΘ : (σ', gasLeft, AS', z, out) = Θ fork σ s0.σ₀ AIn
      (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
      (AccountAddress.ofUInt256 target) (toExecute fork σ (AccountAddress.ofUInt256 target))
      callGas (UInt256.ofNat I.gasPrice) value value calldata (I.depth + 1) I.header
      I.blobVersionedHashes I.blocks I.perm) :
    callViaEVM fork (callState evm σ) (AccountAddress.ofUInt256 target) (Int.ofNat value.toNat)
      calldata (z,
        { callState evm σ with
          accountMap := σ'
          substate := AS' }, out) := by
  apply callViaEVM.callMade (valueWord := value) (g' := gasLeft) (A' := AS')
    (wordOfInt_ofNat_toNat value).symm ?_ rfl ?_ ?_
  · refine ⟨callGas, AIn, ?_⟩
    simp only [callState, hs.env]
    rw [hs.world]
    simpa only [accountAddress_roundtrip, Bool.true_and] using hΘ
  · simpa only [callState, hs.env] using hbalance
  · simp only [callState, hs.env]
    intro hd
    have hval := congrArg Fin.val hd
    change I.depth.val = 1024 at hval
    omega

-- GENERALIZES Reasoning.ExternalCall.callBridge to zero-value CALL in static mode.
theorem callBridgeOr {code I g s0 pc R mem aw rdata σ k C evm}
    {gasArg target value inOffset inSize outOffset outSize : UInt256} {calldata : ByteArray}
    (h : RD fork code I g s0 pc
      (gasArg :: target :: value :: inOffset :: inSize :: outOffset :: outSize :: R)
      mem aw rdata σ k C)
    (hs : SourceState s0 I σ evm) (hperm : I.perm = true ∨ value = ⟨0⟩)
    (hdec : decode code pc = some (.CALL, .none))
    (hcd : mem.readWithPadding inOffset.toNat inSize.toNat = calldata)
    (hsmall : calldata.size ≤ Ethereum.EVM.maxReturnDataSizeByGas)
    (hov : R.length + 1 ≤ 1024) :
    ∃ (evm' : EVM.State) (σ' : AccountMap)
      (z : Bool) (out : ByteArray) (k' C' : Nat),
      callViaEVM fork evm (AccountAddress.ofUInt256 target) (Int.ofNat value.toNat)
        calldata (z, evm', out) ∧
      SourceState s0 I σ' evm' ∧
      RD fork code I g s0 (pc + ⟨1⟩) ((if z then ⟨1⟩ else ⟨0⟩) :: R)
        (callOutputMem mem out outOffset outSize)
        (callActiveWords aw inOffset inSize outOffset outSize) out σ' k' C' ∧
      out.size < 2 ^ 138 := by
  by_cases hd : I.depth = 1024
  · obtain ⟨_, _, rd⟩ := h.callValueDepthLimitOr hperm hdec hd hov
    have hraw := callStateNotMade (fork := fork) (target := target) (value := value) (calldata := calldata)
      hs (fun hn => hn.2 hd)
    obtain ⟨evm', hcall, hs'⟩ := hs.callTransport hraw
    exact ⟨evm', σ, false, ByteArray.empty, _, _, hcall, hs', rd, by decide⟩
  · have hdlt : I.depth.val < 1024 := by
      have hb := I.depth.isLt
      have hn : I.depth.val ≠ 1024 := by
        intro hv
        exact hd (Fin.ext hv)
      omega
    by_cases hb : value ≤ (σ.get? I.codeOwner |>.elim ⟨0⟩ (·.balance))
    · obtain ⟨σ', z, out, AIn, callGas, k', C', ⟨gasLeft, AS', hΘ⟩, rd, _⟩ :=
        h.callValueMadeOr hdec hperm hb hdlt hov
      rw [hcd] at hΘ
      have ho : out.size < 2 ^ 138 :=
        Theta_returnData_size_lt_2pow138_of_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hΘ hsmall
      have hraw := callStateMadeAny hs hb hdlt hΘ
      obtain ⟨evm', hcall, hs'⟩ := hs.callTransport hraw
      exact ⟨evm', σ', z, out, k', C', hcall, hs', rd, ho⟩
    · obtain ⟨_, _, rd⟩ := h.callValueInsufficientBalanceOr hperm hdec hb hdlt hov
      have hraw := callStateNotMade (fork := fork) (target := target) (value := value) (calldata := calldata)
        hs (fun hn => hb hn.1)
      obtain ⟨evm', hcall, hs'⟩ := hs.callTransport hraw
      exact ⟨evm', σ, false, ByteArray.empty, _, _, hcall, hs', rd, by decide⟩

end Benchmarks.EAS.EAS
