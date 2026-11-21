import Benchmarks.Midnight.CallGas
import Benchmarks.Midnight.PrecompileOutput

/-! Couple a zero-value CALL with its source execution, including static contexts. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

-- GENERALIZES Reasoning.ExternalCall.callBridge to zero-value calls in either permission mode.
theorem zeroValueCallBridge {code I g s0 pc R mem aw rdata σ k C evm}
    {gasArg target inOffset inSize : UInt256} {calldata : ByteArray}
    (rd : RD code I g s0 pc
      (gasArg :: target :: ⟨0⟩ :: inOffset :: inSize :: ⟨0⟩ :: ⟨0⟩ :: R)
      mem aw rdata σ k C)
    (hs : SourceState s0 I σ evm)
    (hdec : decode code pc = some (.CALL, .none))
    (hcd : mem.readWithPadding inOffset.toNat inSize.toNat = calldata)
    (hsmall : calldata.size ≤ Ethereum.EVM.maxReturnDataSizeByGas)
    (hfork : I.fork ≥ .osaka)
    (hstack : R.length + 1 ≤ 1024) :
    X (g.toNat + 1) (D_J code 0) s0 = .error .OutOfGass ∨
    ∃ (evm' : EVM.State) (σ' : AccountMap) (z : Bool) (out : ByteArray) (aw' : UInt256)
      (k' C' : Nat),
      callViaEVM evm (AccountAddress.ofUInt256 target) 0 calldata (z, evm', out) true ∧
      SourceState s0 I σ' evm' ∧
      RD code I g s0 (pc + ⟨1⟩) ((if z then ⟨1⟩ else ⟨0⟩) :: R)
        mem aw' out σ' k' C' ∧
      out.size < 2 ^ 138 ∧
      (out.size ≤ max 1024 calldata.size ∨ memoryCost ((out.size + 31) / 32) ≤ g.toNat) := by
  have hmem (out : ByteArray) :
      out.write 0 mem (⟨0⟩ : UInt256).toNat (min (⟨0⟩ : UInt256) (UInt256.ofNat out.size)).toNat =
        mem := by
    have hmin : min (⟨0⟩ : UInt256) (UInt256.ofNat out.size) = ⟨0⟩ := by
      change (if (⟨0⟩ : UInt256) ≤ UInt256.ofNat out.size then (⟨0⟩ : UInt256)
        else UInt256.ofNat out.size) = _
      rw [if_pos (show (⟨0⟩ : UInt256) ≤ UInt256.ofNat out.size from Fin.zero_le _)]
    rw [hmin]
    exact byteArray_write_len_zero _ _ _ _
  by_cases hd : I.depth = 1024
  · obtain ⟨k', C', rd'⟩ := rd.callDepthLimit hdec hd hstack
    rw [hmem] at rd'
    let evm' := { evm with
      substate := callSubstate evm.executionEnv.fork evm.accountMap
        (AccountAddress.ofUInt256 target) evm.substate }
    refine Or.inr ⟨evm', σ, false, ByteArray.empty, _, k', C', ?_,
      ⟨hs.world, hs.env, hs.accounts⟩, rd', by decide, Or.inl (Nat.zero_le _)⟩
    apply callViaEVM.callNotMade rfl rfl
    intro h
    exact h.2 (hs.env ▸ hd)
  · have hdlt : I.depth.val < 1024 := by
      have hb := I.depth.isLt
      have hn : I.depth.val ≠ 1024 := fun h ↦ hd (Fin.ext h)
      omega
    obtain ⟨σ', z, out, AIn, callGas, k', C', ⟨gasLeft, A', hΘ⟩, rd', _, hgas⟩ :=
      callWithGasBound rd hdec hdlt hstack
    rcases hgas with hoog | hgas
    · exact Or.inl hoog
    rw [hcd] at hΘ
    rw [hmem] at rd'
    let evm' := { evm with accountMap := σ', substate := A' }
    refine Or.inr ⟨evm', σ', z, out, _, k', C', ?_, ⟨hs.world, hs.env, rfl⟩, rd', ?_, ?_⟩
    · apply callViaEVM.callMade (valueWord := ⟨0⟩) (g' := gasLeft) (A' := A')
        wordOfInt_zero.symm ?_ rfl (Fin.zero_le _) ?_
      · refine ⟨callGas, AIn, ?_⟩
        simpa only [hs.env, hs.world, ← hs.accounts, Bool.true_and, accountAddress_roundtrip]
          using hΘ
      · simpa only [hs.env] using hd
    · exact Theta_returnData_size_lt_2pow138_of_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        hΘ hsmall
    · have hb := theta_output_memoryCost_or_small I.fork σ s0.σ₀ AIn
        (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
        (AccountAddress.ofUInt256 target) (toExecute I.fork σ (AccountAddress.ofUInt256 target))
        calldata callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩ (I.depth + 1) I.header
        I.blobVersionedHashes I.blocks I.perm hfork
      rw [← hΘ] at hb
      exact hb.imp_right (fun h ↦ h.trans (by omega))

end Benchmarks.Midnight
