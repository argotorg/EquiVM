import Benchmarks.Midnight.DelegateCallDepthLimit
import Benchmarks.Midnight.GasOutputSpent

variable {fork : Ethereum.Fork}

/-! Source coupling for DELEGATECALLs, retaining the parent and child gas costs. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

-- LIBRARY CANDIDATE: source coupling for delegate calls with gas and output-size bounds.
theorem delegateCallCostBridge {code I g s0 pc R mem aw rdata σ k C evm}
    {gasArg target inOffset inSize : UInt256} {calldata : ByteArray}
    (rd : RD fork code I g s0 pc
      (gasArg :: target :: inOffset :: inSize :: ⟨0⟩ :: ⟨0⟩ :: R)
      mem aw rdata σ k C)
    (hs : SourceState s0 I σ evm)
    (hdec : decode code pc = some (.DELEGATECALL, .none))
    (hcd : mem.readWithPadding inOffset.toNat inSize.toNat = calldata)
    (hsmall : calldata.size ≤ Ethereum.EVM.maxReturnDataSizeByGas)
    (hfork : fork ≥ .osaka)
    (hstack : R.length + 1 ≤ 1024) :
    X fork (g.toNat + 1) (D_J code 0) s0 = .error .OutOfGass ∨
    ∃ (evm' : EVM.State) (σ' : AccountMap) (z : Bool) (out : ByteArray) (aw' : UInt256)
      (k' C' : Nat),
      delegateCallViaEVM fork evm (AccountAddress.ofUInt256 target) calldata (z, evm', out) ∧
      SourceState s0 I σ' evm' ∧
      RD fork code I g s0 (pc + ⟨1⟩) ((if z then ⟨1⟩ else ⟨0⟩) :: R)
        mem aw' out σ' k' C' ∧
      out.size < 2 ^ 138 ∧
      (out.size ≤ max 1024 calldata.size ∨ C + 100 + forwardingMinimum (memoryCost ((out.size + 31) / 32)) ≤ g.toNat) ∧
      (z = false ∨ C + 100 ≤ C' ∧ aw.toNat ≤ aw'.toNat ∧
        Cₘ aw' + C + 100 ≤ Cₘ aw + C' ∧
        (out.size ≤ max 1024 calldata.size ∨
          Cₘ aw' + C + 100 + memoryCost ((out.size + 31) / 32) ≤ Cₘ aw + C')) := by
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
  · obtain ⟨k', C', rd'⟩ := rd.delegateCallDepthLimit hdec hd hstack
    rw [hmem] at rd'
    let evm' := { evm with
      substate := callSubstate fork evm.accountMap
        (AccountAddress.ofUInt256 target) evm.substate }
    refine Or.inr ⟨evm', σ, false, ByteArray.empty, _, k', C', ?_,
      ⟨hs.world, hs.env, hs.accounts⟩, rd', by decide, Or.inl (Nat.zero_le _), Or.inl rfl⟩
    exact delegateCallViaEVM.callNotMade rfl rfl (hs.env ▸ hd)
  · have hdlt : I.depth.val < 1024 := by
      have hb := I.depth.isLt
      have hn : I.depth.val ≠ 1024 := fun h ↦ hd (Fin.ext h)
      omega
    obtain ⟨σ', z, out, AIn, callGas, k', C', ⟨gasLeft, A', hΘ, hpaid⟩, rd', _, hgas⟩ :=
      delegateCallWithForwardingCost rd hdec hdlt hstack
    rcases hgas with hoog | hgas
    · exact Or.inl hoog
    rcases hpaid with hoog | ⟨hC, hpaid⟩
    · exact Or.inl hoog
    rw [hcd] at hΘ
    rw [hmem] at rd'
    let evm' := { evm with accountMap := σ', substate := A' }
    refine Or.inr ⟨evm', σ', z, out, _, k', C', ?_, ⟨hs.world, hs.env, rfl⟩, rd', ?_, ?_, ?_⟩
    · apply delegateCallViaEVM.callMade (g' := gasLeft) (A' := A') ?_ rfl ?_
      · refine ⟨callGas, AIn, ?_⟩
        simpa only [hs.env, hs.world, ← hs.accounts] using hΘ
      · simpa only [hs.env] using hd
    · exact Theta_returnData_size_lt_2pow138_of_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        hΘ hsmall
    · have hb := theta_output_memoryCost_or_small fork σ s0.σ₀ AIn
        I.source I.sender
        I.codeOwner (toExecute fork σ (AccountAddress.ofUInt256 target))
        calldata callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ I.weiValue (I.depth + 1) I.header
        I.blobVersionedHashes I.blocks I.perm hfork
      rw [← hΘ] at hb
      rcases hb with hsmall | hcost
      · exact Or.inl hsmall
      · have hmin := forwardingMinimum_mono hcost
        change forwardingMinimum (memoryCost ((out.size + 31) / 32)) ≤
          forwardingMinimum callGas.toNat at hmin
        exact Or.inr (by omega)

    · apply Or.inr
      refine ⟨hC, ?_, ?_, ?_⟩
      · have hb : MachineState.M (MachineState.M aw.toNat inOffset.toNat inSize.toNat)
            (⟨0⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat < UInt256.size :=
          MachineState.M_M_lt_uint256_size aw.val.isLt inOffset.val.isLt inSize.val.isLt
            (by decide) (by decide)
        rw [UInt256.toNat_ofNat_of_lt hb]
        exact MachineState.M_M_ge_active _ _ _ _ _
      · omega
      · have hb := theta_output_memoryCost_remaining_or_small fork σ s0.σ₀ AIn
          I.source I.sender
          I.codeOwner (toExecute fork σ (AccountAddress.ofUInt256 target))
          calldata callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ I.weiValue (I.depth + 1) I.header
          I.blobVersionedHashes I.blocks I.perm hfork
        rw [← hΘ] at hb
        rcases hb with hsmall | hcost
        · exact Or.inl hsmall
        · exact Or.inr (by dsimp only at hcost; omega)

end Benchmarks.Midnight
