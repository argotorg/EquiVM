import Benchmarks.CompoundIII.Comet.Common
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

-- GENERALIZES Reasoning.ExternalCall.callBridge to zero-value CALL in either permission mode.
theorem zeroCallBridge {code I g s0 pc R mem aw rdata σ k C evm}
    {gasArg target inOffset inSize outOffset outSize : UInt256} {calldata : ByteArray}
    (h : RD code I g s0 pc
      (gasArg :: target :: ⟨0⟩ :: inOffset :: inSize :: outOffset :: outSize :: R)
      mem aw rdata σ k C)
    (hs : SourceState s0 I σ evm)
    (hdec : decode code pc = some (.CALL, .none))
    (hcd : mem.readWithPadding inOffset.toNat inSize.toNat = calldata)
    (hsmall : calldata.size ≤ Ethereum.EVM.maxReturnDataSizeByGas)
    (hov : R.length + 1 ≤ 1024) :
    ∃ (evm' : EVM.State) (σ' : AccountMap) (z : Bool) (out : ByteArray) (k' C' : Nat),
      callViaEVM evm (AccountAddress.ofUInt256 target) 0 calldata (z, evm', out) ∧
      SourceState s0 I σ' evm' ∧
      RD code I g s0 (pc + ⟨1⟩) ((if z then ⟨1⟩ else ⟨0⟩) :: R)
        (out.write 0 mem outOffset.toNat (min outSize (UInt256.ofNat out.size)).toNat)
        (UInt256.ofNat (MachineState.M (MachineState.M aw.toNat inOffset.toNat inSize.toNat)
          outOffset.toNat outSize.toNat)) out σ' k' C' ∧ out.size < 2^138 := by
  by_cases hd : I.depth = 1024
  · obtain ⟨k', C', rd⟩ := h.callDepthLimit hdec hd hov
    let evm' := { evm with substate := (evm.addAccessedAccount
      (AccountAddress.ofUInt256 target)).substate }
    have hc : callViaEVM evm (AccountAddress.ofUInt256 target) 0 calldata
        (false, evm', ByteArray.empty) := by
      apply callViaEVM.callNotMade rfl rfl
      rintro ⟨_, hn⟩
      exact hn (hs.env ▸ hd)
    exact ⟨evm', σ, false, ByteArray.empty, k', C', hc,
      ⟨hs.world, hs.env, hs.accounts⟩, rd, by decide⟩
  · have hdepth : I.depth.val < 1024 := by
      have hb := I.depth.isLt
      have hn : I.depth.val ≠ 1024 := by intro hh; exact hd (Fin.ext hh)
      omega
    obtain ⟨σ', z, out, Ain, gas, k', C', ⟨gasLeft, As, hθ⟩, rd, _⟩ :=
      h.call hdec hdepth hov
    rw [hcd] at hθ
    have ho : out.size < 2^138 :=
      Theta_returnData_size_lt_2pow138_of_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hθ hsmall
    let evm' := { evm with accountMap := σ', substate := As }
    have hc : callViaEVM evm (AccountAddress.ofUInt256 target) 0 calldata
        (z, evm', out) := by
      apply callViaEVM.callMade (valueWord := ⟨0⟩) (g' := gasLeft) (A' := As)
        wordOfInt_zero.symm ?_ rfl (Fin.zero_le _) ?_
      · refine ⟨gas, Ain, ?_⟩
        rw [hs.env, hs.world, ← hs.accounts]
        simpa only [accountAddress_roundtrip, Bool.true_and] using hθ
      · rw [hs.env]
        exact hd
    exact ⟨evm', σ', z, out, k', C', hc, ⟨hs.world, hs.env, rfl⟩, rd, ho⟩

end Benchmarks.CompoundIII.Comet
