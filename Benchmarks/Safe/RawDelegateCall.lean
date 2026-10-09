import Benchmarks.Safe.DelegateCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

-- LIBRARY CANDIDATE: couple a DELEGATECALL cursor to any matching source state.
theorem rawDelegateCallTraceFromBounded {σ : AccountMap} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} (evm : EVM.State)
    {code mem rdata : ByteArray} {pc aw gasArg target inOffset inSize outOffset outSize : UInt256}
    {k C : Nat} {R : List UInt256}
    (h : RD code I g s0 pc
      (gasArg :: target :: inOffset :: inSize :: outOffset :: outSize :: R)
      mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hdec : decode code pc = some (.DELEGATECALL, .none)) (hov : R.length + 1 ≤ 1024) :
    ∃ (evm' : EVM.State) (σ' : AccountMap) (z : Bool) (out : ByteArray) (aw' : UInt256)
      (k' C' : Nat),
      delegateCallViaEVM evm (AccountAddress.ofUInt256 target)
        (mem.readWithPadding inOffset.toNat inSize.toNat) (z, evm', out) ∧
      evm'.executionEnv = I ∧ evm'.accountMap = σ' ∧ evm'.σ₀ = s0.σ₀ ∧
      RD code I g s0 (pc + ⟨1⟩)
        ((if z then ⟨1⟩ else ⟨0⟩) :: R) (callOutputMem mem out outOffset outSize)
        aw' out σ' k' C' ∧ out.size < UInt256.size ∧
      ((mem.readWithPadding inOffset.toNat inSize.toNat).size ≤ maxReturnDataSizeByGas →
        out.size < 2 ^ 138) := by
  by_cases hd : I.depth = 1024
  · obtain ⟨k', C', hr⟩ := delegateCallDepthLimitReach h hdec hd hov
    refine ⟨{ evm with substate :=
        (evm.addAccessedAccount (AccountAddress.ofUInt256 target)).substate },
      σ, false, ByteArray.empty, _, k', C', ?_, hee, hacc, hworld, hr,
      by decide, fun _ ↦ by decide⟩
    exact delegateCallViaEVM.callNotMade rfl rfl (by simpa only [hee] using hd)
  · have hdl : I.depth.val < 1024 := by
      have hbound := I.depth.isLt
      have hne : I.depth.val ≠ 1024 := fun he ↦ hd (Fin.ext he)
      omega
    obtain ⟨σ', z, out, AIn, gasCall, k', C', ⟨gasLeft, A', hΘ⟩, hr, hout⟩ :=
      delegateCallReach h hdec hdl hov
    refine ⟨{ evm with accountMap := σ', substate := A' },
      σ', z, out, _, k', C', ?_, hee, rfl, hworld, hr, hout, ?_⟩
    · apply delegateCallViaEVM.callMade (g' := gasLeft) ⟨gasCall, AIn, ?_⟩ rfl
        (by simpa only [hee] using hd)
      simpa only [hee, hacc, hworld] using hΘ
    · exact fun hsmall ↦
        Theta_returnData_size_lt_2pow138_of_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hΘ hsmall

theorem rawDelegateCallTraceFrom {σ : AccountMap} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} (evm : EVM.State)
    {code mem rdata : ByteArray} {pc aw gasArg target inOffset inSize outOffset outSize : UInt256}
    {k C : Nat} {R : List UInt256}
    (h : RD code I g s0 pc
      (gasArg :: target :: inOffset :: inSize :: outOffset :: outSize :: R)
      mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hdec : decode code pc = some (.DELEGATECALL, .none)) (hov : R.length + 1 ≤ 1024) :
    ∃ (evm' : EVM.State) (σ' : AccountMap) (z : Bool) (out : ByteArray) (aw' : UInt256)
      (k' C' : Nat),
      delegateCallViaEVM evm (AccountAddress.ofUInt256 target)
        (mem.readWithPadding inOffset.toNat inSize.toNat) (z, evm', out) ∧
      evm'.executionEnv = I ∧ evm'.accountMap = σ' ∧ evm'.σ₀ = s0.σ₀ ∧
      RD code I g s0 (pc + ⟨1⟩)
        ((if z then ⟨1⟩ else ⟨0⟩) :: R) (callOutputMem mem out outOffset outSize)
        aw' out σ' k' C' ∧ out.size < UInt256.size := by
  obtain ⟨evm', σ', z, out, aw', k', C', hc, he, ha, hw, hr, hs, _⟩ :=
    rawDelegateCallTraceFromBounded evm h hee hacc hworld hdec hov
  exact ⟨evm', σ', z, out, aw', k', C', hc, he, ha, hw, hr, hs⟩

-- LIBRARY CANDIDATE: the initial-state specialization of the delegate-call bridge.
theorem rawDelegateCallTrace {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    {code mem rdata : ByteArray} {pc aw gasArg target inOffset inSize outOffset outSize : UInt256}
    {k C : Nat} {R : List UInt256}
    (h : RD code I g (initState σ σ₀ g A I) pc
      (gasArg :: target :: inOffset :: inSize :: outOffset :: outSize :: R)
      mem aw rdata σ k C)
    (hdec : decode code pc = some (.DELEGATECALL, .none)) (hov : R.length + 1 ≤ 1024) :
    ∃ (evm' : EVM.State) (σ' : AccountMap) (z : Bool) (out : ByteArray) (aw' : UInt256)
      (k' C' : Nat),
      delegateCallViaEVM (initState σ σ₀ g A I) (AccountAddress.ofUInt256 target)
        (mem.readWithPadding inOffset.toNat inSize.toNat) (z, evm', out) ∧
      evm'.executionEnv = I ∧ evm'.accountMap = σ' ∧
      RD code I g (initState σ σ₀ g A I) (pc + ⟨1⟩)
        ((if z then ⟨1⟩ else ⟨0⟩) :: R) (callOutputMem mem out outOffset outSize)
        aw' out σ' k' C' ∧ out.size < UInt256.size := by
  obtain ⟨evm', σ', z, out, aw', k', C', hc, he, ha, _, hr, hs⟩ :=
    rawDelegateCallTraceFrom (initState σ σ₀ g A I) h rfl rfl rfl hdec hov
  exact ⟨evm', σ', z, out, aw', k', C', hc, he, ha, hr, hs⟩

-- LIBRARY CANDIDATE: source delegate calls have a result for any gas and substate witness.
theorem delegateCallExists (evm : EVM.State) (target : EVM.Address) (payload : ByteArray)
    (gas : UInt256) (AIn : Substate) :
    ∃ z evm' out, delegateCallViaEVM evm target payload (z, evm', out) := by
  by_cases hd : evm.executionEnv.depth = 1024
  · exact ⟨false, _, ByteArray.empty, delegateCallViaEVM.callNotMade rfl rfl hd⟩
  · let result := Θ evm.accountMap evm.σ₀ AIn evm.executionEnv.source
      evm.executionEnv.sender evm.executionEnv.codeOwner (toExecute evm.accountMap target)
      gas (UInt256.ofNat evm.executionEnv.gasPrice) ⟨0⟩ evm.executionEnv.weiValue payload
      (evm.executionEnv.depth + 1) evm.executionEnv.header evm.executionEnv.blobVersionedHashes
      evm.executionEnv.blocks evm.executionEnv.perm
    exact ⟨result.2.2.2.1, { evm with accountMap := result.1, substate := result.2.2.1 },
      result.2.2.2.2,
      delegateCallViaEVM.callMade (g' := result.2.1) ⟨gas, AIn, rfl⟩ rfl hd⟩

end Benchmarks.Safe
