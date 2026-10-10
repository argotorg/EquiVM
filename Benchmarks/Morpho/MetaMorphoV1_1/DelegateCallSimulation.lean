import Benchmarks.Morpho.MetaMorphoV1_1.DelegateCallReach

/-! The source and runtime delegate calls use the same invocation of Θ. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

-- LIBRARY CANDIDATE: a raw DELEGATECALL bridge with no contract-specific hypotheses.
theorem delegateCallSimulation {code : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {mem rdata data : ByteArray} {aw : UInt256} {σ : AccountMap}
    {k C : Nat} {pc gasArg target input inputSize output outputSize : UInt256}
    {R : List UInt256} {address : AccountAddress}
    (hstack : R.length + 1 ≤ 1024) (hdec : decode code pc = some (.DELEGATECALL, none))
    (hs : SourceState s0 I σ evm) (htarget : address = AccountAddress.ofUInt256 target)
    (hdata : mem.readWithPadding input.toNat inputSize.toNat = data)
    (rd : RD code I g s0 pc
      (gasArg :: target :: input :: inputSize :: output :: outputSize :: R)
      mem aw rdata σ k C) :
    ∃ (evm' : State) (ok : Bool) (out : ByteArray) (aw' : UInt256) (k' C' : Nat),
      delegateCallViaEVM evm address data (ok, evm', out) ∧
      SourceState s0 I evm'.accountMap evm' ∧ out.size < UInt256.size ∧
      RD code I g s0 (pc + ⟨1⟩) ((if ok then ⟨1⟩ else ⟨0⟩) :: R)
        (callOutputMem mem out output outputSize) aw' out evm'.accountMap k' C' := by
  obtain ⟨A, callGas, k', C', hrd⟩ := delegateCallReach rd hdec hstack
  by_cases hdepth : I.depth < 1024
  · simp only [delegateCallResult, hdepth, if_pos, hdata, ← htarget] at hrd
    let result := Θ σ s0.σ₀ A I.source I.sender I.codeOwner (toExecute σ address) callGas
      (UInt256.ofNat I.gasPrice) ⟨0⟩ I.weiValue data (I.depth + 1) I.header
      I.blobVersionedHashes I.blocks I.perm
    let evm' := { evm with accountMap := result.1, substate := result.2.2.1 }
    have hcall : delegateCallViaEVM evm address data (result.2.2.2.1, evm', result.2.2.2.2) := by
      apply delegateCallViaEVM.callMade (g' := result.2.1) (A' := result.2.2.1)
        (σ' := result.1) ?_ rfl (by rw [hs.env]; exact ne_of_lt hdepth)
      refine ⟨callGas, A, ?_⟩
      simp only [result, hs.env, hs.world, ← hs.accounts]
    have hout : result.2.2.2.2.size < UInt256.size := by
      apply theta_projection_output_size_lt_uint256
      rw [← hdata]
      exact readWithPadding_size_lt_uint256_of_word _ input inputSize
    exact ⟨evm', result.2.2.2.1, result.2.2.2.2, _, k', C', hcall,
      ⟨hs.world, hs.env, rfl⟩, hout, hrd⟩
  · have hd : I.depth = 1024 := by
      apply Fin.ext
      have hb := I.depth.isLt
      have hn : ¬ I.depth.val < 1024 := hdepth
      change I.depth.val = 1024
      omega
    simp only [delegateCallResult, hdepth, if_false, Bool.false_eq_true] at hrd
    have hcall : delegateCallViaEVM evm address data
        (false, { evm with substate := (evm.addAccessedAccount address).substate },
          ByteArray.empty) :=
      delegateCallViaEVM.callNotMade rfl rfl (by rw [hs.env]; exact hd)
    exact ⟨_, false, ByteArray.empty, _, k', C', hcall, ⟨hs.world, hs.env, rfl⟩,
      by decide, by simpa only [hs.accounts] using hrd⟩

-- LIBRARY CANDIDATE: a result-uniform source rule for delegate calls.
theorem delegateCallSource {cfg : Config} {frame : Frame} {evm evm' : State}
    {target : AccountAddress} {receiver cdata : Expr} {data out : ByteArray}
    {ok : Bool} {okVar dataVar : Ident}
    (htarget : evalExpr? cfg frame evm receiver = .ok (.address target))
    (hdata : evalExpr? cfg frame evm cdata = .ok (.bytes data))
    (hcall : delegateCallViaEVM evm target data (ok, evm', out)) :
    ExecStmt cfg frame evm (.delegateCall receiver cdata okVar dataVar)
      (.ok { frame with
        locals := (frame.locals.insert okVar (.bool ok)).insert dataVar (.bytes out) } evm') := by
  rw [← address_of_val target] at hcall
  cases ok with
  | false => exact ExecStmt.delegateCallFailure htarget hdata hcall
  | true => exact ExecStmt.delegateCallSuccess htarget hdata hcall

end Benchmarks.Morpho.MetaMorphoV1_1
