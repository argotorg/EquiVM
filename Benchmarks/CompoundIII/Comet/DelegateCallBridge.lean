import Benchmarks.CompoundIII.Comet.DelegateCallReach

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

theorem delegateCallBridge {code I g s0 pc R mem aw rdata σ k C evm}
    {gasArg target inOffset inSize outOffset outSize : UInt256} {calldata : ByteArray}
    (h : RD code I g s0 pc
      (gasArg :: target :: inOffset :: inSize :: outOffset :: outSize :: R)
      mem aw rdata σ k C)
    (hs : SourceState s0 I σ evm)
    (hdec : decode code pc = some (.DELEGATECALL, .none))
    (hcd : mem.readWithPadding inOffset.toNat inSize.toNat = calldata)
    (hov : R.length + 1 ≤ 1024) :
    ∃ (evm' : State) (σ' : AccountMap) (z : Bool) (out : ByteArray) (k' C' : Nat),
      delegateCallViaEVM evm (AccountAddress.ofUInt256 target) calldata (z, evm', out) ∧
      SourceState s0 I σ' evm' ∧
      RD code I g s0 (pc + ⟨1⟩) ((if z then ⟨1⟩ else ⟨0⟩) :: R)
        (out.write 0 mem outOffset.toNat (min outSize (UInt256.ofNat out.size)).toNat)
        (UInt256.ofNat (MachineState.M (MachineState.M aw.toNat inOffset.toNat inSize.toNat)
          outOffset.toNat outSize.toNat)) out σ' k' C' ∧ out.size < UInt256.size := by
  by_cases hd : I.depth = 1024
  · obtain ⟨k', C', rd⟩ := h.cometDelegatecallDepthLimit hdec hd hov
    let evm' := { evm with substate := (evm.addAccessedAccount
      (AccountAddress.ofUInt256 target)).substate }
    have hc : delegateCallViaEVM evm (AccountAddress.ofUInt256 target) calldata
        (false, evm', ByteArray.empty) :=
      delegateCallViaEVM.callNotMade rfl rfl (hs.env ▸ hd)
    exact ⟨evm', σ, false, ByteArray.empty, k', C', hc,
      ⟨hs.world, hs.env, hs.accounts⟩, rd, by decide⟩
  · have hdepth : I.depth.val < 1024 := by
      have hb := I.depth.isLt
      have hn : I.depth.val ≠ 1024 := by intro hh; exact hd (Fin.ext hh)
      omega
    obtain ⟨σ', z, out, Ain, gas, k', C', ⟨gasLeft, As, hθ⟩, rd, ho⟩ :=
      h.cometDelegatecall hdec hdepth hov
    rw [hcd] at hθ
    let evm' := { evm with accountMap := σ', substate := As }
    have hc : delegateCallViaEVM evm (AccountAddress.ofUInt256 target) calldata
        (z, evm', out) := by
      apply delegateCallViaEVM.callMade (g' := gasLeft) (A' := As) ?_ rfl ?_
      · refine ⟨gas, Ain, ?_⟩
        rw [hs.env, hs.world, ← hs.accounts]
        exact hθ
      · rw [hs.env]; exact hd
    exact ⟨evm', σ', z, out, k', C', hc, ⟨hs.world, hs.env, rfl⟩, rd, ho⟩

theorem delegateCallSource {cfg : Config} {frame : Frame} {evm evm' : State}
    {receiver cdata : Expr} {target : AccountAddress} {calldata out : ByteArray}
    {success data : Ident} {z : Bool}
    (hr : evalExpr? cfg frame evm receiver = .ok (.address target))
    (hd : evalExpr? cfg frame evm cdata = .ok (.bytes calldata))
    (hc : delegateCallViaEVM evm target calldata (z, evm', out)) :
    ExecStmt cfg frame evm (.delegateCall receiver cdata success data)
      (.ok { frame with locals := (frame.locals.insert success (.bool z)).insert data (.bytes out) }
        evm') := by
  have ht : EVM.address target.val = target := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt target.isLt
  rw [← ht] at hc
  cases z with
  | false => exact ExecStmt.delegateCallFailure hr hd hc
  | true => exact ExecStmt.delegateCallSuccess hr hd hc

end Benchmarks.CompoundIII.Comet
