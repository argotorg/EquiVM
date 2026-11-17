import Benchmarks.EAS.EAS.Common
import Reasoning.ExternalCall
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- GENERALIZES Reasoning.ExternalCall.callBridge to the STATICCALL opcode and permission bit.
theorem staticcallBridge {code : ByteArray} {I : ExecutionEnv} {g : Sat256} {s0 evm : EVM.State}
    {pc : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {gasArg target inOffset inSize outOffset outSize : UInt256} {calldata : ByteArray}
    (rd : RD code I g s0 pc (gasArg::target::inOffset::inSize::outOffset::outSize::R) mem aw rdata σ k C)
    (hs : SourceState s0 I σ evm) (hdec : decode code pc = some (.STATICCALL, none))
    (hcd : mem.readWithPadding inOffset.toNat inSize.toNat = calldata)
    (hsmall : calldata.size ≤ Ethereum.EVM.maxReturnDataSizeByGas) (hstack : R.length+1 ≤ 1024) :
    ∃ (evm' : EVM.State) (σ' : AccountMap) (success : Bool) (out : ByteArray) (k' C' : Nat),
      callViaEVM evm (AccountAddress.ofUInt256 target) 0 calldata (success,evm',out) false ∧
      SourceState s0 I σ' evm' ∧
      RD code I g s0 (pc+⟨1⟩) ((if success then ⟨1⟩ else ⟨0⟩)::R)
        (callOutputMem mem out outOffset outSize) (callActiveWords aw inOffset inSize outOffset outSize) out σ' k' C' ∧
      out.size < 2^138 := by
  by_cases hd : I.depth = 1024
  · obtain ⟨k',C',rd'⟩ := RD.solcStaticcallDepthLimit rd hdec hd hstack
    let evm' := {evm with substate := (evm.addAccessedAccount (AccountAddress.ofUInt256 target)).substate}
    refine ⟨evm',σ,false,ByteArray.empty,k',C',?_,⟨hs.world,hs.env,hs.accounts⟩,rd',by decide⟩
    apply callViaEVM.callNotMade rfl rfl
    intro hn
    exact hn.2 (by rw [hs.env]; exact hd)
  · have hdlt : I.depth.val < 1024 := by
      have hi := I.depth.isLt
      have hn : I.depth.val ≠ 1024 := fun h => hd (Fin.ext h)
      omega
    obtain ⟨σ',success,out,AIn,callGas,k',C',⟨gasLeft,A',hΘ⟩,rd',_⟩ := RD.solcStaticcall rd hdec hdlt hstack
    rw [hcd] at hΘ
    have hout : out.size < 2^138 := Theta_returnData_size_lt_2pow138_of_eq I.fork _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _  _ hΘ hsmall
    refine ⟨{evm with accountMap := σ', substate := A'},σ',success,out,k',C',?_,⟨hs.world,hs.env,rfl⟩,rd',hout⟩
    apply callViaEVM.callMade (valueWord := ⟨0⟩) (g' := gasLeft) (A' := A') wordOfInt_zero.symm ?_ rfl (Fin.zero_le _) ?_
    · refine ⟨callGas,AIn,?_⟩
      simpa only [hs.env, ← hs.accounts, hs.world, accountAddress_roundtrip, Bool.false_and] using hΘ
    · rw [hs.env]
      exact hd

-- GENERALIZES Reasoning.ExternalCall.lowLevelCallSource over the callee permission bit.
theorem lowLevelCallSource_perm {cfg : Config} {frame : Frame} {evm evm' : EVM.State}
    {receiver eth cdata : Expr} {success data : Ident} {target : AccountAddress} {value : Int}
    {calldata out : ByteArray} {z perm : Bool}
    (hr : evalExpr? cfg frame evm receiver = .ok (.address target))
    (hv : evalExpr? cfg frame evm eth = .ok (.int value))
    (hd : evalExpr? cfg frame evm cdata = .ok (.bytes calldata))
    (hc : callViaEVM evm target value calldata (z,evm',out) perm)
    (hperm : EVM.wordOfInt value = ⟨0⟩ ∨ evm.executionEnv.perm = true) :
    ExecStmt cfg frame evm (.lowLevelCall receiver eth cdata success data perm)
      (.ok {frame with locals := (frame.locals.insert success (.bool z)).insert data (.bytes out)} evm') := by
  have ht : EVM.address target.val = target := by
    apply Fin.ext
    change target.val % AccountAddress.size = target.val
    exact Nat.mod_eq_of_lt target.isLt
  rw [← ht] at hc
  cases z with
  | false => exact ExecStmt.lowLevelCallFailure (hperm := hperm) hr hv hd hc
  | true => exact ExecStmt.lowLevelCallSuccess (hperm := hperm) hr hv hd hc

end Benchmarks.EAS.EAS
