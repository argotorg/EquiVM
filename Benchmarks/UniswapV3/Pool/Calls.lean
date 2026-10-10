import Benchmarks.UniswapV3.Pool.Common
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables

namespace Benchmarks.UniswapV3.Pool

set_option maxRecDepth 10000

-- GENERALIZES Reasoning.ExternalCall.lowLevelCallSource: allow STATICCALL permission.
theorem lowLevelCallWithPermSource {cfg : Config} {frame : Frame} {evm evm' : EVM.State}
    {receiver eth cdata : Expr} {target : AccountAddress} {value : Int} {calldata out : ByteArray}
    {success data : Ident} {z perm : Bool}
    (hr : evalExpr? cfg frame evm receiver = .ok (.address target))
    (hv : evalExpr? cfg frame evm eth = .ok (.int value))
    (hd : evalExpr? cfg frame evm cdata = .ok (.bytes calldata))
    (hc : callViaEVM evm target value calldata (z, evm', out) perm) :
    ExecStmt cfg frame evm (.lowLevelCall receiver eth cdata success data perm)
      (.ok { frame with locals := (frame.locals.insert success (.bool z)).insert data (.bytes out) }
        evm') := by
  have ht : EVM.address target.val = target := by
    apply Fin.ext
    change target.val % AccountAddress.size = target.val
    exact Nat.mod_eq_of_lt target.isLt
  rw [← ht] at hc
  cases z with
  | false => exact ExecStmt.lowLevelCallFailure hr hv hd hc
  | true => exact ExecStmt.lowLevelCallSuccess hr hv hd hc

-- LIBRARY CANDIDATE: couple a raw STATICCALL with its source relation, including depth failure.
theorem RD.staticcallSource {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : EVM.State} {pc : UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {gasArg target inOffset inSize outOffset outSize : UInt256} {R : List UInt256}
    (rd : RD code ee g s0 pc
      (gasArg :: target :: inOffset :: inSize :: outOffset :: outSize :: R) mem aw rdata σ k C)
    (hdec : decode code pc = some (.STATICCALL, .none))
    (hov : R.length + 1 ≤ 1024)
    (hacc : evm.accountMap = σ) (hσ₀ : evm.σ₀ = s0.σ₀) (henv : evm.executionEnv = ee) :
    ∃ (z : Bool) (out : ByteArray) (σ' : AccountMap) (A' : Substate) (k' C' : Nat),
      callViaEVM evm (AccountAddress.ofUInt256 target) 0
        (mem.readWithPadding inOffset.toNat inSize.toNat)
        (z, { evm with accountMap := σ', substate := A' }, out) false ∧
      RD code ee g s0 (pc + ⟨1⟩) ((if z then ⟨1⟩ else ⟨0⟩) :: R)
        (callOutputMem mem out outOffset outSize)
        (callActiveWords aw inOffset inSize outOffset outSize) out σ' k' C' ∧
      out.size < UInt256.size := by
  by_cases hdepth : ee.depth.val < 1024
  · obtain ⟨σ', z, out, A_in, gas, k', C', ⟨g', A', hΘ⟩, rd', hsize⟩ :=
      rd.solcStaticcall hdec hdepth hov
    refine ⟨z, out, σ', A', k', C', ?_, rd', hsize⟩
    apply callViaEVM.callMade (perm := false) (g' := g') wordOfInt_zero.symm
      (A' := A') (σ' := σ')
    · refine ⟨gas, A_in, ?_⟩
      simpa only [hacc, hσ₀, henv, Bool.false_and, accountAddress_roundtrip] using hΘ
    · rfl
    · exact Fin.zero_le _
    · rw [henv]
      exact depth_ne_1024_of_lt hdepth
  · have hdepth' : ee.depth = 1024 := by
      apply Fin.ext
      have hbound := ee.depth.isLt
      change ee.depth.val = 1024
      omega
    obtain ⟨k', C', rd'⟩ := rd.solcStaticcallDepthLimit hdec hdepth' hov
    refine ⟨false, .empty, σ, (evm.addAccessedAccount (AccountAddress.ofUInt256 target)).substate,
      k', C', ?_, rd', by decide⟩
    apply callViaEVM.callNotMade (perm := false) rfl
    · rw [hacc]
    · rintro ⟨_, hn⟩
      exact hn (henv ▸ hdepth')

end Benchmarks.UniswapV3.Pool
