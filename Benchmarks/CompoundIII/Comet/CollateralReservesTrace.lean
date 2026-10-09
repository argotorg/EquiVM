import Benchmarks.CompoundIII.Comet.CollateralReservesInternal
import Benchmarks.CompoundIII.Comet.TransferInEvm
import Benchmarks.CompoundIII.Comet.MappingScratch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

inductive CollateralReservesTrace (asset : AccountAddress) (evm : EVM.State) :
    Option (EVM.State × UInt256) → Prop where
  | response {evm' z out}
      (hc : callViaEVM evm asset 0 (tokenBalancePayload evm.executionEnv.codeOwner)
        (z, evm', out) false) (hh : out.size < 2^255) :
      CollateralReservesTrace asset evm
        (if CollateralReservesValid evm' asset z out then
          some (evm', collateralReservesValue evm' asset out) else none)

theorem collateralReservesTrace_call {asset evm result}
    (ht : CollateralReservesTrace asset evm result) (frame : Frame) (expr : Expr) (ret : Ident)
    (hf : frame.contract = contract)
    (he : evalExpr? config frame evm expr = .ok (.address asset)) :
    ExecStmt config frame evm (.internalCall "getCollateralReserves_body" [expr] ret)
      (wordCallResult frame ret result) := by
  cases ht with
  | @response evm' z out hc hh =>
    by_cases hv : CollateralReservesValid evm' asset z out
    · rw [if_pos hv, wordCallResult]
      obtain rfl := hv.1
      exact collateralReserves_call_ok frame evm evm' asset expr ret out hf he hc hh hv
    · rw [if_neg hv, wordCallResult]
      exact collateralReserves_call_revert frame evm evm' asset expr ret out z hf he hc hh hv

theorem cometCollateralReservesTrace {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {ptr ret : UInt256} {R : List UInt256}
    {asset : AccountAddress} {evm : EVM.State}
    (hstack : R.length + 11 ≤ 1024) (hfree : memLoad ⟨64⟩ mem = ptr) (hlo : 96 ≤ ptr.toNat)
    (hptr : ptr.toNat + 36 < 2^64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨9561⟩ (EVM.word asset.val :: ret :: R)
      mem aw rdata σ k C) :
    ∃ result, CollateralReservesTrace asset evm result ∧
      TransferInRun v ee g s0 ret (ptr + ⟨32⟩) R result := by
  obtain ⟨evm', σ', z, out, hc, hs', hh, hr⟩ :=
    cometCollateralReservesInternal hstack hfree hlo hptr hret hs h
  have ht := CollateralReservesTrace.response hc (lt_trans hh (by decide))
  by_cases hv : CollateralReservesValid evm' asset z out
  · rw [if_pos hv] at hr ht
    obtain ⟨aw', k', C', hr⟩ := hr
    have hb : ptr.toNat + 36 < UInt256.size := by change ptr.toNat + 36 < 2^256; omega
    have hhi : out.size < UInt256.size := lt_trans hh (by change 2^138 < 2^256; decide)
    have hm : 96 ≤ (tokenBalanceReturnMemory mem ptr ee.codeOwner out).size := by
      rw [tokenBalanceReturnMemory_size hlo hb hhi]
      omega
    refine ⟨_, ht, σ', _, aw', out, k', C', hs', ?_, ?_, hr⟩
    · rw [collateralReservesMemory, twoWordHashMem_load_ge (ptr := ⟨64⟩) _ _ (by decide) hm]
      exact memLoad_writeWord_self _ ⟨64⟩ _
    · have hp : (ptr + (⟨32⟩ : UInt256)).toNat = ptr.toNat + 32 :=
        uadd_word_ofNat_toNat ptr 32 (by change ptr.toNat + 32 < 2^256; omega)
      rw [collateralReservesMemory, twoWordHashMem_size_of_ge_64 _ _ (by omega),
        tokenBalanceReturnMemory_size hlo hb hhi, hp]
      omega
  · rw [if_neg hv] at hr ht
    exact ⟨none, ht, hr⟩

end Benchmarks.CompoundIII.Comet
