import Benchmarks.CompoundIII.Comet.ReservesInternal

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

def reservesSnapshot (evm : EVM.State) (slot : UInt256) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot

abbrev ReservesIndicesValid (v : CometWithExtendedAssetListImmutables) (evm : EVM.State) :=
  CurrentIndicesValid v (reservesSnapshot evm ⟨0⟩) (reservesSnapshot evm ⟨1⟩)
    (timestampWord evm.executionEnv)

abbrev ReservesResponseValid (v : CometWithExtendedAssetListImmutables) (evm : EVM.State)
    (z : Bool) (out : ByteArray) :=
  ReservesReplyValid v (reservesSnapshot evm ⟨0⟩) (reservesSnapshot evm ⟨1⟩)
    (timestampWord evm.executionEnv) z out

abbrev reservesResponseWord (v : CometWithExtendedAssetListImmutables) (evm : EVM.State)
    (out : ByteArray) :=
  reservesWord v (reservesSnapshot evm ⟨0⟩) (reservesSnapshot evm ⟨1⟩)
    (timestampWord evm.executionEnv) (calldataWord out 0)

inductive ReservesTrace (v : CometWithExtendedAssetListImmutables) (evm : EVM.State) :
    Option (EVM.State × UInt256) → Prop where
  | indicesFailed (hv : ¬ ReservesIndicesValid v evm) : ReservesTrace v evm none
  | response {evm' : EVM.State} {z : Bool} {out : ByteArray}
      (hi : ReservesIndicesValid v evm)
      (hc : callViaEVM evm v.baseToken 0 (tokenBalancePayload evm.executionEnv.codeOwner)
        (z, evm', out) false) (hh : out.size < 2^255) :
      ReservesTrace v evm (if ReservesResponseValid v evm z out then
        some (evm', reservesResponseWord v evm out) else none)

def reservesCallOutcome (frame : Frame) (ret : Ident)
    (result : Option (EVM.State × UInt256)) : ExecResult :=
  match result with
  | none => .reverted
  | some (evm', value) =>
    .ok { frame with locals := frame.locals.insert ret (.int (signedWord value)) } evm'

theorem reservesTrace_call {v : CometWithExtendedAssetListImmutables}
    {evm : EVM.State} {result : Option (EVM.State × UInt256)}
    (ht : ReservesTrace v evm result) (frame : Frame) (ret : Ident)
    (hf : frame.contract = contract) (hi : frame.immutables = immStore v) :
    ExecStmt config frame evm (.internalCall "getReserves_body" [] ret)
      (reservesCallOutcome frame ret result) := by
  cases ht with
  | indicesFailed hv => exact reserves_call_early_revert v frame evm ret hf hi hv
  | @response evm' z out hv hc hh =>
    have hb := reserves_call_result v frame evm evm' ret z out hf hi hv hc hh
    dsimp only at hb
    by_cases hr : ReservesResponseValid v evm z out
    · rw [if_pos hr]
      simp only [reservesCallOutcome]
      dsimp only [ReservesResponseValid, reservesSnapshot] at hr
      rw [if_pos hr] at hb
      rw [reservesResponseWord, reservesWord_signed hv hr.2.2]
      exact hb
    · rw [if_neg hr]
      simp only [reservesCallOutcome]
      dsimp only [ReservesResponseValid, reservesSnapshot] at hr
      rw [if_neg hr] at hb
      exact hb

def ReservesRun (v : CometWithExtendedAssetListImmutables) (ee : ExecutionEnv)
    (g : Sat256) (s0 : State) (ret free : UInt256) (R : List UInt256)
    (result : Option (EVM.State × UInt256)) : Prop :=
  match result with
  | none => RDrev (deployedRuntime v) g s0
  | some (evm', value) => ∃ σ' mem aw out k C, SourceState s0 ee σ' evm' ∧
      memLoad ⟨64⟩ mem = free + ⟨32⟩ ∧
      RD (deployedRuntime v) ee g s0 ret (value :: R) mem aw out σ' k C

theorem cometReservesTrace {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {ptr ret : UInt256} {R : List UInt256} {evm : EVM.State}
    (hstack : R.length + 35 ≤ 1024) (hfree : memLoad ⟨64⟩ mem = ptr) (hlo : 96 ≤ ptr.toNat)
    (hptr : ptr.toNat + 36 < 2^64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨9825⟩ (ret :: R) mem aw rdata σ k C) :
    ∃ result, ReservesTrace v evm result ∧ ReservesRun v ee g s0 ret ptr R result := by
  have hsnap (slot : UInt256) : reservesSnapshot evm slot = solcSlotWordAt slot σ ee :=
    hs.storageRead slot
  have hr := cometReservesInternal (v := v) hstack hfree hlo hptr hret hs h
  dsimp only at hr
  by_cases hi : ReservesIndicesValid v evm
  · have hi' : CurrentIndicesValid v (solcSlotWordAt ⟨0⟩ σ ee) (solcSlotWordAt ⟨1⟩ σ ee)
        (timestampWord ee) := by simpa only [ReservesIndicesValid, hsnap, hs.env] using hi
    rw [if_pos hi'] at hr
    obtain ⟨evm', σ', z, out, hc, hs', hh, hr⟩ := hr
    have ht := ReservesTrace.response hi hc (lt_trans hh (by decide))
    by_cases hv : ReservesResponseValid v evm z out
    · rw [if_pos hv] at ht
      have hv' : ReservesReplyValid v (solcSlotWordAt ⟨0⟩ σ ee) (solcSlotWordAt ⟨1⟩ σ ee)
          (timestampWord ee) z out := by
        simpa only [ReservesResponseValid, hsnap, hs.env] using hv
      rw [if_pos hv'] at hr
      obtain ⟨aw', k', C', hr⟩ := hr
      refine ⟨_, ht, σ', tokenBalanceReturnMemory mem ptr ee.codeOwner out,
        aw', out, k', C', hs', ?_, ?_⟩
      · apply loadedWord_of_read
        · rw [tokenBalanceReturnMemory, writeWord_sparse_size]
          change 64 + 32 ≤ _
          omega
        · exact writeWord_sparse_read_back _ _ _
      · simpa only [reservesResponseWord, hsnap, hs.env] using hr
    · rw [if_neg hv] at ht
      have hv' : ¬ ReservesReplyValid v (solcSlotWordAt ⟨0⟩ σ ee) (solcSlotWordAt ⟨1⟩ σ ee)
          (timestampWord ee) z out := by
        simpa only [ReservesResponseValid, hsnap, hs.env] using hv
      rw [if_neg hv'] at hr
      exact ⟨none, ht, hr⟩
  · have hi' : ¬ CurrentIndicesValid v (solcSlotWordAt ⟨0⟩ σ ee) (solcSlotWordAt ⟨1⟩ σ ee)
        (timestampWord ee) := by simpa only [ReservesIndicesValid, hsnap, hs.env] using hi
    rw [if_neg hi'] at hr
    exact ⟨none, .indicesFailed hi, hr⟩

end Benchmarks.CompoundIII.Comet
