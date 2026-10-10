import Benchmarks.Morpho.MetaMorphoV1_1.BorrowRateSetup
import Benchmarks.Morpho.MetaMorphoV1_1.BorrowRateReadMemory
import Benchmarks.Morpho.MetaMorphoV1_1.BorrowRateSource

/-! One actual rate-model call, through source/bytecode reverts or the decoded rate word. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

theorem borrowRateSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {mem market : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr params src elapsed : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (p : MarketParamsData) (hstack : R.length + 16 ≤ 1024)
    (hcontract : frame.contract = contract)
    (hp : frame.locals.get? "marketParams" = some p.value)
    (hm : frame.locals.get? "market" = some (marketValue market))
    (hcursor : frame.locals.get? cursorName = some (uint256Value ptr))
    (hfree : memLoad ⟨64⟩ mem = ptr) (hptr : ptr.toNat < 2 ^ 64)
    (hin : ptr.toNat ≤ mem.size) (hparamslo : 96 ≤ params.toNat) (hsrclo : 96 ≤ src.toNat)
    (hparams : params.toNat + 160 ≤ ptr.toNat) (hsrc : src.toNat + 192 ≤ ptr.toNat)
    (hparamsRead : MarketParamsLoads mem params p) (hc : MarketChecks market)
    (hmarket : ∀ off, off + 32 ≤ 192 →
      memLoad (src + UInt256.ofNat off) mem = calldataWord market off)
    (hs : SourceState s0 I σ evm)
    (rd : RD (deployedRuntime v) I g s0 ⟨17069⟩
      (params :: (src + UInt256.ofNat 128) :: elapsed :: src :: R) mem aw rdata σ k C) :
    (ExecBlock config frame evm marketAccrualBody .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
    ∃ (evm' : State) (out : ByteArray),
      typedCallViaEVM config evm p.irm "borrowRateView" 0 [p.value, marketValue market]
        (true, evm', out) false ∧
      SourceState s0 I evm'.accountMap evm' ∧ 32 ≤ out.size ∧ out.size < 2 ^ 255 ∧
      allocationFits ptr ⟨32⟩ ∧
      (∀ result, ExecBlock config (borrowRateReserveFrame frame ptr (calldataWord out 0)) evm'
        (marketAccrualBody.drop 2) result → ExecBlock config frame evm marketAccrualBody result) ∧
      memLoad ⟨64⟩ (borrowRateReadMemory mem ptr p market out) = nextCursor ptr ⟨32⟩ ∧
      (nextCursor ptr ⟨32⟩).toNat ≤ (borrowRateReadMemory mem ptr p market out).size ∧
      MemoryPrefix mem (borrowRateReadMemory mem ptr p market out) ptr.toNat ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨17239⟩
        (⟨17338⟩ :: elapsed :: (src + UInt256.ofNat 160) :: calldataWord out 0 ::
          (src + UInt256.ofNat 64) :: (src + UInt256.ofNat 32) :: src :: R)
        (borrowRateReadMemory mem ptr p market out) aw' out evm'.accountMap k' C' := by
  obtain ⟨gasArg, aw0, k0, C0, h0⟩ := borrowRateReachStaticcall v p (by omega)
    hfree hptr hin hparamslo hsrclo hparams hsrc hparamsRead hc hmarket rd
  obtain ⟨evm', ok, out, aw1, k1, C1, hcall, hs', hout, h1⟩ := borrowRateStaticcall v p
    (by simp only [List.length_cons]; omega) hc hs h0
  cases ok with
  | false =>
      exact .inl ⟨borrowRateSourceCallReverts hp hm hcall,
        borrowRateCallFailure v (by simp only [List.length_cons]; omega) hout h1⟩
  | true =>
      have hh : out.size < 2 ^ 255 := lt_trans (borrowRateReturnSize hc hcall) (by decide)
      rcases borrowRateReturnAllocation v (by simp only [List.length_cons]; omega) hout h1 with
        ⟨hbad, hrev⟩ | ⟨hl, hfit, aw2, k2, C2, h2⟩
      · refine .inl ⟨?_, hrev⟩
        by_cases hl : 32 ≤ out.size
        · exact borrowRateSourceAllocationReverts hcontract hp hm hcursor hcall hl hh
            (fun hf ↦ hbad ⟨hl, hf⟩)
        · exact borrowRateSourceDecodeReverts hp hm hcall (by omega)
      · refine .inr ⟨evm', out, hcall, hs', hl, hh, hfit,
          fun result htail ↦ borrowRateSourcePrefix hcontract hp hm hcursor hcall hl hh hfit htail,
          borrowRateReadMemory_free mem ptr p market out,
          borrowRateReadMemory_cursor_bound mem ptr p market out hl hout hfit,
          borrowRateReadMemory_prefix mem ptr p market out hl hout, ?_⟩
        exact borrowRateReadWord v (by simp only [List.length_cons]; omega)
          (borrowRateReadMemory_load mem ptr p market out (by omega) hptr hl hout) h2

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
