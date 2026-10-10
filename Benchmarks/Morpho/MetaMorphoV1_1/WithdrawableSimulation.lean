import Benchmarks.Morpho.MetaMorphoV1_1.WithdrawableSource
import Benchmarks.Morpho.MetaMorphoV1_1.WithdrawableRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.TokenBalanceMemory

/-! The full withdrawable-assets helper, sharing the actual external token call. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem withdrawableSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr params sa ba supply ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (p : MarketParamsData) (hstack : R.length + 13 ≤ 1024)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hlo : 96 ≤ ptr.toNat) (hhi : ptr.toNat < 2 ^ 64)
    (hload : memLoad params mem = UInt256.ofNat p.loanToken.toNat)
    (hs : SourceState s0 I σ evm)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨19481⟩
      (params :: sa :: ba :: supply :: ret :: R) mem aw rdata σ k C) :
    (ExecFuncBody config (withdrawableFrame (immStore v) p sa ba supply ptr) evm
      allocatedWithdrawableFunction.body .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
    ∃ (evm' : State) (final : Frame) (value cursor : UInt256) (mem' out : ByteArray),
      SourceState s0 I evm'.accountMap evm' ∧
      accountStorageStateEq evm.accountMap evm'.accountMap ∧
      ExecFuncBody config (withdrawableFrame (immStore v) p sa ba supply ptr) evm
        allocatedWithdrawableFunction.body
        (.returned final evm' (some [uint256Value value, uint256Value cursor])) ∧
      memLoad ⟨64⟩ mem' = cursor ∧ 96 ≤ cursor.toNat ∧ cursor.toNat < 2 ^ 64 ∧
      cursor.toNat ≤ mem'.size ∧ MemoryPrefix mem mem' ptr.toNat ∧ ptr.toNat ≤ cursor.toNat ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret
        (value :: R) mem' aw' out evm'.accountMap k' C' := by
  by_cases hfit : ba.toNat ≤ sa.toNat
  swap
  · exact .inl ⟨withdrawableSubtractSourceReverts (immStore v) p sa ba supply ptr evm
      (Nat.lt_of_not_ge hfit),
      withdrawableSubtractReverts v (by simp only [List.length_cons]; omega)
        (Nat.lt_of_not_ge hfit) rd⟩
  let frame0 := withdrawableFrame (immStore v) p sa ba supply ptr
  let frame1 := withdrawableAvailableFrame frame0 sa ba
  have hsub := withdrawableSubtractSource (immStore v) p sa ba supply ptr evm hfit
  have hp : frame1.locals.get? "marketParams" = some p.value := by
    simp [frame1, frame0, withdrawableAvailableFrame, withdrawableFrame,
      Std.HashMap.getElem_insert]
  have ho : frame1.immutables.get? "MORPHO" = some (.address v.MORPHO) :=
    immStore_get_MORPHO v
  have hc : frame1.locals.get? cursorName = some (uint256Value ptr) := by
    simp [frame1, frame0, withdrawableAvailableFrame, withdrawableFrame, cursorName,
      Std.HashMap.getElem_insert]
  obtain ⟨aw1, k1, C1, h1⟩ := withdrawableSubtract v
    (by simp only [List.length_cons]; omega) hfit rd
  obtain ⟨gasArg, aw2, k2, C2, h2⟩ := tokenBalanceReachStaticcall v p.loanToken
    (by simp only [List.length_cons]; omega) hfree hhi hload h1
  obtain ⟨evm', ok, out, aw3, k3, C3, hcall, hs', hout, h3⟩ := tokenBalanceStaticcall v
    p.loanToken v.MORPHO (by simp only [List.length_cons]; omega) hs h2
  cases ok with
  | false =>
      exact .inl ⟨ExecFuncBody.execBlockRevert (hsub.run
        (ExecBlock.consRevert (tokenBalanceSourceCallReverts hp ho hcall))),
        tokenBalanceCallFailure v (by simp only [List.length_cons]; omega) hout h3⟩
  | true =>
      have hh : out.size < 2 ^ 255 := lt_trans (tokenBalanceReturnSize hcall) (by decide)
      rcases tokenBalanceReturnAllocation v (by simp only [List.length_cons]; omega) hout h3 with
        ⟨hbad, hrev⟩ | ⟨hl, halloc, aw4, k4, C4, h4⟩
      · refine .inl ⟨ExecFuncBody.execBlockRevert (hsub.run ?_), hrev⟩
        by_cases hl : 32 ≤ out.size
        · exact tokenBalanceSourceAllocationReverts rfl hp ho hc hcall hl hh
            (fun hf ↦ hbad ⟨hl, hf⟩) withdrawableTail
        · exact ExecBlock.consRevert (tokenBalanceSourceDecodeReverts hp ho hcall (by omega))
      · let balance := calldataWord out 0
        let available := UInt256.sub sa ba
        let value := minimumWord supply (minimumWord available balance)
        let frame2 := tokenBalanceReserveFrame frame1 ptr balance
        let cursor := nextCursor ptr ⟨32⟩
        let mem' := tokenBalanceReadMemory mem ptr v.MORPHO out
        have hsource : ExecBlock config frame1 evm withdrawableCallBody
            (.returned (withdrawableResultFrame frame2 available balance supply) evm'
              [uint256Value value, uint256Value cursor]) := by
          apply tokenBalanceSourcePrefix rfl hp ho hc hcall hl hh halloc
          apply withdrawableTailSource rfl
          · simp [tokenBalanceReserveFrame, tokenBalanceFrame,
              frame1, withdrawableAvailableFrame, cursorName, available,
              Std.HashMap.getElem_insert]
          · simp [tokenBalanceReserveFrame, tokenBalanceFrame, cursorName, balance,
              Std.HashMap.getElem_insert]
          · simp [tokenBalanceReserveFrame, tokenBalanceFrame, frame1, frame0,
              withdrawableAvailableFrame, withdrawableFrame, cursorName,
              Std.HashMap.getElem_insert]
          · simp [tokenBalanceReserveFrame, cursor]
        obtain ⟨aw5, k5, C5, h5⟩ := tokenBalanceReadWord v
          (by simp only [List.length_cons]; omega)
          (tokenBalanceReadMemory_load mem ptr v.MORPHO out hlo hhi hl hout) h4
        obtain ⟨aw6, k6, C6, h6⟩ := withdrawableMinimumReturn v (by omega) hret h5
        exact .inr ⟨evm', _, value, cursor, mem', out, hs',
          typedCallViaEVM_static_accountStorageStateEq hcall,
          ExecFuncBody.execBlockRet (hsub.run hsource), tokenBalanceReadMemory_free _ _ _ _,
          le_trans hlo halloc.2, halloc.1,
          tokenBalanceReadMemory_cursor_bound _ _ _ _ hl hout halloc,
          tokenBalanceReadMemory_prefix _ _ _ _ hl hout, halloc.2, aw6, k6, C6, h6⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
