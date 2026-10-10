import Benchmarks.Morpho.MetaMorphoV1_1.MarketReadSimulation
import Benchmarks.Morpho.MetaMorphoV1_1.MarketAccrualSimulation
import Benchmarks.Morpho.MetaMorphoV1_1.WordWindow

/-! The complete allocated market-balance helper, with actual external-call outcomes. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

theorem marketBalancesSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr params morpho ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (p : MarketParamsData) (hstack : R.length + 21 ≤ 1024)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hlo : 96 ≤ ptr.toNat) (hptr : ptr.toNat < 2 ^ 64)
    (hmem : ptr.toNat ≤ mem.size) (hparamslo : 96 ≤ params.toNat)
    (hparams : params.toNat + 160 ≤ ptr.toNat)
    (hbytes : mem.readWithPadding params.toNat 160 = p.bytes)
    (hloads : MarketParamsLoads mem params p) (hs : SourceState s0 I σ evm)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨16911⟩ (morpho :: params :: ret :: R)
      mem aw rdata σ k C) :
    (ExecFuncBody config
        (allocatedMarketBalancesFrame (immStore v) (AccountAddress.ofNat morpho.toNat) p ptr)
        evm allocatedMarketBalancesFunction.body .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
    (∃ (market : ByteArray) (evm' : State) (result : BalanceSnapshot market mem ptr.toNat)
        (out : ByteArray),
      SourceState s0 I evm'.accountMap evm' ∧
      accountStorageStateEq evm.accountMap evm'.accountMap ∧
      ExecFuncBody config
        (allocatedMarketBalancesFrame (immStore v) (AccountAddress.ofNat morpho.toNat) p ptr)
        evm allocatedMarketBalancesFunction.body
        (.returned result.frame evm'
          [marketUpdatedBalancesValue market result.supplyAssets result.supplyShares
            result.borrowAssets, uint256Value result.cursor]) ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret
        (calldataWord market 96 :: result.borrowAssets :: result.supplyShares ::
          result.supplyAssets :: R) result.memory aw' out evm'.accountMap k' C') := by
  rcases marketReadSimulation v p (by simp only [List.length_cons]; omega)
      hfree hlo hptr hbytes hs rd with
    ⟨hbad, hrev⟩ | ⟨evm1, market, aw1, k1, C1, hcall, hs1, hc, hbound, halloc,
      hfree1, hmem1, hfields, hprefix, h1⟩
  · exact .inl ⟨hbad, hrev⟩
  have hdecode : config.externalABI.decode? "market" market = some [marketValue market] := by
    rw [marketDecode hbound, if_pos hc]
  have hfit := (allocationFits_aligned ptr ⟨384⟩ (by decide +kernel)).mp halloc
  have hsrc : (nextCursor ptr ⟨192⟩).toNat = ptr.toNat + 192 :=
    uadd_word_ofNat_toNat ptr 192 (by change _ < 2 ^ 256; omega)
  have hcur : (nextCursor ptr ⟨384⟩).toNat = ptr.toNat + 384 :=
    uadd_word_ofNat_toNat ptr 384 (by change _ < 2 ^ 256; omega)
  let mem1 := marketReadMemory mem ptr p.id market
  let src := nextCursor ptr ⟨192⟩
  have hspan : src.toNat + 192 ≤ mem1.size := by
    change (nextCursor ptr ⟨384⟩).toNat ≤ mem1.size at hmem1
    dsimp only [src]
    rw [hcur] at hmem1
    rw [hsrc]
    omega
  have hsrcfit : src.toNat + 192 < UInt256.size := by
    dsimp only [src]
    rw [hsrc]
    change _ < 2 ^ 256
    omega
  have hread : ∀ off, off + 32 ≤ 192 →
      memLoad (src + UInt256.ofNat off) mem1 = calldataWord market off :=
    wordWindowLoad_of_read (mem := mem1) (out := market) (src := src) (len := 192)
      hc.1 hspan hsrcfit (wordWindowRead_of_fields (count := 6) hc.1 hspan hsrcfit hfields)
  have hloads1 : MarketParamsLoads mem1 params p := hloads.prefix hprefix hparamslo
    (by omega) hparams (by change _ < 2 ^ 256; omega)
  let frame1 := allocatedMarketBalancesReserveFrame (immStore v)
    (AccountAddress.ofNat morpho.toNat) p ptr market
  have hm1 : frame1.locals.get? "market" = some (marketValue market) :=
    allocatedMarketBalancesReserveFrame_market _ _ _ _ _
  have hp1 : frame1.locals.get? "marketParams" = some p.value :=
    allocatedMarketBalancesReserveFrame_params _ _ _ _ _
  rcases marketElapsedRoutine v (by simp only [List.length_cons]; omega) hc.2.2.2.2.2.1
      (hread 128 (by decide)) h1 with ⟨hbad, hrev⟩ | ⟨hle, aw2, k2, C2, h2⟩
  · exact .inl ⟨allocatedMarketBalancesBodyTimeUnderflow hcall hdecode halloc
      (by rw [hs1.env]; exact hbad), hrev⟩
  have hleSource : (calldataWord market 128).toNat ≤
      (UInt256.ofNat evm1.executionEnv.header.timestamp).toNat := by
    rw [hs1.env]
    exact hle
  let elapsed := marketBalancesElapsed evm1 market
  have he : UInt256.sub (UInt256.ofNat I.header.timestamp) (calldataWord market 128) =
      elapsed := by dsimp only [elapsed, marketBalancesElapsed]; rw [hs1.env]
  rw [he] at h2
  let frame2 := marketBalancesElapsedFrame frame1 elapsed
  have hm2 : frame2.locals.get? "market" = some (marketValue market) := by
    rw [show frame2 = marketBalancesElapsedFrame frame1 elapsed from rfl,
      marketBalancesElapsedFrame, store_get_ne _ _ (by decide)]
    exact hm1
  have hp2 : frame2.locals.get? "marketParams" = some p.value := by
    rw [show frame2 = marketBalancesElapsedFrame frame1 elapsed from rfl,
      marketBalancesElapsedFrame, store_get_ne _ _ (by decide)]
    exact hp1
  have hcursor2 : frame2.locals.get? cursorName = some (uint256Value (nextCursor ptr ⟨384⟩)) := by
    rw [show frame2 = marketBalancesElapsedFrame frame1 elapsed from rfl,
      marketBalancesElapsedFrame, store_get_ne _ _ (by decide)]
    exact store_get_self _ _ _
  have helapsed : frame2.locals.get? "elapsed" = some (uint256Value elapsed) := store_get_self _ _ _
  obtain ⟨aw3, k3, C3, h3⟩ := marketAccrualBranch v p
    (by simp only [List.length_cons]; omega) hc.2.2.2.1 (hread 64 (by decide)) hloads1.2.2.2.1 h2
  by_cases haccrue : marketAccrues p elapsed market
  · rw [if_pos haccrue] at h3
    rcases marketAccrualSimulation (frame := frame2) v p hstack rfl hp2 hm2 hcursor2 helapsed
        hfree1 (by rw [hcur]; exact hfit) hmem1 hparamslo (by dsimp only [src]; rw [hsrc]; omega)
        (by rw [hcur]; omega) (by dsimp only [src]; rw [hsrc, hcur]) hloads1 hc hread
        hs1 hret h3 with ⟨hbad, hrev⟩ | ⟨evm2, result, out, hs2, hstore2, hdone, hrd⟩
    · refine .inl ⟨ExecFuncBody.execBlockRevert ?_, hrev⟩
      apply allocatedMarketBalancesAllocationPrefix hcall hdecode halloc
      apply (marketBalancesElapsedPrefix hm1 hleSource).run
      exact ExecBlock.consRevert (ExecStmt.iteTrue
        (by rw [marketAccrualSource hm2 hp2 helapsed]; simp only [haccrue, decide_true]) hbad)
    · let final := result.rebase hprefix (by dsimp only [src]; rw [hsrc]; omega)
      refine .inr ⟨market, evm2, final, out, hs2,
        accountStorageStateEq_trans (typedCallViaEVM_static_accountStorageStateEq hcall) hstore2,
        ExecFuncBody.execBlockRet ?_, hrd⟩
      apply allocatedMarketBalancesAllocationPrefix hcall hdecode halloc
      apply (marketBalancesElapsedPrefix hm1 hleSource).run
      apply ExecBlock.consNormal (ExecStmt.iteTrue
        (by rw [marketAccrualSource hm2 hp2 helapsed]; simp only [haccrue, decide_true]) hdone)
      exact marketUpdatedReturn result.marketLocal result.cursorLocal
  · rw [if_neg haccrue] at h3
    obtain ⟨aw4, k4, C4, h4⟩ := marketBalancesReturnRoutine v (by omega) hc
      (fun i hi ↦ hfields i (by omega)) hret h3
    let result : BalanceSnapshot market mem ptr.toNat :=
      { memory := mem1, frame := frame2, supplyAssets := calldataWord market 0,
        supplyShares := calldataWord market 32, borrowAssets := calldataWord market 64,
        cursor := nextCursor ptr ⟨384⟩
        marketLocal := hm2, cursorLocal := hcursor2, free := hfree1
        lower := by rw [hcur]; omega
        upper := by rw [hcur]; exact hfit
        size := hmem1
        preserves := hprefix }
    exact .inr ⟨market, evm1, result, market, hs1,
      typedCallViaEVM_static_accountStorageStateEq hcall,
      allocatedMarketBalancesBodyNoAccrual hcall hdecode halloc hleSource haccrue,
      aw4, k4, C4, h4⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
