import Benchmarks.Midnight.Dispatch
import Benchmarks.Midnight.SupplyCollateralEntry
import Benchmarks.Midnight.SupplyAuthorizationTrace
import Benchmarks.Midnight.SupplySourceEntry
import Benchmarks.Midnight.SupplyCollateralCore
import Benchmarks.Midnight.TouchMarketCapacity
import Benchmarks.Midnight.TouchMarketHashSpace

/-!
# Midnight `supplyCollateral((uint256,address,address,(address,uint256,uint256,address)[],uint256,uint256,address,address),uint256,uint256,address)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Stele body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 16934; reach lemma `midnightReachSupplyCollateralBody`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000
set_option maxHeartbeats 200000

/-- `supplyCollateral((uint256,address,address,(address,uint256,uint256,address)[],uint256,uint256,address,address),uint256,uint256,address)`: the theorem `Correct.lean` routes selector 6 to. -/
theorem midnightSupplyCollateralBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = midnightBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwf : midnightWF σ I)
    (hgas : midnightGasBound g)
    (hsel : selIs I (midnightSelBytes 6)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (midnightSelBytes 6) rfl hsel
  have hd : dispatchMsg contract I.calldata = some supplyCollateralTransition := by
    apply midnightDispatch_supplyCollateral <;>
      first | exact hsel | exact selectorNe_of_selIs hsel (by decide +kernel)
  obtain ⟨k, C, rd⟩ := midnightReachSupplyCollateralBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
  change RD midnightBytecode I (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
    ⟨16934⟩ [solcSelectorWord I] midnightEntryMemory (UInt256.ofNat 26) ByteArray.empty σ k C at rd
  have ha : MemoryAccounting midnightEntryMemory (UInt256.ofNat 26) C := by
    refine ⟨MemoryPaid.entry C, ?_⟩
    change midnightEntryMemory.size ≤ 832
    rw [midnightEntryMemory_size]
  have hk : MemoryWords midnightEntryMemory 96 [⟨0⟩] := by
    refine ⟨by decide, by rw [midnightEntryMemory_size]; decide, ?_⟩
    intro i
    fin_cases i
    native_decide
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := midnightBlocks.midnight_block_16934_fallthrough (by simp) hwv rd
    have ha1 := memoryAccountingAt rd1 (by memory_account ha)
    have hselector : ¬ 0xac9650d8 = (bytesToWord (I.calldata.toList.take 4)).toNat := by
      rw [calldataSelector_of_selIs hsel]
      decide +kernel
    rcases midnightSupplyCollateralEntry (by simp) hsz hsize hselector
        midnightEntryMemory_freePtr hk (by decide) (by decide) ha1 rd1 with
      ⟨hdec, hr⟩ | ⟨m, hdec, h132, hhi, hu, mem', root, aw2, k2, C2,
        hroot, hm, hfree, hused, hk2, ha2, rd2⟩
    · exact hr.reEquivDecodingFailed hcode hd hdec
    · let origin := initState σ σ₀ (Sat256.ofUInt256 g) A I
      let user := calldataWord I.calldata 100
      let index := calldataWord I.calldata 36
      let assets := calldataWord I.calldata 68
      have hlimit : I.calldata.size < calldataLimit := by
        change I.calldata.size < 2^255 + 4
        omega
      have hzero : memLoad (UInt256.ofNat 96) mem' = ⟨0⟩ := hk2.load ⟨0, by decide⟩
      have h128 : 128 ≤ mem'.size := by omega
      rcases supplyAuthorizationGuard origin rfl (by simp) (by omega) hu ha2 rd2 with
        ⟨hbad, hr⟩ | ⟨hauth, mem2, aw3, k3, C3, hp2, hsize2, hfree2, ha3, rd3⟩
      · apply hr.reEquivExecutionRevert hcode hd hdec
        apply ExecFuncBody.execBlockRevert
        apply guardedBodyBlock hwv hlimit
        apply ExecBlock.consRevert (ExecStmt.requireFalse ?_)
        exact (supplyAuthEval origin m user index assets hu).trans (by rw [decide_eq_false hbad])
      · have hm2 := hm.preserve (hp2.mono hused)
        have hz2 : memLoad (UInt256.ofNat 96) mem2 = ⟨0⟩ := by
          rw [hp2.load (UInt256.ofNat 96) (by decide) h128 h128, hzero]
        have hf2 : memLoad (UInt256.ofNat 64) mem2 = root := hfree2.trans hfree
        have hu2 : root.toNat ≤ mem2.size := by rw [hsize2]; exact hused
        have rd4 := midnightBlocks.midnight_block_17021 (by simp) (by jump_dest) rd3
        have ha4 := memoryAccountingAt rd4 (by memory_account ha3)
        simp only [midnightBlocks.midnight_block_17021_stack] at rd4
        have rejectTouch (hr : RDrev midnightBytecode (Sat256.ofUInt256 g) origin)
            (hs : ExecFuncBody config (touchMarketCallFrame ∅ m) origin
              touchMarketFunction.body .reverted) :
            runtimeRefinementFor config contract σ σ₀ g A I := by
          apply hr.reEquivExecutionRevert hcode hd hdec
          apply ExecFuncBody.execBlockRevert
          apply supplyAfterAuthSource hu hwv hlimit hauth
          exact ExecBlock.consRevert (internalCallFunctionRevert
            (supplyTouchArgs origin m user index assets) rfl rfl hs)
        have finish {evm : EVM.State} {frame : Frame} {mem3 out : ByteArray}
            {free aw4 : UInt256} {credit k4 C4 : Nat}
            (hs : SourceState origin I evm.accountMap evm)
            (htouch : ExecFuncBody config (touchMarketCallFrame ∅ m) origin touchMarketFunction.body
              (.returned frame evm (some [wordBytes32Value m.id])))
            (hm3 : MarketStored mem3 ⟨832⟩ ⟨1088⟩ root m)
            (hroom : free.toNat + 32 < 2^64) (hlo : 128 ≤ free.toNat)
            (hfree3 : memLoad (UInt256.ofNat 64) mem3 = free)
            (hz3 : memLoad (UInt256.ofNat 96) mem3 = ⟨0⟩)
            (hb : TransferBudget (free + UInt256.ofNat 32) credit mem3 aw4 C4)
            (hcredit : 4 * (((free + UInt256.ofNat 32).toNat + safeTransferCallAllocation true + 31) / 32)
              ≤ credit + 999921)
            (rd5 : RD midnightBytecode I (Sat256.ofUInt256 g) origin ⟨17031⟩
              [m.id, UInt256.ofNat 96, user, index, assets, ⟨832⟩, solcSelectorWord I]
              mem3 aw4 out evm.accountMap k4 C4) :
            runtimeRefinementFor config contract σ σ₀ g A I := by
          have hmem3 : 128 ≤ mem3.size := by
            have hh := hm3.words.size
            change 832 + 32 * (m.words ⟨1088⟩).length ≤ mem3.size at hh
            omega
          have sourcePrefix {result : ExecResult}
              (hbody : ExecBlock config (supplyAfterTouchFrame origin m user index assets) evm
                (supplyCollateralTransition.body.drop 5) result) :
              ExecBlock config { contract := contract, locals := (marketIndexAmountArguments
                m index assets (AccountAddress.ofNat user.toNat)), immutables := ∅ }
                origin supplyCollateralTransition.body result :=
            supplyAfterAuthSource hu hwv hlimit hauth (supplyAfterTouchSource htouch hbody)
          rcases supplyCollateralCore (R := []) hs (supplyAfterTouch_get origin m user index assets)
              hu (by simp) hmem3 hm3 hroom hlo hfree3 hz3 hb hcredit hgas hwf rd5 with
            hoog | ⟨hr, hbody⟩ | ⟨hr, hbody⟩ | ⟨frame', evm', hbody, hr⟩
          · exact reEquiv_outOfGas (Xi_error_of_X (by rw [← hcode] at hoog; exact hoog))
          · exact hr.reEquivExecutionRevert hcode hd hdec
              (ExecFuncBody.execBlockRevert (sourcePrefix hbody))
          · exact hr.reEquivStaticHalt hcode hd hdec
              (ExecFuncBody.execBlockStatic (sourcePrefix hbody))
          · exact hr.reEquivExecutionGen hcode hd hdec
              (ExecFuncBody.execBlockOK (sourcePrefix hbody)) rfl voidReturnEquiv
        by_cases hsmall : m.collaterals.length ≤ 128
        · rcases midnightTouchMarketInternal_bounded (evm := origin) (g := Sat256.ofUInt256 g)
              (imms := ∅) m (by simp) hm2 hu2 hgas ha4 hf2 rfl (by jump_dest) rd4 with
            hoog | ⟨hr, hs⟩ | ⟨hr, hs⟩ |
              ⟨frame', evm', σ', out, mem3, free, aw4, k4, C4, hs, htouch,
                hp3, hlo, hbound, hfreeBound, hfree3, rd5⟩
          · exact reEquiv_outOfGas (Xi_error_of_X (by rw [← hcode] at hoog; exact hoog))
          · exact rejectTouch hr hs
          · apply hr.reEquivStaticHalt hcode hd hdec
            apply ExecFuncBody.execBlockStatic
            apply supplyAfterAuthSource hu hwv hlimit hauth
            exact ExecBlock.consStatic (ExecStmt.internalCallStatic
              (supplyTouchArgs origin m user index assets) rfl rfl hs)
          · have hm3 := hm2.preserve hp3
            have hz3 : memLoad (UInt256.ofNat 96) mem3 = ⟨0⟩ := by
              rw [hp3.load (UInt256.ofNat 96) (by decide)
                (by change 128 ≤ root.toNat; omega) (by rw [hsize2]; exact h128), hz2]
            have hmax : free.toNat ≤ 90000 := by
              dsimp only [MarketData.encodingSize] at hfreeBound
              omega
            have hn : (free + UInt256.ofNat 32).toNat = free.toNat + 32 :=
              addWord_toNat free (UInt256.ofNat 32) (by change _ + 32 < 2^256; omega)
            rw [hs.accounts] at rd5
            exact finish ⟨hs.world, hs.env, rfl⟩ htouch hm3 (by omega) (by omega)
              hfree3 hz3 (Or.inl (by rw [hn]; omega))
              (by change 4 * (((free + UInt256.ofNat 32).toNat + 160 + 31) / 32) ≤ 999921
                  rw [hn]; omega) rd5
        · rcases midnightTouchMarketLarge_funded (evm := origin) (g := Sat256.ofUInt256 g)
              (imms := ∅) m (by simp) hm2 (by omega) hu2 hgas ha4 hf2 (by jump_dest) rd4 with
            hoog | ⟨hr, hs⟩ | ⟨hb, htouch, aw4, k4, C4, hfund, rd5⟩
          · exact reEquiv_outOfGas (Xi_error_of_X (by rw [← hcode] at hoog; exact hoog))
          · exact rejectTouch hr hs
          · have hp3 := touchMarketHashMemory_prefix mem2 m (by omega) hb
            have hm3 := hm2.preserve hp3
            let free := touchMarketHashFree root m
            have hfn : free.toNat = root.toNat + 2 * m.encodingSize + 288 := by
              rw [show free = marketIdPreimagePtr root m + UInt256.ofNat 128 from rfl,
                uadd_word_ofNat_toNat _ _
                  (by rw [(marketIdPointers m hb).2.2]; change _ < 2^256; omega),
                (marketIdPointers m hb).2.2]
            have hn : free.toNat = 2048 + 416 * m.collaterals.length := by
              rw [hfn, hroot, MarketData.encodingSize]; omega
            have hz3 : memLoad (UInt256.ofNat 96) (touchMarketHashMemory mem2 root m) = ⟨0⟩ := by
              rw [hp3.load (UInt256.ofNat 96) (by decide) (by change 128 ≤ root.toNat; omega)
                (by rw [hsize2]; exact h128), hz2]
            rcases memoryAccounting_headroom rd5 hfund.accounting hgas with hoog | hspace
            · exact reEquiv_outOfGas (Xi_error_of_X (by rw [← hcode] at hoog; exact hoog))
            · have hused3 := touchMarketHashFree_space mem2 root m hb
              have hroom : free.toNat + 32 < 2^64 := by
                change free.toNat ≤ _ at hused3
                omega
              have hn32 : (free + UInt256.ofNat 32).toNat = free.toNat + 32 :=
                addWord_toNat free (UInt256.ofNat 32) (by change _ + 32 < 2^256; omega)
              exact finish (credit := 128 * m.collaterals.length) ⟨rfl, rfl, rfl⟩ htouch hm3 hroom
                (by rw [hn]; omega) (touchMarketHashMemory_free mem2 root m) hz3
                (Or.inr ⟨by rw [hn32, hn]; omega, hfund⟩)
                (by change 4 * (((free + UInt256.ofNat 32).toNat + 160 + 31) / 32) ≤ _
                    rw [hn32, hn]; omega) rd5
  · have rd1 := midnightBlocks.midnight_block_16934_taken (by simp) hwv (by jump_dest) rd
    have hr := midnightBlocks.midnight_block_6350 (by simp) rd1
    cases hdec : config.externalABI.decodeCalldata? (supplyCollateralTransition.params.map Param.name)
        (transitionSignature supplyCollateralTransition).paramTypes I.calldata with
    | none => exact hr.reEquivDecodingFailed hcode hd hdec
    | some args => exact hr.reEquivExecutionRevert hcode hd hdec (bodyReverts_nonPayable hwv)

end Benchmarks.Midnight
