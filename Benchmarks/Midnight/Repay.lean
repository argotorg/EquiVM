import Benchmarks.Midnight.Dispatch
import Benchmarks.Midnight.RepayEntry
import Benchmarks.Midnight.RepayAuthorization
import Benchmarks.Midnight.RepayCore
import Benchmarks.Midnight.TouchMarketCapacity
import Benchmarks.Midnight.TouchMarketHashSpace

/-!
# Midnight `repay((uint256,address,address,(address,uint256,uint256,address)[],uint256,uint256,address,address),uint256,address,address,bytes)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Stele body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 9725; reach lemma `midnightReachRepayBody`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

/-- `repay((uint256,address,address,(address,uint256,uint256,address)[],uint256,uint256,address,address),uint256,address,address,bytes)`: the theorem `Correct.lean` routes selector 19 to. -/
theorem midnightRepayBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = midnightBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwf : midnightWF σ I)
    (hgas : midnightGasBound g)
    (hsel : selIs I (midnightSelBytes 19)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (midnightSelBytes 19) rfl hsel
  have hd : dispatchMsg contract I.calldata = some repayTransition := by
    apply midnightDispatch_repay <;>
      first | exact hsel | exact selectorNe_of_selIs hsel (by decide +kernel)
  obtain ⟨k, C, rd⟩ := midnightReachRepayBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
  change RD midnightBytecode I (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
    ⟨9725⟩ [solcSelectorWord I] midnightEntryMemory (UInt256.ofNat 26) ByteArray.empty σ k C at rd
  have ha : MemoryAccounting midnightEntryMemory (UInt256.ofNat 26) C := by
    refine ⟨MemoryPaid.entry C, ?_⟩
    change midnightEntryMemory.size ≤ 832
    rw [midnightEntryMemory_size]
  have hk : MemoryWords midnightEntryMemory 96 (List.replicate 23 ⟨0⟩) := by
    refine ⟨by decide, by rw [midnightEntryMemory_size]; decide, ?_⟩
    native_decide
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := midnightBlocks.midnight_block_9725_fallthrough (by simp) hwv rd
    have ha1 := memoryAccountingAt rd1 (by memory_account ha)
    have hselector : ¬ 0xac9650d8 = (bytesToWord (I.calldata.toList.take 4)).toNat := by
      rw [calldataSelector_of_selIs hsel]
      decide +kernel
    rcases midnightRepayEntry (by simp) hsz hsize hselector midnightEntryMemory_freePtr
        hk (by decide) (by decide) ha1 rd1 with
      ⟨hdec, hr⟩ | ⟨m, hdec, h164, hhi, hu, hcb, hdata, mem', root, aw2, k2, C2,
        hroot, hm, hfree, hused, hk2, ha2, rd2⟩
    · exact hr.reEquivDecodingFailed hcode hd hdec
    · let origin := initState σ σ₀ (Sat256.ofUInt256 g) A I
      let user := calldataWord I.calldata 68
      let units := calldataWord I.calldata 36
      let callback := AccountAddress.ofNat (calldataWord I.calldata 100).toNat
      let dp := calldataArgumentPointer I.calldata 132
      let dl := calldataArgumentLength I.calldata 132
      let data := I.calldata.extract dp.toNat (dp.toNat + dl.toNat)
      have hcallback : UInt256.ofNat callback.val = calldataWord I.calldata 100 :=
        addressWord_eq_ofNat_address hcb
      have hdl : dl.toNat < 2^64 := hdata.bounds.1
      have hdp : dp.toNat + dl.toNat ≤ I.calldata.size := by
        have hp := hdata.bounds.2
        change dp.toNat + 1 * dl.toNat ≤ I.calldata.size at hp
        simpa only [Nat.one_mul] using hp
      have hlimit : I.calldata.size < calldataLimit := by
        change I.calldata.size < 2^255 + 4
        omega
      have hzero : memLoad (UInt256.ofNat 96) mem' = ⟨0⟩ := hk2.load ⟨0, by decide⟩
      have h832 : 832 ≤ mem'.size := by omega
      have hzero800 : memLoad (UInt256.ofNat 800) mem' = ⟨0⟩ := hk2.load ⟨22, by decide⟩
      rw [← hcallback] at rd2
      rcases repayAuthorizationGuard origin rfl (by simp) h832 hzero800 hu ha2 rd2 with
        ⟨hbad, hr⟩ | ⟨hauth, mem2, aw3, k3, C3, hp2, hsize2, hfree2, ha3, rd3⟩
      · apply hr.reEquivExecutionRevert hcode hd hdec
        apply ExecFuncBody.execBlockRevert
        apply guardedBodyBlock hwv hlimit
        apply ExecBlock.consRevert (ExecStmt.requireFalse ?_)
        exact (repayAuthEval origin m user units callback data hu).trans
          (by rw [decide_eq_false hbad])
      · have hm2 := hm.preserve (hp2.mono hused)
        have hz2 : memLoad (UInt256.ofNat 96) mem2 = ⟨0⟩ := by
          rw [hp2.load (UInt256.ofNat 96) (by decide) (by change 128 ≤ mem'.size; omega)
            (by change 128 ≤ mem'.size; omega), hzero]
        have hz8002 : memLoad (UInt256.ofNat 800) mem2 = ⟨0⟩ := by
          rw [hp2.load (UInt256.ofNat 800) (by decide) h832 h832, hzero800]
        have hf2 : memLoad (UInt256.ofNat 64) mem2 = root := hfree2.trans hfree
        have hu2 : root.toNat ≤ mem2.size := by rw [hsize2]; exact hused
        have rd4 := midnightBlocks.midnight_block_9853 (by simp) (by jump_dest) rd3
        have ha4 := memoryAccountingAt rd4 (by memory_account ha3)
        simp only [midnightBlocks.midnight_block_9853_stack] at rd4
        have rejectTouch (hr : RDrev midnightBytecode (Sat256.ofUInt256 g) origin)
            (ht : ExecFuncBody config (touchMarketCallFrame ∅ m) origin
              touchMarketFunction.body .reverted) :
            runtimeRefinementFor config contract σ σ₀ g A I := by
          apply hr.reEquivExecutionRevert hcode hd hdec
          apply ExecFuncBody.execBlockRevert
          apply repayAfterAuthSource hu hwv hlimit hauth
          exact ExecBlock.consRevert (internalCallFunctionRevert
            (repayTouchArgs origin m user units callback data) rfl rfl ht)
        have finish {evm : EVM.State} {frame : Frame} {mem3 out : ByteArray}
            {free aw4 : UInt256} {credit k4 C4 : Nat}
            (hs : SourceState origin I evm.accountMap evm)
            (htouch : ExecFuncBody config (touchMarketCallFrame ∅ m) origin touchMarketFunction.body
              (.returned frame evm (some [wordBytes32Value m.id])))
            (hm3 : MarketStored mem3 ⟨832⟩ ⟨1088⟩ root m)
            (hroom : free.toNat + 32 < 2^64) (hlo : root.toNat ≤ free.toNat)
            (hfree3 : memLoad (UInt256.ofNat 64) mem3 = free)
            (hz3 : memLoad (UInt256.ofNat 96) mem3 = ⟨0⟩)
            (hz8003 : memLoad (UInt256.ofNat 800) mem3 = ⟨0⟩)
            (hb : TransferBudget (free + UInt256.ofNat 32) credit mem3 aw4 C4)
            (hcredit : 4 * (((free + UInt256.ofNat 32).toNat + safeTransferCallAllocation true + 31)
              / 32) ≤ credit + 999921)
            (rd5 : RD midnightBytecode I (Sat256.ofUInt256 g) origin ⟨9861⟩
              [m.id, dp, dl, user, UInt256.ofNat callback.val, units, ⟨832⟩, solcSelectorWord I]
              mem3 aw4 out evm.accountMap k4 C4) :
            runtimeRefinementFor config contract σ σ₀ g A I := by
          have hmem3 : 832 ≤ mem3.size := by
            have hh := hm3.words.size
            change 832 + 32 * (m.words ⟨1088⟩).length ≤ mem3.size at hh
            omega
          have sourcePrefix {result : ExecResult}
              (hbody : ExecBlock config (repayAfterTouchFrame origin m user units callback data)
                evm (repayTransition.body.drop 5) result) :
              ExecBlock config { contract := contract, locals := (repayArguments m units
                (AccountAddress.ofNat user.toNat) callback data), immutables := ∅ }
                origin repayTransition.body result :=
            repayAfterAuthSource hu hwv hlimit hauth (repayAfterTouchSource htouch hbody)
          rcases midnightRepayCore (R := []) hs
              (repayAfterTouchFrame_spec origin m user units callback data) hu (by simp)
              hmem3 hm3 hlo hroom (by omega) hfree3 hz3 hz8003 hdl hdp hb hcredit hgas hwf rd5 with
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
            hoog | ⟨hr, ht⟩ | ⟨hr, ht⟩ |
              ⟨frame', evm', σ', out, mem3, free, aw4, k4, C4, hs, htouch,
                hp3, hlo, hbound, hfreeBound, hfree3, rd5⟩
          · exact reEquiv_outOfGas (Xi_error_of_X (by rw [← hcode] at hoog; exact hoog))
          · exact rejectTouch hr ht
          · apply hr.reEquivStaticHalt hcode hd hdec
            apply ExecFuncBody.execBlockStatic
            apply repayAfterAuthSource hu hwv hlimit hauth
            exact ExecBlock.consStatic (ExecStmt.internalCallStatic
              (repayTouchArgs origin m user units callback data) rfl rfl ht)
          · have hm3 := hm2.preserve hp3
            have hz3 : memLoad (UInt256.ofNat 96) mem3 = ⟨0⟩ := by
              rw [hp3.load (UInt256.ofNat 96) (by decide) (by change 128 ≤ root.toNat; omega)
                (by rw [hsize2]; change 128 ≤ mem'.size; omega), hz2]
            have hz8003 : memLoad (UInt256.ofNat 800) mem3 = ⟨0⟩ := by
              rw [hp3.load (UInt256.ofNat 800) (by decide) (by change 832 ≤ root.toNat; omega)
                (by rw [hsize2]; exact h832), hz8002]
            have hmax : free.toNat ≤ 90000 := by
              dsimp only [MarketData.encodingSize] at hfreeBound
              omega
            have hn : (free + UInt256.ofNat 32).toNat = free.toNat + 32 :=
              addWord_toNat free (UInt256.ofNat 32) (by change _ + 32 < 2^256; omega)
            rw [hs.accounts] at rd5
            exact finish ⟨hs.world, hs.env, rfl⟩ htouch hm3 (by omega) hlo
              hfree3 hz3 hz8003 (Or.inl (by rw [hn]; omega))
              (by change 4 * (((free + UInt256.ofNat 32).toNat + 160 + 31) / 32) ≤ 999921
                  rw [hn]; omega) rd5
        · rcases midnightTouchMarketLarge_funded (evm := origin) (g := Sat256.ofUInt256 g)
              (imms := ∅) m (by simp) hm2 (by omega) hu2 hgas ha4 hf2 (by jump_dest) rd4 with
            hoog | ⟨hr, ht⟩ | ⟨hb, htouch, aw4, k4, C4, hfund, rd5⟩
          · exact reEquiv_outOfGas (Xi_error_of_X (by rw [← hcode] at hoog; exact hoog))
          · exact rejectTouch hr ht
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
                (by rw [hsize2]; change 128 ≤ mem'.size; omega), hz2]
            have hz8003 : memLoad (UInt256.ofNat 800) (touchMarketHashMemory mem2 root m) = ⟨0⟩ := by
              rw [hp3.load (UInt256.ofNat 800) (by decide) (by change 832 ≤ root.toNat; omega)
                (by rw [hsize2]; exact h832), hz8002]
            rcases memoryAccounting_headroom rd5 hfund.accounting hgas with hoog | hspace
            · exact reEquiv_outOfGas (Xi_error_of_X (by rw [← hcode] at hoog; exact hoog))
            · have hused3 := touchMarketHashFree_space mem2 root m hb
              have hroom : free.toNat + 32 < 2^64 := by
                change free.toNat ≤ _ at hused3
                omega
              have hn32 : (free + UInt256.ofNat 32).toNat = free.toNat + 32 :=
                addWord_toNat free (UInt256.ofNat 32) (by change _ + 32 < 2^256; omega)
              exact finish (credit := 128 * m.collaterals.length) ⟨rfl, rfl, rfl⟩ htouch hm3 hroom
                (by rw [hfn]; omega) (touchMarketHashMemory_free mem2 root m) hz3 hz8003
                (Or.inr ⟨by rw [hn32, hn]; omega, hfund⟩)
                (by change 4 * (((free + UInt256.ofNat 32).toNat + 160 + 31) / 32) ≤ _
                    rw [hn32, hn]; omega) rd5
  · have rd1 := midnightBlocks.midnight_block_9725_taken (by simp) hwv (by jump_dest) rd
    have hr := midnightBlocks.midnight_block_712 (by simp) rd1
    cases hdec : config.externalABI.decodeCalldata? (repayTransition.params.map Param.name)
        (transitionSignature repayTransition).paramTypes I.calldata with
    | none => exact hr.reEquivDecodingFailed hcode hd hdec
    | some args => exact hr.reEquivExecutionRevert hcode hd hdec (bodyReverts_nonPayable hwv)

end Benchmarks.Midnight
