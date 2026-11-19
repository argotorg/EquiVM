import Benchmarks.Midnight.Dispatch
import Benchmarks.Midnight.WithdrawCollateralEntry
import Benchmarks.Midnight.WithdrawAuthorizationTrace
import Benchmarks.Midnight.WithdrawSourceEntry
import Benchmarks.Midnight.WithdrawCollateralCore
import Benchmarks.Midnight.TouchMarketCapacity
import Benchmarks.Midnight.TouchMarketHashSpace

/-!
# Midnight `withdrawCollateral((uint256,address,address,(address,uint256,uint256,address)[],uint256,uint256,address,address),uint256,uint256,address,address)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Stele body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 4361; reach lemma `midnightReachWithdrawCollateralBody`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

/-- `withdrawCollateral((uint256,address,address,(address,uint256,uint256,address)[],uint256,uint256,address,address),uint256,uint256,address,address)`: the theorem `Correct.lean` routes selector 32 to. -/
theorem midnightWithdrawCollateralBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = midnightBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwf : midnightWF σ I)
    (hgas : midnightGasBound g)
    (hsel : selIs I (midnightSelBytes 32)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (midnightSelBytes 32) rfl hsel
  have hd : dispatchMsg contract I.calldata = some withdrawCollateralTransition := by
    apply midnightDispatch_withdrawCollateral <;>
      first | exact hsel | exact selectorNe_of_selIs hsel (by decide +kernel)
  obtain ⟨k, C, rd⟩ := midnightReachWithdrawCollateralBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
  change RD midnightBytecode I (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
    ⟨4361⟩ [solcSelectorWord I] midnightEntryMemory (UInt256.ofNat 26) ByteArray.empty σ k C at rd
  have ha : MemoryAccounting midnightEntryMemory (UInt256.ofNat 26) C := by
    refine ⟨MemoryPaid.entry C, ?_⟩
    change midnightEntryMemory.size ≤ 832
    rw [midnightEntryMemory_size]
  have hk : MemoryWords midnightEntryMemory 96 (List.replicate 23 ⟨0⟩) := by
    refine ⟨by decide, by rw [midnightEntryMemory_size]; decide, ?_⟩
    native_decide
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := midnightBlocks.midnight_block_4361_fallthrough (by simp) hwv rd
    have ha1 := memoryAccountingAt rd1 (by memory_account ha)
    have hselector : ¬ 0xac9650d8 = (bytesToWord (I.calldata.toList.take 4)).toNat := by
      rw [calldataSelector_of_selIs hsel]
      decide +kernel
    rcases midnightWithdrawCollateralEntry (by simp) hsz hsize hselector
        midnightEntryMemory_freePtr hk (by decide) (by decide) ha1 rd1 with
      ⟨hdec, hr⟩ | ⟨m, hdec, h164, hhi, hu, hv, mem', root, aw2, k2, C2,
        hroot, hm, hfree, hused, hk2, ha2, rd2⟩
    · exact hr.reEquivDecodingFailed hcode hd hdec
    · let origin := initState σ σ₀ (Sat256.ofUInt256 g) A I
      let user := calldataWord I.calldata 100
      let index := calldataWord I.calldata 36
      let assets := calldataWord I.calldata 68
      let receiver := AccountAddress.ofNat (calldataWord I.calldata 132).toNat
      have hreceiver : UInt256.ofNat receiver.val = calldataWord I.calldata 132 :=
        u256_inj (by
          change (UInt256.ofNat ((calldataWord I.calldata 132).toNat % EVM.addressModulus)).toNat = _
          rw [Nat.mod_eq_of_lt hv]
          exact UInt256.toNat_ofNat_of_lt (calldataWord I.calldata 132).val.isLt)
      have hlimit : I.calldata.size < calldataLimit := by
        change I.calldata.size < 2^255 + 4
        omega
      have hzero : memLoad (UInt256.ofNat 96) mem' = ⟨0⟩ := hk2.load ⟨0, by decide⟩
      have h832 : 832 ≤ mem'.size := by omega
      have hzero800 : memLoad (UInt256.ofNat 800) mem' = ⟨0⟩ := hk2.load ⟨22, by decide⟩
      rw [← hreceiver] at rd2
      rcases withdrawAuthorizationGuard origin rfl (by simp) h832 hzero800 hu ha2 rd2 with
        ⟨hbad, hr⟩ | ⟨hauth, mem2, aw3, k3, C3, hp2, hsize2, hfree2, ha3, rd3⟩
      · apply hr.reEquivExecutionRevert hcode hd hdec
        apply ExecFuncBody.execBlockRevert
        apply guardedBodyBlock hwv hlimit
        apply ExecBlock.consRevert (ExecStmt.requireFalse ?_)
        exact (withdrawAuthEval origin m user index assets receiver hu).trans (by rw [decide_eq_false hbad])
      · have hm2 := hm.preserve (hp2.mono hused)
        have hz2 : memLoad (UInt256.ofNat 96) mem2 = ⟨0⟩ := by
          rw [hp2.load (UInt256.ofNat 96) (by decide) (by change 128 ≤ mem'.size; omega) (by change 128 ≤ mem'.size; omega), hzero]
        have hz8002 : memLoad (UInt256.ofNat 800) mem2 = ⟨0⟩ := by
          rw [hp2.load (UInt256.ofNat 800) (by decide) h832 h832, hzero800]
        have hf2 : memLoad (UInt256.ofNat 64) mem2 = root := hfree2.trans hfree
        have hu2 : root.toNat ≤ mem2.size := by rw [hsize2]; exact hused
        have rd4 := midnightBlocks.midnight_block_4460 (by simp) (by jump_dest) rd3
        have ha4 := memoryAccountingAt rd4 (by memory_account ha3)
        simp only [midnightBlocks.midnight_block_4460_stack] at rd4
        have rejectTouch (hr : RDrev midnightBytecode (Sat256.ofUInt256 g) origin)
            (hs : ExecFuncBody config (touchMarketCallFrame ∅ m) origin
              touchMarketFunction.body .reverted) :
            runtimeRefinementFor config contract σ σ₀ g A I := by
          apply hr.reEquivExecutionRevert hcode hd hdec
          apply ExecFuncBody.execBlockRevert
          apply withdrawAfterAuthSource hu hwv hlimit hauth
          exact ExecBlock.consRevert (internalCallFunctionRevert
            (withdrawTouchArgs origin m user index assets receiver) rfl rfl hs)
        have finish {evm : EVM.State} {frame : Frame} {mem3 out : ByteArray}
            {free aw4 : UInt256} {credit k4 C4 : Nat}
            (hs : SourceState origin I evm.accountMap evm)
            (htouch : ExecFuncBody config (touchMarketCallFrame ∅ m) origin touchMarketFunction.body
              (.returned frame evm (some [wordBytes32Value m.id])))
            (hm3 : MarketStored mem3 ⟨832⟩ ⟨1088⟩ root m)
            (hroom : free.toNat + 4096 < 2^64) (hlo : root.toNat ≤ free.toNat)
            (halign : free.toNat % 32 = 0 ∨ (free + UInt256.ofNat 4096).toNat + 160 ≤ 2^62)
            (hfree3 : memLoad (UInt256.ofNat 64) mem3 = free)
            (hz3 : memLoad (UInt256.ofNat 96) mem3 = ⟨0⟩)
            (hz8003 : memLoad (UInt256.ofNat 800) mem3 = ⟨0⟩)
            (hb : TransferBudget (free + UInt256.ofNat 4096) credit mem3 aw4 C4)
            (hcredit : 4 * (((free + UInt256.ofNat 4096).toNat + safeTransferCallAllocation false + 31) / 32)
              ≤ credit + 999921)
            (rd5 : RD midnightBytecode I (Sat256.ofUInt256 g) origin ⟨4472⟩
              [m.id, user, UInt256.ofNat 4643, user, index, UInt256.ofNat receiver.val, assets,
                ⟨832⟩, solcSelectorWord I]
              mem3 aw4 out evm.accountMap k4 C4) :
            runtimeRefinementFor config contract σ σ₀ g A I := by
          have hmem3 : 832 ≤ mem3.size := by
            have hh := hm3.words.size
            change 832 + 32 * (m.words ⟨1088⟩).length ≤ mem3.size at hh
            omega
          have sourcePrefix {result : ExecResult}
              (hbody : ExecBlock config (withdrawAfterTouchFrame origin m user index assets receiver) evm
                (withdrawCollateralTransition.body.drop 5) result) :
              ExecBlock config { contract := contract, locals := (marketIndexAmountReceiverArguments
                m index assets (AccountAddress.ofNat user.toNat) receiver), immutables := ∅ }
                origin withdrawCollateralTransition.body result :=
            withdrawAfterAuthSource hu hwv hlimit hauth (withdrawAfterTouchSource htouch hbody)
          have hbudgetRoot : (free + UInt256.ofNat 4096).toNat = free.toNat + 4096 :=
            uadd_word_ofNat_toNat free 4096 (by change _ < 2^256; omega)
          rcases withdrawCollateralCore (R := []) hs
              (withdrawAfterTouch_get origin m user index assets receiver)
              (withdrawAfterTouch_receiver origin m user index assets receiver)
              hu (by simp) hmem3 hm3 hroom (by omega) hlo halign
              (by rw [hbudgetRoot]) hfree3 hz3 hz8003 hb hcredit hgas hwf rd5 with
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
            apply withdrawAfterAuthSource hu hwv hlimit hauth
            exact ExecBlock.consStatic (ExecStmt.internalCallStatic
              (withdrawTouchArgs origin m user index assets receiver) rfl rfl hs)
          · have hm3 := hm2.preserve hp3
            have hz3 : memLoad (UInt256.ofNat 96) mem3 = ⟨0⟩ := by
              rw [hp3.load (UInt256.ofNat 96) (by decide)
                (by change 128 ≤ root.toNat; omega) (by rw [hsize2]; change 128 ≤ mem'.size; omega), hz2]
            have hz8003 : memLoad (UInt256.ofNat 800) mem3 = ⟨0⟩ := by
              rw [hp3.load (UInt256.ofNat 800) (by decide)
                (by change 832 ≤ root.toNat; omega) (by rw [hsize2]; exact h832), hz8002]
            have hmax : free.toNat ≤ 90000 := by
              dsimp only [MarketData.encodingSize] at hfreeBound
              omega
            have hn : (free + UInt256.ofNat 4096).toNat = free.toNat + 4096 :=
              uadd_word_ofNat_toNat free 4096 (by change _ + 4096 < 2^256; omega)
            rw [hs.accounts] at rd5
            exact finish ⟨hs.world, hs.env, rfl⟩ htouch hm3 (by omega) hlo
              (Or.inr (by rw [hn]; omega)) hfree3 hz3 hz8003 (Or.inl (by rw [hn]; omega))
              (by change 4 * (((free + UInt256.ofNat 4096).toNat + 128 + 31) / 32) ≤ 999921
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
                (by rw [hsize2]; change 128 ≤ mem'.size; omega), hz2]
            have hz8003 : memLoad (UInt256.ofNat 800) (touchMarketHashMemory mem2 root m) = ⟨0⟩ := by
              rw [hp3.load (UInt256.ofNat 800) (by decide) (by change 832 ≤ root.toNat; omega)
                (by rw [hsize2]; exact h832), hz8002]
            rcases memoryAccounting_headroom rd5 hfund.accounting hgas with hoog | hspace
            · exact reEquiv_outOfGas (Xi_error_of_X (by rw [← hcode] at hoog; exact hoog))
            · have hused3 := touchMarketHashFree_space mem2 root m hb
              have hroom : free.toNat + 4096 < 2^64 := by
                change free.toNat ≤ _ at hused3
                omega
              have hn32 : (free + UInt256.ofNat 4096).toNat = free.toNat + 4096 :=
                uadd_word_ofNat_toNat free 4096 (by change _ + 4096 < 2^256; omega)
              exact finish (credit := 128 * m.collaterals.length) ⟨rfl, rfl, rfl⟩ htouch hm3 hroom
                (by rw [hfn]; omega) (Or.inl (by rw [hn]; omega))
                (touchMarketHashMemory_free mem2 root m) hz3 hz8003
                (Or.inr ⟨by rw [hn32, hn]; omega, hfund⟩)
                (by change 4 * (((free + UInt256.ofNat 4096).toNat + 128 + 31) / 32) ≤ _
                    rw [hn32, hn]; omega) rd5
  · have rd1 := midnightBlocks.midnight_block_4361_taken (by simp) hwv (by jump_dest) rd
    have hr := midnightBlocks.midnight_block_712 (by simp) rd1
    cases hdec : config.externalABI.decodeCalldata? (withdrawCollateralTransition.params.map Param.name)
        (transitionSignature withdrawCollateralTransition).paramTypes I.calldata with
    | none => exact hr.reEquivDecodingFailed hcode hd hdec
    | some args => exact hr.reEquivExecutionRevert hcode hd hdec (bodyReverts_nonPayable hwv)


end Benchmarks.Midnight
