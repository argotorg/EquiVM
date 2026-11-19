import Benchmarks.Midnight.Dispatch
import Benchmarks.Midnight.LiquidateEntry
import Benchmarks.Midnight.LiquidateSourceEntry
import Benchmarks.Midnight.LiquidateCore
import Benchmarks.Midnight.TouchMarketInternalFunding
import Benchmarks.Midnight.RuntimeBlocks_019

/-!
# Midnight `liquidate((uint256,address,address,(address,uint256,uint256,address)[],uint256,uint256,address,address),uint256,uint256,uint256,address,bool,address,address,bytes)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Stele body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 4977; reach lemma `midnightReachLiquidateBody`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

/-- `liquidate((uint256,address,address,(address,uint256,uint256,address)[],uint256,uint256,address,address),uint256,uint256,uint256,address,bool,address,address,bytes)`: the theorem `Correct.lean` routes selector 30 to. -/
theorem midnightLiquidateBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = midnightBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwf : midnightWF σ I)
    (hgas : midnightGasBound g)
    (hsel : selIs I (midnightSelBytes 30)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (midnightSelBytes 30) rfl hsel
  have hd : dispatchMsg contract I.calldata = some liquidateTransition := by
    apply midnightDispatch_liquidate <;>
      first | exact hsel | exact selectorNe_of_selIs hsel (by decide +kernel)
  obtain ⟨k, C, rd⟩ := midnightReachLiquidateBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
  change RD midnightBytecode I (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
    ⟨4977⟩ [solcSelectorWord I] midnightEntryMemory (UInt256.ofNat 26) ByteArray.empty σ k C at rd
  have ha : MemoryAccounting midnightEntryMemory (UInt256.ofNat 26) C := by
    refine ⟨MemoryPaid.entry C, ?_⟩
    change midnightEntryMemory.size ≤ 832
    rw [midnightEntryMemory_size]
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := midnightBlocks.midnight_block_4977_fallthrough (by simp) hwv rd
    have ha1 := memoryAccountingAt rd1 (by memory_account ha)
    have hselector : ¬ 0xac9650d8 = (bytesToWord (I.calldata.toList.take 4)).toNat := by
      rw [calldataSelector_of_selIs hsel]
      decide +kernel
    rcases midnightLiquidateEntry_decoded (by simp) hsz hsize hselector
        (by rw [midnightEntryMemory_size]) midnightEntryMemory_freePtr ha1 rd1 with
      ⟨hdec, hr⟩ | ⟨m, hdec, hmarket, h292, hhi, hv, hdata, mem', root, aw2, k2, C2,
        hroot, hm, hfree, hused, hk2, ha2, rd2⟩
    · exact hr.reEquivDecodingFailed hcode hd hdec
    · let origin := initState σ σ₀ (Sat256.ofUInt256 g) A I
      let index := calldataWord I.calldata 36
      let seized := calldataWord I.calldata 68
      let repaid := calldataWord I.calldata 100
      let borrower := calldataWord I.calldata 132
      let mode := calldataWord I.calldata 164
      let receiver := AccountAddress.ofNat (calldataWord I.calldata 196).toNat
      let callback := AccountAddress.ofNat (calldataWord I.calldata 228).toNat
      let dp := calldataArgumentPointer I.calldata 260
      let dl := calldataArgumentLength I.calldata 260
      let data := I.calldata.extract dp.toNat (dp.toNat + dl.toNat)
      have hreceiver : UInt256.ofNat receiver.val = calldataWord I.calldata 196 :=
        addressWord_eq_ofNat_address hv.2.2.1
      have hcallback : UInt256.ofNat callback.val = calldataWord I.calldata 228 :=
        addressWord_eq_ofNat_address hv.2.2.2
      have hdl : dl.toNat < 2^64 := hdata.bounds.1
      have hdp : dp.toNat + dl.toNat ≤ I.calldata.size := by
        have hp := hdata.bounds.2
        change dp.toNat + 1 * dl.toNat ≤ I.calldata.size at hp
        simpa only [Nat.one_mul] using hp
      have hlimit : I.calldata.size < calldataLimit := by
        change I.calldata.size < 2^255 + 4
        omega
      have hentry : 832 ≤ midnightEntryMemory.size := by rw [midnightEntryMemory_size]
      have hz96 : memLoad (UInt256.ofNat 96) mem' = ⟨0⟩ := by
        have hk := hk2.snapshot_load 0 (by decide)
        change memLoad (UInt256.ofNat 96) mem' =
          memLoad (UInt256.ofNat 96) (liquidateEntryMemory midnightEntryMemory I.calldata) at hk
        rw [hk, liquidateEntryMemory_load hentry _
          (by rw [midnightEntryMemory_size]; decide) (Or.inl (by decide))]
        native_decide
      have hz800 : memLoad (UInt256.ofNat 800) mem' = ⟨0⟩ := by
        have hk := hk2.snapshot_load 22 (by decide)
        change memLoad (UInt256.ofNat 800) mem' =
          memLoad (UInt256.ofNat 800) (liquidateEntryMemory midnightEntryMemory I.calldata) at hk
        rw [hk, liquidateEntryMemory_load hentry _
          (by rw [midnightEntryMemory_size]; decide) (Or.inr (by decide))]
        exact midnightEntryMemory_zero
      have hcb : memLoad (UInt256.ofNat 736) mem' = UInt256.ofNat callback.val :=
        (hk2.snapshot_load 20 (by decide)).trans
          ((liquidateEntryMemory_callback _ _).trans hcallback.symm)
      have hseized : memLoad (UInt256.ofNat 640) mem' = seized :=
        (hk2.snapshot_load 17 (by decide)).trans (liquidateEntryMemory_seized _ _)
      have hrepaid : memLoad (UInt256.ofNat 608) mem' = repaid :=
        (hk2.snapshot_load 16 (by decide)).trans (liquidateEntryMemory_repaid _ _)
      have h832 : 832 ≤ mem'.size := by omega
      have halign : root.toNat % 32 = 0 := by rw [hroot]; omega
      rw [← hreceiver] at rd2
      have rd3 := midnightBlocks.midnight_block_4356 (by simp) (by jump_dest) rd2
      have ha3 := memoryAccountingAt rd3 (by memory_account ha2)
      have rejectTouch (hr : RDrev midnightBytecode (Sat256.ofUInt256 g) origin)
          (ht : ExecFuncBody config (touchMarketCallFrame ∅ m) origin
            touchMarketFunction.body .reverted) :
          runtimeRefinementFor config contract σ σ₀ g A I := by
        apply hr.reEquivExecutionRevert hcode hd hdec
        apply ExecFuncBody.execBlockRevert
        apply guardedBodyBlock hwv hlimit
        exact ExecBlock.consRevert (internalCallFunctionRevert
          (liquidateTouchArgs origin m index seized repaid borrower mode receiver callback data)
          rfl rfl ht)
      have finish {evm : State} {callee : Frame} {mem2 out : ByteArray}
          {free aw3 : UInt256} {credit k3 C3 : Nat}
          (hs : SourceState origin I evm.accountMap evm)
          (htouch : ExecFuncBody config (touchMarketCallFrame ∅ m) origin touchMarketFunction.body
            (.returned callee evm (some [wordBytes32Value m.id])))
          (hp : MemoryPrefix mem' mem2 root.toNat)
          (hlo : root.toNat ≤ free.toNat)
          (hf : memLoad (UInt256.ofNat 64) mem2 = free)
          (haligned : free.toNat % 32 = 0) (hspace : free.toNat ≤ mem2.size + 31)
          (hfund : MemoryFunding credit mem2 aw3 C3)
          (hcredit : 4 * ((free.toNat + 20831) / 32) ≤ credit + 999921)
          (rd4 : RD midnightBytecode I (Sat256.ofUInt256 g) origin ⟨5161⟩
            [m.id, dl, borrower, dp, UInt256.ofNat receiver.val, mode, solcSelectorWord I]
            mem2 aw3 out evm.accountMap k3 C3) :
          runtimeRefinementFor config contract σ σ₀ g A I := by
        have hm2 := hm.preserve hp
        have keep (read : UInt256) (hr : 96 ≤ read.toNat) (hb : read.toNat + 32 ≤ 832) :
            memLoad read mem2 = memLoad read mem' :=
          hp.load read hr (by omega) (by omega)
        have sourcePrefix {result : ExecResult}
            (hbody : ExecBlock config
              (liquidateReadyFrame origin m index seized repaid borrower mode receiver callback data)
              evm (liquidateTransition.body.drop 6) result) :
            ExecBlock config { contract := contract, locals := (liquidateArguments m index seized repaid
              (AccountAddress.ofNat borrower.toNat) mode receiver callback data), immutables := ∅ }
              origin liquidateTransition.body result :=
          guardedBodyBlock hwv hlimit (liquidateAfterTouchSource htouch hbody)
        rcases midnightLiquidateCore (R := []) (by simp)
            (liquidateReadyFrame_spec origin m index seized repaid borrower mode receiver callback data)
            hmarket rfl rfl (by omega) (h832.trans hp.size) hspace hf haligned hm2 hlo
            ((keep _ (by decide) (by decide)).trans hz96)
            ((keep _ (by decide) (by decide)).trans hz800)
            ((keep _ (by decide) (by decide)).trans hcb) hv.1
            ((keep _ (by decide) (by decide)).trans hseized)
            ((keep _ (by decide) (by decide)).trans hrepaid)
            hdl hdp hfund hcredit hgas hwf hs rd4 with
          hoog | ⟨ht, hr⟩ | ⟨ht, hr⟩ | ⟨frame', evm', seized', repaid', ht, hr⟩
        · exact reEquiv_outOfGas (Xi_error_of_X (by rw [← hcode] at hoog; exact hoog))
        · exact hr.reEquivExecutionRevert hcode hd hdec
            (ExecFuncBody.execBlockRevert (sourcePrefix ht))
        · exact hr.reEquivStaticHalt hcode hd hdec
            (ExecFuncBody.execBlockStatic (sourcePrefix ht))
        · exact hr.reEquivExecutionGen hcode hd hdec
            (ExecFuncBody.execBlockRet (sourcePrefix ht)) rfl
            (returnEquiv.returned rfl (liquidateReturnEncoding seized' repaid'))
      by_cases hsmall : m.collaterals.length ≤ 128
      · rcases midnightTouchMarketInternal_funded (evm := origin) (g := Sat256.ofUInt256 g)
            (imms := ∅) m (by simp) hm
            (by rw [hroot]; dsimp only [MarketData.encodingSize]; omega)
            hused halign hgas ha3 hfree rfl (by jump_dest) rd3 with
          hoog | ⟨hr, ht⟩ | ⟨hr, ht⟩ |
            ⟨frame', evm', σ', out, mem2, free, aw3, k3, C3, hs, htouch,
              hp, hlo, hbound, hfreeBound, hf, haligned, hspace, hfund, rd4⟩
        · exact reEquiv_outOfGas (Xi_error_of_X (by rw [← hcode] at hoog; exact hoog))
        · exact rejectTouch hr ht
        · apply hr.reEquivStaticHalt hcode hd hdec
          apply ExecFuncBody.execBlockStatic
          apply guardedBodyBlock hwv hlimit
          exact ExecBlock.consStatic (ExecStmt.internalCallStatic
            (liquidateTouchArgs origin m index seized repaid borrower mode receiver callback data)
            rfl rfl ht)
        · have hmax : free.toNat ≤ 90000 := by
            dsimp only [MarketData.encodingSize] at hfreeBound
            omega
          rw [hs.accounts] at rd4
          exact finish ⟨hs.world, hs.env, rfl⟩ htouch hp hlo hf haligned hspace hfund
            (by omega) rd4
      · rcases midnightTouchMarketLarge_funded (evm := origin) (g := Sat256.ofUInt256 g)
            (imms := ∅) m (by simp) hm (by omega) hused hgas ha3 hfree (by jump_dest) rd3 with
          hoog | ⟨hr, ht⟩ | ⟨hb, htouch, aw3, k3, C3, hfund, rd4⟩
        · exact reEquiv_outOfGas (Xi_error_of_X (by rw [← hcode] at hoog; exact hoog))
        · exact rejectTouch hr ht
        · have hp := touchMarketHashMemory_prefix mem' m (by omega) hb
          let free := touchMarketHashFree root m
          have hfn : free.toNat = root.toNat + 2 * m.encodingSize + 288 := by
            rw [show free = marketIdPreimagePtr root m + UInt256.ofNat 128 from rfl,
              uadd_word_ofNat_toNat _ _
                (by rw [(marketIdPointers m hb).2.2]; change _ < 2^256; omega),
              (marketIdPointers m hb).2.2]
          have hn : free.toNat = 2048 + 416 * m.collaterals.length := by
            rw [hfn, hroot, MarketData.encodingSize]
            omega
          exact finish (credit := 128 * m.collaterals.length) ⟨rfl, rfl, rfl⟩ htouch hp
            (by rw [hfn]; omega) (touchMarketHashMemory_free mem' root m)
            (by rw [hn]; omega) ((touchMarketHashFree_space mem' root m hb).trans (by omega))
            hfund (by rw [hn]; omega) rd4
  · have rd1 := midnightBlocks.midnight_block_4977_taken (by simp) hwv (by jump_dest) rd
    have hr := midnightBlocks.midnight_block_712 (by simp) rd1
    cases hdec : config.externalABI.decodeCalldata? (liquidateTransition.params.map Param.name)
        (transitionSignature liquidateTransition).paramTypes I.calldata with
    | none => exact hr.reEquivDecodingFailed hcode hd hdec
    | some args => exact hr.reEquivExecutionRevert hcode hd hdec (bodyReverts_nonPayable hwv)

end Benchmarks.Midnight
