import Benchmarks.Midnight.Dispatch
import Benchmarks.Midnight.TakeEntryLoads
import Benchmarks.Midnight.TakeAuthorization
import Benchmarks.Midnight.TakeAfterAuthFinish

variable {fork : Ethereum.Fork}

/-!
# Midnight `take(((uint256,address,address,(address,uint256,uint256,address)[],uint256,uint256,address,address),bool,address,uint256,uint256,uint256,bytes32,address,bytes,address,address,bool,uint128,uint128,uint256),bytes,uint256,address,address,address,bytes)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Stele body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 10407; reach lemma `midnightReachTakeBody`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

/-- `take(((uint256,address,address,(address,uint256,uint256,address)[],uint256,uint256,address,address),bool,address,uint256,uint256,uint256,bytes32,address,bytes,address,address,bool,uint128,uint128,uint256),bytes,uint256,address,address,address,bytes)`: the theorem `Correct.lean` routes selector 18 to. -/
theorem midnightTakeBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = midnightBytecode) (hsize : I.calldata.size < UInt256.size)
    (hfork : fork ≥ .osaka)
    (hgas : midnightGasBound g)
    (hsel : selIs I (midnightSelBytes 18)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (midnightSelBytes 18) rfl hsel
  have hd : dispatchMsg contract I.calldata = some takeTransition := by
    apply midnightDispatch_take <;>
      first | exact hsel | exact selectorNe_of_selIs hsel (by decide +kernel)
  obtain ⟨k, C, rd⟩ := midnightReachTakeBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
  change RD fork midnightBytecode I (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
    ⟨10407⟩ [solcSelectorWord I] midnightEntryMemory (UInt256.ofNat 26) ByteArray.empty σ k C at rd
  have ha : MemoryAccounting midnightEntryMemory (UInt256.ofNat 26) C := by
    refine ⟨MemoryPaid.entry C, ?_⟩
    change midnightEntryMemory.size ≤ 832
    rw [midnightEntryMemory_size]
  have hm : 832 ≤ midnightEntryMemory.size := by rw [midnightEntryMemory_size]
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := midnightBlocks.midnight_block_10407_fallthrough (by simp) hwv rd
    have ha1 := memoryAccountingAt rd1 (by memory_account ha)
    have hselector : ¬ 0xac9650d8 = (bytesToWord (I.calldata.toList.take 4)).toNat := by
      rw [calldataSelector_of_selIs hsel]
      decide +kernel
    rcases midnightTakeEntry (by simp) hsz hsize hselector hm midnightEntryMemory_freePtr
        ha1 rd1 with
      ⟨hdec, hr⟩ | ⟨offer, ratifierData, data, hdec, hdecodeOffer, hdecodeRatifier, hdecodeData,
        hv, h228, hhi, mem2, callbackPtr, ratifierPtr, takerPtr, root, aw2, k2, C2,
        hcallbackPtr, hratifierPtr, htakerPtr, hroot, hi, hfree, hused, hk2, ha2, rd2⟩
    · exact hr.reEquivDecodingFailed hcode hd hdec
    · let origin := initState σ σ₀ (Sat256.ofUInt256 g) A I
      let units := calldataWord I.calldata 68
      let taker := calldataWord I.calldata 100
      let receiver := AccountAddress.ofNat (calldataWord I.calldata 132).toNat
      let callback := AccountAddress.ofNat (calldataWord I.calldata 164).toNat
      have hlimit : I.calldata.size < calldataLimit := by
        change I.calldata.size < 2^255 + 4
        omega
      have hc := decodeCalldataOffer_canonical hdecodeOffer
      have hmem2 : 832 ≤ mem2.size := by
        have hh := hk2.size
        rw [memoryWordSnapshot_length] at hh
        exact hh
      have htaker2 : memLoad (UInt256.ofNat 544) mem2 = taker :=
        (hk2.snapshot_load 14 (by decide)).trans (takeEntryMemory_taker hm)
      have hoffer2 : memLoad (UInt256.ofNat 384) mem2 = ⟨832⟩ :=
        (hk2.snapshot_load 9 (by decide)).trans (takeEntryMemory_root hm)
      have hzero2 : memLoad (UInt256.ofNat 96) mem2 = ⟨0⟩ := by
        apply (hk2.snapshot_load 0 (by decide)).trans
        apply (takeEntryMemory_load hm (UInt256.ofNat 96) (by
          rw [midnightEntryMemory_size]; decide) (by decide) (Or.inl (by decide))
          (Or.inl (by decide)) (Or.inl (by decide)) (Or.inl (by decide))).trans
        native_decide
      have hreceiver2 : memLoad (UInt256.ofNat 288) mem2 = UInt256.ofNat receiver.val :=
        ((hk2.snapshot_load 6 (by decide)).trans (takeEntryMemory_receiver hm)).trans
          (addressWord_eq_ofNat_address hv.2.1).symm
      have hcallback2 : memLoad (UInt256.ofNat 192) mem2 = UInt256.ofNat callback.val :=
        ((hk2.snapshot_load 3 (by decide)).trans (takeEntryMemory_callback ..)).trans
          (addressWord_eq_ofNat_address hv.2.2).symm
      rcases midnightTakeAuthorization origin rfl (by simp) (by omega) htaker2 hv.1 ha2 rd2 with
        ⟨hbad, hr⟩ | ⟨hauth, mem3, aw3, k3, C3, hp3, hsize3, hfree3, ha3, rd3⟩
      · apply hr.reEquivExecutionRevert hcode hd hdec
        apply ExecFuncBody.execBlockRevert
        apply guardedBodyBlock hwv hlimit
        apply ExecBlock.consRevert (ExecStmt.requireFalse ?_)
        exact (takeAuthEval origin offer ratifierData units taker receiver callback data hv.1).trans
          (by rw [decide_eq_false hbad])
      · have hbase : (writeWord mem2 320 takerPtr).size = mem2.size := by
          rw [writeWord_sparse_size]; omega
        have hread (off : UInt256) (hl : 96 ≤ off.toNat) (hh : off.toNat + 32 ≤ 832)
            (hdisj : off.toNat + 32 ≤ 320 ∨ 352 ≤ off.toNat) :
            memLoad off mem3 = memLoad off mem2 :=
          (hp3.load off hl (hh.trans hmem2) (by rw [hbase]; exact hh.trans hmem2)).trans
            (memLoad_writeWord_preserved _ _ _ _ (hh.trans hmem2) hdisj)
        have hdata3 : memLoad (UInt256.ofNat 320) mem3 = takerPtr :=
          (hp3.load (UInt256.ofNat 320) (by decide) (by change 352 ≤ _; omega)
            (by rw [hbase]; change 352 ≤ _; omega)).trans
              (memLoad_writeWord mem2 (UInt256.ofNat 320) takerPtr)
        have hi3 := (hi.writeWord_below (off := 320) takerPtr (by decide)).preserve
          (hp3.mono hused)
        rcases midnightTakeAfterAuthFinish (origin := origin) (R := []) (by decide) hfork hgas hc
            hv.1 hi3 hroot (by rw [hsize3]; exact hused) ha3 (hfree3.trans hfree)
            ((hread _ (by decide) (by decide) (Or.inl (by decide))).trans hzero2)
            ((hread _ (by decide) (by decide) (Or.inr (by decide))).trans hoffer2) hdata3
            ((hread _ (by decide) (by decide) (Or.inl (by decide))).trans hreceiver2)
            ((hread _ (by decide) (by decide) (Or.inl (by decide))).trans hcallback2)
            ((hread _ (by decide) (by decide) (Or.inr (by decide))).trans htaker2) rfl rd3 with
          hoog | ⟨hx, hr⟩ | ⟨hx, hr⟩ | ⟨bought, sold, frame', evm', hx, hr⟩
        · exact reEquiv_outOfGas (Xi_error_of_X (by rw [← hcode] at hoog; exact hoog))
        · exact hr.reEquivStaticHalt hcode hd hdec (ExecFuncBody.execBlockStatic
            (takeAfterAuthSource hv.1 hwv hlimit hauth hx))
        · exact hr.reEquivExecutionRevert hcode hd hdec (ExecFuncBody.execBlockRevert
            (takeAfterAuthSource hv.1 hwv hlimit hauth hx))
        · exact hr.reEquivExecutionGen hcode hd hdec (ExecFuncBody.execBlockRet
            (takeAfterAuthSource hv.1 hwv hlimit hauth hx)) rfl
            (returnEquiv.returned rfl (takeReturnEncoding bought sold))
  · have rd1 := midnightBlocks.midnight_block_10407_taken (by simp) hwv (by jump_dest) rd
    have hr := midnightBlocks.midnight_block_6350 (by simp) rd1
    cases hdec : config.externalABI.decodeCalldata? (takeTransition.params.map Param.name)
        (transitionSignature takeTransition).paramTypes I.calldata with
    | none => exact hr.reEquivDecodingFailed hcode hd hdec
    | some args => exact hr.reEquivExecutionRevert hcode hd hdec (bodyReverts_nonPayable hwv)

end Benchmarks.Midnight
