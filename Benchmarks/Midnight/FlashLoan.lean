import Benchmarks.Midnight.Dispatch
import Benchmarks.Midnight.FlashLoanEntry
import Benchmarks.Midnight.FlashLoanEventLog
import Benchmarks.Midnight.FlashLoanTail
import Benchmarks.Midnight.MarketEntryDecode

/-!
# Midnight `flashLoan(address[],uint256[],address,bytes)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Stele body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 16032; reach lemma `midnightReachFlashLoanBody`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

/-- `flashLoan(address[],uint256[],address,bytes)`: the theorem `Correct.lean` routes selector 9 to. -/
theorem midnightFlashLoanBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = midnightBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwf : midnightWF σ I)
    (hgas : midnightGasBound g)
    (hsel : selIs I (midnightSelBytes 9)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (midnightSelBytes 9) rfl hsel
  have hd : dispatchMsg contract I.calldata = some flashLoanTransition := by
    apply midnightDispatch_flashLoan <;>
      first | exact hsel | exact selectorNe_of_selIs hsel (by decide +kernel)
  obtain ⟨k, C, rd⟩ := midnightReachFlashLoanBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
  change RD midnightBytecode I (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
    ⟨16032⟩ [solcSelectorWord I] midnightEntryMemory (UInt256.ofNat 26) ByteArray.empty σ k C at rd
  have ha : MemoryAccounting midnightEntryMemory (UInt256.ofNat 26) C := by
    refine ⟨MemoryPaid.entry C, ?_⟩
    change midnightEntryMemory.size ≤ 832
    rw [midnightEntryMemory_size]
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := midnightBlocks.midnight_block_16032_fallthrough (by simp) hwv rd
    have hselector : ¬ 0xac9650d8 = (bytesToWord (I.calldata.toList.take 4)).toNat := by
      rw [calldataSelector_of_selIs hsel]
      decide +kernel
    rcases midnightFlashLoanEntry (by simp) hsz hsize hselector rd1 with
      ⟨hdec, hr⟩ | ⟨_, ht, haRef, hcallback, hdRef, hdecode, k2, C2, hC2, rd2⟩
    · exact hr.reEquivDecodingFailed hcode hd hdec
    have hlimit : I.calldata.size < calldataLimit := by
      have hb := ht.2.1
      change I.calldata.size < 2^255 + 4
      omega
    have htn := ht.bounds.1
    have han := haRef.bounds.1
    have hdl := hdRef.bounds.1
    have htp : (calldataArgumentPointer I.calldata 4).toNat +
        32 * (calldataArgumentLength I.calldata 4).toNat ≤ I.calldata.size := ht.bounds.2
    have hap : (calldataArgumentPointer I.calldata 36).toNat +
        32 * (calldataArgumentLength I.calldata 36).toNat ≤ I.calldata.size := haRef.bounds.2
    have hdp : (calldataArgumentPointer I.calldata 100).toNat +
        (calldataArgumentLength I.calldata 100).toNat ≤ I.calldata.size := by
      simpa only [calldataSliceStride, if_true, Nat.one_mul] using hdRef.bounds.2
    have hdecode' := hdecode.trans (decodeFlashLoanArguments_valid ht haRef hcallback hdRef)
    let origin := initState σ σ₀ (Sat256.ofUInt256 g) A I
    let callback := AccountAddress.ofNat (calldataWord I.calldata 68).toNat
    have hcb : UInt256.ofNat callback.val = calldataWord I.calldata 68 :=
      u256_inj (by
        change (UInt256.ofNat ((calldataWord I.calldata 68).toNat % EVM.addressModulus)).toNat = _
        rw [Nat.mod_eq_of_lt hcallback]
        exact UInt256.toNat_ofNat_of_lt (calldataWord I.calldata 68).val.isLt)
    by_cases hlen : (calldataArgumentLength I.calldata 4).toNat =
        (calldataArgumentLength I.calldata 36).toNat
    · have he : calldataArgumentLength I.calldata 4 = calldataArgumentLength I.calldata 36 :=
        u256_inj hlen
      have rd3 := midnightBlocks.midnight_block_16153_fallthrough (by simp)
        (u256_sub_eq_zero_iff_eq.mpr he) rd2
      have ha3 := memoryAccountingAt rd3 ⟨ha.paid.mono (by omega), ha.covered⟩
      rcases midnightFlashLoanEventEncode (by simp) htn han (by omega) hcallback
          (by decide) midnightEntryMemory_freePtr ha3 rd3 with
        ⟨hnoncanon, hr⟩ | ⟨hcanon, aw4, k4, C4, _, ha4, rd4⟩
      · exact hr.reEquivDecodingFailed hcode hd
          (hdecode'.trans (if_neg hnoncanon))
      have hdec : config.externalABI.decodeCalldata? (flashLoanTransition.params.map Param.name)
          (transitionSignature flashLoanTransition).paramTypes I.calldata =
          some (flashLoanArguments (calldataArgumentWords I.calldata 4)
            (calldataArgumentWords I.calldata 36) callback (calldataArgumentBytes I.calldata 100)) :=
        hdecode'.trans (if_pos hcanon)
      have hf := flashLoanExternalFrame_spec origin (calldataArgumentWords I.calldata 4)
        (calldataArgumentWords I.calldata 36) callback (calldataArgumentBytes I.calldata 100)
      have sourcePrefix {result : ExecResult}
          (htail : ExecBlock config (flashLoanExternalFrame origin (calldataArgumentWords I.calldata 4)
            (calldataArgumentWords I.calldata 36) callback (calldataArgumentBytes I.calldata 100)) origin
            (flashLoanTransition.body.drop 4) result) :
          ExecBlock config
            { contract := contract
              locals := flashLoanArguments (calldataArgumentWords I.calldata 4)
                (calldataArgumentWords I.calldata 36) callback (calldataArgumentBytes I.calldata 100)
              immutables := ∅ } origin flashLoanTransition.body result :=
        flashLoanEntrySource hwv hlimit (by simpa only [calldataArgumentWords_length] using hlen) htail
      by_cases hp : I.perm = true
      · obtain ⟨aw5, k5, C5, _, ha5, rd5⟩ := midnightFlashLoanEventLog (by simp) hp ha4 rd4
        let emem := flashLoanEventMemory midnightEntryMemory I.calldata 832
          (calldataArgumentPointer I.calldata 4).toNat (calldataArgumentLength I.calldata 4).toNat
          (calldataArgumentPointer I.calldata 36).toNat (calldataArgumentLength I.calldata 36).toNat
        have hmem := flashLoanEventMemory_size midnightEntryMemory I.calldata 832
          (calldataArgumentPointer I.calldata 4).toNat (calldataArgumentLength I.calldata 4).toNat
          (calldataArgumentPointer I.calldata 36).toNat (calldataArgumentLength I.calldata 36).toNat hap
        change emem.size = _ at hmem
        have hload (read : UInt256) (hb : read.toNat + 32 ≤ 832) :
            memLoad read emem = memLoad read midnightEntryMemory :=
          flashLoanEventMemory_load_below _ _ _ _ _ _ _ _ hap
            (by rw [midnightEntryMemory_size]; exact hb) hb
        have hh : TransferHeap emem aw5 (UInt256.ofNat 832) C5 := by
          refine ⟨by rw [hmem, midnightEntryMemory_size]; omega, by decide, ?_, ?_, ?_, by decide, ?_⟩
          · rw [hload _ (by decide)]
            exact midnightEntryMemory_freePtr
          · rw [hload _ (by decide)]
            native_decide
          · have hc := ha5.covered
            change emem.size ≤ 32 * aw5.toNat at hc
            rw [hmem, midnightEntryMemory_size] at hc
            change 832 ≤ 32 * aw5.toNat
            omega
          · exact MemoryFunding.of_accounting ha5
        rw [← hcb] at rd5
        rcases midnightFlashLoanTail (by simp) hlen.symm htn hdl (by omega) hap hdp hsize
            hcanon hf hh hgas hwf (by exact ⟨rfl, rfl, rfl⟩) rd5 with
          hoog | ⟨hbody, hr⟩ | ⟨frame', evm', σ', hbody, hs', hr⟩
        · exact reEquiv_outOfGas (Xi_error_of_X (by rw [← hcode] at hoog; exact hoog))
        · exact hr.reEquivExecutionRevert hcode hd hdec
            (.execBlockRevert (sourcePrefix ((flashLoanEmit (evm := origin) hf hp).run hbody)))
        · rw [hs'.accounts] at hr
          exact hr.reEquivExecutionGen hcode hd hdec
            (.execBlockOK (sourcePrefix ((flashLoanEmit (evm := origin) hf hp).run hbody)))
            rfl voidReturnEquiv
      · have hp' : I.perm = false := Bool.eq_false_iff.mpr hp
        have hr := midnightFlashLoanEventStatic (by simp [flashLoanAfterEventStack]) hp' rd4
        exact hr.reEquivStaticHalt hcode hd hdec
          (.execBlockStatic (sourcePrefix (flashLoanEmitStatic hf hp')))
    · have hn : calldataArgumentLength I.calldata 4 ≠ calldataArgumentLength I.calldata 36 :=
        fun h ↦ hlen (congrArg UInt256.toNat h)
      have rd3 := midnightBlocks.midnight_block_16153_taken (by simp)
        (fun h ↦ hn (u256_sub_eq_zero_iff_eq.mp h)) (by jump_dest) rd2
      have hr := midnightBlocks.midnight_block_16593 (by simp [midnightBlocks.midnight_block_16153_taken_stack]) rd3
      by_cases hcanon : CanonicalAddressWords (calldataArgumentWords I.calldata 4)
      · exact hr.reEquivExecutionRevert hcode hd (hdecode'.trans (if_pos hcanon))
          (.execBlockRevert (flashLoanLengthRevertSource hwv hlimit
            (by simpa only [calldataArgumentWords_length] using hlen)))
      · exact hr.reEquivDecodingFailed hcode hd (hdecode'.trans (if_neg hcanon))
  · have rd1 := midnightBlocks.midnight_block_16032_taken (by simp) hwv (by jump_dest) rd
    have hr := midnightBlocks.midnight_block_6350 (by simp) rd1
    cases hdec : config.externalABI.decodeCalldata? (flashLoanTransition.params.map Param.name)
        (transitionSignature flashLoanTransition).paramTypes I.calldata with
    | none => exact hr.reEquivDecodingFailed hcode hd hdec
    | some args => exact hr.reEquivExecutionRevert hcode hd hdec (bodyReverts_nonPayable hwv)

end Benchmarks.Midnight
