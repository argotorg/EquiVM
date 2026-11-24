import Benchmarks.EAS.EAS.TimeArrayEntry
import Benchmarks.EAS.EAS.TimestampLoop
import Benchmarks.EAS.EAS.TimeArrayRead

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

private theorem multiTimestamp_body : multiTimestampTransition.body =
    timeArrayPrefix ++ [timestampArrayLoop, .return [.var "time"]] := by native_decide

theorem easMultiTimestampBody {σ σ₀ A I} {g : UInt256} (v : EASImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (easSelBytes 17)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (easSelBytes 17) rfl hsel
  have hd : dispatchMsg contract I.calldata = some multiTimestampTransition := by
    apply easDispatch_multiTimestamp (hsel := hsel)
    all_goals
      change ¬ (_ == I.calldata.extract 0 4) = true
      rw [← byteArray_eq_of_beq hsel]
      decide +kernel
  have hplans : easPlans (bytesToWord (I.calldata.toList.take 4)).toNat = [] :=
    easPlans_empty_of_selector hsel (by native_decide)
  obtain ⟨k, C, rd⟩ := easReachMultiTimestampBody (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  by_cases hv : I.weiValue = ⟨0⟩
  · have rd1 := easBlocks.eas_block_779_fallthrough (immWords := wordsOf (immStore v)) (by simp) hv rd
    by_cases h36 : 36 ≤ I.calldata.size
    · by_cases hbig : I.calldata.size < 2^255 + 4
      · have rd2 := easBlocks.eas_block_785_fallthrough (immWords := wordsOf (immStore v)) (by simp)
          (by rw [easCalldataSub4 hsz hsize]; exact solcDecodeLenCheckOk_4_32 h36 hbig hsize) rd1
        have hdec := easDecodeWordArray "data" h36 hbig hsize hplans
        by_cases ho : wordArrayOffset I.calldata ≤ solcMaxU64
        · have rd3 := easBlocks.eas_block_827_fallthrough (immWords := wordsOf (immStore v)) (by simp)
            (ugt_zero ho) rd2
          have rd4 := easBlocks.eas_block_845 (immWords := wordsOf (immStore v)) (by simp)
            (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd3
          have hr := easWordArrayDecode (ret := UInt256.ofNat 858) v (by simp) hsize ho
            (by rw [easPatchedValidJumps v]; jump_dest) rd4
          by_cases hok : wordArrayValid I.calldata
          · rw [if_pos hok] at hr hdec
            obtain ⟨k5, C5, rd5⟩ := hr
            have rd6 := easBlocks.eas_block_858 (immWords := wordsOf (immStore v)) (by simp) rd5
            let words := calldataWordList I.calldata (wordArrayOffset I.calldata + 36) (wordArrayLength I.calldata)
            have hlen : words.length = wordArrayLength I.calldata := by
              simp only [words, calldataWordList, List.length_map, List.length_range]
            have hlenbound : words.length < UInt256.size := by
              rw [hlen]
              exact (calldataWord I.calldata (4 + wordArrayOffset I.calldata)).val.isLt
            let args := (∅ : Store).insert "data" (wordArrayValue I.calldata)
            have hdata : args.get? "data" = some (.array (words.map wordBytes32Value)) := store_get_self _ _ _
            have hinv := timeArrayInitialInv (ee := I) hdata
            have hprefix := timeArrayPrefixSource (fork := fork) (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I)
              (imms := immStore v) hv hsz hsize (by change I.calldata.size - 4 < 2^255; omega) hdata
            have hread := calldataWordList_read (ee := I) rfl hok.2.2.2.2 hsize
            have hloop := timestampArrayLoop_correct (R := [solcSelectorWord I]) (imms := immStore v)
              (time := easTimeWord I) (start := UInt256.ofNat (wordArrayOffset I.calldata + 36))
              v words 224 hlenbound (by simp) hread
              words.length 0 (timeArrayLocals args I words) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
              _ _ _ _ (by omega) hinv rfl (by simpa only [hlen] using rd6)
            obtain (⟨locals', evm', hsource, hfinal, hout⟩ | ⟨hsource, hout⟩ | ⟨hsource, hout⟩) := hloop
            · refine RDret.reEquivExecutionGen
                (retVal := some [.int (Int.ofNat (easTimeWord I).toNat)])
                (cs := {contract := contract, locals := locals', immutables := immStore v})
                (evm'' := evm') hcode hout hd hdec ?_ rfl ?_
              · rw [multiTimestamp_body]
                apply ExecFuncBody.execBlockRet
                apply execBlock_append hprefix
                refine ExecBlock.consNormal hsource (ExecBlock.consReturn (ExecStmt.return ?_))
                simp only [evalExprs?, evalExpr?, hfinal.time, EvalResult.ofOption, EvalResult.bind, bind, pure]
              · exact returnEquiv_of_encode (uintReturnEncoding ⟨64, by decide⟩ (easTimeWord I)
                  (u256LandMaskToNatLtOfToNat _ _ (by decide)))
            · refine RDrev.reEquivExecutionRevert hcode hout hd hdec ?_
              rw [multiTimestamp_body]
              apply ExecFuncBody.execBlockRevert
              exact execBlock_append hprefix (ExecBlock.consRevert hsource)
            · refine RDstatic.reEquivStaticHalt hcode hout hd hdec ?_
              rw [multiTimestamp_body]
              apply ExecFuncBody.execBlockStatic
              exact execBlock_append hprefix (ExecBlock.consStatic hsource)
          · rw [if_neg hok] at hr hdec
            exact RDrev.reEquivDecodingFailed hcode hr hd hdec
        · have rd3 := easBlocks.eas_block_827_taken (immWords := wordsOf (immStore v)) (by simp)
            (ne_of_eq_of_ne (ugt_one (a := calldataWord I.calldata 4)
              (b := UInt256.ofNat 18446744073709551615) (Nat.lt_of_not_ge ho)) (by decide))
            (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd2
          have hr := easBlocks.eas_block_402 (immWords := wordsOf (immStore v)) (by simp [easBlocks.eas_block_827_taken_stack]) rd3
          rw [if_neg (by intro h; exact ho h.1)] at hdec
          exact RDrev.reEquivDecodingFailed hcode hr hd hdec
      · have rd2 := easBlocks.eas_block_785_taken (immWords := wordsOf (immStore v)) (by simp)
          (by rw [easCalldataSub4 hsz hsize]
              exact ne_of_eq_of_ne (solcDecodeLenCheckHuge_4_32 (by omega) hsize) (by decide))
          (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
        have hr := easBlocks.eas_block_402 (immWords := wordsOf (immStore v)) (by simp) rd2
        exact RDrev.reEquivDecodingFailed hcode hr hd
          (decodeWordArray_none_head "data" easPlanTable hsz
            (solcSLT_sub4_of_check (need := ⟨32⟩) (bit := true) (solcDecodeLenCheckHuge_4_32 (by omega) hsize)))
    · have rd2 := easBlocks.eas_block_785_taken (immWords := wordsOf (immStore v)) (by simp)
        (by rw [easCalldataSub4 hsz hsize]
            exact ne_of_eq_of_ne (solcDecodeLenCheckShort_4_32 hsz (by omega) hsize) (by decide))
        (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
      have hr := easBlocks.eas_block_402 (immWords := wordsOf (immStore v)) (by simp) rd2
      exact RDrev.reEquivDecodingFailed hcode hr hd
        (decodeWordArray_none_head "data" easPlanTable hsz
          (solcSLT_sub4_of_check (need := ⟨32⟩) (bit := true) (solcDecodeLenCheckShort_4_32 hsz (by omega) hsize)))
  · have rd1 := easBlocks.eas_block_779_taken (immWords := wordsOf (immStore v)) (by simp) hv
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    have hr := easBlocks.eas_block_402 (immWords := wordsOf (immStore v)) (by simp) rd1
    cases hdec : config.externalABI.decodeCalldata?
        (multiTimestampTransition.params.map Param.name)
        (transitionSignature multiTimestampTransition).paramTypes I.calldata with
    | none => exact RDrev.reEquivDecodingFailed hcode hr hd hdec
    | some args =>
      refine RDrev.reEquivExecutionRevert hcode hr hd hdec ?_
      rw [multiTimestamp_body, timeArrayPrefix, List.append_assoc, List.append_assoc]
      exact easEntryBody_value_revert hv

end Benchmarks.EAS.EAS
