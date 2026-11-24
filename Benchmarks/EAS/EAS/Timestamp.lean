import Benchmarks.EAS.EAS.TimestampEVM
import Benchmarks.EAS.EAS.ScalarDecode
import Benchmarks.EAS.EAS.ReturnWord
import Benchmarks.EAS.EAS.TimePublic

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

private def timestampPublicRest : Body := [
  .internalCall "_timestamp" [.var "data", .var "time", .var "$EAS.freeMemory"] "__c1$allocation",
  .letDecl "__c1" none (.tupleGet (.var "__c1$allocation") 0),
  .assign .localVar {base := "$EAS.freeMemory"} (.tupleGet (.var "__c1$allocation") 1),
  .return [.var "time"]]

private theorem timestampPublic_body : timestampTransition.body = easEntryPrefix ++ (timeEntryCall ++ timestampPublicRest) := by
  native_decide

private theorem timestampPublicArgs {evm : EVM.State} {locals imms : Store} {word : UInt256}
    (hkey : locals.get? "data" = some (wordBytes32Value word)) :
    evalExprs? config {contract := contract, locals := timeEntryLocals locals evm.executionEnv, immutables := imms}
      evm [.var "data", .var "time", .var "$EAS.freeMemory"] =
      .ok [wordBytes32Value word, .int (Int.ofNat (easTimeWord evm.executionEnv).toNat), .int (Int.ofNat (224 : Nat))] := by
  have hd := (timeEntry_data locals evm.executionEnv).trans hkey
  have ht := timeEntry_time locals evm.executionEnv
  have hh : (timeEntryLocals locals evm.executionEnv).get? "$EAS.freeMemory" = some (.int (Int.ofNat (224 : Nat))) :=
    store_get_self _ _ _
  simp only [evalExprs?, evalExpr?, hd, ht, hh, EvalResult.ofOption, EvalResult.bind, bind, pure]

private theorem timestampPublicSource_ok {evm : EVM.State} {locals imms : Store} {word : UInt256}
    (hv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsz : 4 ≤ evm.executionEnv.calldata.size)
    (hsize : evm.executionEnv.calldata.size < UInt256.size)
    (hs : evm.executionEnv.calldata.size - 4 < 2^255)
    (hkey : locals.get? "data" = some (wordBytes32Value word))
    (hz : timestampWord evm word = ⟨0⟩)
    (hperm : evm.executionEnv.perm = true) :
    ExecTransitionBody fork config contract evm locals timestampTransition.body
      (.returned {contract := contract, locals := timePublicFinalLocals locals evm.executionEnv, immutables := imms}
        (timestampStore evm word (easTimeWord evm.executionEnv))
        (some [.int (Int.ofNat (easTimeWord evm.executionEnv).toNat)])) imms := by
  rw [timestampPublic_body, ← List.append_assoc]
  apply ExecFuncBody.execBlockRet
  apply execBlock_append (timeEntrySource hv hsz hsize hs)
  exact timePublicFinish (timestampCall_ok (fork := fork) (hperm := hperm) (timestampPublicArgs hkey) hz)

private theorem timestampPublicSource_revert {evm : EVM.State} {locals imms : Store} {word : UInt256}
    (hv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsz : 4 ≤ evm.executionEnv.calldata.size)
    (hsize : evm.executionEnv.calldata.size < UInt256.size)
    (hs : evm.executionEnv.calldata.size - 4 < 2^255)
    (hkey : locals.get? "data" = some (wordBytes32Value word))
    (hz : timestampWord evm word ≠ ⟨0⟩) :
    ExecTransitionBody fork config contract evm locals timestampTransition.body .reverted imms := by
  rw [timestampPublic_body, ← List.append_assoc]
  apply ExecFuncBody.execBlockRevert
  apply execBlock_append (timeEntrySource hv hsz hsize hs)
  exact ExecBlock.consRevert (timestampCall_revert (timestampPublicArgs hkey) hz)

private theorem timestampPublicSource_static {evm : EVM.State} {locals imms : Store} {word : UInt256}
    (hv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsz : 4 ≤ evm.executionEnv.calldata.size)
    (hsize : evm.executionEnv.calldata.size < UInt256.size)
    (hs : evm.executionEnv.calldata.size - 4 < 2^255)
    (hkey : locals.get? "data" = some (wordBytes32Value word))
    (hz : timestampWord evm word = ⟨0⟩) (hp : evm.executionEnv.perm = false) :
    ExecTransitionBody fork config contract evm locals timestampTransition.body .staticViolation imms := by
  rw [timestampPublic_body, ← List.append_assoc]
  apply ExecFuncBody.execBlockStatic
  apply execBlock_append (timeEntrySource hv hsz hsize hs)
  exact ExecBlock.consStatic (timestampCall_static (timestampPublicArgs hkey) hz hp)

theorem easTimestampBody {σ σ₀ A I} {g : UInt256} (v : EASImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (easSelBytes 6)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (easSelBytes 6) rfl hsel
  have hd : dispatchMsg contract I.calldata = some timestampTransition := by
    apply easDispatch_timestamp (hsel := hsel)
    all_goals
      change ¬ (_ == I.calldata.extract 0 4) = true
      rw [← byteArray_eq_of_beq hsel]
      decide +kernel
  obtain ⟨k, C, rd⟩ := easReachTimestampBody (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  by_cases hv : I.weiValue = ⟨0⟩
  · have rd1 := easBlocks.eas_block_3208_fallthrough (immWords := wordsOf (immStore v)) (by simp) hv rd
    by_cases h36 : 36 ≤ I.calldata.size
    · by_cases hbig : I.calldata.size < 2^255 + 4
      · have rd2 := easBlocks.eas_block_3214_fallthrough (immWords := wordsOf (immStore v)) (by simp)
          (by rw [easCalldataSub4 hsz hsize]; exact solcDecodeLenCheckOk_4_32 h36 hbig hsize) rd1
        have rd3 := easBlocks.eas_block_3256 (immWords := wordsOf (immStore v)) (by simp)
          (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd2
        let word := calldataWord I.calldata 4
        let time := easTimeWord I
        have hdec : config.externalABI.decodeCalldata?
            (timestampTransition.params.map Param.name)
            (transitionSignature timestampTransition).paramTypes I.calldata =
            some ((∅ : Store).insert "data" (wordBytes32Value word)) :=
          easDecodeBytes32_ok "data" h36 hbig hsize
        have hs : I.calldata.size - 4 < 2^255 := by omega
        by_cases hz : UInt256.land (solcSlotWord σ I (timestampSlot word)) easUint64Mask = ⟨0⟩
        · have hsourcezero : timestampWord (initState σ σ₀ (Sat256.ofUInt256 g) A I) word = ⟨0⟩ := by
            rw [timestampWord_solc]
            exact hz
          by_cases hp : I.perm = true
          · obtain ⟨aw4, k4, C4, rd4⟩ := easTimestamp_ok v
              (word := word) (time := time) (ret := UInt256.ofNat 771)
              (by simp) hz hp (by rw [easPatchedValidJumps v]; jump_dest) rd3
            have hr := easReturnWord v (by simp) rd4
            refine RDret.reEquivExecutionGen hcode hr hd hdec
              (timestampPublicSource_ok (fork := fork) (hperm := hp) hv hsz hsize hs (store_get_self _ _ _) hsourcezero) ?_ ?_
            · exact (timestampStore_accounts (initState σ σ₀ (Sat256.ofUInt256 g) A I) word time).symm
            · exact returnEquiv_of_encode (uintReturnEncoding ⟨64, by decide⟩ time
                (u256LandMaskToNatLtOfToNat _ _ (by decide)))
          · have hp' : I.perm = false := Bool.eq_false_iff.mpr hp
            have hr := easTimestamp_static v (word := word) (time := time) (ret := UInt256.ofNat 771)
              (by simp) hz hp' rd3
            exact RDstatic.reEquivStaticHalt hcode hr hd hdec
              (timestampPublicSource_static hv hsz hsize hs (store_get_self _ _ _) hsourcezero hp')
        · have hsourcezero : timestampWord (initState σ σ₀ (Sat256.ofUInt256 g) A I) word ≠ ⟨0⟩ := by
            rw [timestampWord_solc]
            exact hz
          have hr := easTimestamp_revert v (word := word) (time := time) (by simp) hz rd3
          exact RDrev.reEquivExecutionRevert hcode hr hd hdec
            (timestampPublicSource_revert hv hsz hsize hs (store_get_self _ _ _) hsourcezero)
      · have rd2 := easBlocks.eas_block_3214_taken (immWords := wordsOf (immStore v)) (by simp)
          (by rw [easCalldataSub4 hsz hsize]
              exact ne_of_eq_of_ne (solcDecodeLenCheckHuge_4_32 (by omega) hsize) (by decide))
          (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
        have hr := easBlocks.eas_block_402 (immWords := wordsOf (immStore v)) (by simp) rd2
        exact RDrev.reEquivDecodingFailed hcode hr hd
          (easDecodeScalar_none_huge "data" (.bytes abiBytes32Width) (by omega) hsize)
    · have rd2 := easBlocks.eas_block_3214_taken (immWords := wordsOf (immStore v)) (by simp)
        (by rw [easCalldataSub4 hsz hsize]
            exact ne_of_eq_of_ne (solcDecodeLenCheckShort_4_32 hsz (by omega) hsize) (by decide))
        (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
      have hr := easBlocks.eas_block_402 (immWords := wordsOf (immStore v)) (by simp) rd2
      exact RDrev.reEquivDecodingFailed hcode hr hd
        (easDecodeScalar_none_short "data" (.bytes abiBytes32Width) hsz (by omega) hsize)
  · have rd1 := easBlocks.eas_block_3208_taken (immWords := wordsOf (immStore v)) (by simp) hv
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    have hr := easBlocks.eas_block_402 (immWords := wordsOf (immStore v)) (by simp) rd1
    cases hdec : config.externalABI.decodeCalldata?
        (timestampTransition.params.map Param.name)
        (transitionSignature timestampTransition).paramTypes I.calldata with
    | none => exact RDrev.reEquivDecodingFailed hcode hr hd hdec
    | some args =>
      refine RDrev.reEquivExecutionRevert hcode hr hd hdec ?_
      rw [timestampPublic_body]
      exact easEntryBody_value_revert hv


end Benchmarks.EAS.EAS
