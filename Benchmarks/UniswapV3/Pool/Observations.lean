import Benchmarks.UniswapV3.Pool.Dispatch
import Benchmarks.UniswapV3.Pool.Calldata
import Benchmarks.UniswapV3.Pool.ObservationStorage
import Benchmarks.UniswapV3.Pool.TupleReturn

/-!
# UniswapV3Pool `observations(uint256)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 737; reach lemma `uniswapV3PoolReachObservationsBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV3.Pool.Immutables

open uniswapV3PoolBlocks

namespace Benchmarks.UniswapV3.Pool

set_option maxRecDepth 2000000

def observationsReturnItems (index : UInt256) (σ : AccountMap) (I : ExecutionEnv) : List (ABIType × Value × EVM.Word) :=
  [(.elem (.int (.uint ⟨32, by decide⟩)), .int (Int.ofNat (observationFieldWord index 0 4 σ I).toNat), observationFieldWord index 0 4 σ I),
   (.elem (.int (.sint ⟨56, by decide⟩)), .int (observationTickValue index σ I), EVM.wordOfInt (observationTickValue index σ I)),
   (.elem (.int (.uint ⟨160, by decide⟩)), .int (Int.ofNat (observationFieldWord index 11 20 σ I).toNat), observationFieldWord index 11 20 σ I),
   (.elem (.bool), wordToElem .bool (observationFieldWord index 31 1 σ I), UInt256.isZero (UInt256.isZero (observationFieldWord index 31 1 σ I)))]

def observationsReturnValues (index : UInt256) (σ : AccountMap) (I : ExecutionEnv) : List Value :=
  (observationsReturnItems index σ I).map (·.2.1)

def observationsReturnWords (index : UInt256) (σ : AccountMap) (I : ExecutionEnv) : List UInt256 :=
  (observationsReturnItems index σ I).map (·.2.2)

theorem uniswapV3PoolObservationsReturns (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (locals : Store) (index : UInt256) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hbase : locals.get? "observations" = none)
    (hindex : locals.get? "arg0" = some (.int (Int.ofNat index.toNat))) (hin : index.toNat < 65535) :
    ExecTransitionBody config contract evm locals observationsTransition.body
      (.returned { contract := contract, locals := locals, immutables := immStore v } evm
        (some (observationsReturnValues index evm.accountMap evm.executionEnv))) (immStore v) := by
  apply ExecFuncBody.execBlockRet
  apply ABlock.returnsMany (ABlock.start.requireStep (evalCallvalueEq_true hwv))
  simp only [evalExprs?.eq_def,
    evalObservationBlockTimestamp locals (immStore v) evm index hbase hindex hin,
    evalObservationTickCumulative locals (immStore v) evm index hbase hindex hin,
    evalObservationSecondsPerLiquidityCumulativeX128 locals (immStore v) evm index hbase hindex hin,
    evalObservationInitialized locals (immStore v) evm index hbase hindex hin, EvalResult.bind, bind, pure,
    observationsReturnValues, observationsReturnItems, List.map_cons, List.map_nil]

theorem uniswapV3PoolObservationsOutOfBounds (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (locals : Store) (index : UInt256) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hbase : locals.get? "observations" = none)
    (hindex : locals.get? "arg0" = some (.int (Int.ofNat index.toNat))) (hout : ¬ index.toNat < 65535) :
    ExecTransitionBody config contract evm locals observationsTransition.body .reverted (immStore v) := by
  apply ExecFuncBody.execBlockRevert
  apply (ABlock.start.requireStep (evalCallvalueEq_true hwv)).run
  apply ExecBlock.consRevert
  apply ExecStmt.returnRevert
  simp only [evalExprs?.eq_def,
    evalObservationFieldOutOfBounds "blockTimestamp" locals (immStore v) evm index hbase hindex hout,
    EvalResult.bind, bind]

theorem observationsReturnEncoding (index : UInt256) (σ : AccountMap) (I : ExecutionEnv) :
    encodeReturnValues? observationsTransition.returnType (observationsReturnValues index σ I) =
      some (wordBytes (observationsReturnWords index σ I)) := by
  have h := staticWordsReturnEncoding (observationsReturnItems index σ I) 128
    (by simp only [observationsReturnItems, List.map_cons, List.map_nil, abiTupleHeadSize?,
          staticABIEncodedSize?, isDynamicABIType, bind, Option.bind]; rfl)
    (by intro x hx
        simp only [observationsReturnItems, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl <;> rfl)
    (by intro x hx
        simp only [observationsReturnItems, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl
        · exact encodeABIValue_uint ⟨32, by decide⟩ (observationFieldWord index 0 4 σ I)
            (u256LandMaskToNatLtOfToNat (bits := 32) _ _ (by native_decide))
        · simpa only [observationTickValue] using encodeABIValue_sintCast ⟨56, by decide⟩
            (UInt256.div (solcSlotWordAt (observationSlot index) σ I) (UInt256.ofNat (2 ^ 32)))
        · exact encodeABIValue_uint ⟨160, by decide⟩ (observationFieldWord index 11 20 σ I)
            (u256LandMaskToNatLtOfToNat (bits := 160) _ _ (by native_decide))
        · exact encodeABIValue_boolWord (observationFieldWord index 31 1 σ I))
  rw [wordBytes_eq_list]
  simpa only [observationsReturnWords, observationsReturnValues, List.flatMap_map, Function.comp_def] using h

def observationsCleanWords (a b c d : UInt256) : List UInt256 :=
  [UInt256.land a (UInt256.ofNat 4294967295),
   UInt256.signextend (UInt256.ofNat 6) b,
   UInt256.land c (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)),
   UInt256.isZero (UInt256.isZero d)]

theorem observationsReturnX {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : Nat} {v : UniswapV3PoolImmutables} {a b c d aw : UInt256} {R : List UInt256}
    {rdata : ByteArray} {acc : AccountMap}
    (h : RD (deployedRuntime v) ee g s0 ⟨766⟩ (d :: c :: b :: a :: R)
      solcFreePtrMem aw rdata acc k C) (hov : R.length + 7 ≤ 1024) :
    RDret (deployedRuntime v) g s0 acc (wordBytes (observationsCleanWords a b c d)) := by
  have hret := uniswapV3Pool_block_766 (immWords := wordsOf (immStore v)) hov h
  have hload : memLoad (UInt256.ofNat 64) solcFreePtrMem = ⟨128⟩ := solcFreePtrMem_mload64
  simp only [hload, show (⟨128⟩ : UInt256).toNat = 128 from rfl,
    show ((⟨128⟩ : UInt256) + UInt256.ofNat 32).toNat = 160 from by native_decide,
    show (UInt256.ofNat 64 + (⟨128⟩ : UInt256)).toNat = 192 from by native_decide,
    show ((⟨128⟩ : UInt256) + UInt256.ofNat 96).toNat = 224 from by native_decide] at hret
  have hfirst : (UInt256.land a (UInt256.ofNat 4294967295)).toByteArray.write 0
      solcFreePtrMem 128 32 = returnMem [UInt256.land a (UInt256.ofNat 4294967295)] :=
    returnMem_single _
  simp only [hfirst,
    returnMem_write_at [UInt256.land a (UInt256.ofNat 4294967295)] (UInt256.signextend (UInt256.ofNat 6) b) 160 rfl,
    returnMem_write_at [UInt256.land a (UInt256.ofNat 4294967295), UInt256.signextend (UInt256.ofNat 6) b] (UInt256.land c (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) 192 rfl,
    returnMem_write_at [UInt256.land a (UInt256.ofNat 4294967295), UInt256.signextend (UInt256.ofNat 6) b, UInt256.land c (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))] (UInt256.isZero (UInt256.isZero d)) 224 rfl,
    List.cons_append, List.nil_append] at hret
  rw [returnMem_mload64] at hret
  simp only [show (⟨128⟩ : UInt256).toNat = 128 from rfl,
    show (UInt256.ofNat 128 + UInt256.sub ⟨128⟩ ⟨128⟩).toNat = 128 from by native_decide] at hret
  have hread := returnMem_read128 (observationsCleanWords a b c d)
    (by change 0 < 4; decide) (by change 128 < 2 ^ 64; decide)
  change (returnMem (observationsCleanWords a b c d)).readWithPadding 128 128 = _ at hread
  dsimp only [observationsCleanWords] at hread
  rwa [hread] at hret

theorem uniswapV3PoolObservationsDecodedX {σ σ₀ A I} {g : Sat256} (v : UniswapV3PoolImmutables)
    (hcode : I.code = deployedRuntime v) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (uniswapV3PoolSelBytes 4)) (hlen : 36 ≤ I.calldata.size) :
    ∃ k C, RD (deployedRuntime v) I g (initState σ σ₀ g A I) ⟨5334⟩
      [calldataWord I.calldata 4, UInt256.ofNat 766, solcSelectorWord I]
      solcFreePtrMem ⟨3⟩ ByteArray.empty σ k C := by
  obtain ⟨k, C, rdEntry⟩ := uniswapV3PoolReachObservationsBody (g := g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode hwv hsz hsize hsel
  have rdDecode := uniswapV3Pool_block_737_taken (immWords := wordsOf (immStore v))
    (by simp) (by rw [solcDecodeLenCheckOkUnsigned (by exact hlen) hsize]; decide)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdEntry
  simp only [uniswapV3Pool_block_737_taken_stack] at rdDecode
  have rdRead := uniswapV3Pool_block_759 (immWords := wordsOf (immStore v))
    (by simp) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdDecode
  exact ⟨_, _, rdRead⟩

theorem uniswapV3PoolObservationsX {σ σ₀ A I} {g : Sat256} (v : UniswapV3PoolImmutables)
    (hcode : I.code = deployedRuntime v) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (uniswapV3PoolSelBytes 4)) (hlen : 36 ≤ I.calldata.size)
    (hin : (calldataWord I.calldata 4).toNat < 65535) :
    RDret (deployedRuntime v) g (initState σ σ₀ g A I) σ
      (wordBytes (observationsReturnWords (calldataWord I.calldata 4) σ I)) := by
  obtain ⟨k, C, rdRead⟩ := uniswapV3PoolObservationsDecodedX (g := g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode hwv hsz hsize hsel hlen
  have rdLoad := uniswapV3Pool_block_5334_taken (immWords := wordsOf (immStore v))
    (by simp) (by rw [ult_one (by exact hin)]; decide)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdRead
  simp only [uniswapV3Pool_block_5334_taken_stack] at rdLoad
  obtain ⟨k', C', rdValues⟩ := uniswapV3Pool_block_5351 (immWords := wordsOf (immStore v))
    (by simp) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdLoad
  simp only [uniswapV3Pool_block_5351_stack] at rdValues
  have hret := observationsReturnX (v := v) rdValues (by simp)
  have hmask160 : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 160 - 1) := by native_decide
  simp only [observationsCleanWords, hmask160,
    u256_land_comm (UInt256.ofNat (2 ^ 160 - 1)), maskTwice,
    signextend_idem ⟨56, by decide⟩ (UInt256.ofNat 6) _ (by native_decide) (by native_decide)] at hret
  rw [signextend_normalizeSint ⟨56, by decide⟩ (UInt256.ofNat 6) _
    (by native_decide) (by native_decide)] at hret
  simp only [show UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 88) =
      UInt256.ofNat (2 ^ 88) from by native_decide,
    show UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 248) =
      UInt256.ofNat (2 ^ 248) from by native_decide] at hret
  simpa only [observationsReturnWords, observationsReturnItems, List.map_cons, List.map_nil,
    observationFieldWord, observationTickValue, observationSlot, solcSlotWordAt, Nat.pow_zero,
    show UInt256.ofNat 1 = (⟨1⟩ : UInt256) from rfl,
    show UInt256.ofNat (256 ^ 11) = UInt256.ofNat (2 ^ 88) from by native_decide,
    show UInt256.ofNat (256 ^ 31) = UInt256.ofNat (2 ^ 248) from by native_decide,
    show UInt256.ofNat (256 ^ 4 - 1) = UInt256.ofNat 4294967295 from by native_decide,
    show UInt256.ofNat (256 ^ 20 - 1) = UInt256.ofNat (2 ^ 160 - 1) from by native_decide,
    show UInt256.ofNat (256 ^ 1 - 1) = UInt256.ofNat 255 from by native_decide,
    word_div_one, u256_land_comm (UInt256.ofNat 255)] using hret

theorem uniswapV3PoolObservationsOutOfBoundsX {σ σ₀ A I} {g : Sat256} (v : UniswapV3PoolImmutables)
    (hcode : I.code = deployedRuntime v) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (uniswapV3PoolSelBytes 4)) (hlen : 36 ≤ I.calldata.size)
    (hout : ¬ (calldataWord I.calldata 4).toNat < 65535) :
    RDrev (deployedRuntime v) g (initState σ σ₀ g A I) := by
  obtain ⟨k, C, rdRead⟩ := uniswapV3PoolObservationsDecodedX (g := g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode hwv hsz hsize hsel hlen
  have rdRevert := uniswapV3Pool_block_5334_fallthrough (immWords := wordsOf (immStore v))
    (by simp) (ult_zero (by change 65535 ≤ _; omega)) rdRead
  exact uniswapV3Pool_block_5347 (immWords := wordsOf (immStore v))
    (by simp [uniswapV3Pool_block_5334_fallthrough_stack]) rdRevert

theorem uniswapV3PoolObservationsShortX {σ σ₀ A I} {g : Sat256} (v : UniswapV3PoolImmutables)
    (hcode : I.code = deployedRuntime v) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (uniswapV3PoolSelBytes 4)) (hshort : I.calldata.size < 36) :
    RDrev (deployedRuntime v) g (initState σ σ₀ g A I) := by
  obtain ⟨k, C, rdEntry⟩ := uniswapV3PoolReachObservationsBody (g := g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode hwv hsz hsize hsel
  have rdRevert := uniswapV3Pool_block_737_fallthrough (immWords := wordsOf (immStore v))
    (by simp) (by rw [solcDecodeLenCheckShortUnsigned (by exact hsz) (by exact hshort) hsize]; decide)
    rdEntry
  exact uniswapV3Pool_block_755 (immWords := wordsOf (immStore v))
    (by simp [uniswapV3Pool_block_737_fallthrough_stack]) rdRevert

/-- `observations(uint256)`: the theorem `Correct.lean` routes selector 4 to. -/
theorem uniswapV3PoolObservationsBody {σ σ₀ A I} {g : UInt256} (v : UniswapV3PoolImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (uniswapV3PoolSelBytes 4)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (uniswapV3PoolSelBytes 4) rfl hsel
  have hd : dispatchMsg contract I.calldata = some observationsTransition := by
    apply uniswapV3PoolDispatch_observations <;>
      first | exact hsel | exact selectorMismatch_of_match hsel (by decide +kernel)
  by_cases hlen : 36 ≤ I.calldata.size
  · have hdec : decodeCalldataWithMode config.abiDecodeMode
        (observationsTransition.params.map Param.name)
        (transitionSignature observationsTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "arg0" (.int (Int.ofNat (calldataWord I.calldata 4).toNat))) := by
      simpa only [normalizeInt_uint256_word] using
        decodeCalldata_legacyInt_ok (.uint ⟨256, by decide⟩) (x := "arg0") hlen
    by_cases hin : (calldataWord I.calldata 4).toNat < 65535
    · exact (uniswapV3PoolObservationsX (g := Sat256.ofUInt256 g) v hcode hwv hsz hsize hsel hlen hin)
        |>.reEquivExecution hcode hd hdec
          (uniswapV3PoolObservationsReturns v _ _ (calldataWord I.calldata 4) hwv
            (by simp) (by simp) hin)
          (returnEquiv.returned rfl (observationsReturnEncoding (calldataWord I.calldata 4) σ I))
    · exact RDrev.reEquivExecutionRevert hcode
        (uniswapV3PoolObservationsOutOfBoundsX (g := Sat256.ofUInt256 g) v hcode hwv hsz hsize hsel hlen hin)
        hd hdec (uniswapV3PoolObservationsOutOfBounds v _ _ (calldataWord I.calldata 4) hwv
          (by simp) (by simp) hin)
  · have hshort : I.calldata.size < 36 := by omega
    have hdec : decodeCalldataWithMode config.abiDecodeMode
        (observationsTransition.params.map Param.name)
        (transitionSignature observationsTransition).paramTypes I.calldata = none :=
      decodeCalldata_legacyInt_none_short (.uint ⟨256, by decide⟩) hsz hshort
    exact RDrev.reEquivDecodingFailed hcode
      (uniswapV3PoolObservationsShortX (g := Sat256.ofUInt256 g) v hcode hwv hsz hsize hsel hshort)
      hd hdec

end Benchmarks.UniswapV3.Pool
