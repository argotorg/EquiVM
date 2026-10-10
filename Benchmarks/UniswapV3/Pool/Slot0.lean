import Benchmarks.UniswapV3.Pool.Dispatch
import Benchmarks.UniswapV3.Pool.Slot0Storage
import Benchmarks.UniswapV3.Pool.TupleReturn

/-!
# UniswapV3Pool `slot0()`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 859; reach lemma `uniswapV3PoolReachSlot0Body`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks

namespace Benchmarks.UniswapV3.Pool

set_option maxRecDepth 2000000


def slot0ReturnItems (σ : AccountMap) (I : ExecutionEnv) : List (ABIType × Value × EVM.Word) :=
  [(.elem (.int (.uint ⟨160, by decide⟩)), .int (Int.ofNat (slot0FieldWord 0 20 σ I).toNat),
      slot0FieldWord 0 20 σ I),
    (.elem (.int (.sint ⟨24, by decide⟩)), .int (slot0TickValue σ I),
      EVM.wordOfInt (slot0TickValue σ I)),
    (.elem (.int (.uint ⟨16, by decide⟩)), .int (Int.ofNat (slot0FieldWord 23 2 σ I).toNat),
      slot0FieldWord 23 2 σ I),
    (.elem (.int (.uint ⟨16, by decide⟩)), .int (Int.ofNat (slot0FieldWord 25 2 σ I).toNat),
      slot0FieldWord 25 2 σ I),
    (.elem (.int (.uint ⟨16, by decide⟩)), .int (Int.ofNat (slot0FieldWord 27 2 σ I).toNat),
      slot0FieldWord 27 2 σ I),
    (.elem (.int (.uint ⟨8, by decide⟩)), .int (Int.ofNat (slot0FieldWord 29 1 σ I).toNat),
      slot0FieldWord 29 1 σ I),
    (.elem .bool, wordToElem .bool (slot0FieldWord 30 1 σ I),
      UInt256.isZero (UInt256.isZero (slot0FieldWord 30 1 σ I)))]

def slot0ReturnValues (σ : AccountMap) (I : ExecutionEnv) : List Value :=
  (slot0ReturnItems σ I).map (·.2.1)

def slot0ReturnWords (σ : AccountMap) (I : ExecutionEnv) : List UInt256 :=
  (slot0ReturnItems σ I).map (·.2.2)

theorem uniswapV3PoolSlot0Returns (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (locals : Store) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hbase : locals.get? "slot0" = none) :
    ExecTransitionBody config contract evm locals slot0Transition.body
      (.returned { contract := contract, locals := locals, immutables := immStore v } evm
        (some (slot0ReturnValues evm.accountMap evm.executionEnv))) (immStore v) := by
  apply ExecFuncBody.execBlockRet
  apply ABlock.returnsMany (ABlock.start.requireStep (evalCallvalueEq_true hwv))
  simp only [evalExprs?.eq_def, evalSlot0SqrtPriceX96 locals (immStore v) evm hbase,
    evalSlot0Tick locals (immStore v) evm hbase,
    evalSlot0ObservationIndex locals (immStore v) evm hbase,
    evalSlot0ObservationCardinality locals (immStore v) evm hbase,
    evalSlot0ObservationCardinalityNext locals (immStore v) evm hbase,
    evalSlot0FeeProtocol locals (immStore v) evm hbase,
    evalSlot0Unlocked locals (immStore v) evm hbase, EvalResult.bind, bind, pure,
    slot0ReturnValues, slot0ReturnItems, List.map_cons, List.map_nil]

set_option maxRecDepth 10000 in
theorem slot0ReturnEncoding (σ : AccountMap) (I : ExecutionEnv) :
    encodeReturnValues? slot0Transition.returnType (slot0ReturnValues σ I) =
      some (wordBytes (slot0ReturnWords σ I)) := by
  have h := staticWordsReturnEncoding (slot0ReturnItems σ I) 224
    (by simp only [slot0ReturnItems, List.map_cons, List.map_nil, abiTupleHeadSize?,
          staticABIEncodedSize?, isDynamicABIType, bind, Option.bind]; rfl)
    (by intro x hx
        simp only [slot0ReturnItems, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
    (by intro x hx
        simp only [slot0ReturnItems, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact encodeABIValue_uint ⟨160, by decide⟩ (slot0FieldWord 0 20 σ I)
            (u256LandMaskToNatLtOfToNat (bits := 160) _ _ (by native_decide))
        · simpa only [slot0TickValue] using encodeABIValue_sintCast ⟨24, by decide⟩
            (UInt256.div (solcSlotWordAt ⟨0⟩ σ I) (UInt256.ofNat (2 ^ 160)))
        · exact encodeABIValue_uint ⟨16, by decide⟩ (slot0FieldWord 23 2 σ I)
            (u256LandMaskToNatLtOfToNat (bits := 16) _ _ (by native_decide))
        · exact encodeABIValue_uint ⟨16, by decide⟩ (slot0FieldWord 25 2 σ I)
            (u256LandMaskToNatLtOfToNat (bits := 16) _ _ (by native_decide))
        · exact encodeABIValue_uint ⟨16, by decide⟩ (slot0FieldWord 27 2 σ I)
            (u256LandMaskToNatLtOfToNat (bits := 16) _ _ (by native_decide))
        · exact encodeABIValue_uint ⟨8, by decide⟩ (slot0FieldWord 29 1 σ I)
            (u256LandMaskToNatLtOfToNat (bits := 8) _ _ (by native_decide))
        · exact encodeABIValue_boolWord (slot0FieldWord 30 1 σ I))
  rw [wordBytes_eq_list]
  simpa only [slot0ReturnWords, slot0ReturnValues, List.flatMap_map, Function.comp_def] using h


def slot0CleanWords (a b c d e f j : UInt256) : List UInt256 :=
  [UInt256.land a (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
      (UInt256.ofNat 1)), UInt256.signextend (UInt256.ofNat 2) b,
    UInt256.land (UInt256.ofNat 65535) c, UInt256.land (UInt256.ofNat 65535) d,
    UInt256.land (UInt256.ofNat 65535) e, UInt256.land f (UInt256.ofNat 255),
    UInt256.isZero (UInt256.isZero j)]

theorem slot0ReturnMemory (a b c d e f j : UInt256) :
    uniswapV3Pool_block_867_memory (mem := solcFreePtrMem)
      (x0 := j) (x1 := f) (x2 := e) (x3 := d) (x4 := c) (x5 := b) (x6 := a) =
      returnMem (slot0CleanWords a b c d e f j) := by
  have hload : memLoad (UInt256.ofNat 64) solcFreePtrMem = ⟨128⟩ := solcFreePtrMem_mload64
  simp only [uniswapV3Pool_block_867_memory, hload,
    show (⟨128⟩ : UInt256).toNat = 128 from rfl,
    show ((⟨128⟩ : UInt256) + UInt256.ofNat 32).toNat = 160 from by native_decide,
    show (UInt256.ofNat 64 + (⟨128⟩ : UInt256)).toNat = 192 from by native_decide,
    show ((⟨128⟩ : UInt256) + UInt256.ofNat 96).toNat = 224 from by native_decide,
    show ((⟨128⟩ : UInt256) + UInt256.ofNat 128).toNat = 256 from by native_decide,
    show ((⟨128⟩ : UInt256) + UInt256.ofNat 160).toNat = 288 from by native_decide,
    show ((⟨128⟩ : UInt256) + UInt256.ofNat 192).toNat = 320 from by native_decide]
  let a' := UInt256.land a (UInt256.sub
    (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))
  let b' := UInt256.signextend (UInt256.ofNat 2) b
  let c' := UInt256.land (UInt256.ofNat 65535) c
  let d' := UInt256.land (UInt256.ofNat 65535) d
  let e' := UInt256.land (UInt256.ofNat 65535) e
  let f' := UInt256.land f (UInt256.ofNat 255)
  let j' := UInt256.isZero (UInt256.isZero j)
  change (j'.toByteArray.write 0 (f'.toByteArray.write 0 (e'.toByteArray.write 0
    (d'.toByteArray.write 0 (c'.toByteArray.write 0
      (b'.toByteArray.write 0 (solcReturnMem a') 160 32) 192 32) 224 32) 256 32) 288 32) 320 32) = _
  simp only [returnMem_single, returnMem_write_at [a'] b' 160 rfl,
    returnMem_write_at [a', b'] c' 192 rfl, returnMem_write_at [a', b', c'] d' 224 rfl,
    returnMem_write_at [a', b', c', d'] e' 256 rfl,
    returnMem_write_at [a', b', c', d', e'] f' 288 rfl,
    returnMem_write_at [a', b', c', d', e', f'] j' 320 rfl, List.cons_append, List.nil_append]
  rfl

theorem uniswapV3PoolSlot0ReturnX {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : Nat} {v : UniswapV3PoolImmutables} {a b c d e f j aw : UInt256} {R : List UInt256}
    {rdata : ByteArray} {acc : AccountMap}
    (h : RD (deployedRuntime v) ee g s0 ⟨867⟩ (j :: f :: e :: d :: c :: b :: a :: R)
      solcFreePtrMem aw rdata acc k C)
    (hov : R.length + 12 ≤ 1024) :
    RDret (deployedRuntime v) g s0 acc (wordBytes (slot0CleanWords a b c d e f j)) := by
  obtain ⟨aw', k', C', rdReturn⟩ := uniswapV3Pool_block_867_packed
    (immWords := wordsOf (immStore v)) hov h
  have hmem := slot0ReturnMemory a b c d e f j
  rw [hmem] at rdReturn
  have hload : memLoad (UInt256.ofNat 64) solcFreePtrMem = ⟨128⟩ := solcFreePtrMem_mload64
  have hstack : uniswapV3Pool_block_867_stack (mem := solcFreePtrMem)
      (x0 := j) (x1 := f) (x2 := e) (x3 := d) (x4 := c) (x5 := b) (x6 := a) (R := R) =
      UInt256.ofNat 224 :: ⟨0⟩ :: ⟨128⟩ :: R := by
    change UInt256.ofNat 224 ::
      UInt256.sub (memLoad (UInt256.ofNat 64) solcFreePtrMem)
        (memLoad (UInt256.ofNat 64) (uniswapV3Pool_block_867_memory (mem := solcFreePtrMem)
          (x0 := j) (x1 := f) (x2 := e) (x3 := d) (x4 := c) (x5 := b) (x6 := a))) ::
      memLoad (UInt256.ofNat 64) (uniswapV3Pool_block_867_memory (mem := solcFreePtrMem)
          (x0 := j) (x1 := f) (x2 := e) (x3 := d) (x4 := c) (x5 := b) (x6 := a)) :: R = _
    rw [hmem, hload, returnMem_mload64, u256_sub_self]
  rw [hstack] at rdReturn
  have hret := uniswapV3Pool_block_945 (immWords := wordsOf (immStore v))
    (by omega) rdReturn
  simp only [show (⟨128⟩ : UInt256).toNat = 128 from rfl,
    show (UInt256.ofNat 224 + (⟨0⟩ : UInt256)).toNat = 224 from by native_decide] at hret
  have hread : (returnMem (slot0CleanWords a b c d e f j)).readWithPadding 128 224 =
      wordBytes (slot0CleanWords a b c d e f j) := by
    simpa only [slot0CleanWords, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul] using
      returnMem_read128 (slot0CleanWords a b c d e f j)
        (by change 0 < 7; decide) (by change 224 < 2 ^ 64; decide)
  rwa [hread] at hret

set_option maxRecDepth 10000 in
theorem uniswapV3PoolSlot0X {σ σ₀ A I} {g : Sat256} (v : UniswapV3PoolImmutables)
    (hcode : I.code = deployedRuntime v) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (uniswapV3PoolSelBytes 6)) :
    RDret (deployedRuntime v) g (initState σ σ₀ g A I) σ (wordBytes (slot0ReturnWords σ I)) := by
  obtain ⟨k, C, rdEntry⟩ := uniswapV3PoolReachSlot0Body (g := g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode hwv hsz hsize hsel
  have rdRoutine := uniswapV3Pool_block_859
    (immWords := wordsOf (immStore v)) (by simp)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdEntry
  obtain ⟨k', C', rdValues⟩ := uniswapV3Pool_block_5654
    (immWords := wordsOf (immStore v)) (by simp)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdRoutine
  have hmask : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 160 - 1) := by native_decide
  simp only [uniswapV3Pool_block_5654_stack, hmask] at rdValues
  have h160 : UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160) =
      UInt256.ofNat (2 ^ 160) := by native_decide
  have h184 : UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 184) =
      UInt256.ofNat (2 ^ 184) := by native_decide
  have h200 : UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 200) =
      UInt256.ofNat (2 ^ 200) := by native_decide
  have h216 : UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 216) =
      UInt256.ofNat (2 ^ 216) := by native_decide
  have h232 : UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 232) =
      UInt256.ofNat (2 ^ 232) := by native_decide
  have h240 : UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 240) =
      UInt256.ofNat (2 ^ 240) := by native_decide
  simp only [h160, h184, h200, h216, h232, h240] at rdValues
  have hret := uniswapV3PoolSlot0ReturnX (v := v) rdValues (by simp)
  simp only [slot0CleanWords, hmask, u256_land_comm (UInt256.ofNat 65535),
    u256_land_comm (UInt256.ofNat 255), maskTwice,
    signextend_idem ⟨24, by decide⟩ (UInt256.ofNat 2) _ (by native_decide) (by native_decide)] at hret
  rw [signextend_normalizeSint ⟨24, by decide⟩ (UInt256.ofNat 2) _
    (by native_decide) (by native_decide)] at hret
  simpa only [slot0ReturnWords, slot0ReturnItems, List.map_cons, List.map_nil,
    slot0FieldWord, slot0TickValue, show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul,
    Nat.reduceMul, Nat.pow_zero, show UInt256.ofNat 1 = (⟨1⟩ : UInt256) from rfl, word_div_one,
    show UInt256.ofNat (2 ^ 16 - 1) = UInt256.ofNat 65535 from by native_decide,
    show UInt256.ofNat (2 ^ 8 - 1) = UInt256.ofNat 255 from by native_decide] using hret

/-- `slot0()`: the theorem `Correct.lean` routes selector 6 to. -/
theorem uniswapV3PoolSlot0Body {σ σ₀ A I} {g : UInt256} (v : UniswapV3PoolImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (uniswapV3PoolSelBytes 6)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (uniswapV3PoolSelBytes 6) rfl hsel
  have hd : dispatchMsg contract I.calldata = some slot0Transition := by
    apply uniswapV3PoolDispatch_slot0 <;>
      first | exact hsel | exact selectorMismatch_of_match hsel (by decide +kernel)
  have hdec : decodeCalldataWithMode config.abiDecodeMode
      (slot0Transition.params.map Param.name)
      (transitionSignature slot0Transition).paramTypes
      I.calldata = some (∅ : Store) := decodeCalldataWithMode_empty_ok hsz
  exact (uniswapV3PoolSlot0X (g := Sat256.ofUInt256 g) v hcode hwv hsz hsize hsel)
    |>.reEquivExecution hcode hd hdec (uniswapV3PoolSlot0Returns v _ ∅ hwv (by simp))
      (returnEquiv.returned rfl (slot0ReturnEncoding σ I))

end Benchmarks.UniswapV3.Pool
