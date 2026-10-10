import Benchmarks.UniswapV3.Pool.Dispatch
import Benchmarks.UniswapV3.Pool.Calldata
import Benchmarks.UniswapV3.Pool.TickStorage
import Benchmarks.UniswapV3.Pool.TupleMemory

/-!
# UniswapV3Pool `ticks(int24)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 2088; reach lemma `uniswapV3PoolReachTicksBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV3.Pool.Immutables

open uniswapV3PoolBlocks

namespace Benchmarks.UniswapV3.Pool

set_option maxRecDepth 2000000

def ticksCleanPrefix (a b c d e f j : UInt256) : List UInt256 :=
  [UInt256.land a (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)),
   UInt256.signextend (UInt256.ofNat 15) b,
   c,
   d,
   UInt256.signextend (UInt256.ofNat 6) e,
   UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) f,
   UInt256.land (UInt256.ofNat 4294967295) j]

theorem ticksReturnMemory (scratch : ByteArray) (a b c d e f j : UInt256)
    (hs : scratch.size = 96)
    (hr : scratch.readWithPadding 64 32 = (⟨128⟩ : UInt256).toByteArray) :
    uniswapV3Pool_block_2120_memory (mem := scratch)
      (x1 := j) (x2 := f) (x3 := e) (x4 := d) (x5 := c) (x6 := b) (x7 := a) =
      scratchReturnMem scratch (ticksCleanPrefix a b c d e f j) := by
  have hload : memLoad (UInt256.ofNat 64) scratch = ⟨128⟩ :=
    mloadFreePtrValue (by rw [hs]; decide) hr
  simp only [uniswapV3Pool_block_2120_memory, hload,
    show (⟨128⟩ : UInt256).toNat = 128 from rfl,
    show ((⟨128⟩ : UInt256) + UInt256.ofNat 32).toNat = 160 from by native_decide,
    show (UInt256.ofNat 64 + (⟨128⟩ : UInt256)).toNat = 192 from by native_decide,
    show ((⟨128⟩ : UInt256) + UInt256.ofNat 96).toNat = 224 from by native_decide,
    show ((⟨128⟩ : UInt256) + UInt256.ofNat 128).toNat = 256 from by native_decide,
    show ((⟨128⟩ : UInt256) + UInt256.ofNat 160).toNat = 288 from by native_decide,
    show ((⟨128⟩ : UInt256) + UInt256.ofNat 192).toNat = 320 from by native_decide]
  simp only [ticksCleanPrefix, scratchReturnMem_single scratch (UInt256.land a (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))) hs,
    scratchReturnMem_write scratch [UInt256.land a (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))] (UInt256.signextend (UInt256.ofNat 15) b) hs 160 rfl,
    scratchReturnMem_write scratch [UInt256.land a (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)), UInt256.signextend (UInt256.ofNat 15) b] (c) hs 192 rfl,
    scratchReturnMem_write scratch [UInt256.land a (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)), UInt256.signextend (UInt256.ofNat 15) b, c] (d) hs 224 rfl,
    scratchReturnMem_write scratch [UInt256.land a (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)), UInt256.signextend (UInt256.ofNat 15) b, c, d] (UInt256.signextend (UInt256.ofNat 6) e) hs 256 rfl,
    scratchReturnMem_write scratch [UInt256.land a (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)), UInt256.signextend (UInt256.ofNat 15) b, c, d, UInt256.signextend (UInt256.ofNat 6) e] (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) f) hs 288 rfl,
    scratchReturnMem_write scratch [UInt256.land a (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)), UInt256.signextend (UInt256.ofNat 15) b, c, d, UInt256.signextend (UInt256.ofNat 6) e, UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) f] (UInt256.land (UInt256.ofNat 4294967295) j) hs 320 rfl,
    List.cons_append, List.nil_append]

theorem ticksReturnX {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : Nat} {v : UniswapV3PoolImmutables} {a b c d e f j q aw : UInt256} {R : List UInt256}
    {rdata scratch : ByteArray} {acc : AccountMap}
    (h : RD (deployedRuntime v) ee g s0 ⟨2120⟩ (q :: j :: f :: e :: d :: c :: b :: a :: R)
      scratch aw rdata acc k C)
    (hs : scratch.size = 96)
    (hr : scratch.readWithPadding 64 32 = (⟨128⟩ : UInt256).toByteArray)
    (hov : R.length + 13 ≤ 1024) :
    RDret (deployedRuntime v) g s0 acc
      (wordBytes (ticksCleanPrefix a b c d e f j ++ [UInt256.isZero (UInt256.isZero q)])) := by
  obtain ⟨aw', k', C', rdFinal⟩ := uniswapV3Pool_block_2120_packed
    (immWords := wordsOf (immStore v)) hov h
  rw [ticksReturnMemory scratch a b c d e f j hs hr] at rdFinal
  have hload : memLoad (UInt256.ofNat 64) scratch = ⟨128⟩ :=
    mloadFreePtrValue (by rw [hs]; decide) hr
  simp only [uniswapV3Pool_block_2120_stack, hload] at rdFinal
  have hret := uniswapV3Pool_block_2202 (immWords := wordsOf (immStore v)) (by omega) rdFinal
  simp only [show ((⟨128⟩ : UInt256) + UInt256.ofNat 224).toNat = 352 from by native_decide] at hret
  rw [scratchReturnMem_write scratch (ticksCleanPrefix a b c d e f j)
    (UInt256.isZero (UInt256.isZero q)) hs 352 rfl,
    scratchReturnMem_mload64 _ _ hs hr] at hret
  simp only [show (⟨128⟩ : UInt256).toNat = 128 from rfl,
    show (UInt256.ofNat 256 + UInt256.sub ⟨128⟩ ⟨128⟩).toNat = 256 from by native_decide] at hret
  have hread := scratchReturnMem_read128 scratch
    (ticksCleanPrefix a b c d e f j ++ [UInt256.isZero (UInt256.isZero q)]) hs
    (by change 0 < 8; decide) (by change 256 < 2 ^ 64; decide)
  change (scratchReturnMem scratch (ticksCleanPrefix a b c d e f j ++
    [UInt256.isZero (UInt256.isZero q)])).readWithPadding 128 256 = _ at hread
  rwa [hread] at hret

def ticksReturnItems (key : Int) (σ : AccountMap) (I : ExecutionEnv) : List (ABIType × Value × EVM.Word) :=
  [(.elem (.int (.uint ⟨128, by decide⟩)), .int (Int.ofNat (tickFieldWord key 0 0 16 σ I).toNat), tickFieldWord key 0 0 16 σ I),
   (.elem (.int (.sint ⟨128, by decide⟩)), .int (tickSignedFieldValue key 0 16 ⟨128, by decide⟩ σ I), EVM.wordOfInt (tickSignedFieldValue key 0 16 ⟨128, by decide⟩ σ I)),
   (.elem (.int (.uint ⟨256, by decide⟩)), .int (Int.ofNat (tickFieldWord key 1 0 32 σ I).toNat), tickFieldWord key 1 0 32 σ I),
   (.elem (.int (.uint ⟨256, by decide⟩)), .int (Int.ofNat (tickFieldWord key 2 0 32 σ I).toNat), tickFieldWord key 2 0 32 σ I),
   (.elem (.int (.sint ⟨56, by decide⟩)), .int (tickSignedFieldValue key 3 0 ⟨56, by decide⟩ σ I), EVM.wordOfInt (tickSignedFieldValue key 3 0 ⟨56, by decide⟩ σ I)),
   (.elem (.int (.uint ⟨160, by decide⟩)), .int (Int.ofNat (tickFieldWord key 3 7 20 σ I).toNat), tickFieldWord key 3 7 20 σ I),
   (.elem (.int (.uint ⟨32, by decide⟩)), .int (Int.ofNat (tickFieldWord key 3 27 4 σ I).toNat), tickFieldWord key 3 27 4 σ I),
   (.elem (.bool), wordToElem .bool (tickFieldWord key 3 31 1 σ I), UInt256.isZero (UInt256.isZero (tickFieldWord key 3 31 1 σ I)))]

def ticksReturnValues (key : Int) (σ : AccountMap) (I : ExecutionEnv) : List Value :=
  (ticksReturnItems key σ I).map (·.2.1)

def ticksReturnWords (key : Int) (σ : AccountMap) (I : ExecutionEnv) : List UInt256 :=
  (ticksReturnItems key σ I).map (·.2.2)

theorem uniswapV3PoolTicksReturns (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (locals : Store) (key : Int) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hbase : locals.get? "ticks" = none) (hkey : locals.get? "arg0" = some (.int key)) :
    ExecTransitionBody config contract evm locals ticksTransition.body
      (.returned { contract := contract, locals := locals, immutables := immStore v } evm
        (some (ticksReturnValues key evm.accountMap evm.executionEnv))) (immStore v) := by
  apply ExecFuncBody.execBlockRet
  apply ABlock.returnsMany (ABlock.start.requireStep (evalCallvalueEq_true hwv))
  simp only [evalExprs?.eq_def,
    evalTickLiquidityGross locals (immStore v) evm key hbase hkey,
    evalTickLiquidityNet locals (immStore v) evm key hbase hkey,
    evalTickFeeGrowthOutside0X128 locals (immStore v) evm key hbase hkey,
    evalTickFeeGrowthOutside1X128 locals (immStore v) evm key hbase hkey,
    evalTickTickCumulativeOutside locals (immStore v) evm key hbase hkey,
    evalTickSecondsPerLiquidityOutsideX128 locals (immStore v) evm key hbase hkey,
    evalTickSecondsOutside locals (immStore v) evm key hbase hkey,
    evalTickInitialized locals (immStore v) evm key hbase hkey, EvalResult.bind, bind, pure,
    ticksReturnValues, ticksReturnItems, List.map_cons, List.map_nil]

theorem ticksReturnEncoding (key : Int) (σ : AccountMap) (I : ExecutionEnv) :
    encodeReturnValues? ticksTransition.returnType (ticksReturnValues key σ I) =
      some (wordBytes (ticksReturnWords key σ I)) := by
  have h := staticWordsReturnEncoding (ticksReturnItems key σ I) 256
    (by simp only [ticksReturnItems, List.map_cons, List.map_nil, abiTupleHeadSize?,
          staticABIEncodedSize?, isDynamicABIType, bind, Option.bind]; rfl)
    (by intro x hx
        simp only [ticksReturnItems, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
    (by intro x hx
        simp only [ticksReturnItems, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact encodeABIValue_uint ⟨128, by decide⟩ (tickFieldWord key 0 0 16 σ I)
            (u256LandMaskToNatLtOfToNat (bits := 128) _ _ (by native_decide))
        · simpa only [tickSignedFieldValue] using encodeABIValue_sintCast ⟨128, by decide⟩
            (UInt256.div (solcSlotWordAt (tickFieldSlot key 0) σ I) (UInt256.ofNat (256 ^ 16)))
        · exact encodeABIValue_uint ⟨256, by decide⟩ (tickFieldWord key 1 0 32 σ I)
            (u256LandMaskToNatLtOfToNat (bits := 256) _ _ (by native_decide))
        · exact encodeABIValue_uint ⟨256, by decide⟩ (tickFieldWord key 2 0 32 σ I)
            (u256LandMaskToNatLtOfToNat (bits := 256) _ _ (by native_decide))
        · simpa only [tickSignedFieldValue] using encodeABIValue_sintCast ⟨56, by decide⟩
            (UInt256.div (solcSlotWordAt (tickFieldSlot key 3) σ I) (UInt256.ofNat (256 ^ 0)))
        · exact encodeABIValue_uint ⟨160, by decide⟩ (tickFieldWord key 3 7 20 σ I)
            (u256LandMaskToNatLtOfToNat (bits := 160) _ _ (by native_decide))
        · exact encodeABIValue_uint ⟨32, by decide⟩ (tickFieldWord key 3 27 4 σ I)
            (u256LandMaskToNatLtOfToNat (bits := 32) _ _ (by native_decide))
        · exact encodeABIValue_boolWord (tickFieldWord key 3 31 1 σ I))
  rw [wordBytes_eq_list]
  simpa only [ticksReturnWords, ticksReturnValues, List.flatMap_map, Function.comp_def] using h

def ticksKey (I : ExecutionEnv) : Int :=
  normalizeInt (.sint ⟨24, by decide⟩) (Int.ofNat (calldataWord I.calldata 4).toNat)

theorem uniswapV3PoolTicksX {σ σ₀ A I} {g : Sat256} (v : UniswapV3PoolImmutables)
    (hcode : I.code = deployedRuntime v) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (uniswapV3PoolSelBytes 24)) (hlen : 36 ≤ I.calldata.size) :
    RDret (deployedRuntime v) g (initState σ σ₀ g A I) σ
      (wordBytes (ticksReturnWords (ticksKey I) σ I)) := by
  obtain ⟨k, C, rdEntry⟩ := uniswapV3PoolReachTicksBody (g := g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode hwv hsz hsize hsel
  have rdDecode := uniswapV3Pool_block_2088_taken (immWords := wordsOf (immStore v))
    (by simp) (by rw [solcDecodeLenCheckOkUnsigned (by exact hlen) hsize]; decide)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdEntry
  simp only [uniswapV3Pool_block_2088_taken_stack] at rdDecode
  have rdRead := uniswapV3Pool_block_2110 (immWords := wordsOf (immStore v))
    (by simp) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdDecode
  simp only [uniswapV3Pool_block_2110_stack] at rdRead
  change RD _ _ _ _ _ (UInt256.signextend (UInt256.ofNat 2) (calldataWord I.calldata 4) :: _)
    solcFreePtrMem _ _ _ _ _ at rdRead
  have hkey : UInt256.signextend (UInt256.ofNat 2) (calldataWord I.calldata 4) =
      EVM.wordOfInt (ticksKey I) :=
    signextend_normalizeSint ⟨24, by decide⟩ (UInt256.ofNat 2) _
      (by native_decide) (by native_decide)
  rw [hkey] at rdRead
  obtain ⟨k', C', rdPacked⟩ := uniswapV3Pool_block_10605 (immWords := wordsOf (immStore v))
    (by simp) rdRead
  have hhash : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      ((EVM.wordOfInt (ticksKey I)).toByteArray.write 0
        ((UInt256.ofNat 5).toByteArray.write 0 solcFreePtrMem (UInt256.ofNat 32).toNat 32)
        (UInt256.ofNat 0).toNat 32) =
      solcMappingSlot ⟨5⟩ (EVM.wordOfInt (ticksKey I)) := solcMappingKeccakSlot _ _
  simp only [uniswapV3Pool_block_10605_stack] at rdPacked
  rw [hhash] at rdPacked
  have rdValues := uniswapV3Pool_block_10696 (immWords := wordsOf (immStore v))
    (by simp) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdPacked
  simp only [uniswapV3Pool_block_10696_stack] at rdValues
  have hret := ticksReturnX (v := v) rdValues (solcMappingHashMem_size _ _)
    (solcMappingHashMem_read64 _ _) (by simp)
  have hmask160 : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 160 - 1) := by native_decide
  simp only [ticksCleanPrefix, List.cons_append, List.nil_append, solcMask128, hmask160,
    u256_land_comm (UInt256.ofNat (2 ^ 160 - 1)), u256_land_comm (UInt256.ofNat 4294967295),
    maskTwice,
    signextend_idem ⟨128, by decide⟩ (UInt256.ofNat 15) _ (by native_decide) (by native_decide),
    signextend_idem ⟨56, by decide⟩ (UInt256.ofNat 6) _ (by native_decide) (by native_decide)] at hret
  simp only [signextend_normalizeSint ⟨128, by decide⟩ (UInt256.ofNat 15) _
      (by native_decide) (by native_decide),
    signextend_normalizeSint ⟨56, by decide⟩ (UInt256.ofNat 6) _
      (by native_decide) (by native_decide)] at hret
  simp only [
    show UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128) = UInt256.ofNat (2 ^ 128) from by native_decide,
    show UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 216) = UInt256.ofNat (2 ^ 216) from by native_decide,
    show UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 248) = UInt256.ofNat (2 ^ 248) from by native_decide] at hret
  have hfull (w : UInt256) : UInt256.land w (UInt256.ofNat (256 ^ 32 - 1)) = w :=
    u256LandMaskCleanOfToNat (bits := 256) w _ (by native_decide) w.val.isLt
  simpa only [ticksReturnWords, ticksReturnItems, List.map_cons, List.map_nil,
    tickFieldWord, tickSignedFieldValue, tickFieldSlot, solcSlotWordAt, Nat.pow_zero,
    show UInt256.ofNat 1 = (⟨1⟩ : UInt256) from rfl,
    show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl,
    show UInt256.ofNat (256 ^ 16) = UInt256.ofNat (2 ^ 128) from by native_decide,
    show UInt256.ofNat (256 ^ 27) = UInt256.ofNat (2 ^ 216) from by native_decide,
    show UInt256.ofNat (256 ^ 31) = UInt256.ofNat (2 ^ 248) from by native_decide,
    show UInt256.ofNat (256 ^ 7) = UInt256.ofNat 72057594037927936 from by native_decide,
    show UInt256.ofNat (256 ^ 16 - 1) = UInt256.ofNat (2 ^ 128 - 1) from by native_decide,
    show UInt256.ofNat (256 ^ 20 - 1) = UInt256.ofNat (2 ^ 160 - 1) from by native_decide,
    show UInt256.ofNat (256 ^ 4 - 1) = UInt256.ofNat 4294967295 from by native_decide,
    show UInt256.ofNat (256 ^ 1 - 1) = UInt256.ofNat 255 from by native_decide,
    u256_add_zero, word_div_one, hfull, u256_land_comm (UInt256.ofNat 255)] using hret

theorem uniswapV3PoolTicksShortX {σ σ₀ A I} {g : Sat256} (v : UniswapV3PoolImmutables)
    (hcode : I.code = deployedRuntime v) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (uniswapV3PoolSelBytes 24)) (hshort : I.calldata.size < 36) :
    RDrev (deployedRuntime v) g (initState σ σ₀ g A I) := by
  obtain ⟨k, C, rdEntry⟩ := uniswapV3PoolReachTicksBody (g := g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode hwv hsz hsize hsel
  have rdRevert := uniswapV3Pool_block_2088_fallthrough (immWords := wordsOf (immStore v))
    (by simp) (by rw [solcDecodeLenCheckShortUnsigned (by exact hsz) (by exact hshort) hsize]; decide)
    rdEntry
  exact uniswapV3Pool_block_2106 (immWords := wordsOf (immStore v))
    (by simp [uniswapV3Pool_block_2088_fallthrough_stack]) rdRevert

/-- `ticks(int24)`: the theorem `Correct.lean` routes selector 24 to. -/
theorem uniswapV3PoolTicksBody {σ σ₀ A I} {g : UInt256} (v : UniswapV3PoolImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (uniswapV3PoolSelBytes 24)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (uniswapV3PoolSelBytes 24) rfl hsel
  have hd : dispatchMsg contract I.calldata = some ticksTransition := by
    apply uniswapV3PoolDispatch_ticks <;>
      first | exact hsel | exact selectorMismatch_of_match hsel (by decide +kernel)
  by_cases hlen : 36 ≤ I.calldata.size
  · have hdec : decodeCalldataWithMode config.abiDecodeMode
        (ticksTransition.params.map Param.name)
        (transitionSignature ticksTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "arg0" (.int (ticksKey I))) :=
      decodeCalldata_legacyInt_ok (.sint ⟨24, by decide⟩) hlen
    exact (uniswapV3PoolTicksX (g := Sat256.ofUInt256 g) v hcode hwv hsz hsize hsel hlen)
      |>.reEquivExecution hcode hd hdec
        (uniswapV3PoolTicksReturns v _ _ (ticksKey I) hwv
          (by simp) (by simp))
        (returnEquiv.returned rfl (ticksReturnEncoding (ticksKey I) σ I))
  · have hshort : I.calldata.size < 36 := by omega
    have hdec : decodeCalldataWithMode config.abiDecodeMode
        (ticksTransition.params.map Param.name)
        (transitionSignature ticksTransition).paramTypes I.calldata = none :=
      decodeCalldata_legacyInt_none_short (.sint ⟨24, by decide⟩) hsz hshort
    exact RDrev.reEquivDecodingFailed hcode
      (uniswapV3PoolTicksShortX (g := Sat256.ofUInt256 g) v hcode hwv hsz hsize hsel hshort)
      hd hdec

end Benchmarks.UniswapV3.Pool
