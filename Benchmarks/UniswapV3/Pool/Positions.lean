import Benchmarks.UniswapV3.Pool.Dispatch
import Benchmarks.UniswapV3.Pool.Calldata
import Benchmarks.UniswapV3.Pool.PositionStorage
import Benchmarks.UniswapV3.Pool.TupleMemory

/-!
# UniswapV3Pool `positions(bytes32)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 1357; reach lemma `uniswapV3PoolReachPositionsBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV3.Pool.Immutables

open uniswapV3PoolBlocks

namespace Benchmarks.UniswapV3.Pool

set_option maxRecDepth 2000000

theorem positionsReturnX {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : Nat} {v : UniswapV3PoolImmutables} {a b c d e aw : UInt256} {R : List UInt256}
    {rdata scratch : ByteArray} {acc : AccountMap}
    (h : RD (deployedRuntime v) ee g s0 ⟨1386⟩ (e :: d :: c :: b :: a :: R)
      scratch aw rdata acc k C)
    (hs : scratch.size = 96)
    (hr : scratch.readWithPadding 64 32 = (⟨128⟩ : UInt256).toByteArray)
    (hov : R.length + 10 ≤ 1024) :
    RDret (deployedRuntime v) g s0 acc (wordBytes
      [UInt256.land (UInt256.ofNat (2 ^ 128 - 1)) a, b, c,
        UInt256.land (UInt256.ofNat (2 ^ 128 - 1)) d,
        UInt256.land (UInt256.ofNat (2 ^ 128 - 1)) e]) := by
  have hret := uniswapV3Pool_block_1386 (immWords := wordsOf (immStore v)) hov h
  have hload : memLoad (UInt256.ofNat 64) scratch = ⟨128⟩ :=
    mloadFreePtrValue (by rw [hs]; decide) hr
  simp only [solcMask128, hload,
    show (⟨128⟩ : UInt256).toNat = 128 from rfl,
    show ((⟨128⟩ : UInt256) + UInt256.ofNat 32).toNat = 160 from by native_decide,
    show (UInt256.ofNat 64 + (⟨128⟩ : UInt256)).toNat = 192 from by native_decide,
    show ((⟨128⟩ : UInt256) + UInt256.ofNat 96).toNat = 224 from by native_decide,
    show ((⟨128⟩ : UInt256) + UInt256.ofNat 128).toNat = 256 from by native_decide] at hret
  simp only [scratchReturnMem_single scratch (UInt256.land (UInt256.ofNat (2 ^ 128 - 1)) a) hs,
    scratchReturnMem_write scratch [(UInt256.land (UInt256.ofNat (2 ^ 128 - 1)) a)] b hs 160 rfl,
    scratchReturnMem_write scratch [(UInt256.land (UInt256.ofNat (2 ^ 128 - 1)) a), b] c hs 192 rfl,
    scratchReturnMem_write scratch [(UInt256.land (UInt256.ofNat (2 ^ 128 - 1)) a), b, c] (UInt256.land (UInt256.ofNat (2 ^ 128 - 1)) d) hs 224 rfl,
    scratchReturnMem_write scratch [(UInt256.land (UInt256.ofNat (2 ^ 128 - 1)) a), b, c, (UInt256.land (UInt256.ofNat (2 ^ 128 - 1)) d)] (UInt256.land (UInt256.ofNat (2 ^ 128 - 1)) e) hs 256 rfl,
    List.cons_append, List.nil_append] at hret
  rw [scratchReturnMem_mload64 _ _ hs hr] at hret
  simp only [show (⟨128⟩ : UInt256).toNat = 128 from rfl,
    show (UInt256.ofNat 160 + UInt256.sub ⟨128⟩ ⟨128⟩).toNat = 160 from by native_decide] at hret
  have hread : (scratchReturnMem scratch [(UInt256.land (UInt256.ofNat (2 ^ 128 - 1)) a), b, c, (UInt256.land (UInt256.ofNat (2 ^ 128 - 1)) d), (UInt256.land (UInt256.ofNat (2 ^ 128 - 1)) e)]).readWithPadding 128 160 =
      wordBytes [(UInt256.land (UInt256.ofNat (2 ^ 128 - 1)) a), b, c, (UInt256.land (UInt256.ofNat (2 ^ 128 - 1)) d), (UInt256.land (UInt256.ofNat (2 ^ 128 - 1)) e)] := by
    simpa only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul] using
      scratchReturnMem_read128 scratch [(UInt256.land (UInt256.ofNat (2 ^ 128 - 1)) a), b, c, (UInt256.land (UInt256.ofNat (2 ^ 128 - 1)) d), (UInt256.land (UInt256.ofNat (2 ^ 128 - 1)) e)] hs
        (by change 0 < 5; decide) (by change 160 < 2 ^ 64; decide)
  rwa [hread] at hret

def positionsReturnItems (key : UInt256) (σ : AccountMap) (I : ExecutionEnv) : List (ABIType × Value × EVM.Word) :=
  [(.elem (.int (.uint ⟨128, by decide⟩)), .int (Int.ofNat (positionFieldWord key 0 0 16 σ I).toNat), positionFieldWord key 0 0 16 σ I),
   (.elem (.int (.uint ⟨256, by decide⟩)), .int (Int.ofNat (positionFieldWord key 1 0 32 σ I).toNat), positionFieldWord key 1 0 32 σ I),
   (.elem (.int (.uint ⟨256, by decide⟩)), .int (Int.ofNat (positionFieldWord key 2 0 32 σ I).toNat), positionFieldWord key 2 0 32 σ I),
   (.elem (.int (.uint ⟨128, by decide⟩)), .int (Int.ofNat (positionFieldWord key 3 0 16 σ I).toNat), positionFieldWord key 3 0 16 σ I),
   (.elem (.int (.uint ⟨128, by decide⟩)), .int (Int.ofNat (positionFieldWord key 3 16 16 σ I).toNat), positionFieldWord key 3 16 16 σ I)]

def positionsReturnValues (key : UInt256) (σ : AccountMap) (I : ExecutionEnv) : List Value :=
  (positionsReturnItems key σ I).map (·.2.1)

def positionsReturnWords (key : UInt256) (σ : AccountMap) (I : ExecutionEnv) : List UInt256 :=
  (positionsReturnItems key σ I).map (·.2.2)

theorem uniswapV3PoolPositionsReturns (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (locals : Store) (key : UInt256) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hbase : locals.get? "positions" = none)
    (hkey : locals.get? "arg0" = some (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE key))) :
    ExecTransitionBody config contract evm locals positionsTransition.body
      (.returned { contract := contract, locals := locals, immutables := immStore v } evm
        (some (positionsReturnValues key evm.accountMap evm.executionEnv))) (immStore v) := by
  apply ExecFuncBody.execBlockRet
  apply ABlock.returnsMany (ABlock.start.requireStep (evalCallvalueEq_true hwv))
  simp only [evalExprs?.eq_def,
    evalPositionLiquidity locals (immStore v) evm key hbase hkey,
    evalPositionFeeGrowthInside0LastX128 locals (immStore v) evm key hbase hkey,
    evalPositionFeeGrowthInside1LastX128 locals (immStore v) evm key hbase hkey,
    evalPositionTokensOwed0 locals (immStore v) evm key hbase hkey,
    evalPositionTokensOwed1 locals (immStore v) evm key hbase hkey, EvalResult.bind, bind, pure,
    positionsReturnValues, positionsReturnItems, List.map_cons, List.map_nil]

theorem positionsReturnEncoding (key : UInt256) (σ : AccountMap) (I : ExecutionEnv) :
    encodeReturnValues? positionsTransition.returnType (positionsReturnValues key σ I) =
      some (wordBytes (positionsReturnWords key σ I)) := by
  have h := staticWordsReturnEncoding (positionsReturnItems key σ I) 160
    (by simp only [positionsReturnItems, List.map_cons, List.map_nil, abiTupleHeadSize?,
          staticABIEncodedSize?, isDynamicABIType, bind, Option.bind]; rfl)
    (by intro x hx
        simp only [positionsReturnItems, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl <;> rfl)
    (by intro x hx
        simp only [positionsReturnItems, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl
        · exact encodeABIValue_uint ⟨128, by decide⟩ (positionFieldWord key 0 0 16 σ I)
            (u256LandMaskToNatLtOfToNat (bits := 128) _ _ (by native_decide))
        · exact encodeABIValue_uint ⟨256, by decide⟩ (positionFieldWord key 1 0 32 σ I)
            (u256LandMaskToNatLtOfToNat (bits := 256) _ _ (by native_decide))
        · exact encodeABIValue_uint ⟨256, by decide⟩ (positionFieldWord key 2 0 32 σ I)
            (u256LandMaskToNatLtOfToNat (bits := 256) _ _ (by native_decide))
        · exact encodeABIValue_uint ⟨128, by decide⟩ (positionFieldWord key 3 0 16 σ I)
            (u256LandMaskToNatLtOfToNat (bits := 128) _ _ (by native_decide))
        · exact encodeABIValue_uint ⟨128, by decide⟩ (positionFieldWord key 3 16 16 σ I)
            (u256LandMaskToNatLtOfToNat (bits := 128) _ _ (by native_decide)))
  rw [wordBytes_eq_list]
  simpa only [positionsReturnWords, positionsReturnValues, List.flatMap_map, Function.comp_def] using h

theorem uniswapV3PoolPositionsX {σ σ₀ A I} {g : Sat256} (v : UniswapV3PoolImmutables)
    (hcode : I.code = deployedRuntime v) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (uniswapV3PoolSelBytes 11)) (hlen : 36 ≤ I.calldata.size) :
    RDret (deployedRuntime v) g (initState σ σ₀ g A I) σ
      (wordBytes (positionsReturnWords (calldataWord I.calldata 4) σ I)) := by
  obtain ⟨k, C, rdEntry⟩ := uniswapV3PoolReachPositionsBody (g := g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode hwv hsz hsize hsel
  have rdDecode := uniswapV3Pool_block_1357_taken (immWords := wordsOf (immStore v))
    (by simp) (by rw [solcDecodeLenCheckOkUnsigned (by exact hlen) hsize]; decide)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdEntry
  simp only [uniswapV3Pool_block_1357_taken_stack] at rdDecode
  have rdRead := uniswapV3Pool_block_1379 (immWords := wordsOf (immStore v))
    (by simp) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdDecode
  simp only [uniswapV3Pool_block_1379_stack] at rdRead
  change RD _ _ _ _ _ (calldataWord I.calldata 4 :: _) solcFreePtrMem _ _ _ _ _ at rdRead
  obtain ⟨k', C', rdReturn⟩ := uniswapV3Pool_block_8093 (immWords := wordsOf (immStore v))
    (by simp) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdRead
  have hhash : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      ((calldataWord I.calldata 4).toByteArray.write 0
        ((UInt256.ofNat 7).toByteArray.write 0 solcFreePtrMem (UInt256.ofNat 32).toNat 32)
        (UInt256.ofNat 0).toNat 32) =
      solcMappingSlot ⟨7⟩ (calldataWord I.calldata 4) := solcMappingKeccakSlot _ _
  simp only [uniswapV3Pool_block_8093_stack] at rdReturn
  rw [hhash] at rdReturn
  have hret := positionsReturnX (v := v) rdReturn (solcMappingHashMem_size _ _)
    (solcMappingHashMem_read64 _ _) (by simp)
  simp only [solcMask128] at hret
  simp only [show UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128) =
    UInt256.ofNat (2 ^ 128) from by native_decide] at hret
  have hfull (w : UInt256) : UInt256.land w (UInt256.ofNat (256 ^ 32 - 1)) = w :=
    u256LandMaskCleanOfToNat (bits := 256) w _ (by native_decide) w.val.isLt
  simpa only [positionsReturnWords, positionsReturnItems, List.map_cons, List.map_nil,
    positionFieldWord, solcSlotWordAt, Nat.pow_zero, show UInt256.ofNat 1 = (⟨1⟩ : UInt256) from rfl,
    show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl,
    show UInt256.ofNat (256 ^ 16) = UInt256.ofNat (2 ^ 128) from by native_decide,
    show UInt256.ofNat (256 ^ 16 - 1) = UInt256.ofNat (2 ^ 128 - 1) from by native_decide,
    u256_add_zero, word_div_one, hfull,
    u256_land_comm (UInt256.ofNat (2 ^ 128 - 1)), maskTwice] using hret

theorem uniswapV3PoolPositionsShortX {σ σ₀ A I} {g : Sat256} (v : UniswapV3PoolImmutables)
    (hcode : I.code = deployedRuntime v) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (uniswapV3PoolSelBytes 11)) (hshort : I.calldata.size < 36) :
    RDrev (deployedRuntime v) g (initState σ σ₀ g A I) := by
  obtain ⟨k, C, rdEntry⟩ := uniswapV3PoolReachPositionsBody (g := g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode hwv hsz hsize hsel
  have rdRevert := uniswapV3Pool_block_1357_fallthrough (immWords := wordsOf (immStore v))
    (by simp) (by rw [solcDecodeLenCheckShortUnsigned (by exact hsz) (by exact hshort) hsize]; decide)
    rdEntry
  exact uniswapV3Pool_block_1375 (immWords := wordsOf (immStore v))
    (by simp [uniswapV3Pool_block_1357_fallthrough_stack]) rdRevert

/-- `positions(bytes32)`: the theorem `Correct.lean` routes selector 11 to. -/
theorem uniswapV3PoolPositionsBody {σ σ₀ A I} {g : UInt256} (v : UniswapV3PoolImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (uniswapV3PoolSelBytes 11)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (uniswapV3PoolSelBytes 11) rfl hsel
  have hd : dispatchMsg contract I.calldata = some positionsTransition := by
    apply uniswapV3PoolDispatch_positions <;>
      first | exact hsel | exact selectorMismatch_of_match hsel (by decide +kernel)
  by_cases hlen : 36 ≤ I.calldata.size
  · have hdec : decodeCalldataWithMode config.abiDecodeMode
        (positionsTransition.params.map Param.name)
        (transitionSignature positionsTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "arg0" (.fixedBytes ⟨31, by decide⟩
          (EVM.Word.toBytesBE (calldataWord I.calldata 4)))) :=
      decodeCalldata_legacyBytes32Word_ok hlen
    exact (uniswapV3PoolPositionsX (g := Sat256.ofUInt256 g) v hcode hwv hsz hsize hsel hlen)
      |>.reEquivExecution hcode hd hdec
        (uniswapV3PoolPositionsReturns v _ _ (calldataWord I.calldata 4) hwv
          (by simp) (by simp))
        (returnEquiv.returned rfl (positionsReturnEncoding (calldataWord I.calldata 4) σ I))
  · have hshort : I.calldata.size < 36 := by omega
    have hdec : decodeCalldataWithMode config.abiDecodeMode
        (positionsTransition.params.map Param.name)
        (transitionSignature positionsTransition).paramTypes I.calldata = none :=
      decodeCalldataWithMode_legacyBytes32_none_short hsz hshort
    exact RDrev.reEquivDecodingFailed hcode
      (uniswapV3PoolPositionsShortX (g := Sat256.ofUInt256 g) v hcode hwv hsz hsize hsel hshort)
      hd hdec

end Benchmarks.UniswapV3.Pool
