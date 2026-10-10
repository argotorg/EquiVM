import Benchmarks.UniswapV3.Pool.Dispatch
import Benchmarks.UniswapV3.Pool.Calldata
import Benchmarks.UniswapV3.Pool.Routines
import Benchmarks.UniswapV3.Pool.Storage
import Benchmarks.UniswapV3.Pool.SignedWords

/-!
# UniswapV3Pool `tickBitmap(int16)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 1446; reach lemma `uniswapV3PoolReachTickBitmapBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV3.Pool.Immutables

open uniswapV3PoolBlocks

namespace Benchmarks.UniswapV3.Pool

set_option maxRecDepth 2000000

def tickBitmapKey (I : ExecutionEnv) : Int :=
  normalizeInt (.sint ⟨16, by decide⟩) (Int.ofNat (calldataWord I.calldata 4).toNat)

def tickBitmapWord (key : Int) (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWordAt (solcMappingSlot ⟨6⟩ (EVM.wordOfInt key)) σ I

theorem uniswapV3PoolTickBitmapReturns (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (locals : Store) (key : Int) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hbase : locals.get? "tickBitmap" = none) (hkey : locals.get? "arg0" = some (.int key)) :
    ExecTransitionBody config contract evm locals tickBitmapTransition.body
      (.returned { contract := contract, locals := locals, immutables := immStore v } evm
        (some [.int (Int.ofNat (tickBitmapWord key evm.accountMap evm.executionEnv).toNat)]))
      (immStore v) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true hwv)).returns
      (evalTickBitmap locals (immStore v) evm key hbase hkey)

theorem uniswapV3PoolTickBitmapX {σ σ₀ A I} {g : Sat256} (v : UniswapV3PoolImmutables)
    (hcode : I.code = deployedRuntime v) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (uniswapV3PoolSelBytes 12)) (hlen : 36 ≤ I.calldata.size) :
    RDret (deployedRuntime v) g (initState σ σ₀ g A I) σ
      (UInt256.toByteArray (tickBitmapWord (tickBitmapKey I) σ I)) := by
  obtain ⟨k, C, rdEntry⟩ := uniswapV3PoolReachTickBitmapBody (g := g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode hwv hsz hsize hsel
  have rdDecode := uniswapV3Pool_block_1446_taken (immWords := wordsOf (immStore v))
    (by simp) (by rw [solcDecodeLenCheckOkUnsigned (by exact hlen) hsize]; decide)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdEntry
  simp only [uniswapV3Pool_block_1446_taken_stack] at rdDecode
  have rdRead := uniswapV3Pool_block_1468 (immWords := wordsOf (immStore v))
    (by simp) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdDecode
  simp only [uniswapV3Pool_block_1468_stack] at rdRead
  have hkey : UInt256.signextend (UInt256.ofNat 1) (calldataWord I.calldata 4) =
      EVM.wordOfInt (tickBitmapKey I) :=
    signextend_normalizeSint ⟨16, by decide⟩ (UInt256.ofNat 1) _
      (by native_decide) (by native_decide)
  change RD _ _ _ _ _ (UInt256.signextend (UInt256.ofNat 1) (calldataWord I.calldata 4) :: _) _ _ _ _ _ _ at rdRead
  rw [hkey] at rdRead
  obtain ⟨k', C', rdReturn⟩ := uniswapV3Pool_block_8154 (immWords := wordsOf (immStore v))
    (by simp) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdRead
  have hhash : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      (solcMappingHashMem (UInt256.ofNat 6) (EVM.wordOfInt (tickBitmapKey I))) =
      solcMappingSlot ⟨6⟩ (EVM.wordOfInt (tickBitmapKey I)) := solcMappingKeccakSlot _ _
  change RD _ _ _ _ _ (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
    (solcMappingHashMem (UInt256.ofNat 6) (EVM.wordOfInt (tickBitmapKey I)))) σ I :: _)
    (solcMappingHashMem (UInt256.ofNat 6) (EVM.wordOfInt (tickBitmapKey I))) _ _ _ _ _ at rdReturn
  rw [hhash] at rdReturn
  exact RD.poolReturnWordFromScratch (v := v) rdReturn (solcMappingHashMem_size _ _)
    (solcMappingHashMem_read64 _ _) (by simp)

theorem uniswapV3PoolTickBitmapShortX {σ σ₀ A I} {g : Sat256} (v : UniswapV3PoolImmutables)
    (hcode : I.code = deployedRuntime v) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (uniswapV3PoolSelBytes 12)) (hshort : I.calldata.size < 36) :
    RDrev (deployedRuntime v) g (initState σ σ₀ g A I) := by
  obtain ⟨k, C, rdEntry⟩ := uniswapV3PoolReachTickBitmapBody (g := g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode hwv hsz hsize hsel
  have rdRevert := uniswapV3Pool_block_1446_fallthrough (immWords := wordsOf (immStore v))
    (by simp) (by rw [solcDecodeLenCheckShortUnsigned (by exact hsz) (by exact hshort) hsize]; decide)
    rdEntry
  exact uniswapV3Pool_block_1464 (immWords := wordsOf (immStore v))
    (by simp [uniswapV3Pool_block_1446_fallthrough_stack]) rdRevert

/-- `tickBitmap(int16)`: the theorem `Correct.lean` routes selector 12 to. -/
theorem uniswapV3PoolTickBitmapBody {σ σ₀ A I} {g : UInt256} (v : UniswapV3PoolImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (uniswapV3PoolSelBytes 12)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (uniswapV3PoolSelBytes 12) rfl hsel
  have hd : dispatchMsg contract I.calldata = some tickBitmapTransition := by
    apply uniswapV3PoolDispatch_tickBitmap <;>
      first | exact hsel | exact selectorMismatch_of_match hsel (by decide +kernel)
  by_cases hlen : 36 ≤ I.calldata.size
  · have hdec : decodeCalldataWithMode config.abiDecodeMode
        (tickBitmapTransition.params.map Param.name)
        (transitionSignature tickBitmapTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "arg0" (.int (tickBitmapKey I))) :=
      decodeCalldata_legacyInt_ok (.sint ⟨16, by decide⟩) hlen
    exact (uniswapV3PoolTickBitmapX (g := Sat256.ofUInt256 g) v hcode hwv hsz hsize hsel hlen)
      |>.reEquivExecution hcode hd hdec
        (uniswapV3PoolTickBitmapReturns v _ _ (tickBitmapKey I) hwv
          (by simp) (by simp))
        (returnEquiv_of_encode (uint256ReturnEncoding (tickBitmapWord (tickBitmapKey I) σ I)))
  · have hshort : I.calldata.size < 36 := by omega
    have hdec : decodeCalldataWithMode config.abiDecodeMode
        (tickBitmapTransition.params.map Param.name)
        (transitionSignature tickBitmapTransition).paramTypes I.calldata = none :=
      decodeCalldata_legacyInt_none_short (.sint ⟨16, by decide⟩) hsz hshort
    exact RDrev.reEquivDecodingFailed hcode
      (uniswapV3PoolTickBitmapShortX (g := Sat256.ofUInt256 g) v hcode hwv hsz hsize hsel hshort)
      hd hdec

end Benchmarks.UniswapV3.Pool
