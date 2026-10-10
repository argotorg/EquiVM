import Benchmarks.UniswapV3.Pool.SnapshotSource
import Benchmarks.UniswapV3.Pool.Calldata
import Benchmarks.UniswapV3.Pool.Dispatch
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_010

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def snapshotDecodedTick (cd : ByteArray) (offset : Nat) : Int :=
  normalizeInt (.sint ⟨24, by decide⟩) (Int.ofNat (calldataWord cd offset).toNat)
def snapshotDecodedWord (cd : ByteArray) (offset : Nat) : UInt256 :=
  UInt256.signextend (UInt256.ofNat 2) (calldataWord cd offset)

theorem snapshotDecodedWord_clean (cd : ByteArray) (offset : Nat) :
    UInt256.signextend (UInt256.ofNat 2) (snapshotDecodedWord cd offset) =
      EVM.wordOfInt (snapshotDecodedTick cd offset) := by
  rw [snapshotDecodedWord,
    signextend_idem ⟨24, by decide⟩ (UInt256.ofNat 2) _ (by decide) (by decide)]
  exact signextend_normalizeSint ⟨24, by decide⟩ _ _ (by decide) (by decide)

theorem snapshotDecode {cd : ByteArray} (hlen : 68 ≤ cd.size) :
    decodeCalldataWithMode config.abiDecodeMode (snapshotTransition.params.map Param.name)
      (transitionSignature snapshotTransition).paramTypes cd =
      some (snapshotLocals (snapshotDecodedTick cd 4) (snapshotDecodedTick cd 36)) := by
  have h := decodeCalldata_legacyIntPair_ok (.sint ⟨24, by decide⟩) (.sint ⟨24, by decide⟩)
    (x := "tickLower") (y := "tickUpper") hlen
  exact h

theorem snapshotDecodeShort {cd : ByteArray} (hsz : 4 ≤ cd.size) (hshort : cd.size < 68) :
    decodeCalldataWithMode config.abiDecodeMode (snapshotTransition.params.map Param.name)
      (transitionSignature snapshotTransition).paramTypes cd = none :=
  decodeCalldata_legacyIntPair_none_short (.sint ⟨24, by decide⟩) (.sint ⟨24, by decide⟩) hsz hshort

theorem uniswapV3PoolSnapshotDecodedX {σ σ₀ A I} {g : Sat256}
    (v : UniswapV3PoolImmutables) (hcode : I.code = deployedRuntime v)
    (hwv : I.weiValue = ⟨0⟩) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (uniswapV3PoolSelBytes 18))
    (hlen : 68 ≤ I.calldata.size) :
    ∃ k C, RD (deployedRuntime v) I g (initState σ σ₀ g A I) ⟨9952⟩
      [snapshotDecodedWord I.calldata 36, snapshotDecodedWord I.calldata 4,
       UInt256.ofNat 1952, solcSelectorWord I] solcFreePtrMem ⟨3⟩ ByteArray.empty σ k C := by
  obtain ⟨_, _, rdEntry⟩ := uniswapV3PoolReachSnapshotCumulativesInsideBody
    (g := g) (σ := σ) (σ₀ := σ₀) (A := A) v hcode hwv hsz hsize hsel
  have rdDecode := uniswapV3Pool_block_1910_taken (immWords := wordsOf (immStore v))
    (by simp) (by rw [solcDecodeLenCheckOkUnsigned (by exact hlen) hsize]; decide)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdEntry
  simp only [uniswapV3Pool_block_1910_taken_stack] at rdDecode
  have rdRead := uniswapV3Pool_block_1932 (immWords := wordsOf (immStore v)) (by simp)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdDecode
  exact ⟨_, _, rdRead⟩

theorem uniswapV3PoolSnapshotShortX {σ σ₀ A I} {g : Sat256}
    (v : UniswapV3PoolImmutables) (hcode : I.code = deployedRuntime v)
    (hwv : I.weiValue = ⟨0⟩) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (uniswapV3PoolSelBytes 18))
    (hshort : I.calldata.size < 68) : RDrev (deployedRuntime v) g (initState σ σ₀ g A I) := by
  obtain ⟨_, _, rdEntry⟩ := uniswapV3PoolReachSnapshotCumulativesInsideBody
    (g := g) (σ := σ) (σ₀ := σ₀) (A := A) v hcode hwv hsz hsize hsel
  have rdShort := uniswapV3Pool_block_1910_fallthrough (immWords := wordsOf (immStore v))
    (by simp) (by rw [solcDecodeLenCheckShortUnsigned (by exact hsz) (by exact hshort) hsize]; decide) rdEntry
  simp only [uniswapV3Pool_block_1910_fallthrough_stack] at rdShort
  exact uniswapV3Pool_block_1928 (immWords := wordsOf (immStore v)) (by simp) rdShort

end Benchmarks.UniswapV3.Pool
