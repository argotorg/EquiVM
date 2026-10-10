import Benchmarks.UniswapV3.Pool.InitializePrefix
import Benchmarks.UniswapV3.Pool.Calldata
import Benchmarks.UniswapV3.Pool.Routines
import Benchmarks.UniswapV3.Pool.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def initializePriceWord (cd : ByteArray) : UInt256 :=
  UInt256.land (calldataWord cd 4) (UInt256.ofNat (2 ^ 160 - 1))

theorem initializePriceWord_lt (cd : ByteArray) :
    (initializePriceWord cd).toNat < 2 ^ 160 :=
  u256LandMaskToNatLtOfToNat _ _ (by decide)

theorem initializeDecode {cd : ByteArray} (hlen : 36 ≤ cd.size) :
    decodeCalldataWithMode config.abiDecodeMode (initializeTransition.params.map Param.name)
      (transitionSignature initializeTransition).paramTypes cd =
      some (initializeLocals (initializePriceWord cd)) := by
  have h := decodeCalldata_legacyInt_ok (.uint ⟨160, by decide⟩)
    (x := "sqrtPriceX96") hlen
  rw [normalizeUIntWord_mask ⟨160, by decide⟩ (calldataWord cd 4)
    (UInt256.ofNat (2 ^ 160 - 1)) (by decide)] at h
  exact h

theorem initializeDecodeShort {cd : ByteArray} (hsz : 4 ≤ cd.size) (hshort : cd.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (initializeTransition.params.map Param.name)
      (transitionSignature initializeTransition).paramTypes cd = none :=
  decodeCalldata_legacyInt_none_short (.uint ⟨160, by decide⟩) hsz hshort

theorem uniswapV3PoolInitializeDecodedX {σ σ₀ A I} {g : Sat256}
    (v : UniswapV3PoolImmutables) (hcode : I.code = deployedRuntime v)
    (hwv : I.weiValue = ⟨0⟩) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (uniswapV3PoolSelBytes 25))
    (hlen : 36 ≤ I.calldata.size) :
    ∃ k C, RD (deployedRuntime v) I g (initState σ σ₀ g A I) ⟨10715⟩
      [initializePriceWord I.calldata, UInt256.ofNat 857, solcSelectorWord I]
      solcFreePtrMem ⟨3⟩ ByteArray.empty σ k C := by
  obtain ⟨_, _, rdEntry⟩ := uniswapV3PoolReachInitializeBody
    (g := g) (σ := σ) (σ₀ := σ₀) (A := A) v hcode hwv hsz hsize hsel
  have rdDecode := uniswapV3Pool_block_2218_taken (immWords := wordsOf (immStore v))
    (by simp) (by rw [solcDecodeLenCheckOkUnsigned (by exact hlen) hsize]; decide)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdEntry
  simp only [uniswapV3Pool_block_2218_taken_stack] at rdDecode
  have rdRead := uniswapV3Pool_block_2240 (immWords := wordsOf (immStore v)) (by simp)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdDecode
  have hmask : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 160 - 1) := by decide
  simp only [uniswapV3Pool_block_2240_stack, hmask] at rdRead
  change RD (deployedRuntime v) I g (initState σ σ₀ g A I) ⟨10715⟩
    [UInt256.land (UInt256.ofNat (2 ^ 160 - 1)) (calldataWord I.calldata 4),
      UInt256.ofNat 857, solcSelectorWord I] solcFreePtrMem ⟨3⟩ ByteArray.empty σ _ _ at rdRead
  rw [u256_land_comm (UInt256.ofNat (2 ^ 160 - 1))] at rdRead
  exact ⟨_, _, rdRead⟩

theorem uniswapV3PoolInitializeShortX {σ σ₀ A I} {g : Sat256}
    (v : UniswapV3PoolImmutables) (hcode : I.code = deployedRuntime v)
    (hwv : I.weiValue = ⟨0⟩) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (uniswapV3PoolSelBytes 25))
    (hshort : I.calldata.size < 36) : RDrev (deployedRuntime v) g (initState σ σ₀ g A I) := by
  obtain ⟨_, _, rdEntry⟩ := uniswapV3PoolReachInitializeBody
    (g := g) (σ := σ) (σ₀ := σ₀) (A := A) v hcode hwv hsz hsize hsel
  have rdShort := uniswapV3Pool_block_2218_fallthrough (immWords := wordsOf (immStore v))
    (by simp) (by rw [solcDecodeLenCheckShortUnsigned (by exact hsz) (by exact hshort) hsize]; decide) rdEntry
  simp only [uniswapV3Pool_block_2218_fallthrough_stack] at rdShort
  exact uniswapV3Pool_block_2236 (immWords := wordsOf (immStore v)) (by simp) rdShort

end Benchmarks.UniswapV3.Pool
