import Benchmarks.UniswapV3.Pool.IncreaseSource
import Benchmarks.UniswapV3.Pool.Calldata
import Benchmarks.UniswapV3.Pool.Routines
import Benchmarks.UniswapV3.Pool.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def increaseRequestedWord (cd : ByteArray) : UInt256 :=
  UInt256.land (calldataWord cd 4) (UInt256.ofNat 65535)

theorem increaseRequestedWord_lt (cd : ByteArray) :
    (increaseRequestedWord cd).toNat < 2 ^ 16 :=
  u256LandMaskToNatLtOfToNat _ _ (by decide)

theorem increaseDecode {cd : ByteArray} (hlen : 36 ≤ cd.size) :
    decodeCalldataWithMode config.abiDecodeMode (increaseTransition.params.map Param.name)
      (transitionSignature increaseTransition).paramTypes cd =
      some (increaseLocals (increaseRequestedWord cd)) := by
  have h := decodeCalldata_legacyInt_ok (.uint ⟨16, by decide⟩)
    (x := "observationCardinalityNext") hlen
  rw [normalizeUIntWord_mask ⟨16, by decide⟩ (calldataWord cd 4)
    (UInt256.ofNat 65535) (by decide)] at h
  exact h

theorem increaseDecodeShort {cd : ByteArray} (hsz : 4 ≤ cd.size) (hshort : cd.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (increaseTransition.params.map Param.name)
      (transitionSignature increaseTransition).paramTypes cd = none :=
  decodeCalldata_legacyInt_none_short (.uint ⟨16, by decide⟩) hsz hshort

theorem uniswapV3PoolIncreaseDecodedX {σ σ₀ A I} {g : Sat256}
    (v : UniswapV3PoolImmutables) (hcode : I.code = deployedRuntime v)
    (hwv : I.weiValue = ⟨0⟩) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (uniswapV3PoolSelBytes 5))
    (hlen : 36 ≤ I.calldata.size) :
    ∃ k C, RD (deployedRuntime v) I g (initState σ σ₀ g A I) ⟨5404⟩
      [increaseRequestedWord I.calldata, UInt256.ofNat 857, solcSelectorWord I]
      solcFreePtrMem ⟨3⟩ ByteArray.empty σ k C := by
  obtain ⟨_, _, rdEntry⟩ := uniswapV3PoolReachIncreaseObservationCardinalityNextBody
    (g := g) (σ := σ) (σ₀ := σ₀) (A := A) v hcode hwv hsz hsize hsel
  have rdDecode := uniswapV3Pool_block_824_taken (immWords := wordsOf (immStore v))
    (by simp) (by rw [solcDecodeLenCheckOkUnsigned (by exact hlen) hsize]; decide)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdEntry
  simp only [uniswapV3Pool_block_824_taken_stack] at rdDecode
  have rdRead := uniswapV3Pool_block_846 (immWords := wordsOf (immStore v)) (by simp)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdDecode
  simp only [uniswapV3Pool_block_846_stack] at rdRead
  change RD (deployedRuntime v) I g (initState σ σ₀ g A I) ⟨5404⟩
    [UInt256.land (UInt256.ofNat 65535) (calldataWord I.calldata 4),
      UInt256.ofNat 857, solcSelectorWord I] solcFreePtrMem ⟨3⟩ ByteArray.empty σ _ _ at rdRead
  rw [u256_land_comm (UInt256.ofNat 65535)] at rdRead
  exact ⟨_, _, rdRead⟩

theorem uniswapV3PoolIncreaseShortX {σ σ₀ A I} {g : Sat256}
    (v : UniswapV3PoolImmutables) (hcode : I.code = deployedRuntime v)
    (hwv : I.weiValue = ⟨0⟩) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (uniswapV3PoolSelBytes 5))
    (hshort : I.calldata.size < 36) : RDrev (deployedRuntime v) g (initState σ σ₀ g A I) := by
  obtain ⟨_, _, rdEntry⟩ := uniswapV3PoolReachIncreaseObservationCardinalityNextBody
    (g := g) (σ := σ) (σ₀ := σ₀) (A := A) v hcode hwv hsz hsize hsel
  have rdShort := uniswapV3Pool_block_824_fallthrough (immWords := wordsOf (immStore v))
    (by simp) (by rw [solcDecodeLenCheckShortUnsigned (by exact hsz) (by exact hshort) hsize]; decide) rdEntry
  simp only [uniswapV3Pool_block_824_fallthrough_stack] at rdShort
  exact uniswapV3Pool_block_842 (immWords := wordsOf (immStore v)) (by simp) rdShort

end Benchmarks.UniswapV3.Pool
