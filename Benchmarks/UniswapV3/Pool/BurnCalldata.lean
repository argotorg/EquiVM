import Benchmarks.UniswapV3.Pool.LegacyThreeInts
import Benchmarks.UniswapV3.Pool.LegacyAddressFourInts
import Benchmarks.UniswapV3.Pool.BurnModel
import Benchmarks.UniswapV3.Pool.ProtocolFeeStorage
import Benchmarks.UniswapV3.Pool.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def burnArgs (cd : ByteArray) : BurnArgs :=
  {lower := positionTick (calldataWord cd 4), upper := positionTick (calldataWord cd 36),
    amount := uint128Word (calldataWord cd 68)}

theorem burnArgs_fits (cd : ByteArray) : (burnArgs cd).Fits := by
  dsimp only [burnArgs, BurnArgs.Fits, positionTick]
  exact ⟨normalizeSint_bounds ⟨24, by decide⟩ (Int.ofNat (calldataWord cd 4).toNat),
    normalizeSint_bounds ⟨24, by decide⟩ (Int.ofNat (calldataWord cd 36).toNat), uint128Word_lt _⟩

theorem burnDecode {cd : ByteArray} (hlen : 100 ≤ cd.size) :
    decodeCalldataWithMode config.abiDecodeMode (burnTransition.params.map Param.name)
      (transitionSignature burnTransition).paramTypes cd = some (burnLocals (burnArgs cd)) := by
  have h := decodeCalldata_legacyThreeInts_ok
    (.sint ⟨24, by decide⟩) (.sint ⟨24, by decide⟩) (.uint ⟨128, by decide⟩)
    (x := "tickLower") (y := "tickUpper") (z := "amount") hlen
  rw [normalizeUIntWord_mask ⟨128, by decide⟩ (calldataWord cd 68)
    (UInt256.ofNat (2 ^ 128 - 1)) (by decide), u256_land_comm] at h
  simpa only [burnArgs, burnLocals, positionTick, uint128Word] using h

theorem burnDecodeShort {cd : ByteArray} (hshort : cd.size < 100) :
    decodeCalldataWithMode config.abiDecodeMode (burnTransition.params.map Param.name)
      (transitionSignature burnTransition).paramTypes cd = none :=
  decodeCalldata_legacyScalarWords_none_short rfl hshort

theorem uniswapV3PoolBurnDecodedX {σ σ₀ A I} {g : Sat256}
    (v : UniswapV3PoolImmutables) (hcode : I.code = deployedRuntime v)
    (hwv : I.weiValue = ⟨0⟩) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (uniswapV3PoolSelBytes 17))
    (hlen : 100 ≤ I.calldata.size) :
    ∃ k C, RD (deployedRuntime v) I g (initState σ σ₀ g A I) ⟨9577⟩
      [(burnArgs I.calldata).amount, EVM.wordOfInt (burnArgs I.calldata).upper,
        EVM.wordOfInt (burnArgs I.calldata).lower, ⟨621⟩, solcSelectorWord I]
      solcFreePtrMem ⟨3⟩ ByteArray.empty σ k C := by
  obtain ⟨k0, C0, r0⟩ := uniswapV3PoolReachBurnBody
    (g := g) (σ := σ) (σ₀ := σ₀) (A := A) v hcode hwv hsz hsize hsel
  have r1 := uniswapV3Pool_block_1852_taken (immWords := wordsOf (immStore v))
    (by simp) (by rw [solcDecodeLenCheckOkUnsigned (by exact hlen) hsize]; decide)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r0
  simp only [uniswapV3Pool_block_1852_taken_stack] at r1
  have r2 := uniswapV3Pool_block_1874 (immWords := wordsOf (immStore v)) (by simp)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
  simp only [uniswapV3Pool_block_1874_stack, solcMask128] at r2
  change RD (deployedRuntime v) I g (initState σ σ₀ g A I) ⟨9577⟩
    [uint128Word (calldataWord I.calldata 68), positionTickWord (calldataWord I.calldata 36),
      positionTickWord (calldataWord I.calldata 4), ⟨621⟩, solcSelectorWord I]
    solcFreePtrMem ⟨3⟩ ByteArray.empty σ _ _ at r2
  rw [positionTickWord_eq, positionTickWord_eq] at r2
  exact ⟨_, _, by simpa only [burnArgs] using r2⟩

theorem uniswapV3PoolBurnShortX {σ σ₀ A I} {g : Sat256}
    (v : UniswapV3PoolImmutables) (hcode : I.code = deployedRuntime v)
    (hwv : I.weiValue = ⟨0⟩) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (uniswapV3PoolSelBytes 17))
    (hshort : I.calldata.size < 100) : RDrev (deployedRuntime v) g (initState σ σ₀ g A I) := by
  obtain ⟨k0, C0, r0⟩ := uniswapV3PoolReachBurnBody
    (g := g) (σ := σ) (σ₀ := σ₀) (A := A) v hcode hwv hsz hsize hsel
  have r1 := uniswapV3Pool_block_1852_fallthrough (immWords := wordsOf (immStore v))
    (by simp) (by rw [solcDecodeLenCheckShortUnsigned (by exact hsz) (by exact hshort) hsize]; decide) r0
  simp only [uniswapV3Pool_block_1852_fallthrough_stack] at r1
  exact uniswapV3Pool_block_1870 (immWords := wordsOf (immStore v)) (by simp) r1

end Benchmarks.UniswapV3.Pool
