import Benchmarks.UniswapV3.Pool.LegacyAddressFourInts
import Benchmarks.UniswapV3.Pool.CollectSource
import Benchmarks.UniswapV3.Pool.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def collectRequestedWord (cd : ByteArray) (second : Bool) : UInt256 :=
  UInt256.land (calldataWord cd (if second then 132 else 100)) (UInt256.ofNat (2 ^ 128 - 1))

def collectRecipient (cd : ByteArray) : AccountAddress :=
  AccountAddress.ofNat (calldataWord cd 4).toNat

theorem collectRequestedWord_lt (cd : ByteArray) (second : Bool) :
    (collectRequestedWord cd second).toNat < 2 ^ 128 :=
  u256LandMaskToNatLtOfToNat _ _ (by decide)

theorem collectDecode {cd : ByteArray} (hlen : 164 ≤ cd.size) :
    decodeCalldataWithMode config.abiDecodeMode (collectTransition.params.map Param.name)
      (transitionSignature collectTransition).paramTypes cd =
      some (collectLocals (collectRecipient cd) (calldataWord cd 36) (calldataWord cd 68)
        (collectRequestedWord cd false) (collectRequestedWord cd true)) := by
  have h := decodeCalldata_legacyAddress_fourInts_ok
    (.sint ⟨24, by decide⟩) (.sint ⟨24, by decide⟩)
    (.uint ⟨128, by decide⟩) (.uint ⟨128, by decide⟩)
    (x := "recipient") (y := "tickLower") (z := "tickUpper")
    (u := "amount0Requested") (w := "amount1Requested") hlen
  rw [normalizeUIntWord_mask ⟨128, by decide⟩ (calldataWord cd 100) (UInt256.ofNat (2 ^ 128 - 1))
    (by decide), normalizeUIntWord_mask ⟨128, by decide⟩ (calldataWord cd 132)
      (UInt256.ofNat (2 ^ 128 - 1)) (by decide)] at h
  exact h

theorem collectDecodeShort {cd : ByteArray} (hshort : cd.size < 164) :
    decodeCalldataWithMode config.abiDecodeMode (collectTransition.params.map Param.name)
      (transitionSignature collectTransition).paramTypes cd = none :=
  decodeCalldata_legacyScalarWords_none_short rfl hshort

theorem uniswapV3PoolCollectDecodedX {σ σ₀ A I} {g : Sat256}
    (v : UniswapV3PoolImmutables) (hcode : I.code = deployedRuntime v)
    (hwv : I.weiValue = ⟨0⟩) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (uniswapV3PoolSelBytes 10))
    (hlen : 164 ≤ I.calldata.size) :
    ∃ k C, RD (deployedRuntime v) I g (initState σ σ₀ g A I) ⟨7555⟩
      [collectRequestedWord I.calldata true, collectRequestedWord I.calldata false,
       positionTickWord (calldataWord I.calldata 68), positionTickWord (calldataWord I.calldata 36),
       EVM.word (collectRecipient I.calldata).val, UInt256.ofNat 690, solcSelectorWord I]
      solcFreePtrMem ⟨3⟩ ByteArray.empty σ k C := by
  obtain ⟨_, _, rdEntry⟩ := uniswapV3PoolReachCollectBody
    (g := g) (σ := σ) (σ₀ := σ₀) (A := A) v hcode hwv hsz hsize hsel
  have rdDecode := uniswapV3Pool_block_1276_taken (immWords := wordsOf (immStore v))
    (by simp) (by rw [solcDecodeLenCheckOkUnsigned (by exact hlen) hsize]; decide)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdEntry
  simp only [uniswapV3Pool_block_1276_taken_stack] at rdDecode
  have rdRead := uniswapV3Pool_block_1298 (immWords := wordsOf (immStore v)) (by simp)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdDecode
  have hmask : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
      (UInt256.ofNat 1) = solcAddrMask := by native_decide
  simp only [uniswapV3Pool_block_1298_stack, solcMask128, hmask] at rdRead
  change RD (deployedRuntime v) I g (initState σ σ₀ g A I) ⟨7555⟩
    [UInt256.land (calldataWord I.calldata 132) (UInt256.ofNat (2 ^ 128 - 1)),
     UInt256.land (UInt256.ofNat (2 ^ 128 - 1)) (calldataWord I.calldata 100),
     positionTickWord (calldataWord I.calldata 68), positionTickWord (calldataWord I.calldata 36),
     UInt256.land (calldataWord I.calldata 4) solcAddrMask,
     UInt256.ofNat 690, solcSelectorWord I] solcFreePtrMem ⟨3⟩ ByteArray.empty σ _ _ at rdRead
  rw [u256_land_comm (UInt256.ofNat (2 ^ 128 - 1)), ← word_of_addressOfNat_eq_mask] at rdRead
  exact ⟨_, _, rdRead⟩

theorem uniswapV3PoolCollectShortX {σ σ₀ A I} {g : Sat256}
    (v : UniswapV3PoolImmutables) (hcode : I.code = deployedRuntime v)
    (hwv : I.weiValue = ⟨0⟩) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (uniswapV3PoolSelBytes 10))
    (hshort : I.calldata.size < 164) : RDrev (deployedRuntime v) g (initState σ σ₀ g A I) := by
  obtain ⟨_, _, rdEntry⟩ := uniswapV3PoolReachCollectBody
    (g := g) (σ := σ) (σ₀ := σ₀) (A := A) v hcode hwv hsz hsize hsel
  have rdShort := uniswapV3Pool_block_1276_fallthrough (immWords := wordsOf (immStore v))
    (by simp) (by rw [solcDecodeLenCheckShortUnsigned (by exact hsz) (by exact hshort) hsize]; decide) rdEntry
  simp only [uniswapV3Pool_block_1276_fallthrough_stack] at rdShort
  exact uniswapV3Pool_block_1294 (immWords := wordsOf (immStore v)) (by simp) rdShort

end Benchmarks.UniswapV3.Pool
