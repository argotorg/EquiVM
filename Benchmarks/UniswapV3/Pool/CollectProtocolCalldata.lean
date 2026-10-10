import Benchmarks.UniswapV3.Pool.LegacyAddressInts
import Benchmarks.UniswapV3.Pool.CollectProtocolSource
import Benchmarks.UniswapV3.Pool.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def collectProtocolRequestedWord (cd : ByteArray) (second : Bool) : UInt256 :=
  UInt256.land (calldataWord cd (if second then 68 else 36)) (UInt256.ofNat (2 ^ 128 - 1))

def collectProtocolRecipient (cd : ByteArray) : AccountAddress :=
  AccountAddress.ofNat (calldataWord cd 4).toNat

theorem collectProtocolRequestedWord_lt (cd : ByteArray) (second : Bool) :
    (collectProtocolRequestedWord cd second).toNat < 2 ^ 128 :=
  u256LandMaskToNatLtOfToNat _ _ (by decide)

theorem collectProtocolDecode {cd : ByteArray} (hlen : 100 ≤ cd.size) :
    decodeCalldataWithMode config.abiDecodeMode (collectProtocolTransition.params.map Param.name)
      (transitionSignature collectProtocolTransition).paramTypes cd =
      some (collectProtocolLocals (collectProtocolRecipient cd)
        (collectProtocolRequestedWord cd false) (collectProtocolRequestedWord cd true)) := by
  have h := decodeCalldata_legacyAddress_int_int_ok (.uint ⟨128, by decide⟩) (.uint ⟨128, by decide⟩)
    (x := "recipient") (y := "amount0Requested") (z := "amount1Requested") hlen
  rw [normalizeUIntWord_mask ⟨128, by decide⟩ (calldataWord cd 36) (UInt256.ofNat (2 ^ 128 - 1))
    (by decide), normalizeUIntWord_mask ⟨128, by decide⟩ (calldataWord cd 68)
      (UInt256.ofNat (2 ^ 128 - 1)) (by decide)] at h
  exact h

theorem collectProtocolDecodeShort {cd : ByteArray} (hsz : 4 ≤ cd.size) (hshort : cd.size < 100) :
    decodeCalldataWithMode config.abiDecodeMode (collectProtocolTransition.params.map Param.name)
      (transitionSignature collectProtocolTransition).paramTypes cd = none :=
  decodeCalldata_legacyAddress_int_int_none_short (.uint ⟨128, by decide⟩) (.uint ⟨128, by decide⟩) hsz hshort

theorem uniswapV3PoolCollectProtocolDecodedX {σ σ₀ A I} {g : Sat256}
    (v : UniswapV3PoolImmutables) (hcode : I.code = deployedRuntime v)
    (hwv : I.weiValue = ⟨0⟩) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (uniswapV3PoolSelBytes 15))
    (hlen : 100 ≤ I.calldata.size) :
    ∃ k C, RD (deployedRuntime v) I g (initState σ σ₀ g A I) ⟨8719⟩
      [collectProtocolRequestedWord I.calldata true, collectProtocolRequestedWord I.calldata false,
       EVM.word (collectProtocolRecipient I.calldata).val, UInt256.ofNat 690, solcSelectorWord I]
      solcFreePtrMem ⟨3⟩ ByteArray.empty σ k C := by
  obtain ⟨_, _, rdEntry⟩ := uniswapV3PoolReachCollectProtocolBody
    (g := g) (σ := σ) (σ₀ := σ₀) (A := A) v hcode hwv hsz hsize hsel
  have rdDecode := uniswapV3Pool_block_1526_taken (immWords := wordsOf (immStore v))
    (by simp) (by rw [solcDecodeLenCheckOkUnsigned (by exact hlen) hsize]; decide)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdEntry
  simp only [uniswapV3Pool_block_1526_taken_stack] at rdDecode
  have rdRead := uniswapV3Pool_block_1548 (immWords := wordsOf (immStore v)) (by simp)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdDecode
  have hmask : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
      (UInt256.ofNat 1) = solcAddrMask := by native_decide
  simp only [uniswapV3Pool_block_1548_stack, solcMask128, hmask] at rdRead
  change RD (deployedRuntime v) I g (initState σ σ₀ g A I) ⟨8719⟩
    [UInt256.land (calldataWord I.calldata 68) (UInt256.ofNat (2 ^ 128 - 1)),
     UInt256.land (UInt256.ofNat (2 ^ 128 - 1)) (calldataWord I.calldata 36),
     UInt256.land (calldataWord I.calldata 4) solcAddrMask,
     UInt256.ofNat 690, solcSelectorWord I] solcFreePtrMem ⟨3⟩ ByteArray.empty σ _ _ at rdRead
  rw [u256_land_comm (UInt256.ofNat (2 ^ 128 - 1)), ← word_of_addressOfNat_eq_mask] at rdRead
  exact ⟨_, _, rdRead⟩

theorem uniswapV3PoolCollectProtocolShortX {σ σ₀ A I} {g : Sat256}
    (v : UniswapV3PoolImmutables) (hcode : I.code = deployedRuntime v)
    (hwv : I.weiValue = ⟨0⟩) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (uniswapV3PoolSelBytes 15))
    (hshort : I.calldata.size < 100) : RDrev (deployedRuntime v) g (initState σ σ₀ g A I) := by
  obtain ⟨_, _, rdEntry⟩ := uniswapV3PoolReachCollectProtocolBody
    (g := g) (σ := σ) (σ₀ := σ₀) (A := A) v hcode hwv hsz hsize hsel
  have rdShort := uniswapV3Pool_block_1526_fallthrough (immWords := wordsOf (immStore v))
    (by simp) (by rw [solcDecodeLenCheckShortUnsigned (by exact hsz) (by exact hshort) hsize]; decide) rdEntry
  simp only [uniswapV3Pool_block_1526_fallthrough_stack] at rdShort
  exact uniswapV3Pool_block_1544 (immWords := wordsOf (immStore v)) (by simp) rdShort

end Benchmarks.UniswapV3.Pool
