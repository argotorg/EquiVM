import Benchmarks.UniswapV3.Pool.FlashProtocolCalc
import Benchmarks.UniswapV3.Pool.FlashProtocolSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def flashProtocolMap (σ : AccountMap) (ee : ExecutionEnv) (second : Bool)
    (fees : UInt256) : AccountMap :=
  if uint128Word fees = ⟨0⟩ then σ else sstoreAccountMap ee.codeOwner σ ⟨3⟩
    (protocolFeeUpdateWord second (solcSlotWordAt ⟨3⟩ σ ee) (protocolFeesWord second σ ee + fees))

theorem SourceState.flashProtocolState {s0 ee σ evm} (hs : SourceState s0 ee σ evm)
    (second : Bool) (fees : UInt256) :
    SourceState s0 ee (flashProtocolMap σ ee second fees) (flashProtocolState evm second fees) := by
  by_cases hz : uint128Word fees = ⟨0⟩
  · simpa only [flashProtocolMap, Benchmarks.UniswapV3.Pool.flashProtocolState, if_pos hz] using hs
  · have h := hs.readModifyWrite ⟨3⟩ (fun old ↦ protocolFeeUpdateWord second old
      (protocolFeesWord second σ ee + fees))
    simpa only [flashProtocolMap, Benchmarks.UniswapV3.Pool.flashProtocolState, if_neg hz,
      storeProtocolFee, hs.accounts, hs.env, solcSlotWordAt] using h

theorem flashProtocolStoreX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw fees junk : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (second : Bool)
    (rd : RD (deployedRuntime v) ee g s0 (flashProtocolStoreEntry second)
      (fees :: junk :: R) mem aw rdata σ k C)
    (hperm : ee.perm = true) (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 (flashGrowthEntry second) (fees :: R)
      mem aw rdata (flashProtocolMap σ ee second fees) k' C' := by
  have hmask : UInt256.land fees (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1)
      (UInt256.ofNat 128)) (UInt256.ofNat 1)) = uint128Word fees := by
    rw [solcMask128, u256_land_comm]; rfl
  cases second
  · by_cases hz : uint128Word fees = ⟨0⟩
    · have rdSkip := uniswapV3Pool_block_7193_taken (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [hmask, hz]; decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
      exact ⟨_, _, by simpa only [flashProtocolMap, if_pos hz] using rdSkip⟩
    · have rdStore := uniswapV3Pool_block_7193_fallthrough (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [hmask]; exact isZero_eq_zero_of_ne hz) rd
      obtain ⟨k', C', rdDone⟩ := uniswapV3Pool_block_7211 (immWords := wordsOf (immStore v))
        hov hperm rdStore
      refine ⟨k', C', ?_⟩
      rw [flashProtocolMap, if_neg hz]
      simpa only [flashGrowthEntry, protocolFeeUpdateWord, Bool.false_eq_true,
        protocolFeesWord, protocolFeesToken0Word, uint128Word, solcSlotWordAt, solcSlotWord, ↓reduceIte,
        solcMask128, u256_lor_comm, u256_add_comm, u256_land_comm] using rdDone
  · by_cases hz : uint128Word fees = ⟨0⟩
    · have rdSkip := uniswapV3Pool_block_7333_taken (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [hmask, hz]; decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
      exact ⟨_, _, by simpa only [flashProtocolMap, if_pos hz] using rdSkip⟩
    · have rdStore := uniswapV3Pool_block_7333_fallthrough (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [hmask]; exact isZero_eq_zero_of_ne hz) rd
      obtain ⟨k', C', rdDone⟩ := uniswapV3Pool_block_7351 (immWords := wordsOf (immStore v))
        hov hperm rdStore
      refine ⟨k', C', ?_⟩
      rw [flashProtocolMap, if_neg hz]
      simp only [solcMask128] at rdDone
      simpa only [flashGrowthEntry, protocolFeeUpdateWord,
        protocolFeesWord, protocolFeesToken1Word, uint128Word, solcSlotWordAt, solcSlotWord, ↓reduceIte,
        solcShift128, u256_lor_comm, u256_add_comm, u256_land_comm] using rdDone

theorem flashProtocolX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : EVM.State} {k C : Nat} {aw paid0 paid1 : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (locals : Store) (second : Bool)
    (rd : RD (deployedRuntime v) ee g s0 (flashProtocolEntry second) (paid1 :: paid0 :: R)
      mem aw rdata σ k C) (hs : SourceState s0 ee σ evm) (hperm : ee.perm = true)
    (hp : locals.get? (flashPaidName second) =
      some (.int (Int.ofNat (if second then paid1 else paid0).toNat)))
    (hslot : locals.get? "slot0" = none) (hfees : locals.get? "protocolFees" = none)
    (hov : R.length + 10 ≤ 1024) :
    let paid := if second then paid1 else paid0
    let divisor := poolProtocolDivisor second σ ee
    let fees := poolProtocolFees paid divisor
    SourceState s0 ee (flashProtocolMap σ ee second fees) (flashProtocolState evm second fees) ∧
      ExecBlock config {contract := contract, locals := locals, immutables := immStore v} evm
        (flashProtocolStmts second)
        (.ok (flashProtocolFrame locals (immStore v) second paid divisor)
          (flashProtocolState evm second fees)) ∧
      ∃ k' C', RD (deployedRuntime v) ee g s0 (flashGrowthEntry second)
        (fees :: divisor :: paid1 :: paid0 :: R) mem aw rdata
        (flashProtocolMap σ ee second fees) k' C' := by
  dsimp only
  refine ⟨SourceState.flashProtocolState hs second _, ?_, ?_⟩
  · have h := flashProtocolSource locals (immStore v) evm second _ hp hslot hfees
    simpa only [← hs.accounts, hs.env] using h
  · obtain ⟨_, _, rdCalc⟩ := flashProtocolCalcX (v := v) second rd (by omega)
    exact flashProtocolStoreX (v := v) second rdCalc hperm (by evm_ov)

end Benchmarks.UniswapV3.Pool
