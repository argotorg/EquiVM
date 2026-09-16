import Examples.UniswapV2Pair.BurnTailSource
import Examples.UniswapV2Pair.BurnKLastRuntime
import Examples.UniswapV2Pair.BurnEventRuntime
import Examples.UniswapV2Pair.BurnReturnRuntime
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

set_option maxHeartbeats 1000000 in
theorem uniswapBurnAfterUpdateRuntimeReturns {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {supply feeWord liquidity balance1 balance0 token1 token0 reserve1 reserve0 amount1 amount0 toWord : UInt256}
    {aw ptr : UInt256} {R : List UInt256} {mem rdata : ByteArray} {k C : Nat}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {locals : Store}
    (evm : EVM.State) (fee : Bool)
    (rd : RD uniswapV2PairBytecode I g s0 ⟨4885⟩
      (supply :: feeWord :: liquidity :: balance1 :: balance0 :: token1 :: token0 :: reserve1 :: reserve0 ::
        amount1 :: amount0 :: toWord :: ⟨1201⟩ :: R) mem aw rdata (cA, σ) k C)
    (hAccounts : accountMapEquiv σ evm.accountMap) (henv : evm.executionEnv = I)
    (hflag : feeWord = if fee then ⟨1⟩ else ⟨0⟩)
    (hfee : locals.get? "feeOn" = some (.bool fee))
    (ha0 : locals.get? "amount0" = some (uniswapUint256Value amount0))
    (ha1 : locals.get? "amount1" = some (uniswapUint256Value amount1))
    (hr0 : locals.get? "reserve0" = none) (hr1 : locals.get? "reserve1" = none)
    (hk : locals.get? "kLast" = none) (hu : locals.get? "unlocked" = none)
    (hin : 96 ≤ mem.size) (hlo : 96 ≤ ptr.toNat) (hgap : ptr.toNat - mem.size < USize.size)
    (hfit : ptr.toNat + 95 < UInt256.size) (haw : aw.toNat * 32 < UInt256.size)
    (hcover : ptr.toNat + 64 ≤ aw.toNat * 32) (hread : mem.readWithPadding 64 32 = ptr.toByteArray)
    (hperm : I.perm = true) (hov : R.length + 23 ≤ 1024) :
    ∃ evm' σ',
      ExecBlock config { contract := contract, locals := locals } evm burnAfterUpdateTail
        (.returned { contract := contract, locals := locals } evm'
          (some [uniswapUint256Value amount0, uniswapUint256Value amount1])) ∧
      accountMapEquiv σ' evm'.accountMap ∧ evm'.createdAccounts = evm.createdAccounts ∧
      RDret uniswapV2PairBytecode g s0 (cA, σ') (amount0.toByteArray ++ amount1.toByteArray) := by
  have hKLast : ∃ σK kK CK,
      accountMapEquiv σK (uniswapKLastIfFeeState evm fee).accountMap ∧
      RD uniswapV2PairBytecode I g s0 ⟨4933⟩
        (supply :: feeWord :: liquidity :: balance1 :: balance0 :: token1 :: token0 :: reserve1 :: reserve0 ::
          amount1 :: amount0 :: toWord :: ⟨1201⟩ :: R) mem aw rdata (cA, σK) kK CK := by
    cases fee with
    | false =>
      obtain ⟨_, _, rd4933⟩ := RD.uniswapBurnAfterUpdateFeeOff rd hflag (by simp only [List.length_cons]; omega)
      exact ⟨σ, _, _, hAccounts, rd4933⟩
    | true =>
      have hslot8 : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ = uniswapSlotWord ⟨8⟩ σ I := by
        have h := accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨8⟩ ⟨0⟩
        simpa only [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage, uniswapSlotWord, henv] using h.symm
      have hkValue : mintFeeReserveProductWord (uniswapReserve0Word evm) (uniswapReserve1Word evm) =
          UInt256.mul (UInt256.land (uniswapSlotWord ⟨8⟩ σ I) reserve112Mask)
            (UInt256.land (UInt256.div (uniswapSlotWord ⟨8⟩ σ I) reserve112Shift) reserve112Mask) := by
        rw [mintFeeReserveProductWord_eq_mul _ _ (mintFeeReserveProductNat_source_lt evm)]
        simp only [uniswapReserve0Word, uniswapReserve1Word, hslot8]
      obtain ⟨_, _, rd4933⟩ := RD.uniswapBurnAfterUpdateFeeOn rd (by rw [hflag]; decide)
        (mintFeeReserveProductNat_masked_lt _) hperm (by simp only [List.length_cons]; omega)
      refine ⟨_, _, _, ?_, rd4933⟩
      simpa only [uniswapKLastIfFeeState, ↓reduceIte, mintKLastUpdatedState,
        storageStore_accountMap, henv, hkValue] using
        accountMapEquiv_sstoreAccountMap I.codeOwner ⟨11⟩
          (mintFeeReserveProductWord (uniswapReserve0Word evm) (uniswapReserve1Word evm)) hAccounts
  obtain ⟨σK, _, _, hAccountsK, rd4933⟩ := hKLast
  have heK : (uniswapKLastIfFeeState evm fee).executionEnv = I := by
    cases fee <;> simp only [uniswapKLastIfFeeState, Bool.false_eq_true, ↓reduceIte,
      mintKLastUpdatedState, storageStore_executionEnv, henv]
  obtain ⟨_, _, rd5006⟩ := RD.uniswapBurnEmitEvent rd4933 hin hlo hgap hfit haw hcover hread hperm (by omega)
  obtain ⟨_, _, rd1201⟩ := RD.uniswapBurnUnlockAndJump rd5006 hperm (by native_decide) (by omega)
  have hsLog := (pairDynamicMem_sizes ptr amount0 amount1 hgap (by omega)).2
  have hgLog : ptr.toNat - (pairDynamicMem mem ptr amount0 amount1).size < USize.size := by
    rw [hsLog]
    have hz : 0 < USize.size := lt_usize 0 (by omega)
    omega
  have hreadLog := (pairDynamicMem_read_below ptr amount0 amount1 64 hin hlo hgap (by omega)).trans hread
  have rdRet := RD.uniswapBurnReturnPair rd1201 (by rw [hsLog]; omega) hlo hgLog hfit haw hcover hreadLog (by omega)
  refine ⟨uniswapLockExitedState (uniswapKLastIfFeeState evm fee), _,
    uniswapBurnAfterUpdateSourceReturns evm fee amount0 amount1 hfee ha0 ha1 hr0 hr1 hk hu, ?_, ?_, rdRet⟩
  · simpa only [uniswapLockExitedState, uniswapUnlockedState, storageStore_accountMap, heK] using
      accountMapEquiv_sstoreAccountMap I.codeOwner ⟨12⟩ ⟨1⟩ hAccountsK
  · cases fee <;> simp only [uniswapLockExitedState, uniswapUnlockedState, uniswapKLastIfFeeState,
      Bool.false_eq_true, ↓reduceIte, mintKLastUpdatedState, storageStore_createdAccounts]

end UniswapV2Pair
