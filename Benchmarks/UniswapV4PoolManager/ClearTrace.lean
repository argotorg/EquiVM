import Benchmarks.UniswapV4PoolManager.AccountDeltaTrace
import Benchmarks.UniswapV4PoolManager.SafeCast
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_006
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_012
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_013

/-! The `clear` bytecode after canonical ABI decoding. -/
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem clearLoadTrace {I : ExecutionEnv} {g : Sat256} {s0 : State} {evm : EVM.State}
    {mem rdata : ByteArray} {aw : UInt256} {currency : AccountAddress} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length + 5 ≤ 1024) (hI : evm.executionEnv = I)
    (h : RD (deployedRuntime v) I g s0 ⟨3558⟩ (accountWord currency :: R) mem aw rdata evm.accountMap k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨12458⟩
      (calldataWord I.calldata 36 :: ⟨3604⟩ :: transientWord evm (currencyDeltaSlot I.source currency) :: accountWord currency :: R)
      (currencyDeltaMemory I.source currency mem) aw' rdata evm.accountMap k' C' := by
  have hj : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 12458) = true := by
    rw [deployedRuntime_jumps]; jump_dest
  obtain ⟨aw', k', C', hcast⟩ := poolManagerBlocks.poolManager_block_3558_packed hstack hj h
  have hm : poolManagerBlocks.poolManager_block_3558_memory (ee := I) (mem := mem) (x0 := accountWord currency) =
      currencyDeltaMemory I.source currency mem := by
    change twoWordHashMem (accountWord I.source) (UInt256.land (accountWord currency) solcAddrMask) mem = _
    rw [solcAddrMask_clean (accountWord_canonical currency)]; rfl
  change RD (deployedRuntime v) I g s0 ⟨12458⟩
    (calldataWord I.calldata 36 :: ⟨3604⟩ :: codeOwnerTransientWord I evm.accountMap
      (keccakWord ⟨0⟩ ⟨64⟩ (poolManagerBlocks.poolManager_block_3558_memory
        (ee := I) (mem := mem) (x0 := accountWord currency))) :: accountWord currency :: R)
    (poolManagerBlocks.poolManager_block_3558_memory (ee := I) (mem := mem) (x0 := accountWord currency))
    aw' rdata evm.accountMap k' C' at hcast
  rw [hm] at hcast
  have hhash : keccakWord ⟨0⟩ ⟨64⟩ (currencyDeltaMemory I.source currency mem) = currencyDeltaSlot I.source currency :=
    mappingMemory_slot_any _ _ _
  rw [hhash, ← transientWord_accountMap hI] at hcast
  exact ⟨_, _, _, hcast⟩

def clearTraceResult (v : PoolManagerImmutables) (I : ExecutionEnv) (g : Sat256) (s0 : State)
    (evm : EVM.State) (currency : AccountAddress) (amount : UInt256) : Prop :=
  if transientWord evm lockSlot = ⟨0⟩ then RDrev (deployedRuntime v) g s0 else
  if amount.toNat < 2^127 then
    if Int.ofNat amount.toNat = currencyDeltaValue evm I.source currency then
      if amount.toNat ≠ 0 ∧ I.perm = false then RDstatic (deployedRuntime v) g s0 else
      RDret (deployedRuntime v) g s0 (accountDeltaPost evm I.source currency (-(Int.ofNat amount.toNat))).accountMap .empty
    else RDrev (deployedRuntime v) g s0
  else RDrev (deployedRuntime v) g s0

theorem clearTrace {I : ExecutionEnv} {g : Sat256} {s0 : State} {evm : EVM.State}
    {mem rdata : ByteArray} {aw amount : UInt256} {currency : AccountAddress} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length + 9 ≤ 1024) (hI : evm.executionEnv = I)
    (ha : calldataWord I.calldata 36 = amount)
    (h : RD (deployedRuntime v) I g s0 ⟨3518⟩ (accountWord currency :: R) mem aw rdata evm.accountMap k C) :
    clearTraceResult v I g s0 evm currency amount := by
  rw [clearTraceResult]
  by_cases hl : transientWord evm lockSlot = ⟨0⟩
  · rw [if_pos hl]
    have hj : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 1239) = true := by
      rw [deployedRuntime_jumps]; jump_dest
    have hrev := poolManagerBlocks.poolManager_block_3518_taken
      (by simp only [List.length_cons]; omega)
      (by change UInt256.isZero (codeOwnerTransientWord I evm.accountMap lockSlot) ≠ ⟨0⟩
          rw [← transientWord_accountMap hI, hl]; decide) hj h
    exact poolManagerBlocks.poolManager_block_1239 (by simp only [List.length_cons]; omega) hrev
  · rw [if_neg hl]
    generalize hcurrent : currencyDeltaValue evm I.source currency = currentValue at ⊢
    have hload := poolManagerBlocks.poolManager_block_3518_fallthrough
      (by simp only [List.length_cons]; omega)
      (by change UInt256.isZero (codeOwnerTransientWord I evm.accountMap lockSlot) = ⟨0⟩
          rw [← transientWord_accountMap hI]; exact isZero_eq_zero_of_ne hl) h
    obtain ⟨aw', k', C', hcast⟩ := clearLoadTrace v (by omega) hI hload
    rw [ha] at hcast
    by_cases hfit : amount.toNat < 2^127
    · rw [if_pos hfit]
      have hj : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 3604) = true := by
        rw [deployedRuntime_jumps]; jump_dest
      obtain ⟨k'', C'', heqCheck⟩ := uintToInt128Trace v (by simp only [List.length_cons]; omega) hfit hj hcast
      let previous := transientWord evm (currencyDeltaSlot I.source currency)
      have heqIff : Int.ofNat amount.toNat = currencyDeltaValue evm I.source currency ↔ amount = previous := by
        rw [currencyDeltaValue, eq_comm, signedWord_eq_nat_iff previous amount.toNat (by change amount.toNat < 2^255; omega)]
        exact ⟨fun he => (u256_inj he).symm, fun he => congrArg UInt256.toNat he.symm⟩
      by_cases heqValue : Int.ofNat amount.toNat = currentValue
      · rw [if_pos heqValue]
        have heq : Int.ofNat amount.toNat = currencyDeltaValue evm I.source currency := heqValue.trans hcurrent.symm
        have hnext := poolManagerBlocks.poolManager_block_3604_fallthrough
          (by simp only [List.length_cons]; omega)
          (by change UInt256.sub (UInt256.signextend ⟨15⟩ amount) previous = ⟨0⟩
              rw [signextend128_of_lt amount hfit]; exact u256_sub_eq_zero_iff_eq.mpr (heqIff.mp heq)) heqCheck
        have hjAccount : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 12528) = true := by
          rw [deployedRuntime_jumps]; jump_dest
        have haccount := poolManagerBlocks.poolManager_block_3615
          (by change R.length + 5 ≤ 1024; omega) hjAccount hnext
        have hlo : -(2^127 : Int) ≤ -(Int.ofNat amount.toNat) := by simp only [Int.ofNat_eq_natCast]; omega
        have hhi : -(Int.ofNat amount.toNat) < (2^127 : Int) := by simp only [Int.ofNat_eq_natCast]; omega
        change RD (deployedRuntime v) I g s0 ⟨12528⟩
          (accountWord currency :: UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ amount) :: accountWord I.source :: ⟨3631⟩ :: R)
          (currencyDeltaMemory I.source currency mem) aw' rdata evm.accountMap _ _ at haccount
        rw [← wordOfInt_neg_natCast_eq_sub_zero, signextend128_wordOfInt hlo hhi] at haccount
        have hjRet : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 3631) = true := by
          rw [deployedRuntime_jumps]; jump_dest
        have hdone := accountDeltaTrace v hstack hI hlo hhi hjRet haccount
        rw [accountDeltaTraceResult] at hdone
        have hsum : currencyDeltaValue evm I.source currency + -(Int.ofNat amount.toNat) = 0 := by rw [← heq]; omega
        have hsumFit : int256Fits (currencyDeltaValue evm I.source currency + -(Int.ofNat amount.toNat)) := by
          rw [hsum]; constructor <;> decide
        by_cases hz : amount.toNat = 0
        · have hzInt : -(Int.ofNat amount.toNat) = 0 := by rw [hz]; rfl
          rw [if_pos hzInt] at hdone
          rw [if_neg (by simp only [hz, ne_eq, not_true_eq_false, false_and, not_false_eq_true]),
            accountDeltaPost, if_pos hzInt]
          obtain ⟨awf, kf, Cf, hstop⟩ := hdone
          exact poolManagerBlocks.poolManager_block_3631 (by omega) hstop
        · have hzInt : -(Int.ofNat amount.toNat) ≠ 0 := by simp only [Int.ofNat_eq_natCast]; omega
          rw [if_neg hzInt, if_pos hsumFit] at hdone
          by_cases hp : I.perm = false
          · rw [if_pos hp] at hdone
            rw [if_pos ⟨hz, hp⟩]; exact hdone
          · rw [if_neg hp] at hdone
            rw [if_neg (fun he => hp he.2)]
            obtain ⟨awf, kf, Cf, hstop⟩ := hdone
            exact poolManagerBlocks.poolManager_block_3631 (by omega) hstop
      · rw [if_neg heqValue]
        have heq : Int.ofNat amount.toNat ≠ currencyDeltaValue evm I.source currency :=
          fun he => heqValue (he.trans hcurrent)
        have hj : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 3633) = true := by
          rw [deployedRuntime_jumps]; jump_dest
        have hrev := poolManagerBlocks.poolManager_block_3604_taken
          (by simp only [List.length_cons]; omega)
          (by change UInt256.sub (UInt256.signextend ⟨15⟩ amount) previous ≠ ⟨0⟩
              rw [signextend128_of_lt amount hfit]
              exact fun he => heq (heqIff.mpr (u256_sub_eq_zero_iff_eq.mp he))) hj heqCheck
        exact poolManagerBlocks.poolManager_block_3633 (by change R.length + 1 + 1 + 2 ≤ 1024; omega) hrev
    · rw [if_neg hfit]
      exact uintToInt128TraceReverts v (by simp only [List.length_cons]; omega) hfit hcast

end Benchmarks.UniswapV4PoolManager
