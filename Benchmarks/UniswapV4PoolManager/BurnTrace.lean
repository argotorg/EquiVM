import Benchmarks.UniswapV4PoolManager.CurrencyId
import Benchmarks.UniswapV4PoolManager.SafeCast
import Benchmarks.UniswapV4PoolManager.AccountDeltaTrace
import Benchmarks.UniswapV4PoolManager.BurnFromTrace

/-! Public burn bytecode: checked amount, currency accounting, then ERC6909 burnFrom. -/
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def burnAccountTraceResult (v : PoolManagerImmutables) (I : ExecutionEnv) (g : Sat256) (s0 : State)
    (evm : EVM.State) (sender : UInt256) (currency : AccountAddress) (amount : UInt256) : Prop :=
  if amount.toNat = 0 then burnFromTraceResult v I g s0 evm sender (accountWord currency) amount else
  if int256Fits (currencyDeltaValue evm I.source currency + Int.ofNat amount.toNat) then
    if I.perm = false then RDstatic (deployedRuntime v) g s0 else
    burnFromTraceResult v I g s0 (accountDeltaPost evm I.source currency (Int.ofNat amount.toNat))
      sender (accountWord currency) amount
  else RDrev (deployedRuntime v) g s0

theorem burnAccountTrace {I : ExecutionEnv} {g : Sat256} {s0 : State} {evm : EVM.State}
    {mem rdata : ByteArray} {aw sender amount extra : UInt256} {currency : AccountAddress} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length + 17 ≤ 1024) (hmem : mem.size = 96)
    (hI : evm.executionEnv = I) (hcs : sender.toNat < EVM.addressModulus) (hfit : amount.toNat < 2^127)
    (h : RD (deployedRuntime v) I g s0 ⟨12528⟩
      (accountWord currency :: EVM.wordOfInt (Int.ofNat amount.toNat) :: accountWord I.source :: ⟨955⟩ ::
        burnFromStack sender (accountWord currency) amount (extra :: R)) mem aw rdata evm.accountMap k C) :
    burnAccountTraceResult v I g s0 evm sender currency amount := by
  have hlo : -(2^127 : Int) ≤ Int.ofNat amount.toNat := by simp only [Int.ofNat_eq_natCast]; omega
  have hhi : Int.ofNat amount.toNat < (2^127 : Int) := by simp only [Int.ofNat_eq_natCast]; omega
  have hj : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 955) = true := by
    rw [deployedRuntime_jumps]; jump_dest
  have haccount := accountDeltaTrace v (by change R.length + 1 + 7 + 9 ≤ 1024; omega) hI hlo hhi hj h
  rw [accountDeltaTraceResult] at haccount
  rw [burnAccountTraceResult]
  generalize hnext : currencyDeltaValue evm I.source currency + Int.ofNat amount.toNat = nextValue at haccount ⊢
  by_cases hz : amount.toNat = 0
  · rw [if_pos hz]
    have hzInt : Int.ofNat amount.toNat = 0 := by rw [hz]; rfl
    rw [if_pos hzInt] at haccount
    obtain ⟨aw', k', C', hburn⟩ := haccount
    exact burnFromTrace v (by omega) hmem hI hcs hburn
  · rw [if_neg hz]
    have hzInt : Int.ofNat amount.toNat ≠ 0 := by simp only [Int.ofNat_eq_natCast]; omega
    rw [if_neg hzInt] at haccount
    by_cases hsum : int256Fits nextValue
    · rw [if_pos hsum] at haccount ⊢
      by_cases hp : I.perm = false
      · rw [if_pos hp] at haccount ⊢; exact haccount
      · rw [if_neg hp] at haccount ⊢
        obtain ⟨aw', k', C', hburn⟩ := haccount
        have hmem' : (currencyDeltaMemory I.source currency mem).size = 96 := twoWordHashMem_size_96 _ _ hmem
        exact burnFromTrace v (by omega) hmem' ((accountDeltaPost_env _ _ _ _).trans hI) hcs hburn
    · rw [if_neg hsum] at haccount ⊢; exact haccount

def burnTraceResult (v : PoolManagerImmutables) (I : ExecutionEnv) (g : Sat256) (s0 : State)
    (evm : EVM.State) (sender id amount : UInt256) : Prop :=
  if transientWord evm lockSlot = ⟨0⟩ then RDrev (deployedRuntime v) g s0 else
  if amount.toNat < 2^127 then burnAccountTraceResult v I g s0 evm sender (AccountAddress.ofNat id.toNat) amount
  else RDrev (deployedRuntime v) g s0

theorem burnTrace {I : ExecutionEnv} {g : Sat256} {s0 : State} {evm : EVM.State}
    {mem rdata : ByteArray} {aw sender id amount extra : UInt256} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length + 17 ≤ 1024) (hmem : mem.size = 96)
    (hI : evm.executionEnv = I) (hcs : sender.toNat < EVM.addressModulus)
    (h : RD (deployedRuntime v) I g s0 ⟨834⟩ (amount :: id :: sender :: extra :: R) mem aw rdata evm.accountMap k C) :
    burnTraceResult v I g s0 evm sender id amount := by
  rw [burnTraceResult]
  by_cases hl : transientWord evm lockSlot = ⟨0⟩
  · rw [if_pos hl]
    have hj : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 1239) = true := by
      rw [deployedRuntime_jumps]; jump_dest
    have hrev := poolManagerBlocks.poolManager_block_834_taken
      (by simp only [List.length_cons]; omega)
      (by change UInt256.isZero (codeOwnerTransientWord I evm.accountMap lockSlot) ≠ ⟨0⟩
          rw [← transientWord_accountMap hI, hl]; decide) hj h
    exact poolManagerBlocks.poolManager_block_1239 (by change R.length + 4 + 2 ≤ 1024; omega) hrev
  · rw [if_neg hl]
    have hunlocked := poolManagerBlocks.poolManager_block_834_fallthrough
      (by simp only [List.length_cons]; omega)
      (by change UInt256.isZero (codeOwnerTransientWord I evm.accountMap lockSlot) = ⟨0⟩
          rw [← transientWord_accountMap hI]; exact isZero_eq_zero_of_ne hl) h
    have hjCast : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 12458) = true := by
      rw [deployedRuntime_jumps]; jump_dest
    have hcast := poolManagerBlocks.poolManager_block_874 (by simp only [List.length_cons]; omega) hjCast hunlocked
    change RD (deployedRuntime v) I g s0 ⟨12458⟩
      (amount :: ⟨947⟩ :: ⟨955⟩ :: burnFromStack sender (UInt256.land id solcAddrMask) amount (extra :: R))
      mem aw rdata evm.accountMap _ _ at hcast
    rw [← accountWord_fromId] at hcast
    by_cases hfit : amount.toNat < 2^127
    · rw [if_pos hfit]
      have hjReturn : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 947) = true := by
        rw [deployedRuntime_jumps]; jump_dest
      obtain ⟨k', C', hprepare⟩ := uintToInt128Trace v
        (by change R.length + 1 + 7 + 1 + 4 ≤ 1024; omega) hfit hjReturn hcast
      have hjAccount : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 12528) = true := by
        rw [deployedRuntime_jumps]; jump_dest
      have haccount := poolManagerBlocks.poolManager_block_947
        (by change R.length + 1 + 12 ≤ 1024; omega) hjAccount hprepare
      change RD (deployedRuntime v) I g s0 ⟨12528⟩
        (accountWord (AccountAddress.ofNat id.toNat) :: amount :: accountWord I.source :: ⟨955⟩ ::
          burnFromStack sender (accountWord (AccountAddress.ofNat id.toNat)) amount (extra :: R))
        mem aw rdata evm.accountMap _ _ at haccount
      apply burnAccountTrace v hstack hmem hI hcs hfit
      rwa [wordOfInt_ofNat_toNat]
    · rw [if_neg hfit]
      exact uintToInt128TraceReverts v (by change R.length + 1 + 7 + 1 + 1 + 3 ≤ 1024; omega) hfit hcast

end Benchmarks.UniswapV4PoolManager
