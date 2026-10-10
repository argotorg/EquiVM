import Benchmarks.UniswapV4PoolManager.CurrencyId
import Benchmarks.UniswapV4PoolManager.SafeCast
import Benchmarks.UniswapV4PoolManager.AccountDeltaTrace
import Benchmarks.UniswapV4PoolManager.BalanceMintTrace

/-! Mint's bytecode from decoded arguments through accounting and ERC6909 credit. -/
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

-- Keep elaboration from evaluating storage hashing when checking this proposition.
@[irreducible] def mintBalanceTraceResult (v : PoolManagerImmutables) (I : ExecutionEnv) (g : Sat256) (s0 : State)
    (evm : EVM.State) (receiver : UInt256) (currency : AccountAddress) (amount : UInt256) : Prop :=
  if (balanceWord evm receiver (accountWord currency)).toNat + amount.toNat < UInt256.size then
    if I.perm = false then RDstatic (deployedRuntime v) g s0 else
    RDret (deployedRuntime v) g s0 (balanceMintPost evm receiver (accountWord currency) amount).accountMap .empty
  else RDrev (deployedRuntime v) g s0

def mintAccountTraceResult (v : PoolManagerImmutables) (I : ExecutionEnv) (g : Sat256) (s0 : State)
    (evm : EVM.State) (receiver : UInt256) (currency : AccountAddress) (amount : UInt256) : Prop :=
  if amount.toNat = 0 then mintBalanceTraceResult v I g s0 evm receiver currency amount else
  if int256Fits (currencyDeltaValue evm I.source currency + -(Int.ofNat amount.toNat)) then
    if I.perm = false then RDstatic (deployedRuntime v) g s0 else
    mintBalanceTraceResult v I g s0 (accountDeltaPost evm I.source currency (-(Int.ofNat amount.toNat)))
      receiver currency amount
  else RDrev (deployedRuntime v) g s0

theorem mintAccountTrace {I : ExecutionEnv} {g : Sat256} {s0 : State} {evm : EVM.State}
    {mem rdata : ByteArray} {aw receiver amount : UInt256} {currency : AccountAddress} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length + 16 ≤ 1024) (hmem : mem.size = 96)
    (hI : evm.executionEnv = I) (hcr : receiver.toNat < EVM.addressModulus) (hfit : amount.toNat < 2^127)
    (h : RD (deployedRuntime v) I g s0 ⟨12528⟩
      (accountWord currency :: EVM.wordOfInt (-(Int.ofNat amount.toNat)) :: accountWord I.source :: ⟨10850⟩ ::
        balanceMintStack receiver (accountWord currency) amount R) mem aw rdata evm.accountMap k C) :
    mintAccountTraceResult v I g s0 evm receiver currency amount := by
  have hlo : -(2^127 : Int) ≤ -(Int.ofNat amount.toNat) := by simp only [Int.ofNat_eq_natCast]; omega
  have hhi : -(Int.ofNat amount.toNat) < (2^127 : Int) := by simp only [Int.ofNat_eq_natCast]; omega
  have hj : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 10850) = true := by
    rw [deployedRuntime_jumps]; jump_dest
  have haccount := accountDeltaTrace v (by change R.length + 7 + 9 ≤ 1024; omega) hI hlo hhi hj h
  rw [accountDeltaTraceResult] at haccount
  rw [mintAccountTraceResult]
  generalize hnext : currencyDeltaValue evm I.source currency + -(Int.ofNat amount.toNat) = nextValue at haccount ⊢
  by_cases hz : amount.toNat = 0
  · rw [if_pos hz]
    have hzInt : -(Int.ofNat amount.toNat) = 0 := by rw [hz]; rfl
    rw [if_pos hzInt] at haccount
    rw [mintBalanceTraceResult]
    generalize hb : balanceWord evm receiver (accountWord currency) = balance at ⊢
    obtain ⟨aw', k', C', hcredit⟩ := haccount
    have hdone := balanceMintTrace v (by omega) hmem hI hcr hcredit
    rwa [hb] at hdone
  · rw [if_neg hz]
    have hzInt : -(Int.ofNat amount.toNat) ≠ 0 := by simp only [Int.ofNat_eq_natCast]; omega
    rw [if_neg hzInt] at haccount
    by_cases hsum : int256Fits nextValue
    · rw [if_pos hsum] at haccount ⊢
      by_cases hp : I.perm = false
      · rw [if_pos hp] at haccount ⊢; exact haccount
      · rw [if_neg hp] at haccount ⊢
        rw [mintBalanceTraceResult]
        generalize hb : balanceWord (accountDeltaPost evm I.source currency (-(Int.ofNat amount.toNat)))
          receiver (accountWord currency) = balance at ⊢
        obtain ⟨aw', k', C', hcredit⟩ := haccount
        have hmem' : (currencyDeltaMemory I.source currency mem).size = 96 :=
          twoWordHashMem_size_96 _ _ hmem
        have hdone := balanceMintTrace v (by omega) hmem' ((accountDeltaPost_env _ _ _ _).trans hI) hcr hcredit
        rwa [hb] at hdone
    · rw [if_neg hsum] at haccount ⊢; exact haccount

theorem mintPrepareAccountTrace {I : ExecutionEnv} {g : Sat256} {s0 : State} {evm : EVM.State}
    {mem rdata : ByteArray} {aw receiver amount : UInt256} {currency : AccountAddress} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length + 12 ≤ 1024) (hfit : amount.toNat < 2^127)
    (h : RD (deployedRuntime v) I g s0 ⟨10837⟩
      (amount :: ⟨10850⟩ :: balanceMintStack receiver (accountWord currency) amount R)
      mem aw rdata evm.accountMap k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨12528⟩
      (accountWord currency :: EVM.wordOfInt (-(Int.ofNat amount.toNat)) :: accountWord I.source :: ⟨10850⟩ ::
        balanceMintStack receiver (accountWord currency) amount R) mem aw rdata evm.accountMap k' C' := by
  have hj : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 12528) = true := by
    rw [deployedRuntime_jumps]; jump_dest
  have haccount := poolManagerBlocks.poolManager_block_10837 hstack hj h
  change RD (deployedRuntime v) I g s0 ⟨12528⟩
    (accountWord currency :: UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ amount) :: accountWord I.source :: ⟨10850⟩ ::
      balanceMintStack receiver (accountWord currency) amount R) mem aw rdata evm.accountMap _ _ at haccount
  have hlo : -(2^127 : Int) ≤ -(Int.ofNat amount.toNat) := by simp only [Int.ofNat_eq_natCast]; omega
  have hhi : -(Int.ofNat amount.toNat) < (2^127 : Int) := by simp only [Int.ofNat_eq_natCast]; omega
  rw [← wordOfInt_neg_natCast_eq_sub_zero, signextend128_wordOfInt hlo hhi] at haccount
  exact ⟨_, _, haccount⟩

def mintTraceResult (v : PoolManagerImmutables) (I : ExecutionEnv) (g : Sat256) (s0 : State)
    (evm : EVM.State) (receiver id amount : UInt256) : Prop :=
  if transientWord evm lockSlot = ⟨0⟩ then RDrev (deployedRuntime v) g s0 else
  if amount.toNat < 2^127 then mintAccountTraceResult v I g s0 evm receiver (AccountAddress.ofNat id.toNat) amount
  else RDrev (deployedRuntime v) g s0

theorem mintTrace {I : ExecutionEnv} {g : Sat256} {s0 : State} {evm : EVM.State}
    {mem rdata : ByteArray} {aw receiver id amount : UInt256} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length + 16 ≤ 1024) (hmem : mem.size = 96)
    (hI : evm.executionEnv = I) (hcr : receiver.toNat < EVM.addressModulus)
    (h : RD (deployedRuntime v) I g s0 ⟨10723⟩ (amount :: id :: receiver :: R) mem aw rdata evm.accountMap k C) :
    mintTraceResult v I g s0 evm receiver id amount := by
  rw [mintTraceResult]
  by_cases hl : transientWord evm lockSlot = ⟨0⟩
  · rw [if_pos hl]
    have hj : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 1239) = true := by
      rw [deployedRuntime_jumps]; jump_dest
    have hrev := poolManagerBlocks.poolManager_block_10723_taken
      (by simp only [List.length_cons]; omega)
      (by change UInt256.isZero (codeOwnerTransientWord I evm.accountMap lockSlot) ≠ ⟨0⟩
          rw [← transientWord_accountMap hI, hl]; decide) hj h
    exact poolManagerBlocks.poolManager_block_1239 (by change R.length + 3 + 2 ≤ 1024; omega) hrev
  · rw [if_neg hl]
    have hunlocked := poolManagerBlocks.poolManager_block_10723_fallthrough
      (by simp only [List.length_cons]; omega)
      (by change UInt256.isZero (codeOwnerTransientWord I evm.accountMap lockSlot) = ⟨0⟩
          rw [← transientWord_accountMap hI]; exact isZero_eq_zero_of_ne hl) h
    have hjCast : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 12458) = true := by
      rw [deployedRuntime_jumps]; jump_dest
    have hcast := poolManagerBlocks.poolManager_block_10764 (by omega) hjCast hunlocked
    change RD (deployedRuntime v) I g s0 ⟨12458⟩
      (amount :: ⟨10837⟩ :: ⟨10850⟩ :: balanceMintStack receiver (UInt256.land id solcAddrMask) amount R)
      mem aw rdata evm.accountMap _ _ at hcast
    rw [← accountWord_fromId] at hcast
    by_cases hfit : amount.toNat < 2^127
    · rw [if_pos hfit]
      have hjReturn : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 10837) = true := by
        rw [deployedRuntime_jumps]; jump_dest
      obtain ⟨k', C', hprepare⟩ := uintToInt128Trace v
        (by change R.length + 7 + 1 + 4 ≤ 1024; omega) hfit hjReturn hcast
      obtain ⟨k'', C'', haccount⟩ := mintPrepareAccountTrace v (by omega) hfit hprepare
      exact mintAccountTrace v hstack hmem hI hcr hfit haccount
    · rw [if_neg hfit]
      exact uintToInt128TraceReverts v (by change R.length + 7 + 1 + 1 + 3 ≤ 1024; omega) hfit hcast

end Benchmarks.UniswapV4PoolManager
