import Benchmarks.UniswapV4PoolManager.BalanceBurn
import Benchmarks.UniswapV4PoolManager.BalanceMintTrace

/-! The ERC6909 balance debit and Transfer event reached by burn. -/
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def balanceBurnStack (sender id amount : UInt256) (R : List UInt256) : List UInt256 :=
  amount :: ⟨1005⟩ :: transferEventTopic :: sender :: ⟨0⟩ :: id :: R

theorem balanceBurnLoadTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {sender id amount : UInt256} {R : List UInt256} (v : PoolManagerImmutables)
    (hstack : R.length + 11 ≤ 1024) (hmem : mem.size = 96)
    (h : RD (deployedRuntime v) I g s0 ⟨972⟩ (balanceBurnStack sender id amount R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨12269⟩
      (solcSlotWordAt (balanceSlot sender id) σ I :: amount :: ⟨607⟩ :: balanceSlot sender id ::
        balanceBurnStack sender id amount R) (nestedMappingMemory sender id ⟨4⟩ mem) aw' rdata σ k' C' := by
  have hj : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 12269) = true := by
    rw [deployedRuntime_jumps]; jump_dest
  obtain ⟨k', C', hnext⟩ := poolManagerBlocks.poolManager_block_972 (R := R) hstack hj h
  let nextMem := nestedMappingMemory sender id ⟨4⟩ mem
  change RD (deployedRuntime v) I g s0 ⟨12269⟩
    (solcSlotWordAt (keccakWord ⟨0⟩ ⟨64⟩ nextMem) σ I :: amount :: ⟨607⟩ :: keccakWord ⟨0⟩ ⟨64⟩ nextMem ::
      balanceBurnStack sender id amount R) nextMem _ rdata σ k' C' at hnext
  dsimp only [nextMem] at hnext
  rw [nestedMappingMemory_slot _ _ _ hmem] at hnext
  exact ⟨_, _, _, hnext⟩

theorem balanceBurnReturnTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {value slot sender id amount : UInt256} {R : List UInt256} (v : PoolManagerImmutables)
    (hstack : R.length + 10 ≤ 1024) (hp : I.perm = true)
    (h : RD (deployedRuntime v) I g s0 ⟨607⟩
      (value :: slot :: balanceBurnStack sender id amount R) mem aw rdata σ k C) :
    RDret (deployedRuntime v) g s0 (sstoreAccountMap I.codeOwner σ slot value) .empty := by
  have hj : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 1005) = true := by
    rw [deployedRuntime_jumps]; jump_dest
  obtain ⟨k', C', hlog⟩ := poolManagerBlocks.poolManager_block_607
    (R := transferEventTopic :: sender :: ⟨0⟩ :: id :: R)
    (by simp only [List.length_cons]; omega) hp hj h
  exact poolManagerBlocks.poolManager_block_1005 (by change R.length + 7 ≤ 1024; omega) hp hlog

@[irreducible] def balanceBurnTraceResult (v : PoolManagerImmutables) (I : ExecutionEnv) (g : Sat256) (s0 : State)
    (evm : EVM.State) (sender id amount : UInt256) : Prop :=
  if amount.toNat ≤ (balanceWord evm sender id).toNat then
    if I.perm = false then RDstatic (deployedRuntime v) g s0 else
    RDret (deployedRuntime v) g s0 (balanceBurnPost evm sender id amount).accountMap .empty
  else RDrev (deployedRuntime v) g s0

theorem balanceBurnTrace {I : ExecutionEnv} {g : Sat256} {s0 : State} {evm : EVM.State}
    {mem rdata : ByteArray} {aw : UInt256} {k C : Nat} {sender id amount : UInt256} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length + 11 ≤ 1024) (hmem : mem.size = 96)
    (hI : evm.executionEnv = I)
    (h : RD (deployedRuntime v) I g s0 ⟨972⟩ (balanceBurnStack sender id amount R) mem aw rdata evm.accountMap k C) :
    balanceBurnTraceResult v I g s0 evm sender id amount := by
  rw [balanceBurnTraceResult]
  generalize hbalance : balanceWord evm sender id = balance at ⊢
  obtain ⟨aw', k', C', hsub⟩ := balanceBurnLoadTrace v hstack hmem h
  have hread : balanceWord evm sender id = solcSlotWordAt (balanceSlot sender id) evm.accountMap I :=
    storageLoad_codeOwner_eq_solcSlotWordAt evm I _ (by rw [hI])
  rw [← hread, hbalance] at hsub
  by_cases hfit : amount.toNat ≤ balance.toNat
  · rw [if_pos hfit]
    have hj : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 607) = true := by
      rw [deployedRuntime_jumps]; jump_dest
    obtain ⟨k'', C'', hstore⟩ := checkedSubPass v (by simp only [balanceBurnStack, List.length_cons]; omega) hfit hj hsub
    by_cases hp : I.perm = false
    · rw [if_pos hp]
      exact balanceCreditStaticTrace v (by simp only [balanceBurnStack, List.length_cons]; omega) hp hstore
    · rw [if_neg hp]
      have hret := balanceBurnReturnTrace v (by omega) (Bool.eq_true_of_not_eq_false hp) hstore
      have hmap : (balanceBurnPost evm sender id amount).accountMap =
          sstoreAccountMap I.codeOwner evm.accountMap (balanceSlot sender id) (UInt256.sub balance amount) := by
        rw [balanceBurnPost, balancePost, storageStore_accountMap, hI, hbalance]
      rw [hmap]
      exact hret
  · rw [if_neg hfit]
    exact checkedSubReverts v (by simp only [balanceBurnStack, List.length_cons]; omega) (Nat.lt_of_not_ge hfit) hsub

end Benchmarks.UniswapV4PoolManager
