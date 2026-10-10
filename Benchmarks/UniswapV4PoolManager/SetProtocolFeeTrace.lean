import Benchmarks.UniswapV4PoolManager.SetProtocolFeeSource
import Benchmarks.UniswapV4PoolManager.PoolProtocolFeeTrace
import Benchmarks.UniswapV4PoolManager.TransientTrace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_012

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem protocolControllerTrace {I : ExecutionEnv} {g : Sat256} {s0 : State} {evm : EVM.State}
    {mem rdata : ByteArray} {aw fee ptr : UInt256} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+4 ≤ 1024) (hI : evm.executionEnv = I)
    (h : RD (deployedRuntime v) I g s0 ⟨3737⟩ (fee :: ptr :: R) mem aw rdata evm.accountMap k C) :
    (¬protocolControllerAuthorized evm ∧ RDrev (deployedRuntime v) g s0) ∨
    (protocolControllerAuthorized evm ∧ ∃ k' C', RD (deployedRuntime v) I g s0 ⟨3770⟩
      (ptr :: fee :: R) mem aw rdata evm.accountMap k' C') := by
  have hw := protocolControllerWord_accountMap hI
  by_cases ha : protocolControllerAuthorized evm
  · have he : accountWord I.source = protocolControllerWord evm := by
      simpa only [protocolControllerAuthorized, hI] using ha
    obtain ⟨k', C', hr⟩ := poolManagerBlocks.poolManager_block_3737_fallthrough hstack
      (by change UInt256.sub (accountWord I.source) (UInt256.land (solcSlotWordAt ⟨2⟩ evm.accountMap I) solcAddrMask) = ⟨0⟩
          rw [hw]; exact u256_sub_eq_zero_iff_eq.mpr he) h
    exact .inr ⟨ha, k', C', hr⟩
  · have he : accountWord I.source ≠ protocolControllerWord evm := by
      simpa only [protocolControllerAuthorized, hI] using ha
    obtain ⟨k', C', hr⟩ := poolManagerBlocks.poolManager_block_3737_taken hstack
      (by change UInt256.sub (accountWord I.source) (UInt256.land (solcSlotWordAt ⟨2⟩ evm.accountMap I) solcAddrMask) ≠ ⟨0⟩
          rw [hw]; exact u256_sub_ne_zero_of_ne he)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    exact .inl ⟨ha, poolManagerBlocks.poolManager_block_3423 (by change R.length+2+2 ≤ 1024; omega) hr⟩

theorem protocolFeeValidWord (fee : UInt256) :
    UInt256.isZero (UInt256.land
      (UInt256.lt (UInt256.land fee (UInt256.ofNat 4095)) (UInt256.ofNat 1001))
      (UInt256.lt (UInt256.land fee (UInt256.ofNat 16773120)) (UInt256.ofNat 4100096))) =
      if protocolFeeValid fee then ⟨0⟩ else ⟨1⟩ := by
  by_cases h0 : (UInt256.land fee ⟨4095⟩).toNat < 1001 <;>
    by_cases h1 : (UInt256.land fee ⟨16773120⟩).toNat < 4100096
  · rw [ult_one h0, ult_one h1, if_pos ⟨h0, h1⟩]; rfl
  · rw [ult_one h0, ult_zero (Nat.le_of_not_gt h1), if_neg (fun hv => h1 hv.2)]; rfl
  · rw [ult_zero (Nat.le_of_not_gt h0), ult_one h1, if_neg (fun hv => h0 hv.1)]; rfl
  · rw [ult_zero (Nat.le_of_not_gt h0), ult_zero (Nat.le_of_not_gt h1), if_neg (fun hv => h0 hv.1)]; rfl

theorem protocolFeeValidTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw fee ptr : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+6 ≤ 1024)
    (h : RD (deployedRuntime v) I g s0 ⟨3770⟩ (ptr :: fee :: R) mem aw rdata σ k C) :
    (¬protocolFeeValid fee ∧ RDrev (deployedRuntime v) g s0) ∨
    (protocolFeeValid fee ∧ ∃ k' C', RD (deployedRuntime v) I g s0 ⟨3796⟩ (ptr :: fee :: R) mem aw rdata σ k' C') := by
  by_cases hv : protocolFeeValid fee
  · have hr := poolManagerBlocks.poolManager_block_3770_fallthrough hstack
      (by rw [protocolFeeValidWord, if_pos hv]; rfl) h
    exact .inr ⟨hv, _, _, hr⟩
  · have hr := poolManagerBlocks.poolManager_block_3770_taken hstack
      (by rw [protocolFeeValidWord, if_neg hv]; decide)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    exact .inl ⟨hv, poolManagerBlocks.poolManager_block_3941 hstack hr⟩

def protocolFeeTopic : UInt256 := ⟨105735455096664727696358682035932390588164037322273706779794080047481825433337⟩

theorem protocolFeePoolHashTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {aw fee : UInt256} {key : PoolKeyWords} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+8 ≤ 1024)
    (h : RD (deployedRuntime v) I g s0 ⟨3796⟩ (⟨160⟩ :: fee :: R) (poolKeyMemory key) aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨13686⟩
      (poolSlot (poolKeyId key) :: ⟨3855⟩ :: poolSlot (poolKeyId key) :: fee :: ⟨32⟩ :: protocolFeeTopic :: poolKeyId key :: R)
      (twoWordHashMem (poolKeyId key) ⟨6⟩ (poolKeyMemory key)) aw' rdata σ k' C' := by
  obtain ⟨aw', k', C', rd⟩ := poolManagerBlocks.poolManager_block_3796_packed hstack
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  let mem := twoWordHashMem (keccakWord ⟨160⟩ ⟨160⟩ (poolKeyMemory key)) ⟨6⟩ (poolKeyMemory key)
  change RD _ _ _ _ ⟨13686⟩
    (keccakWord ⟨0⟩ ⟨64⟩ mem :: ⟨3855⟩ :: keccakWord ⟨0⟩ ⟨64⟩ mem :: fee :: ⟨32⟩ :: protocolFeeTopic ::
      keccakWord ⟨160⟩ ⟨160⟩ (poolKeyMemory key) :: R) mem aw' rdata σ k' C' at rd
  dsimp only [mem] at rd
  rw [poolKeyMemory_hash, mappingMemory_slot_any] at rd
  exact ⟨_, _, _, rd⟩

@[irreducible] def setProtocolFeeTraceResult (v : PoolManagerImmutables) (I : ExecutionEnv) (g : Sat256) (s0 : State)
    (evm : EVM.State) (key : PoolKeyWords) (fee : UInt256) : Prop :=
  if protocolControllerAuthorized evm then
    if protocolFeeValid fee then poolSetProtocolTraceResult v I g s0 evm (poolKeyId key) fee
    else RDrev (deployedRuntime v) g s0
  else RDrev (deployedRuntime v) g s0

theorem setProtocolFeeTrace {I : ExecutionEnv} {g : Sat256} {s0 : State} {evm : EVM.State}
    {rdata : ByteArray} {aw fee : UInt256} {key : PoolKeyWords} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+9 ≤ 1024) (hI : evm.executionEnv = I)
    (hfee : fee.toNat < 2^24)
    (h : RD (deployedRuntime v) I g s0 ⟨3737⟩ (fee :: ⟨160⟩ :: R) (poolKeyMemory key) aw rdata evm.accountMap k C) :
    setProtocolFeeTraceResult v I g s0 evm key fee := by
  unfold setProtocolFeeTraceResult
  rcases protocolControllerTrace v (by omega) hI h with ⟨ha, hr⟩ | ⟨ha, k1, C1, rd1⟩
  · rw [if_neg ha]; exact hr
  · rw [if_pos ha]
    rcases protocolFeeValidTrace v (by omega) rd1 with ⟨hv, hr⟩ | ⟨hv, k2, C2, rd2⟩
    · rw [if_neg hv]; exact hr
    · rw [if_pos hv]
      obtain ⟨aw3, k3, C3, rd3⟩ := protocolFeePoolHashTrace v (by omega) rd2
      exact poolProtocolFeeTrace v hstack hI hfee rd3

end Benchmarks.UniswapV4PoolManager
