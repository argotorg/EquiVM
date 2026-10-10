import Benchmarks.UniswapV4PoolManager.UnlockReturnTail

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
open poolManagerBlocks

/-- The capacity check selected by a failed callback-return allocation. -/
def unlockAllocationBounds (out : ByteArray) (first : Bool) : Prop :=
  if first then AllocationBounds ⟨160⟩ (UInt256.ofNat out.size)
  else AllocationBounds (unlockRawEnd out) (bytesAllocationSize (unlockReturnLength out))

/-- A valid reply can reach capacity panic only after these charged operations and memory growth. -/
def UnlockAllocationFailure (code : ByteArray) (I : ExecutionEnv) (g : Sat256) (s0 : State)
    (σ : AccountMap) (out : ByteArray) (aw : UInt256) (C : Nat) : Prop :=
  BytesReturnBounds out ∧ ∃ (first : Bool) (mem' : ByteArray) (aw' : UInt256) (k' C' : Nat) (R' : List UInt256),
    ¬unlockAllocationBounds out first ∧ R'.length+2 ≤ 1024 ∧
    (M aw ⟨160⟩ (UInt256.ofNat out.size)).toNat ≤ aw'.toNat ∧
    C+(if first then 98 else 352)+3*((out.size+31)/32)+Cₘ aw' ≤ C'+Cₘ aw ∧
    RD code I g s0 ⟨7857⟩ R' mem' aw' out σ k' C'

def unlockReturnResultTrace (code : ByteArray) (g : Sat256) (s0 evm : State) (out : ByteArray) : Prop :=
  if BytesReturnBounds out then
    if transientWord evm deltaCountSlot = ⟨0⟩ then
      RDret code g s0 (lockSetPost evm false).accountMap (bytesReturnEncoding (bytesReturnPayload out))
    else RDrev code g s0
  else RDrev code g s0

theorem unlockReturnTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem out : ByteArray} {aw flag saved : UInt256} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+13 ≤ 1024)
    (hI : evm.executionEnv = I) (hp : I.perm = true)
    (hout : out.size < 2^138) (hmem : 160 ≤ mem.size)
    (h : RD (deployedRuntime v) I g s0 ⟨9242⟩ (⟨160⟩ :: flag :: saved :: R)
      mem aw out evm.accountMap k C) :
    UnlockAllocationFailure (deployedRuntime v) I g s0 evm.accountMap out aw C ∨
    unlockReturnResultTrace (deployedRuntime v) g s0 evm out := by
  rcases unlockReturnPrefix v (by simp only [List.length_cons]; omega) hout hmem h with
    ⟨hbad, k', C', hc, rd⟩ | ⟨hbad, hr⟩ | ⟨hraw, hh, aw', k', C', hc, ha, rd⟩
  · by_cases hb : BytesReturnBounds out
    · exact .inl ⟨hb, true, _, _, _, _, _, hbad,
        by simp only [List.length_cons]; omega, le_refl _, hc, rd⟩
    · refine .inr ?_
      rw [unlockReturnResultTrace, if_neg hb]
      exact poolManager_block_7857 (by simp only [List.length_cons]; omega) rd
  · refine .inr ?_
    rw [unlockReturnResultTrace, if_neg hbad]
    exact hr
  · rcases unlockReturnTail v hstack hI hp hout hmem hraw hh rd with
      ⟨hbad, hr⟩ | ⟨hbad, hr⟩ | ⟨hb, hr⟩
    · by_cases hb : BytesReturnBounds out
      · refine .inl ⟨hb, false, _, _, _, _, _, hbad,
          by simp only [List.length_cons]; omega, ha, ?_, hr⟩
        change C+352+3*((out.size+31)/32)+Cₘ aw' ≤ C'+59+Cₘ aw
        omega
      · refine .inr ?_
        rw [unlockReturnResultTrace, if_neg hb]
        exact poolManager_block_7857 (by simp only [List.length_cons]; omega) hr
    · refine .inr ?_
      rw [unlockReturnResultTrace, if_neg hbad]
      exact hr
    · refine .inr ?_
      rw [unlockReturnResultTrace, if_pos hb]
      exact hr

end Benchmarks.UniswapV4PoolManager
