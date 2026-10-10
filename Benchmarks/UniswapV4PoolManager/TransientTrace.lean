import Benchmarks.UniswapV4PoolManager.TransientSource
import Benchmarks.UniswapV4PoolManager.MappingMemory

/-! Shared transient-storage bridges and static-call stepping. -/
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

-- GENERALIZES Reasoning.Theory.codeOwnerTransientWord_initState to arbitrary source states.
theorem transientWord_accountMap {evm : EVM.State} {I : ExecutionEnv}
    (hI : evm.executionEnv = I) (slot : UInt256) :
    transientWord evm slot = codeOwnerTransientWord I evm.accountMap slot := by
  simp [transientWord, Solm.EVM.transientLoad, State.lookupAccount,
    Account.lookupTransientStorage, codeOwnerTransientWord, hI]

-- GENERALIZES mappingMemory_slot by removing the memory-size precondition.
theorem mappingMemory_slot_any (key base : UInt256) (mem : ByteArray) :
    keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem key base mem) = mappingSlotWord key base := by
  change UInt256.ofNat (fromByteArrayBigEndian (KEC ((twoWordHashMem key base mem).readWithPadding 0 64))) = _
  have hmem : (twoWordHashMem key base mem).readWithPadding 0 64 = key.toByteArray ++ base.toByteArray :=
    twoWordWrite_read0_64_any mem key base
  rw [hmem]
  exact keccakSlot_eq _

-- GENERALIZES Reasoning.Theory.sstore_xstep_static to the transient storage opcode.
theorem tstore_xstep_static {s : State} {code : ByteArray} {pcv slot val : UInt256}
    {t : List UInt256} (hcode : s.executionEnv.code = code)
    (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.TSTORE, .none))
    (hperm : s.executionEnv.perm = false)
    (hstk : s.machineState.stack = slot :: val :: t) (hov : t.length ≤ 1024) :
    Xstep (D_J code 0) s =
      (if s.machineState.gasAvailable.toNat < Ctstore then .error .OutOfGass
       else .error .StaticModeViolation) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.TSTORE, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_tstore s hd, hstk]
  have hov' : ¬ ((slot :: val :: t).length - 2 + 0 > 1024) := by
    simp only [List.length_cons]; omega
  simp only [if_neg hov', hperm, Bool.false_eq_true, not_false_eq_true, if_true]

-- GENERALIZES Reasoning.Reach.RD.sstoreStatic to the transient storage opcode.
theorem tstoreStatic {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {σ : AccountMap} {k C : Nat} {slot val : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (slot :: val :: t) mem aw rdata σ k C)
    (hperm : ee.perm = false) (hdec : decode code pc = some (.TSTORE, .none))
    (hov : t.length ≤ 1024) : RDstatic code g s0 := by
  unfold RD at h
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, _, hk, hC, _, _, _, _, hee, _⟩
  · exact Or.inl hoog
  · have hperms : s.executionEnv.perm = false := by rw [hee]; exact hperm
    have st := tstore_xstep_static hcode hpc hdec hperms hstk hov
    rcases stepStatic (g := g) st hk hC with h | h
    · exact Or.inl (hX.trans h)
    · exact Or.inr (hX.trans h)

end Benchmarks.UniswapV4PoolManager
