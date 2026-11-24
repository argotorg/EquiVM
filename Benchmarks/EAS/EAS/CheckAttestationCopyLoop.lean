import Benchmarks.EAS.EAS.CheckAttestationCopyExpr

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

structure CheckAttestationCopyLocals (L : Store) (data : UInt256) (len heap i : Nat) : Prop where
  data : L.get? "data"=some (.int (Int.ofNat data.toNat))
  length : L.get? "length"=some (.int (Int.ofNat len))
  heap : L.get? "$EAS.freeMemory"=some (.int (Int.ofNat heap))
  index : L.get? "i"=some (.int (Int.ofNat i))

def checkAttestationCopyOffsetsValid (cd : ByteArray) (data : UInt256) (len : Nat) : Prop :=
  ∀ t, t<len → (calldataWord cd (UInt256.ofNat (data.toNat+32*t)).toNat).toNat≤2^64-1
instance (cd : ByteArray) (data : UInt256) (len : Nat) : Decidable (checkAttestationCopyOffsetsValid cd data len) :=
  inferInstanceAs (Decidable (∀ t, t<len → _))

theorem checkAttestationCopyGuard_eval {L imms : Store} {evm : EVM.State} {data : UInt256} {len heap i : Nat}
    (hf : CheckAttestationCopyLocals L data len heap i) :
    evalExpr? config {contract := contract,locals := L,immutables := imms} evm checkAttestationCopyGuard=
      .ok (.bool (decide (i<len))) := by
  simp only [checkAttestationCopyGuard,evalExpr?,hf.index,hf.length,EvalResult.ofOption,bind,EvalResult.bind,
    evalBinaryOp_lt_int_ok,Int.ofNat_eq_natCast,Nat.cast_lt]

theorem checkAttestationCopyIterationSource {L imms : Store} {evm : EVM.State} {data : UInt256} {len heap i : Nat}
    (hf : CheckAttestationCopyLocals L data len heap i) (hb : i+1<UInt256.size) :
    ((calldataWord evm.executionEnv.calldata (UInt256.ofNat (data.toNat+32*i)).toNat).toNat≤2^64-1 →
      ∃ L', ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm checkAttestationCopyIteration
        (.ok {contract := contract,locals := L',immutables := imms} evm) ∧ CheckAttestationCopyLocals L' data len heap (i+1)) ∧
    (¬(calldataWord evm.executionEnv.calldata (UInt256.ofNat (data.toNat+32*i)).toNat).toNat≤2^64-1 →
      ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm checkAttestationCopyIteration .reverted) := by
  let word := calldataWord evm.executionEnv.calldata (UInt256.ofNat (data.toNat+32*i)).toNat
  let L1 := heapResultLocals L "offset$allocation" "offset" "$EAS.freeMemory" (.int (Int.ofNat word.toNat)) heap
  have hread := checkAttestationCopyWordSource (fork := fork) (imms := imms) (evm := evm) "offset" (by decide) (by decide) (by decide)
    (checkAttestationCopySlot_eval hf.data hf.index) hf.heap
  have ho1 : L1.get? "offset"=some (.int (Int.ofNat word.toNat)) := heapResultLocals_result _ _ _ _ _ _ (by decide)
  have hg : evalExpr? config {contract := contract,locals := L1,immutables := imms} evm
      (.binary .le (.var "offset") (.intLit (2^64-1)))=.ok (.bool (decide (word.toNat≤2^64-1))) :=
    naturalLeSource (evalLocalValue ho1) (by simp only [evalExpr?,pure];rfl)
  constructor
  · intro hv
    change word.toNat≤2^64-1 at hv
    have hi1 : L1.get? "i"=some (.int (Int.ofNat i)) := by
      simpa (disch := decide) only [L1,heapResultLocals_get] using hf.index
    refine ⟨L1.insert "i" (.int (Int.ofNat (i+1))),?_,?_⟩
    · exact execBlock_append hread (ExecBlock.consNormal (ExecStmt.requireTrue (by simpa only [decide_eq_true hv] using hg))
        (ExecBlock.consNormal (execLocalCastIncrement hi1 hb) ExecBlock.nil))
    · constructor
      · simpa (disch := decide) only [L1,store_get_ne,heapResultLocals_get] using hf.data
      · simpa (disch := decide) only [L1,store_get_ne,heapResultLocals_get] using hf.length
      · simp (disch := decide) only [L1,store_get_ne,heapResultLocals_heap]
      · exact store_get_self _ _ _
  · intro hv
    change ¬word.toNat≤2^64-1 at hv
    exact execBlock_append hread (ExecBlock.consRevert (ExecStmt.requireFalse (by simpa only [decide_eq_false hv] using hg)))

theorem checkAttestationCopyLoopSource {L imms : Store} {evm : EVM.State} {data : UInt256} {len heap i : Nat}
    (hbound : len<UInt256.size) (n : Nat) (hn : i+n=len)
    (hf : CheckAttestationCopyLocals L data len heap i) :
    (∀ t, i≤t → t<len → (calldataWord evm.executionEnv.calldata (UInt256.ofNat (data.toNat+32*t)).toNat).toNat≤2^64-1) ∧
      (∃ L', ExecStmt fork config {contract := contract,locals := L,immutables := imms} evm checkAttestationCopyLoop
        (.ok {contract := contract,locals := L',immutables := imms} evm) ∧ CheckAttestationCopyLocals L' data len heap len) ∨
    (¬(∀ t, i≤t → t<len → (calldataWord evm.executionEnv.calldata (UInt256.ofNat (data.toNat+32*t)).toNat).toNat≤2^64-1) ∧
      ExecStmt fork config {contract := contract,locals := L,immutables := imms} evm checkAttestationCopyLoop .reverted) := by
  induction n generalizing L i with
  | zero =>
    have he : i=len := by omega
    subst i
    refine Or.inl ⟨by intros;omega,L,ExecStmt.whileFalse ?_,hf⟩
    simpa only [decide_eq_false (Nat.lt_irrefl len)] using checkAttestationCopyGuard_eval (imms := imms) (evm := evm) hf
  | succ n ih =>
    have hi : i<len := by omega
    have hg : evalExpr? config {contract := contract,locals := L,immutables := imms} evm checkAttestationCopyGuard=.ok (.bool true) :=
      by simpa only [decide_eq_true hi] using checkAttestationCopyGuard_eval (imms := imms) (evm := evm) hf
    have hs := checkAttestationCopyIterationSource (fork := fork) (imms := imms) (evm := evm) hf (by omega)
    by_cases hv : (calldataWord evm.executionEnv.calldata (UInt256.ofNat (data.toNat+32*i)).toNat).toNat≤2^64-1
    · obtain ⟨L1,hs1,hf1⟩ := hs.1 hv
      rcases ih (by omega) hf1 with ⟨hgood,L2,hs2,hf2⟩ | ⟨hbad,hs2⟩
      · refine Or.inl ⟨?_,L2,ExecStmt.whileTrue hg hs1 hs2,hf2⟩
        intro t ht hlt
        by_cases he : t=i
        · simpa only [he] using hv
        · exact hgood t (by omega) hlt
      · exact Or.inr ⟨fun h => hbad (fun t ht hlt => h t (by omega) hlt),ExecStmt.whileTrue hg hs1 hs2⟩
    · exact Or.inr ⟨fun h => hv (h i (le_refl _) hi),ExecStmt.whileRevert hg (hs.2 hv)⟩

end Benchmarks.EAS.EAS
