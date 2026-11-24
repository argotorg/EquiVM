import Benchmarks.EAS.EAS.MultiDelegatedAttestLocals

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach ABI.Solc08Calldata
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def multiDelegatedAttestFieldLocals (L : Store) (data sigs : List Value) : Store :=
  L.insert "data" (.array data) |>.insert "signatures" (.array sigs) |>.insert "j" (.int 0)

theorem localArrayNonempty_eval {L imms : Store} {evm : EVM.State} {name : Ident} {xs : List Value}
    (h : L.get? name=some (.array xs)) :
    evalExpr? config {contract := contract,locals := L,immutables := imms} evm
      (.binary .ne (.arrayLength .localVar {base := name}) (.intLit 0))=.ok (.bool (decide (0<xs.length))) := by
  have he := evalLocalArrayLength (cfg := config) (stele := {contract := contract,locals := L,immutables := imms}) (evm := evm) h
  simp only [evalExpr?,he,pure,bind,EvalResult.bind,evalBinaryOp_ne_int_ok]
  congr 2
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.not_eq_true',beq_eq_false_iff_ne,ne_eq,Value.int.injEq,decide_eq_true_eq]
  change ((xs.length : Int) ≠ 0) ↔ _
  omega

theorem localArrayLengthsEq_eval {L imms : Store} {evm : EVM.State} {a b : Ident} {xs ys : List Value}
    (hx : L.get? a=some (.array xs)) (hy : L.get? b=some (.array ys)) :
    evalExpr? config {contract := contract,locals := L,immutables := imms} evm
      (.binary .eq (.arrayLength .localVar {base := a}) (.arrayLength .localVar {base := b}))=
      .ok (.bool (decide (xs.length=ys.length))) := by
  have he := evalLocalArrayLength (cfg := config) (stele := {contract := contract,locals := L,immutables := imms}) (evm := evm) hx
  have hf := evalLocalArrayLength (cfg := config) (stele := {contract := contract,locals := L,immutables := imms}) (evm := evm) hy
  simp only [evalExpr?,he,hf,pure,bind,EvalResult.bind,evalBinaryOp_eq_int_ok]
  congr 2
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq,Value.int.injEq,decide_eq_true_eq]
  change ((xs.length : Int)=(ys.length : Int)) ↔ _
  omega

theorem multiDelegatedAttestFieldsSource {L imms : Store} {evm : EVM.State} {schema attester : Value} {data sigs : List Value}
    (vd vs : Prop) [Decidable vd] [Decidable vs]
    (hr : L.get? "multiDelegatedRequest"=some (.tuple [schema,if vd then .array data else decodeFailure,
      if vs then .array sigs else decodeFailure,attester])) :
    if vd ∧ 0<data.length ∧ vs ∧ data.length=sigs.length then
      ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm multiDelegatedAttestFields
        (.ok {contract := contract,locals := multiDelegatedAttestFieldLocals L data sigs,immutables := imms} evm)
    else ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm multiDelegatedAttestFields .reverted := by
  let L1 := L.insert "data" (if vd then .array data else decodeFailure)
  have hread1 : ExecStmt fork config {contract := contract,locals := L,immutables := imms} evm
      (.letDecl "data" (some (.dynamicArray requestDataABI)) (.tupleGet (.var "multiDelegatedRequest") 1))
      (.ok {contract := contract,locals := L1,immutables := imms} evm) := by
    apply ExecStmt.letDecl
    simp only [evalExpr?,hr,EvalResult.ofOption,bind,EvalResult.bind,pure]
    rfl
  have hd1 : L1.get? "data"=some (if vd then .array data else decodeFailure) := store_get_self _ _ _
  by_cases hdv : vd
  · rw [if_pos hdv] at hd1
    have hc1 := multiDelegatedAttestCheck_array (fork := fork) (imms := imms) (evm := evm) hd1
    have he1 := localArrayNonempty_eval (imms := imms) (evm := evm) hd1
    by_cases hn : 0<data.length
    · rw [decide_eq_true hn] at he1
      let L2 := L1.insert "signatures" (if vs then .array sigs else decodeFailure)
      have hr1 : L1.get? "multiDelegatedRequest"=some (.tuple [schema,if vd then .array data else decodeFailure,
          if vs then .array sigs else decodeFailure,attester]) := (store_get_ne _ _ (by decide)).trans hr
      have hread2 : ExecStmt fork config {contract := contract,locals := L1,immutables := imms} evm
          (.letDecl "signatures" (some (.dynamicArray signatureABI)) (.tupleGet (.var "multiDelegatedRequest") 2))
          (.ok {contract := contract,locals := L2,immutables := imms} evm) := by
        apply ExecStmt.letDecl
        simp only [evalExpr?,hr1,EvalResult.ofOption,bind,EvalResult.bind,pure]
        rfl
      have hs2 : L2.get? "signatures"=some (if vs then .array sigs else decodeFailure) := store_get_self _ _ _
      by_cases hsv : vs
      · rw [if_pos hsv] at hs2
        have hc2 := multiDelegatedAttestCheck_array (fork := fork) (imms := imms) (evm := evm) hs2
        have hd2 : L2.get? "data"=some (.array data) := (store_get_ne _ _ (by decide)).trans hd1
        have he2 := localArrayLengthsEq_eval (imms := imms) (evm := evm) hd2 hs2
        by_cases heq : data.length=sigs.length
        · rw [if_pos ⟨hdv,hn,hsv,heq⟩,multiDelegatedAttestFields]
          rw [decide_eq_true heq] at he2
          have hinit : ExecStmt fork config {contract := contract,locals := L2,immutables := imms} evm
              (.letDecl "j" (some abiUInt256) (.intLit 0))
              (.ok {contract := contract,locals := multiDelegatedAttestFieldLocals L data sigs,immutables := imms} evm) := by
            have hinit := ExecStmt.letDecl (fork := fork) (cfg := config) (stele := {contract := contract,locals := L2,immutables := imms})
              (evm := evm) (name := "j") (ty := some abiUInt256) (by simp only [evalExpr?,pure] : evalExpr? config {contract := contract,locals := L2,immutables := imms} evm (.intLit 0)=.ok (.int 0))
            simpa only [L2,L1,if_pos hdv,if_pos hsv] using hinit
          exact ExecBlock.consNormal hread1 (ExecBlock.consNormal hc1 (ExecBlock.consNormal (ExecStmt.requireTrue he1)
            (ExecBlock.consNormal hread2 (ExecBlock.consNormal hc2 (ExecBlock.consNormal (ExecStmt.requireTrue he2)
              (ExecBlock.consNormal hinit ExecBlock.nil))))))
        · rw [if_neg (fun h => heq h.2.2.2),multiDelegatedAttestFields]
          rw [decide_eq_false heq] at he2
          exact ExecBlock.consNormal hread1 (ExecBlock.consNormal hc1 (ExecBlock.consNormal (ExecStmt.requireTrue he1)
            (ExecBlock.consNormal hread2 (ExecBlock.consNormal hc2 (ExecBlock.consRevert (ExecStmt.requireFalse he2))))))
      · rw [if_neg hsv] at hs2
        rw [if_neg (fun h => hsv h.2.2.1),multiDelegatedAttestFields]
        exact ExecBlock.consNormal hread1 (ExecBlock.consNormal hc1 (ExecBlock.consNormal (ExecStmt.requireTrue he1)
          (ExecBlock.consNormal hread2 (ExecBlock.consRevert (multiDelegatedAttestCheck_bad hs2)))))
    · rw [if_neg (fun h => hn h.2.1),multiDelegatedAttestFields]
      rw [decide_eq_false hn] at he1
      exact ExecBlock.consNormal hread1 (ExecBlock.consNormal hc1 (ExecBlock.consRevert (ExecStmt.requireFalse he1)))
  · rw [if_neg hdv] at hd1
    rw [if_neg (fun h => hdv h.1),multiDelegatedAttestFields]
    exact ExecBlock.consNormal hread1 (ExecBlock.consRevert (multiDelegatedAttestCheck_bad hd1))

theorem MultiDelegatedAttestLocals.read {L : Store} {requests : List Value} {groups : List (List UInt256)}
    {available : UInt256} {heap i : Nat}
    (h : MultiDelegatedAttestLocals L requests groups available heap i) (last : Bool) (row : Value) :
    MultiDelegatedAttestLocals (batchRowReadLocals L "multiDelegatedRequest" last row) requests groups available heap i := by
  constructor <;> simp (disch := decide) only [batchRowReadLocals,store_get_ne] <;>
    first | exact h.requests | exact h.groups | exact h.count | exact h.available | exact h.heap | exact h.index

theorem MultiDelegatedAttestLocals.fields {L : Store} {requests : List Value} {groups : List (List UInt256)}
    {available : UInt256} {heap i : Nat} {last : Bool} {row : Value} (data sigs : List Value)
    (h : MultiDelegatedAttestLocals L requests groups available heap i)
    (hr : L.get? "multiDelegatedRequest"=some row) (hl : L.get? "last"=some (.bool last)) :
    MultiDelegatedAttestVerifyLocals (multiDelegatedAttestFieldLocals L data sigs) requests groups available heap i 0 last row data sigs := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · constructor <;> simp (disch := decide) only [multiDelegatedAttestFieldLocals,store_get_ne] <;>
      first | exact h.requests | exact h.groups | exact h.count | exact h.available | exact h.heap | exact h.index
  all_goals simp (disch := decide) only [multiDelegatedAttestFieldLocals,store_get_ne,store_get_self]
  all_goals first | exact hr | exact hl | rfl

end Benchmarks.EAS.EAS
