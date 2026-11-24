import Benchmarks.EAS.EAS.MultiDelegatedAttestSource
import Benchmarks.EAS.EAS.DelegatedAttestBuildMemory

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach ABI.Solc08Calldata
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def multiDelegatedAttestDatumLocals (L : Store) (datum signature attester : Value) : Store :=
  L.insert "datum" datum |>.insert "signature" signature |>.insert "attester" attester

theorem multiDelegatedAttestDatumReadSource {L imms : Store} {evm : EVM.State} {data sigs row : List Value}
    {datum signature attester : Value} {j : Nat}
    (hd : L.get? "data"=some (.array data)) (hs : L.get? "signatures"=some (.array sigs))
    (hr : L.get? "multiDelegatedRequest"=some (.tuple row)) (hj : L.get? "j"=some (.int (Int.ofNat j)))
    (hjd : j<data.length) (hjs : j<sigs.length) (hdatum : data[j]=datum) (hsig : sigs[j]=signature)
    (hatt : row[3]?=some attester) (hnd : normalizeRawBoolWord? datum=.ok datum)
    (hns : normalizeRawBoolWord? signature=.ok signature) :
    ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm multiDelegatedAttestDatumRead
      (.ok {contract := contract,locals := multiDelegatedAttestDatumLocals L datum signature attester,immutables := imms} evm) := by
  apply ExecBlock.consNormal (ExecStmt.letDecl (evalArrayIndex (evalLocalValue hd) (evalLocalValue hj) hjd hdatum hnd))
  apply ExecBlock.consNormal (ExecStmt.letDecl (evalArrayIndex
    (evalLocalValue (by simpa (disch := decide) only [store_get_ne] using hs))
    (evalLocalValue (by simpa (disch := decide) only [store_get_ne] using hj)) hjs hsig hns))
  apply ExecBlock.consNormal (ExecStmt.letDecl ?_) ExecBlock.nil
  simp (disch := decide) only [evalExpr?,store_get_ne,hr,EvalResult.ofOption,bind,EvalResult.bind,pure,tupleGetValue?,hatt]

theorem multiDelegatedAttestCheck_tuple {L imms : Store} {evm : EVM.State} {name : Ident} {xs : List Value}
    (h : L.get? name=some (.tuple xs)) :
    ExecStmt fork config {contract := contract,locals := L,immutables := imms} evm (multiDelegatedAttestCheck name)
      (.ok {contract := contract,locals := L,immutables := imms} evm) := by
  apply ExecStmt.requireTrue
  simp only [multiDelegatedAttestCheck,evalExpr?,h,evalStructFields?,EvalResult.ofOption,bind,EvalResult.bind,pure]
  rfl

theorem multiDelegatedAttestCheck_array {L imms : Store} {evm : EVM.State} {name : Ident} {xs : List Value}
    (h : L.get? name=some (.array xs)) :
    ExecStmt fork config {contract := contract,locals := L,immutables := imms} evm (multiDelegatedAttestCheck name)
      (.ok {contract := contract,locals := L,immutables := imms} evm) := by
  apply ExecStmt.requireTrue
  simp only [multiDelegatedAttestCheck,evalExpr?,h,evalStructFields?,EvalResult.ofOption,bind,EvalResult.bind,pure]
  rfl

theorem multiDelegatedAttestCheck_address {L imms : Store} {evm : EVM.State} {name : Ident} {addr : AccountAddress}
    (h : L.get? name=some (.address addr)) :
    ExecStmt fork config {contract := contract,locals := L,immutables := imms} evm (multiDelegatedAttestCheck name)
      (.ok {contract := contract,locals := L,immutables := imms} evm) := by
  apply ExecStmt.requireTrue
  simp only [multiDelegatedAttestCheck,evalExpr?,h,evalStructFields?,EvalResult.ofOption,bind,EvalResult.bind,pure]
  rfl

theorem multiDelegatedAttestCheck_bad {L imms : Store} {evm : EVM.State} {name : Ident}
    (h : L.get? name=some decodeFailure) :
    ExecStmt fork config {contract := contract,locals := L,immutables := imms} evm (multiDelegatedAttestCheck name) .reverted := by
  apply ExecStmt.requireFalse
  simp only [multiDelegatedAttestCheck,evalExpr?,h,evalStructFields?,EvalResult.ofOption,bind,EvalResult.bind,pure]
  rfl

theorem multiDelegatedAttestDatumChecksSource {L imms : Store} {evm : EVM.State}
    {r : AttestationRequestRecord} {s : SignatureRecord} {addr : AccountAddress} (vd va vs : Prop)
    [Decidable vd] [Decidable va] [Decidable vs]
    (hd : L.get? "datum"=some (if vd then r.tuple else decodeFailure))
    (ha : L.get? "attester"=some (if va then .address addr else decodeFailure))
    (hs : L.get? "signature"=some (if vs then s.tuple else decodeFailure)) :
    if vd ∧ va ∧ vs then
      ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm multiDelegatedAttestDatumChecks
        (.ok {contract := contract,locals := L,immutables := imms} evm)
    else ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm multiDelegatedAttestDatumChecks .reverted := by
  by_cases hdv : vd
  · rw [if_pos hdv] at hd
    by_cases hav : va
    · rw [if_pos hav] at ha
      by_cases hsv : vs
      · rw [if_pos hsv] at hs
        rw [if_pos ⟨hdv,hav,hsv⟩]
        exact ExecBlock.consNormal (multiDelegatedAttestCheck_tuple hd)
          (ExecBlock.consNormal (multiDelegatedAttestCheck_address ha)
            (ExecBlock.consNormal (multiDelegatedAttestCheck_tuple hs) ExecBlock.nil))
      · rw [if_neg hsv] at hs
        rw [if_neg (fun h => hsv h.2.2)]
        exact ExecBlock.consNormal (multiDelegatedAttestCheck_tuple hd)
          (ExecBlock.consNormal (multiDelegatedAttestCheck_address ha) (ExecBlock.consRevert (multiDelegatedAttestCheck_bad hs)))
    · rw [if_neg hav] at ha
      rw [if_neg (fun h => hav h.2.1)]
      exact ExecBlock.consNormal (multiDelegatedAttestCheck_tuple hd) (ExecBlock.consRevert (multiDelegatedAttestCheck_bad ha))
  · rw [if_neg hdv] at hd
    rw [if_neg (fun h => hdv h.1)]
    exact ExecBlock.consRevert (multiDelegatedAttestCheck_bad hd)

end Benchmarks.EAS.EAS
