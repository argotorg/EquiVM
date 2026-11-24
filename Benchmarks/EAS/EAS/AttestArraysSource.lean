import Benchmarks.EAS.EAS.ArrayAllocateSource
import Benchmarks.EAS.EAS.DefaultArrayRecords
import Benchmarks.EAS.EAS.AttestLoopLocals
import Benchmarks.EAS.EAS.AttestIterationSource

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def attestArrayDecl : Stmt := .letDecl "attestations" (some (.dynamicArray attestationABI))
  (.newArray attestationType (.var "length"))
def attestValuesDecl : Stmt := .letDecl "values" (some (.dynamicArray abiUInt256))
  (.newArray (.elem (.int (.uint ⟨256,by decide⟩))) (.var "length"))
def attestIndexDecl : Stmt := .letDecl "i" (some abiUInt256) (.intLit 0)
def attestArraysBody : Body := arrayAllocateBlock 352 ++ [attestArrayDecl] ++ arrayAllocateBlock 32 ++
  [attestValuesDecl,attestIndexDecl]

theorem attestArraysBody_eq : (attestFunction.body.drop 15).take 11 = attestArraysBody := by native_decide

def attestArrayLocals (L : Store) (len middle : Nat) : Store :=
  (allocateBlockLocals L middle).insert "attestations" (.array ((List.replicate len defaultAttestationRecord).map AttestationRecord.value))
def attestArraysLocals (L : Store) (len middle next : Nat) : Store :=
  ((allocateBlockLocals (attestArrayLocals L len middle) next).insert "values"
    (.array ((List.replicate len (⟨0⟩ : UInt256)).map (fun w => Value.int (Int.ofNat w.toNat))))).insert "i" (.int 0)

theorem attestArrayDecl_source {cfg : Config} {L imms : Store} {evm : EVM.State} {len : Nat}
    (hl : L.get? "length" = some (.int (Int.ofNat len))) :
    ExecStmt fork cfg {contract := contract,locals := L,immutables := imms} evm attestArrayDecl
      (.ok {contract := contract,locals := (L.insert "attestations"
        (.array ((List.replicate len defaultAttestationRecord).map AttestationRecord.value))),immutables := imms} evm) := by
  unfold attestArrayDecl
  apply ExecStmt.letDecl
  rw [List.map_replicate]
  exact evalLocalNewArray hl defaultAttestationRecord_default

theorem attestValuesDecl_source {cfg : Config} {L imms : Store} {evm : EVM.State} {len : Nat}
    (hl : L.get? "length" = some (.int (Int.ofNat len))) :
    ExecBlock fork cfg {contract := contract,locals := L,immutables := imms} evm [attestValuesDecl,attestIndexDecl]
      (.ok {contract := contract,locals := (L.insert "values"
        (.array ((List.replicate len (⟨0⟩ : UInt256)).map (fun w => Value.int (Int.ofNat w.toNat))))).insert "i" (.int 0),immutables := imms} evm) := by
  unfold attestValuesDecl attestIndexDecl
  have he : evalExpr? cfg {contract := contract,locals := L,immutables := imms} evm
      (.newArray (.elem (.int (.uint ⟨256,by decide⟩))) (.var "length")) =
      .ok (.array ((List.replicate len (⟨0⟩ : UInt256)).map (fun w => Value.int (Int.ofNat w.toNat)))) := by
    rw [List.map_replicate]
    exact evalLocalNewArray hl (by native_decide)
  apply ExecBlock.consNormal (ExecStmt.letDecl he)
  exact ExecBlock.consNormal (ExecStmt.letDecl (by simp only [evalExpr?,pure])) ExecBlock.nil

structure AttestSetupLocals (L : Store) (rs : List AttestationRequestRecord) (s : SchemaRecord)
    (schema : UInt256) (attester : AccountAddress) (available : UInt256) (last : Bool) (heap : Nat) : Prop where
  data : L.get? "data" = some (.array (rs.map AttestationRequestRecord.tuple))
  length : L.get? "length" = some (.int (Int.ofNat rs.length))
  schema : L.get? "schema" = some (wordBytes32Value schema)
  schemaRecord : L.get? "schemaRecord" = some s.value
  attester : L.get? "attester" = some (.address attester)
  available : L.get? "availableValue" = some (.int (Int.ofNat available.toNat))
  last : L.get? "last" = some (.bool last)
  result : L.get? "res" = some (attestationsResultValue (List.replicate rs.length ⟨0⟩) ⟨0⟩)
  heap : L.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap))
  db : L.get? "_db" = none

theorem attestArraysSource {L imms : Store} {evm : EVM.State} {len heap : Nat}
    (hl : L.get? "length" = some (.int (Int.ofNat len)))
    (hh : L.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap))) :
    let middle := allocateNext heap (32+352*len)
    let next := allocateNext middle (32+32*len)
    if len ≤ 2^64-1 then
      if middle ≤ 2^64-1 ∧ heap ≤ middle then
        if next ≤ 2^64-1 ∧ middle ≤ next then
          ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm attestArraysBody
            (.ok {contract := contract,locals := attestArraysLocals L len middle next,immutables := imms} evm)
        else ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm attestArraysBody .reverted
      else ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm attestArraysBody .reverted
    else ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm attestArraysBody .reverted := by
  dsimp only
  have h1 := arrayAllocateSource (fork := fork) (cfg := config) (imms := imms) (evm := evm) hl hh 352
  by_cases hlen : len ≤ 2^64-1
  · rw [if_pos hlen] at h1 ⊢
    by_cases hg1 : allocateNext heap (32+352*len) ≤ 2^64-1 ∧ heap ≤ allocateNext heap (32+352*len)
    · rw [if_pos hg1] at h1 ⊢
      have hl1 : (allocateBlockLocals L (allocateNext heap (32+352*len))).get? "length" = some (.int (Int.ofNat len)) :=
        (allocateBlockLocals_get (by decide) (by decide) (by decide)).trans hl
      have hd := attestArrayDecl_source (fork := fork) (cfg := config) (imms := imms) (evm := evm) hl1
      have hl2 : (attestArrayLocals L len (allocateNext heap (32+352*len))).get? "length" = some (.int (Int.ofNat len)) := by
        simpa only [attestArrayLocals,store_get_ne _ _ (by decide : ("attestations" == "length") = false)] using hl1
      have hh2 : (attestArrayLocals L len (allocateNext heap (32+352*len))).get? "$EAS.freeMemory" =
          some (.int (Int.ofNat (allocateNext heap (32+352*len)))) := by
        simp only [attestArrayLocals,store_get_ne _ _ (by decide : ("attestations" == "$EAS.freeMemory") = false),
          allocateBlockLocals,unpackHeapLocals,store_get_self]
      have h2 := arrayAllocateSource (fork := fork) (cfg := config) (imms := imms) (evm := evm) hl2 hh2 32
      rw [if_pos hlen] at h2
      have hprefix := execBlock_append h1 (ExecBlock.consNormal hd ExecBlock.nil)
      split at h2
      · rename_i hg2
        rw [if_pos hg2]
        have hl3 := (allocateBlockLocals_get (heap := allocateNext (allocateNext heap (32+352*len)) (32+32*len))
          (by decide : ("allocation$allocation" == "length") = false) (by decide) (by decide)).trans hl2
        exact execBlock_append (execBlock_append hprefix h2) (attestValuesDecl_source hl3)
      · rename_i hg2
        rw [if_neg hg2]
        simpa only [attestArraysBody,List.append_assoc] using
          execBlock_append hprefix (execBlock_append_term (s2 := [attestValuesDecl,attestIndexDecl]) h2 (by intros;exact nofun))
    · rw [if_neg hg1] at h1 ⊢
      simpa only [attestArraysBody,List.append_assoc] using execBlock_append_term
        (s2 := [attestArrayDecl] ++ arrayAllocateBlock 32 ++ [attestValuesDecl,attestIndexDecl]) h1 (by intros;exact nofun)
  · rw [if_neg hlen] at h1 ⊢
    simpa only [attestArraysBody,List.append_assoc] using execBlock_append_term
      (s2 := [attestArrayDecl] ++ arrayAllocateBlock 32 ++ [attestValuesDecl,attestIndexDecl]) h1 (by intros;exact nofun)

theorem attestArraysLocals_get (L : Store) (len middle next : Nat) (name : Ident)
    (h1 : ("i" == name) = false) (h2 : ("values" == name) = false)
    (h3 : ("allocation$allocation" == name) = false) (h4 : ("allocation" == name) = false)
    (h5 : ("$EAS.freeMemory" == name) = false) (h6 : ("attestations" == name) = false) :
    (attestArraysLocals L len middle next).get? name = L.get? name := by
  simp only [attestArraysLocals,attestArrayLocals,store_get_ne _ _ h1,store_get_ne _ _ h2,
    allocateBlockLocals_get h3 h4 h5,store_get_ne _ _ h6]


theorem attestArraysLocals_view {L : Store} {rs : List AttestationRequestRecord} {s : SchemaRecord}
    {schema available : UInt256} {attester : AccountAddress} {last : Bool} {heap : Nat}
    (h : AttestSetupLocals L rs s schema attester available last heap) (middle next : Nat) :
    AttestLoopLocals (attestArraysLocals L rs.length middle next) rs s schema attester available last
      (List.replicate rs.length defaultAttestationRecord) (List.replicate rs.length ⟨0⟩)
      (List.replicate rs.length ⟨0⟩) ⟨0⟩ 0 next := by
  have keep (name : Ident) (h1 : ("i" == name) = false) (h2 : ("values" == name) = false)
      (h3 : ("allocation$allocation" == name) = false) (h4 : ("allocation" == name) = false)
      (h5 : ("$EAS.freeMemory" == name) = false) (h6 : ("attestations" == name) = false) :
      (attestArraysLocals L rs.length middle next).get? name = L.get? name :=
    attestArraysLocals_get L rs.length middle next name h1 h2 h3 h4 h5 h6
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.data
  · exact (keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.length
  · exact (keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.schema
  · exact (keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.schemaRecord
  · exact (keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.attester
  · exact (keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.available
  · exact (keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.last
  · simp (disch := decide) only [attestArraysLocals,attestArrayLocals,store_get_ne,allocateBlockLocals_get,store_get_self]
  · simp (disch := decide) only [attestArraysLocals,store_get_ne,store_get_self]
  · exact (keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.result
  · exact store_get_self _ _ _
  · simp (disch := decide) only [attestArraysLocals,allocateBlockLocals,unpackHeapLocals,store_get_ne,store_get_self]
  · exact (keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.db

end Benchmarks.EAS.EAS
