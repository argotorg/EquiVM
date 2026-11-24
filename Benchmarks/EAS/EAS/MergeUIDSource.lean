import Benchmarks.EAS.EAS.ArrayLoopSource
import Benchmarks.EAS.EAS.ArrayAllocateSource

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

abbrev mergeUIDFunction : FunctionDecl := contract.functions[16]!
def wordListValue (words : List UInt256) : Value := .array (words.map wordBytes32Value)
def mergeUIDInitial : Body := [
  .letDecl "uids" (some (.dynamicArray abiBytes32)) (.newArray (.elem (.bytes abiBytes32Width)) (.var "uidsCount")),
  .letDecl "currentIndex" (some abiUInt256) (.intLit 0),resolveManyIndexInit]
def mergeUIDPrefix : Body := arrayAllocateExprBlock (.var "uidsCount") 32 ++ mergeUIDInitial
def mergeUIDInnerIteration : Body := [
  .assign .localVar {base := "uids",steps := [.aindex (.var "currentIndex")]} (.index (.var "currentUids") (.var "j")),
  localCastIncrement "j",localCastIncrement "currentIndex"]
def mergeUIDOuterInitial : Body := [
  .letDecl "currentUids" (some (.dynamicArray abiBytes32)) (.index (.var "uidLists") (.var "i")),
  .letDecl "j" (some abiUInt256) (.intLit 0)]
def mergeUIDOuterIteration : Body := mergeUIDOuterInitial ++
  [.while (localArrayGuard "j" "currentUids") mergeUIDInnerIteration,localCastIncrement "i"]
def mergeUIDReturn : Body := [.return [.var "uids",.var "$EAS.freeMemory"],.return [.tupleLit [],.var "$EAS.freeMemory"]]
def mergeUIDSuffix : Body := [.while (localArrayGuard "i" "uidLists") mergeUIDOuterIteration] ++ mergeUIDReturn

theorem mergeUID_body : mergeUIDFunction.body = mergeUIDPrefix ++ mergeUIDSuffix := by native_decide

structure MergeUIDLocals (L : Store) (groups : List (List UInt256)) (words : List UInt256) (heap c i : Nat) : Prop where
  groups : L.get? "uidLists" = some (.array (groups.map wordListValue))
  words : L.get? "uids" = some (wordListValue words)
  heap : L.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap))
  cursor : L.get? "currentIndex" = some (.int (Int.ofNat c))
  index : L.get? "i" = some (.int (Int.ofNat i))

structure MergeUIDInnerLocals (L : Store) (groups : List (List UInt256)) (words values : List UInt256) (heap c i j : Nat) : Prop where
  outer : MergeUIDLocals L groups words heap c i
  current : L.get? "currentUids" = some (wordListValue values)
  index : L.get? "j" = some (.int (Int.ofNat j))

def mergeUIDInnerNext (L : Store) (words : List UInt256) (word : UInt256) (c j : Nat) : Store :=
  L.insert "uids" (wordListValue (words.set c word)) |>.insert "j" (.int (Int.ofNat (j+1))) |>.insert "currentIndex" (.int (Int.ofNat (c+1)))

theorem MergeUIDInnerLocals.next {L : Store} {groups : List (List UInt256)} {words values : List UInt256} {heap c i j : Nat}
    (h : MergeUIDInnerLocals L groups words values heap c i j) (word : UInt256) :
    MergeUIDInnerLocals (mergeUIDInnerNext L words word c j) groups (words.set c word) values heap (c+1) i (j+1) := by
  constructor
  · constructor
    · simpa (disch := decide) only [mergeUIDInnerNext,store_get_ne] using h.outer.groups
    · simp (disch := decide) only [mergeUIDInnerNext,store_get_ne,store_get_self]
    · simpa (disch := decide) only [mergeUIDInnerNext,store_get_ne] using h.outer.heap
    · exact store_get_self _ _ _
    · simpa (disch := decide) only [mergeUIDInnerNext,store_get_ne] using h.outer.index
  · simpa (disch := decide) only [mergeUIDInnerNext,store_get_ne] using h.current
  · simp (disch := decide) only [mergeUIDInnerNext,store_get_ne,store_get_self]

theorem mergeUIDInnerSource {L imms : Store} {evm : EVM.State} {groups : List (List UInt256)}
    {words values : List UInt256} {heap c i j : Nat}
    (h : MergeUIDInnerLocals L groups words values heap c i j) (hc : c < words.length) (hj : j < values.length)
    (hcb : c+1 < UInt256.size) (hjb : j+1 < UInt256.size) :
    ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm mergeUIDInnerIteration
      (.ok {contract := contract,locals := mergeUIDInnerNext L words values[j] c j,immutables := imms} evm) := by
  apply ExecBlock.consNormal (execLocalWordArrayCopy h.outer.words h.current h.outer.cursor h.index hc hj)
  apply ExecBlock.consNormal (execLocalCastIncrement (by simpa (disch := decide) only [store_get_ne] using h.index) hjb)
  apply ExecBlock.consNormal (execLocalCastIncrement ?_ hcb) ExecBlock.nil
  simpa (disch := decide) only [store_get_ne] using h.outer.cursor

theorem mergeUIDOuterInitialSource {L imms : Store} {evm : EVM.State} {groups : List (List UInt256)}
    {words : List UInt256} {heap c i : Nat}
    (h : MergeUIDLocals L groups words heap c i) (hi : i < groups.length) :
    let next := (L.insert "currentUids" (wordListValue groups[i])).insert "j" (.int 0)
    ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm mergeUIDOuterInitial
      (.ok {contract := contract,locals := next,immutables := imms} evm) ∧
    MergeUIDInnerLocals next groups words groups[i] heap c i 0 := by
  dsimp only
  constructor
  · have he : evalExpr? config {contract := contract,locals := L,immutables := imms} evm (.index (.var "uidLists") (.var "i")) =
        .ok (wordListValue groups[i]) := evalArrayIndex (evalLocalValue h.groups) (evalLocalValue h.index)
          (by simpa only [List.length_map] using hi) (List.getElem_map ..) rfl
    exact ExecBlock.consNormal (ExecStmt.letDecl he)
      (ExecBlock.consNormal (ExecStmt.letDecl (by simp only [evalExpr?,pure])) ExecBlock.nil)
  · constructor
    · constructor <;> simp (disch := decide) only [store_get_ne] <;> first | exact h.groups | exact h.words | exact h.heap | exact h.cursor | exact h.index
    · simp (disch := decide) only [store_get_ne,store_get_self]
    · exact store_get_self _ _ _

theorem MergeUIDLocals.increment {L : Store} {groups : List (List UInt256)} {words : List UInt256} {heap c i : Nat}
    (h : MergeUIDLocals L groups words heap c i) :
    MergeUIDLocals (L.insert "i" (.int (Int.ofNat (i+1)))) groups words heap c (i+1) := by
  constructor
  · simpa (disch := decide) only [store_get_ne] using h.groups
  · simpa (disch := decide) only [store_get_ne] using h.words
  · simpa (disch := decide) only [store_get_ne] using h.heap
  · simpa (disch := decide) only [store_get_ne] using h.cursor
  · exact store_get_self _ _ _

def mergeUIDInitialLocals (L : Store) (n heap : Nat) : Store :=
  (allocateBlockLocals L heap).insert "uids" (wordListValue (List.replicate n ⟨0⟩))
    |>.insert "currentIndex" (.int 0) |>.insert "i" (.int 0)

theorem mergeUIDPrefixSource {L imms : Store} {evm : EVM.State} {groups : List (List UInt256)} {n heap : Nat}
    (hd : L.get? "uidLists" = some (.array (groups.map wordListValue)))
    (hn : L.get? "uidsCount" = some (.int (Int.ofNat n)))
    (hh : L.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap))) :
    let next := allocateNext heap (32+32*n)
    (n ≤ 2^64-1 ∧ (next ≤ 2^64-1 ∧ heap ≤ next) →
      ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm mergeUIDPrefix
        (.ok {contract := contract,locals := mergeUIDInitialLocals L n next,immutables := imms} evm) ∧
      MergeUIDLocals (mergeUIDInitialLocals L n next) groups (List.replicate n ⟨0⟩) next 0 0) ∧
    (¬ (n ≤ 2^64-1 ∧ (next ≤ 2^64-1 ∧ heap ≤ next)) →
      ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm mergeUIDPrefix .reverted) := by
  dsimp only
  have ha := arrayAllocateExprSource (fork := fork) (cfg := config) (imms := imms) (evm := evm) (evalLocalValue hn) hh 32
  constructor
  · intro hv
    rw [if_pos hv.1,if_pos hv.2] at ha
    constructor
    · have hn' : (allocateBlockLocals L (allocateNext heap (32+32*n))).get? "uidsCount" = some (.int (Int.ofNat n)) := by
        simpa (disch := decide) only [allocateBlockLocals,unpackHeapLocals,store_get_ne] using hn
      have he : evalExpr? config {contract := contract,locals := allocateBlockLocals L (allocateNext heap (32+32*n)),immutables := imms} evm
          (.newArray (.elem (.bytes abiBytes32Width)) (.var "uidsCount")) = .ok (wordListValue (List.replicate n ⟨0⟩)) := by
        unfold wordListValue
        rw [List.map_replicate]
        exact evalLocalNewArray hn' (by native_decide)
      exact execBlock_append ha (ExecBlock.consNormal (ExecStmt.letDecl he)
        (ExecBlock.consNormal (ExecStmt.letDecl (by simp only [evalExpr?,pure]))
          (ExecBlock.consNormal (ExecStmt.letDecl (by simp only [evalExpr?,pure])) ExecBlock.nil)))
    · constructor
      · simpa (disch := decide) only [mergeUIDInitialLocals,allocateBlockLocals,unpackHeapLocals,store_get_ne] using hd
      · simp (disch := decide) only [mergeUIDInitialLocals,store_get_ne,store_get_self]
      · simp (disch := decide) only [mergeUIDInitialLocals,allocateBlockLocals,unpackHeapLocals,store_get_ne,store_get_self]
      · simp (disch := decide) only [mergeUIDInitialLocals,store_get_ne,store_get_self,Int.ofNat_eq_natCast,Nat.cast_zero]
      · exact store_get_self _ _ _
  · intro hv
    by_cases hn' : n ≤ 2^64-1
    · rw [if_pos hn',if_neg (fun h => hv ⟨hn',h⟩)] at ha
      exact execBlock_append_term ha (by intros; exact nofun)
    · rw [if_neg hn'] at ha
      exact execBlock_append_term ha (by intros; exact nofun)

def mergeUIDArgs (groups : List (List UInt256)) (n heap : Nat) : Store :=
  (∅ : Store).insert "$EAS.freeMemory" (.int (Int.ofNat heap)) |>.insert "uidsCount" (.int (Int.ofNat n))
    |>.insert "uidLists" (.array (groups.map wordListValue))
theorem mergeUID_lookup : lookupCallable? contract "_mergeUIDs" = some mergeUIDFunction.toCallable := rfl
theorem mergeUID_bind (groups : List (List UInt256)) (n heap : Nat) :
    bindParams? mergeUIDFunction.params [.array (groups.map wordListValue),.int (Int.ofNat n),.int (Int.ofNat heap)] =
      some (mergeUIDArgs groups n heap) := rfl

end Benchmarks.EAS.EAS
