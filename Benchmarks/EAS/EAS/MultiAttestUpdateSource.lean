import Benchmarks.EAS.EAS.MultiAttestFacts

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def multiAttestCopyLocals (L : Store) (heap : Nat) : Store :=
  heapResultLocals L "allocation$allocation" "allocation" "$EAS.freeMemory" (.tuple []) heap
def multiAttestCallLocals (L : Store) (words : List UInt256) (used : UInt256) (heap : Nat) : Store :=
  heapResultLocals L "res$allocation" "res" "$EAS.freeMemory" (attestationsResultValue words used) heap

theorem MultiAttestLocals.copied {L : Store} {requests : List Value} {groups : List (List UInt256)}
    {available : UInt256} {heap i : Nat} (h : MultiAttestLocals L requests groups available heap i) (next : Nat) :
    MultiAttestLocals (multiAttestCopyLocals L next) requests groups available next i := by
  constructor <;> simp (disch := decide) only [multiAttestCopyLocals,heapResultLocals_get,heapResultLocals_heap] <;>
    first | exact h.requests | exact h.groups | exact h.count | exact h.available | exact h.index

theorem MultiAttestLocals.called {L : Store} {requests : List Value} {groups : List (List UInt256)}
    {available : UInt256} {heap i : Nat} (h : MultiAttestLocals L requests groups available heap i)
    (words : List UInt256) (used : UInt256) (next : Nat) :
    MultiAttestLocals (multiAttestCallLocals L words used next) requests groups available next i := by
  constructor <;> simp (disch := decide) only [multiAttestCallLocals,heapResultLocals_get,heapResultLocals_heap] <;>
    first | exact h.requests | exact h.groups | exact h.count | exact h.available | exact h.index

def multiAttestNextLocals (L : Store) (groups : List (List UInt256)) (words : List UInt256)
    (available used : UInt256) (i : Nat) : Store :=
  L.insert "availableValue" (.int (Int.ofNat (UInt256.sub available used).toNat))
    |>.insert "totalUids" (.array ((groups.set i words).map wordListValue))
    |>.insert "totalUidsCount" (.int (Int.ofNat (groups.flatten.length+words.length)))
    |>.insert "i" (.int (Int.ofNat (i+1)))

theorem MultiAttestLocals.next {L : Store} {requests : List Value} {groups : List (List UInt256)}
    {available : UInt256} {heap i : Nat} (h : MultiAttestLocals L requests groups available heap i)
    (words : List UInt256) (used : UInt256) (hi : i<groups.length) (he : groups[i]=[]) :
    MultiAttestLocals (multiAttestNextLocals L groups words available used i)
      requests (groups.set i words) (UInt256.sub available used) heap (i+1) := by
  constructor
  · simpa (disch := decide) only [multiAttestNextLocals,store_get_ne] using h.requests
  · simp (disch := decide) only [multiAttestNextLocals,store_get_ne,store_get_self]
  · simp (disch := decide) only [multiAttestNextLocals,store_get_ne,store_get_self,flattenLength_set_empty groups words i hi he]
  · simp (disch := decide) only [multiAttestNextLocals,store_get_ne,store_get_self]
  · simpa (disch := decide) only [multiAttestNextLocals,store_get_ne] using h.heap
  · exact store_get_self _ _ _

theorem multiAttestUpdateSourceOfFields {L imms : Store} {evm : EVM.State}
    {groups : List (List UInt256)} {words : List UInt256} {available used : UInt256} {i : Nat}
    (hg : L.get? "totalUids"=some (.array (groups.map wordListValue)))
    (hc0 : L.get? "totalUidsCount"=some (.int (Int.ofNat groups.flatten.length)))
    (ha : L.get? "availableValue"=some (.int (Int.ofNat available.toNat)))
    (hi0 : L.get? "i"=some (.int (Int.ofNat i)))
    (hr : L.get? "res" = some (attestationsResultValue words used))
    (hi : i<groups.length) (hib : i+1<UInt256.size)
    (hc : groups.flatten.length+words.length<UInt256.size) (hu : used.toNat≤available.toNat) :
    ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm multiAttestUpdate
      (.ok {contract := contract,locals := multiAttestNextLocals L groups words available used i,immutables := imms} evm) := by
  let L1 := L.insert "availableValue" (.int (Int.ofNat (UInt256.sub available used).toNat))
  let L2 := L1.insert "totalUids" (.array ((groups.set i words).map wordListValue))
  have hr1 : L1.get? "res" = some (attestationsResultValue words used) := by
    simpa (disch := decide) only [L1,store_get_ne] using hr
  have hr2 : L2.get? "res" = some (attestationsResultValue words used) := by
    simpa (disch := decide) only [L2,store_get_ne] using hr1
  have hs1 : ExecStmt fork config {contract := contract,locals := L,immutables := imms} evm
      (.assign .localVar {base := "availableValue"}
        (.inRange abiUInt256Int (.binary .sub (.var "availableValue") (.field (.var "res") "usedValue"))))
      (.ok {contract := contract,locals := L1,immutables := imms} evm) :=
    ExecStmt.assign (hperm := by first | exact Or.inl rfl | assumption | exact Or.inr ‹_›) (evalExpr_uint256_sub (evalLocalValue ha)
      (evalRecordField (evalLocalValue hr) rfl) hu) (assignLocalValue ha)
  have hs2 : ExecStmt fork config {contract := contract,locals := L1,immutables := imms} evm
      (.assign .localVar {base := "totalUids",steps := [.aindex (.var "i")]} (.field (.var "res") "uids"))
      (.ok {contract := contract,locals := L2,immutables := imms} evm) := by
    apply ExecStmt.assign (hperm := by first | exact Or.inl rfl | assumption | exact Or.inr ‹_›) (evalRecordField (evalLocalValue hr1) (value := wordListValue words) rfl)
    simpa only [L2,List.map_set] using assignLocalArrayIndex
      (cfg := config) (stele := {contract := contract,locals := L1,immutables := imms}) (evm := evm)
      (array := "totalUids") (index := "i") (values := groups.map wordListValue) (i := i) (value := wordListValue words)
      (by simpa (disch := decide) only [L1,store_get_ne] using hg)
      (by simpa (disch := decide) only [L1,store_get_ne] using hi0)
      (by simpa only [List.length_map] using hi)
  have hcount : L2.get? "totalUidsCount" = some (.int (Int.ofNat groups.flatten.length)) := by
    simpa (disch := decide) only [L2,L1,store_get_ne] using hc0
  have hlen : evalExpr? config {contract := contract,locals := L2,immutables := imms} evm
      (.arrayLength .localVar {base := "res",steps := [.field "uids"]}) = .ok (.int (Int.ofNat words.length)) := by
    simp only [evalExpr?,readLocalPath?,hr2,attestationsResultValue,lookupField?,bind,EvalResult.bind,pure]
    change EvalResult.ok (Value.int (Int.ofNat (words.map wordBytes32Value).length)) = _
    rw [List.length_map]
  have he := evalCastUint256Add (evalLocalValue hcount) hlen
  rw [Nat.mod_eq_of_lt hc] at he
  apply ExecBlock.consNormal hs1
  apply ExecBlock.consNormal hs2
  apply ExecBlock.consNormal (ExecStmt.assign (fork := fork) (hperm := by first | exact Or.inl rfl | assumption | exact Or.inr ‹_›) he (assignLocalValue hcount))
  apply ExecBlock.consNormal (execLocalCastIncrement ?_ hib) ExecBlock.nil
  simpa (disch := decide) only [L2,L1,store_get_ne] using hi0

theorem multiAttestUpdateSource {L imms : Store} {evm : EVM.State} {requests : List Value}
    {groups : List (List UInt256)} {words : List UInt256} {available used : UInt256} {heap i : Nat}
    (h : MultiAttestLocals L requests groups available heap i)
    (hr : L.get? "res" = some (attestationsResultValue words used))
    (hi : i<groups.length) (hib : i+1<UInt256.size)
    (hc : groups.flatten.length+words.length<UInt256.size) (hu : used.toNat≤available.toNat) :
    ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm multiAttestUpdate
      (.ok {contract := contract,locals := multiAttestNextLocals L groups words available used i,immutables := imms} evm) :=
  multiAttestUpdateSourceOfFields h.groups h.count h.available h.index hr hi hib hc hu

end Benchmarks.EAS.EAS
