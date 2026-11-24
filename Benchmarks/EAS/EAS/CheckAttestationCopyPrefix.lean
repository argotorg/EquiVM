import Benchmarks.EAS.EAS.CheckAttestationCopyExpr

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem checkAttestationCopyPrefixSource {L imms : Store} {evm : EVM.State} {index len heap : Nat}
    (hi : L.get? "index"=some (.int (Int.ofNat index)))
    (hl : L.get? "length"=some (.int (Int.ofNat len)))
    (hh : L.get? "$EAS.freeMemory"=some (.int (Int.ofNat heap))) :
    ∃ L', ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm checkAttestationCopyPrefix
      (.ok {contract := contract,locals := L',immutables := imms} evm) ∧
      L'.get? "data"=some (.int (Int.ofNat (checkAttestationCopyData evm.executionEnv.calldata index).toNat)) ∧
      L'.get? "input"=some (.bytes evm.executionEnv.calldata) ∧
      L'.get? "length"=some (.int (Int.ofNat len)) ∧ L'.get? "$EAS.freeMemory"=some (.int (Int.ofNat heap)) := by
  let cd := evm.executionEnv.calldata
  let base := checkAttestationCopyBase cd
  let ptr := checkAttestationCopyRoot cd index
  let tailWord := calldataWord cd (ptr+UInt256.ofNat 32).toNat
  let L0 := L.insert "input" (.bytes cd)
  let L1 := heapResultLocals L0 "root$allocation" "root" "$EAS.freeMemory" (.int (Int.ofNat (calldataWord cd 4).toNat)) heap
  let L2 := L1.insert "heads" (.int (Int.ofNat base.toNat))
  let L3 := heapResultLocals L2 "relative$allocation" "relative" "$EAS.freeMemory"
    (.int (Int.ofNat (calldataWord cd (UInt256.ofNat (base.toNat+32*index)).toNat).toNat)) heap
  let L4 := L3.insert "request" (.int (Int.ofNat ptr.toNat))
  let L5 := heapResultLocals L4 "tail$allocation" "tail" "$EAS.freeMemory" (.int (Int.ofNat tailWord.toNat)) heap
  let L6 := L5.insert "data" (.int (Int.ofNat (checkAttestationCopyData cd index).toNat))
  have hinput : ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm
      [.letDecl "input" (some .bytes) (.env .msgData)] (.ok {contract := contract,locals := L0,immutables := imms} evm) :=
    ExecBlock.consNormal (ExecStmt.letDecl (by simp only [evalExpr?,envValue,pure];rfl)) ExecBlock.nil
  have hh0 : L0.get? "$EAS.freeMemory"=some (.int (Int.ofNat heap)) := (store_get_ne _ _ (by decide)).trans hh
  have hroot : ExecBlock fork config {contract := contract,locals := L0,immutables := imms} evm
      (checkAttestationCopyWord (.intLit 4) "root") (.ok {contract := contract,locals := L1,immutables := imms} evm) :=
    checkAttestationCopyWordSource (ptr := UInt256.ofNat 4) "root" (by decide) (by decide) (by decide)
      (by simp only [evalExpr?,pure];rfl) hh0
  have hr1 : L1.get? "root"=some (.int (Int.ofNat (calldataWord cd 4).toNat)) := heapResultLocals_result _ _ _ _ _ _ (by decide)
  have he2 : evalExpr? config {contract := contract,locals := L1,immutables := imms} evm
      (checkAttestationCopyCast (.binary .add (.var "root") (.intLit 36)))=.ok (.int (Int.ofNat base.toNat)) :=
    evalCastUint256Add (evalLocalValue hr1) (by simp only [evalExpr?,pure];rfl)
  have hheads : ExecBlock fork config {contract := contract,locals := L1,immutables := imms} evm
      [.letDecl "heads" (some abiUInt256) (checkAttestationCopyCast (.binary .add (.var "root") (.intLit 36)))]
      (.ok {contract := contract,locals := L2,immutables := imms} evm) := ExecBlock.consNormal (ExecStmt.letDecl he2) ExecBlock.nil
  have hh2 : L2.get? "$EAS.freeMemory"=some (.int (Int.ofNat heap)) := by
    simp (disch := decide) only [L2,L1,store_get_ne,heapResultLocals_heap]
  have hi2 : L2.get? "index"=some (.int (Int.ofNat index)) := by
    simpa (disch := decide) only [L2,L1,L0,store_get_ne,heapResultLocals_get] using hi
  have hb2 : L2.get? "heads"=some (.int (Int.ofNat base.toNat)) := store_get_self _ _ _
  have hrelative : ExecBlock fork config {contract := contract,locals := L2,immutables := imms} evm
      (checkAttestationCopyWord (checkAttestationCopySlot "heads" "index") "relative")
      (.ok {contract := contract,locals := L3,immutables := imms} evm) :=
    checkAttestationCopyWordSource "relative" (by decide) (by decide) (by decide) (checkAttestationCopySlot_eval hb2 hi2) hh2
  have hb3 : L3.get? "heads"=some (.int (Int.ofNat base.toNat)) := by
    simpa (disch := decide) only [L3,heapResultLocals_get] using hb2
  have hr3 : L3.get? "relative"=some (.int (Int.ofNat (calldataWord cd (UInt256.ofNat (base.toNat+32*index)).toNat).toNat)) :=
    heapResultLocals_result _ _ _ _ _ _ (by decide)
  have he4 : evalExpr? config {contract := contract,locals := L3,immutables := imms} evm
      (checkAttestationCopyCast (.binary .add (.var "heads") (.var "relative")))=.ok (.int (Int.ofNat ptr.toNat)) :=
    evalCastWordAdd (evalLocalValue hb3) (evalLocalValue hr3)
  have hrequest : ExecBlock fork config {contract := contract,locals := L3,immutables := imms} evm
      [.letDecl "request" (some abiUInt256) (checkAttestationCopyCast (.binary .add (.var "heads") (.var "relative")))]
      (.ok {contract := contract,locals := L4,immutables := imms} evm) := ExecBlock.consNormal (ExecStmt.letDecl he4) ExecBlock.nil
  have hh4 : L4.get? "$EAS.freeMemory"=some (.int (Int.ofNat heap)) := by
    simp (disch := decide) only [L4,L3,store_get_ne,heapResultLocals_heap]
  have hr4 : L4.get? "request"=some (.int (Int.ofNat ptr.toNat)) := store_get_self _ _ _
  have he5 : evalExpr? config {contract := contract,locals := L4,immutables := imms} evm
      (checkAttestationCopyCast (.binary .add (.var "request") (.intLit 32)))=.ok (.int (Int.ofNat (ptr+UInt256.ofNat 32).toNat)) :=
    evalCastWordAdd (evalLocalValue hr4) (by simp only [evalExpr?,pure];rfl)
  have htail : ExecBlock fork config {contract := contract,locals := L4,immutables := imms} evm
      (checkAttestationCopyWord (checkAttestationCopyCast (.binary .add (.var "request") (.intLit 32))) "tail")
      (.ok {contract := contract,locals := L5,immutables := imms} evm) :=
    checkAttestationCopyWordSource "tail" (by decide) (by decide) (by decide) he5 hh4
  have hr5 : L5.get? "request"=some (.int (Int.ofNat ptr.toNat)) := by
    simpa (disch := decide) only [L5,heapResultLocals_get] using hr4
  have ht5 : L5.get? "tail"=some (.int (Int.ofNat tailWord.toNat)) := heapResultLocals_result _ _ _ _ _ _ (by decide)
  have he6 : evalExpr? config {contract := contract,locals := L5,immutables := imms} evm
      (checkAttestationCopyCast (.binary .add (.binary .add (.var "request") (.var "tail")) (.intLit 32)))=
      .ok (.int (Int.ofNat (checkAttestationCopyData cd index).toNat)) := by
    have he := evalCastUint256Add (naturalAddSource
      (evalLocalValue (cfg := config) (stele := {contract := contract,locals := L5,immutables := imms}) (evm := evm) hr5)
      (evalLocalValue ht5)) (show evalExpr? config {contract := contract,locals := L5,immutables := imms} evm (.intLit 32)=.ok (.int (Int.ofNat 32)) from by simp only [evalExpr?,pure];rfl)
    have hn : (checkAttestationCopyData cd index).toNat=((ptr.toNat+tailWord.toNat)+32)%UInt256.size := by
      change ((ptr+tailWord)+UInt256.ofNat 32).toNat=_
      simp only [uadd_toNat,show (UInt256.ofNat 32).toNat=32 from rfl,Nat.mod_add_mod]
    simpa only [hn] using he
  have hdata : ExecBlock fork config {contract := contract,locals := L5,immutables := imms} evm
      [.letDecl "data" (some abiUInt256) (checkAttestationCopyCast (.binary .add (.binary .add (.var "request") (.var "tail")) (.intLit 32)))]
      (.ok {contract := contract,locals := L6,immutables := imms} evm) := ExecBlock.consNormal (ExecStmt.letDecl he6) ExecBlock.nil
  refine ⟨L6,?_,store_get_self _ _ _,?_,?_,?_⟩
  · exact execBlock_append (execBlock_append (execBlock_append (execBlock_append (execBlock_append
      (execBlock_append hinput hroot) hheads) hrelative) hrequest) htail) hdata
  · simp (disch := decide) only [L6,L5,L4,L3,L2,L1,L0,store_get_ne,heapResultLocals_get,store_get_self]
    rfl
  · simpa (disch := decide) only [L6,L5,L4,L3,L2,L1,L0,store_get_ne,heapResultLocals_get] using hl
  · simp (disch := decide) only [L6,L5,store_get_ne,heapResultLocals_heap]

end Benchmarks.EAS.EAS
