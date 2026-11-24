import Benchmarks.EAS.EAS.ResolverCallSource
import Benchmarks.EAS.EAS.StaticCallBridge

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def payablePayload : ByteArray := selectorBytes 0xce 0x46 0xe0 0x46

theorem payablePayload_encode : config.externalABI.encode? "isPayable" [] = some payablePayload := by
  change ABI.encodeCallWithSelector? payablePayload [] [] = some payablePayload
  simp only [ABI.encodeCallWithSelector?, encodeABIValues?, abiTupleHeadSize?, encodeABIValuesFrom?, bind, Option.bind]
  rfl

theorem payablePayload_size : payablePayload.size = 4 := by rfl

def payableProbeBlock : Body :=
  .externalCall (.var "resolver") "isPayable" (.intLit 0) [] "payableResult" false :: allocateBlock (.intLit 32)

def payableProbeLocals (locals : Store) (out : ByteArray) (heap : Nat) : Store :=
  allocateBlockLocals (locals.insert "payableResult" (.bool (decide (calldataWord out 0 ≠ ⟨0⟩)))) (allocateNext heap 32)

theorem payableProbeSource {locals imms : Store} {evm evm' : EVM.State} {target : AccountAddress}
    {heap : Nat} {success : Bool} {out : ByteArray}
    (hr : locals.get? "resolver" = some (.address target))
    (hh : locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)))
    (hc : callViaEVM fork evm target 0 payablePayload (success,evm',out) false) (hout : out.size < 2^255) :
    if resolverCallValid heap success out then
      ExecBlock fork config {contract := contract, locals := locals, immutables := imms} evm payableProbeBlock
        (.ok {contract := contract, locals := payableProbeLocals locals out heap, immutables := imms} evm')
    else ExecBlock fork config {contract := contract, locals := locals, immutables := imms} evm payableProbeBlock .reverted := by
  have ht : EVM.address target.val = target := by
    apply Fin.ext
    change target.val % AccountAddress.size = target.val
    exact Nat.mod_eq_of_lt target.isLt
  have hcall : typedCallViaEVM fork config evm (EVM.address target.val) "isPayable" 0 [] (success,evm',out) false := by
    rw [ht]
    exact ⟨payablePayload,payablePayload_encode,hc⟩
  have hre : evalExpr? config {contract := contract, locals := locals, immutables := imms} evm (.var "resolver") = .ok (.address target) := by
    simp only [evalExpr?, hr, EvalResult.ofOption]
  have hh' : (locals.insert "payableResult" (.bool (decide (calldataWord out 0 ≠ ⟨0⟩)))).get? "$EAS.freeMemory" =
      some (.int (Int.ofNat heap)) := by
    simpa only [store_get_ne _ _ (by decide : ("payableResult" == "$EAS.freeMemory") = false)] using hh
  by_cases hv : resolverCallValid heap success out
  · rw [if_pos hv]
    rw [hv.1] at hcall
    have hd : config.externalABI.decode? "isPayable" out = some [.bool (decide (calldataWord out 0 ≠ ⟨0⟩))] := by
      change (ABI.decodeReturnValue? abiBool out).map (fun v => [v]) = _
      rw [decodeReturnBool_valid hv.2.2 hout]
      rfl
    apply ExecBlock.consNormal (ExecStmt.externalCallSuccess (fork := fork) (hperm := by first | exact Or.inl rfl | assumption | exact Or.inr ‹_›) hre (by simp only [evalExpr?, pure]) rfl hcall hd)
    apply allocateBlock_ok (n := 32) (by simp only [evalExpr?, pure]; rfl) hh'
    simpa only [Nat.min_eq_right hv.2.2.1] using hv.2.1
  · rw [if_neg hv]
    cases success with
    | false => exact ExecBlock.consRevert (ExecStmt.externalCallFailure (fork := fork) (hperm := by first | exact Or.inl rfl | assumption | exact Or.inr ‹_›) hre (by simp only [evalExpr?, pure]) rfl hcall)
    | true =>
      by_cases hd : BoolReturnValid out
      · have hdecode : config.externalABI.decode? "isPayable" out = some [.bool (decide (calldataWord out 0 ≠ ⟨0⟩))] := by
          change (ABI.decodeReturnValue? abiBool out).map (fun v => [v]) = _
          rw [decodeReturnBool_valid hd hout]
          rfl
        apply ExecBlock.consNormal (ExecStmt.externalCallSuccess (fork := fork) (hperm := by first | exact Or.inl rfl | assumption | exact Or.inr ‹_›) hre (by simp only [evalExpr?, pure]) rfl hcall hdecode)
        apply allocateBlock_revert (n := 32) (by simp only [evalExpr?, pure]; rfl) hh'
        intro hg
        exact hv ⟨rfl,by simpa only [Nat.min_eq_right hd.1] using hg,hd⟩
      · apply ExecBlock.consRevert (ExecStmt.externalCallReturnDecodeRevert (fork := fork) (hperm := by first | exact Or.inl rfl | assumption | exact Or.inr ‹_›) hre (by simp only [evalExpr?, pure]) rfl hcall ?_)
        change (ABI.decodeReturnValue? abiBool out).map (fun v => [v]) = none
        rw [decodeReturnBool_invalid hd hout]
        rfl

theorem payableProbeLocals_heap (locals : Store) (out : ByteArray) (heap : Nat) :
    (payableProbeLocals locals out heap).get? "$EAS.freeMemory" = some (.int (Int.ofNat (allocateNext heap 32))) := by
  exact store_get_self _ _ _

theorem payableProbeLocals_result (locals : Store) (out : ByteArray) (heap : Nat) :
    (payableProbeLocals locals out heap).get? "payableResult" = some (.bool (decide (calldataWord out 0 ≠ ⟨0⟩))) := by
  rw [payableProbeLocals, allocateBlockLocals_get (by decide) (by decide) (by decide)]
  exact store_get_self _ _ _

end Benchmarks.EAS.EAS
