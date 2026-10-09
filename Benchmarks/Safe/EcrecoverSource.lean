import Benchmarks.Safe.EcrecoverOutput
import Benchmarks.Safe.AddressReturnDecoder
import Benchmarks.Safe.WordArrayMemory
import Benchmarks.Safe.LocalArrays

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

structure EcrecoverInput where
  digest : UInt256
  v : UInt256
  r : UInt256
  s : UInt256

def ecrecoverWords (p : EcrecoverInput) : List UInt256 := [p.digest, p.v, p.r, p.s]

def ecrecoverArgs (p : EcrecoverInput) : Store :=
  ((((∅ : Store).insert "s" (wordBytes32Value p.s)).insert "r" (wordBytes32Value p.r)).insert
    "v" (uint256Value p.v)).insert "digest" (wordBytes32Value p.digest)

def ecrecoverFrame (p : EcrecoverInput) : Frame :=
  { contract := contract, locals := ecrecoverArgs p }

def ecrecoverFinalFrame (p : EcrecoverInput) (z : Bool) (out : ByteArray) : Frame :=
  { ecrecoverFrame p with
    locals := ((ecrecoverArgs p).insert "ecrecoverSuccess" (.bool z)).insert
      "ecrecoverData" (.bytes out) }

theorem evalEcrecoverPayload (evm : EVM.State) (p : EcrecoverInput) :
    evalExpr? config (ecrecoverFrame p) evm ecrecoverCalldataExpr =
      .ok (.bytes (wordBytes (ecrecoverWords p))) := by
  have hp : evalPackedArgs? config (ecrecoverFrame p) evm
      [(bytes32, .var "digest"), (uint256, .var "v"), (bytes32, .var "r"),
        (bytes32, .var "s")] = .ok ((ecrecoverWords p).flatMap EVM.Word.toBytesBE) := by
    have hl {name : Ident} {value : Value} (he : (ecrecoverFrame p).locals[name]? = some value) :=
      evalLocalValue (cfg := config) (evm := evm) he
    unfold ecrecoverWords
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    apply evalPackedArgs_cons (hl (by
      simp [ecrecoverFrame, ecrecoverArgs, Std.HashMap.getElem_insert])) (encodePacked_bytes32 _)
    apply evalPackedArgs_cons (hl (by
      simp [ecrecoverFrame, ecrecoverArgs, Std.HashMap.getElem_insert])) (encodePacked_uint256 _)
    apply evalPackedArgs_cons (hl (by
      simp [ecrecoverFrame, ecrecoverArgs, Std.HashMap.getElem_insert])) (encodePacked_bytes32 _)
    exact evalPackedArgs_single (hl (by
      simp [ecrecoverFrame, ecrecoverArgs, Std.HashMap.getElem_insert])) (encodePacked_bytes32 _)
  rw [ecrecoverCalldataExpr, evalExpr?, hp]
  simp only [bind, EvalResult.bind, pure, wordBytes_eq_list,
    byteArray_mk_toArray_eq_toByteArray]

theorem evalEcrecoverReturn (evm : EVM.State) (p : EcrecoverInput) (z : Bool) (out : ByteArray)
    (ho : EcrecoverOutput out) :
    evalExpr? config (ecrecoverFinalFrame p z out) evm
      (.ite (eqE (localLength "ecrecoverData") (.intLit 0)) zeroAddr
        (.abiDecode addr (.var "ecrecoverData"))) =
      .ok (.address (AccountAddress.ofUInt256 (calldataWord out 0))) := by
  have hl := evalLocalBytesLength (cfg := config) (evm := evm)
    (frame := ecrecoverFinalFrame p z out) (name := "ecrecoverData") (bytes := out)
    (by simp [ecrecoverFinalFrame, Std.HashMap.getElem_insert])
  have hd := evalLocalValue (cfg := config) (evm := evm)
    (frame := ecrecoverFinalFrame p z out) (name := "ecrecoverData") (value := .bytes out)
    (by simp [ecrecoverFinalFrame, Std.HashMap.getElem_insert])
  change evalExpr? config (ecrecoverFinalFrame p z out) evm (localLength "ecrecoverData") = _
    at hl
  have he : evalExpr? config (ecrecoverFinalFrame p z out) evm
      (eqE (localLength "ecrecoverData") (.intLit 0)) =
      .ok (.bool (decide (out.size = 0))) := by
    rw [eqE, evalExpr?, hl] <;>
      simp [evalExpr?, EvalResult.bind, bind, evalBinaryOp_eq_int_ok,
        Int.ofNat_eq_natCast, pure]
    apply Bool.eq_iff_iff.mpr
    simp [beq_iff_eq, Value.int.injEq]
  rw [evalExpr?, he]
  rcases ho with rfl | ⟨h32, hc⟩
  · simp [ByteArray.size_empty, zeroAddr, evalExpr?, castValue?, addrSt,
      EvalResult.ofOption, EvalResult.bind, bind, pure, intToNat?]
    decide +kernel
  · have hdecode := decodeReturnAddressLong (by omega : 32 ≤ out.size)
      (by rw [h32]; decide) hc
    change ABI.decodeReturnValueWithMode? config.abiDecodeMode addr out = _ at hdecode
    simp only [h32, Nat.reduceEqDiff, decide_false, bind, EvalResult.bind]
    rw [evalExpr?, hd]
    simp only [bind, EvalResult.bind, hdecode, pure,
      accountAddress_ofUInt256_eq_ofNat_toNat]

theorem safeEcrecoverSource {evm evm' : EVM.State} {p : EcrecoverInput} {z : Bool} {out : ByteArray}
    (hc : callViaEVM evm (AccountAddress.ofNat 1) 0 (wordBytes (ecrecoverWords p))
      (z, evm', out) false) :
    ExecFuncBody config (ecrecoverFrame p) evm ecrecoverAddressFunction.body
      (if z then .returned (ecrecoverFinalFrame p true out) evm'
        (some [.address (AccountAddress.ofUInt256 (calldataWord out 0))]) else .reverted) := by
  have ht : evalExpr? config (ecrecoverFrame p) evm ecrecoverPrecompile =
      .ok (.address (AccountAddress.ofNat 1)) := by
    simp [ecrecoverPrecompile, evalExpr?, castValue?, addrSt, EvalResult.ofOption,
      EvalResult.bind, bind, pure, intToNat?]
  have hv : evalExpr? config (ecrecoverFrame p) evm (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hs : evalExpr? config (ecrecoverFinalFrame p z out) evm' (.var "ecrecoverSuccess") =
      .ok (.bool z) := evalLocalValue (by
    simp [ecrecoverFinalFrame, Std.HashMap.getElem_insert])
  have hc' : callViaEVM evm (EVM.address (AccountAddress.ofNat 1)) 0
      (wordBytes (ecrecoverWords p)) (z, evm', out) false := by
    simpa only [addressOfAddress] using hc
  cases z
  · apply ExecFuncBody.execBlockRevert
    exact .consNormal (.lowLevelCallFailure ht hv (evalEcrecoverPayload evm p) hc')
      (.consRevert (.requireFalse hs))
  · apply ExecFuncBody.execBlockRet
    exact .consNormal (.lowLevelCallSuccess ht hv (evalEcrecoverPayload evm p) hc')
      (.consNormal (.requireTrue hs) (.consReturn (.return (evalExprs?_singleton
        (evalEcrecoverReturn evm' p true out (callEcrecoverOutput hc))))))

end Benchmarks.Safe
