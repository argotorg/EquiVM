import Benchmarks.Safe.WordCallResult
import Benchmarks.Safe.WordArrayMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

structure P256Input where
  h : UInt256
  r : UInt256
  s : UInt256
  qx : UInt256
  qy : UInt256

def p256Words (p : P256Input) : List UInt256 := [p.h, p.r, p.s, p.qx, p.qy]

def p256Args (p : P256Input) : Store :=
  (((((∅ : Store).insert "qy" (.int (Int.ofNat p.qy.toNat))).insert
    "qx" (.int (Int.ofNat p.qx.toNat))).insert "s" (wordBytes32Value p.s)).insert
      "r" (wordBytes32Value p.r)).insert "h" (wordBytes32Value p.h)

def p256Frame (p : P256Input) : Frame := { contract := contract, locals := p256Args p }

def p256FinalFrame (p : P256Input) (z : Bool) (out : ByteArray) : Frame :=
  { p256Frame p with
    locals := ((p256Args p).insert "p256Success" (.bool z)).insert "p256Result" (.bytes out) }

def p256Result (z : Bool) (out : ByteArray) : Bool :=
  z && (decide (out.size = 32) && decide (calldataWord out 0 = ⟨1⟩))

theorem evalP256Payload (evm : EVM.State) (p : P256Input) :
    evalExpr? config (p256Frame p) evm (.abiEncodePacked
      [(bytes32, .var "h"), (bytes32, .var "r"), (bytes32, .var "s"),
        (uint256, .var "qx"), (uint256, .var "qy")]) =
      .ok (.bytes (wordBytes (p256Words p))) := by
  have hp : evalPackedArgs? config (p256Frame p) evm
      [(bytes32, .var "h"), (bytes32, .var "r"), (bytes32, .var "s"),
        (uint256, .var "qx"), (uint256, .var "qy")] =
      .ok ((p256Words p).flatMap EVM.Word.toBytesBE) := by
    have hl {name : Ident} {value : Value} (he : (p256Frame p).locals[name]? = some value) :=
      evalLocalValue (cfg := config) (evm := evm) he
    unfold p256Words
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    apply evalPackedArgs_cons (hl (by
      simp [p256Frame, p256Args, Std.HashMap.getElem_insert])) (encodePacked_bytes32 _)
    apply evalPackedArgs_cons (hl (by
      simp [p256Frame, p256Args, Std.HashMap.getElem_insert])) (encodePacked_bytes32 _)
    apply evalPackedArgs_cons (hl (by
      simp [p256Frame, p256Args, Std.HashMap.getElem_insert])) (encodePacked_bytes32 _)
    apply evalPackedArgs_cons (hl (by
      simp [p256Frame, p256Args, Std.HashMap.getElem_insert])) (encodePacked_uint256 _)
    exact evalPackedArgs_single (hl (by
      simp [p256Frame, p256Args, Std.HashMap.getElem_insert])) (encodePacked_uint256 _)
  rw [evalExpr?, hp]
  simp only [bind, EvalResult.bind, pure, wordBytes_eq_list,
    byteArray_mk_toArray_eq_toByteArray]

theorem evalP256Result (evm : EVM.State) (p : P256Input) (z : Bool) (out : ByteArray) :
    evalExpr? config (p256FinalFrame p z out) evm
      (andE (.var "p256Success") (andE (eqE (localLength "p256Result") (.intLit 32))
        (eqE (.abiDecode uint256 (.var "p256Result")) (.intLit 1)))) =
      .ok (.bool (p256Result z out)) := by
  apply evalWordCallResult
    (by simp [p256FinalFrame, Std.HashMap.getElem_insert])
    (by simp [p256FinalFrame, Std.HashMap.getElem_insert])
  intro ho
  have hd := decodeReturnUint_long (out := out) (by omega) (by rw [ho]; decide)
  change ABI.decodeReturnValueWithMode? config.abiDecodeMode uint256 out = _ at hd
  have he : (Value.int (Int.ofNat (calldataWord out 0).toNat) == Value.int 1) =
      decide (calldataWord out 0 = ⟨1⟩) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, Value.int.injEq, decide_eq_true_eq]
    constructor
    · intro h
      exact uInt256_toNat_eq_one (Int.ofNat.inj h)
    · intro h
      rw [h]
      rfl
  simp only [eqE, evalExpr?, p256FinalFrame, Std.HashMap.get?_eq_getElem?,
    Std.HashMap.getElem?_insert_self, String.reduceEq,
    if_true, EvalResult.ofOption, EvalResult.bind, bind, pure, hd, evalBinaryOp_eq_int_ok, he]

theorem safeP256Source {evm evm' : EVM.State} {p : P256Input} {z : Bool} {out : ByteArray}
    (hc : callViaEVM evm (AccountAddress.ofNat 256) 0 (wordBytes (p256Words p))
      (z, evm', out) false) :
    ExecFuncBody config (p256Frame p) evm p256VerifyFunction.body
      (.returned (p256FinalFrame p z out) evm' (some [.bool (p256Result z out)])) := by
  apply ExecFuncBody.execBlockRet
  refine .consNormal ?_ (.consReturn (.return (evalExprs?_singleton
    (evalP256Result evm' p z out))))
  have ht : evalExpr? config (p256Frame p) evm p256Precompile =
      .ok (.address (AccountAddress.ofNat 256)) := by
    simp [p256Precompile, evalExpr?, castValue?, addrSt, EvalResult.ofOption,
      EvalResult.bind, bind, pure, intToNat?]
  have hv : evalExpr? config (p256Frame p) evm (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  have ha : EVM.address (AccountAddress.ofNat 256) = AccountAddress.ofNat 256 := by
    decide +kernel
  rw [← ha] at hc
  cases z
  · exact .lowLevelCallFailure ht hv (evalP256Payload evm p) hc
  · exact .lowLevelCallSuccess ht hv (evalP256Payload evm p) hc

end Benchmarks.Safe
