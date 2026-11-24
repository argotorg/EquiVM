import Benchmarks.Safe.V3_77901a5.EcrecoverSource
import Benchmarks.Safe.V3_77901a5.WordCallResult

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.V3_77901a5

structure P256Input where
  hash : UInt256
  r : UInt256
  s : UInt256
  qx : UInt256
  qy : UInt256

namespace P256Input

def words (p : P256Input) : List UInt256 := [p.hash, p.r, p.s, p.qx, p.qy]

def args (p : P256Input) : Store :=
  (((((∅ : Store).insert "qy" (uint256Value p.qy)).insert "qx" (uint256Value p.qx)).insert
    "s" (wordBytes32Value p.s)).insert "r" (wordBytes32Value p.r)).insert
    "h" (wordBytes32Value p.hash)

def frame (p : P256Input) : Frame := { contract := contract, locals := p.args }

def finalFrame (p : P256Input) (z : Bool) (out : ByteArray) : Frame :=
  { p.frame with locals := (p.args.insert "p256Success" (.bool z)).insert "p256Data" (.bytes out) }

end P256Input

def p256Result (z : Bool) (out : ByteArray) : Bool :=
  z && (decide (out.size = 32) && decide (calldataWord out 0 = ⟨1⟩))

theorem evalP256Payload (evm : EVM.State) (p : P256Input) :
    evalExpr? config p.frame evm p256CalldataExpr = .ok (.bytes (wordBytes p.words)) := by
  have hp : evalPackedArgs? config p.frame evm
      [(bytes32, .var "h"), (bytes32, .var "r"), (bytes32, .var "s"),
        (uint256, .var "qx"), (uint256, .var "qy")] =
      .ok (p.words.flatMap EVM.Word.toBytesBE) := by
    have hl {name : Ident} {value : Value} (he : p.frame.locals[name]? = some value) :=
      evalLocalValue (cfg := config) (evm := evm) he
    unfold P256Input.words
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    apply evalPackedArgs_cons (hl (by
      simp [P256Input.frame, P256Input.args, Std.HashMap.getElem_insert])) (encodePacked_bytes32 _)
    apply evalPackedArgs_cons (hl (by
      simp [P256Input.frame, P256Input.args, Std.HashMap.getElem_insert])) (encodePacked_bytes32 _)
    apply evalPackedArgs_cons (hl (by
      simp [P256Input.frame, P256Input.args, Std.HashMap.getElem_insert])) (encodePacked_bytes32 _)
    apply evalPackedArgs_cons (hl (by
      simp [P256Input.frame, P256Input.args, Std.HashMap.getElem_insert])) (encodePacked_uint256 _)
    exact evalPackedArgs_single (hl (by
      simp [P256Input.frame, P256Input.args, Std.HashMap.getElem_insert])) (encodePacked_uint256 _)
  rw [p256CalldataExpr, evalExpr?, hp]
  simp only [bind, EvalResult.bind, pure, wordBytes_eq_list,
    byteArray_mk_toArray_eq_toByteArray]

theorem evalP256Result (p : P256Input) (evm : EVM.State) (z : Bool) (out : ByteArray) :
    evalExpr? config (p.finalFrame z out) evm
      (andE (.var "p256Success")
        (andE (eqE (localLength "p256Data") (.intLit 32))
          (eqE (.abiDecode uint256 (.var "p256Data")) (.intLit 1)))) =
      .ok (.bool (p256Result z out)) := by
  have hsuccess : (p.finalFrame z out).locals["p256Success"]? = some (.bool z) := by
    simp [P256Input.finalFrame, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert]
  have hdata : (p.finalFrame z out).locals["p256Data"]? = some (.bytes out) := by
    simp [P256Input.finalFrame, Std.HashMap.getElem?_insert]
  apply evalWordCallResult hsuccess hdata
  intro hs
  have hd := decodeReturnUint_long (out := out) (by omega) (by rw [hs]; decide)
  change config.externalABI.decodeValue? uint256 out = _ at hd
  have heq : (Value.int (Int.ofNat (calldataWord out 0).toNat) == Value.int 1) =
      decide (calldataWord out 0 = ⟨1⟩) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, Value.int.injEq, decide_eq_true_eq]
    constructor
    · intro h
      apply u256_inj
      exact Int.ofNat.inj h
    · intro h
      rw [h]
      rfl
  simp only [Int.ofNat_eq_natCast] at heq
  simp [evalExpr?, eqE, hdata, EvalResult.ofOption, EvalResult.bind, bind, pure, hd, heq,
    evalBinaryOp_eq_int_ok]

theorem safeP256Source {evm evm' : EVM.State} {p : P256Input} {z : Bool} {out : ByteArray}
    (hc : callViaEVM fork evm (AccountAddress.ofNat 256) 0 (wordBytes p.words)
      (z, evm', out) false) :
    ExecFuncBody fork config p.frame evm p256VerifyFunction.body
      (.returned (p.finalFrame z out) evm' (some [.bool (p256Result z out)])) := by
  apply ExecFuncBody.execBlockRet
  refine .consNormal ?_ (.consReturn (.return
    (evalExprs?_singleton (evalP256Result p evm' z out))))
  have ht : evalExpr? config p.frame evm p256Precompile =
      .ok (.address (AccountAddress.ofNat 256)) := by
    simp [p256Precompile, evalExpr?, castValue?, addrSt, EvalResult.ofOption,
      EvalResult.bind, bind, pure, intToNat?]
  have hv : evalExpr? config p.frame evm (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hc' : callViaEVM fork evm (EVM.address (AccountAddress.ofNat 256)) 0
      (wordBytes p.words) (z, evm', out) false := by
    simpa only [addressOfAddress] using hc
  cases z
  · exact .lowLevelCallFailure (hperm := by first | exact Or.inl rfl | assumption | exact Or.inr ‹_›) ht hv (evalP256Payload evm p) hc'
  · exact .lowLevelCallSuccess (hperm := by first | exact Or.inl rfl | assumption | exact Or.inr ‹_›) ht hv (evalP256Payload evm p) hc'

end Benchmarks.Safe.V3_77901a5
