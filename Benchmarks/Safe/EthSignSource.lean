import Benchmarks.Safe.EthSignMemory
import Benchmarks.Safe.SignatureRecoverySource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

def ethSignHashExpr : Expr :=
  .keccak256 (.abiEncodePacked [(bytesTy, ethSignPrefix), (bytes32, .var "dataHash")])

def signatureEthFrame (f : Frame) (hash : UInt256) : Frame :=
  signatureSet f "ethSignedHash" (wordBytes32Value (ethSignWord hash))

def signatureEthBody : List Stmt :=
  .letDecl "ethSignedHash" (some bytes32) ethSignHashExpr ::
    signatureRecoverBody (.var "ethSignedHash") (u8 (subE (.var "v") (.intLit 4)))

theorem evalEthSignHash {p : SignatureInput} {f : Frame} {evm : EVM.State}
    (hc : SignatureCore p f) :
    evalExpr? config f evm ethSignHashExpr = .ok (wordBytes32Value (ethSignWord p.hash)) := by
  apply evalKeccakWord
  have hargs : evalPackedArgs? config f evm
      [(bytesTy, ethSignPrefix), (bytes32, .var "dataHash")] =
      .ok (ethSignPrefixBytes.toList ++ EVM.Word.toBytesBE p.hash) := by
    apply evalPackedArgs_cons (v := .bytes ethSignPrefixBytes)
      (by simp [ethSignPrefix, ethSignPrefixBytes, evalExpr?, pure]) (by rfl)
    exact evalPackedArgs_single (evalLocalValue hc.hash) (encodePacked_bytes32 _)
  rw [evalExpr?, hargs]
  simp only [EvalResult.bind, bind, pure, ethSignBytes, byteArray_mk_toArray_eq_toByteArray,
    list_toByteArray_append, byteArray_toList_toByteArray,
    word_toBytesBE_toByteArray_eq_toByteArray]

theorem evalEthSignV {cfg : Config} {f : Frame} {evm : EVM.State} {v : UInt256}
    (hv : f.locals["v"]? = some (uint256Value v)) (hl : 4 ≤ v.toNat) (hh : v.toNat < 256) :
    evalExpr? cfg f evm (u8 (subE (.var "v") (.intLit 4))) =
      .ok (uint256Value (UInt256.sub v ⟨4⟩)) := by
  have hn : ¬(Int.ofNat v.toNat - 4) < 0 := by simp only [Int.ofNat_eq_natCast]; omega
  have hb : ¬(Int.ofNat v.toNat - 4) ≥ 256 := by simp only [Int.ofNat_eq_natCast]; omega
  have he : evalExpr? cfg f evm (subE (.var "v") (.intLit 4)) =
      .ok (.int (Int.ofNat v.toNat - 4)) := by
    rw [subE, evalExpr_binary_nonshort (by decide) (by decide), evalLocalValue hv]
    simp [evalExpr?, uint256Value, evalBinaryOp?, EvalResult.bind, bind, pure]
  simp only [u8, evalExpr?, he, uint8Int, EvalResult.bind, bind]
  simp only [show 2 ^ (8 : Nat) = (256 : Int) from rfl, hn, hb, decide_false,
    Bool.false_or, Bool.false_eq_true, if_false, pure]
  rw [uint256Value, usub_toNat (a := v) (b := ⟨4⟩) hl]
  simp [Int.ofNat_eq_natCast, Int.ofNat_sub hl]
  change (v.toNat : Int) - 4 = ((v.toNat - 4 : Nat) : Int)
  omega

theorem signatureEthSource {p : SignatureInput} {f : Frame} {evm evm' : EVM.State}
    {r s v owner : UInt256} {old : Value} {f' : Frame} (hc : SignatureCore p f)
    (hr : f.locals["r"]? = some (wordBytes32Value r))
    (hs : f.locals["s"]? = some (wordBytes32Value s))
    (hv : f.locals["v"]? = some (uint256Value v)) (ho : f.locals["currentOwner"]? = some old)
    (hl : 4 ≤ v.toNat) (hh : v.toNat < 256)
    (hbody : ExecFuncBody config (ecrecoverFrame ⟨ethSignWord p.hash, UInt256.sub v ⟨4⟩, r, s⟩)
      evm ecrecoverAddressFunction.body
      (.returned f' evm' (some [.address (AccountAddress.ofUInt256 owner)]))) :
    ExecBlock config f evm signatureEthBody
      (.ok (signatureRecoveredFrame (signatureEthFrame f p.hash) owner) evm') := by
  have hc' : SignatureCore p (signatureEthFrame f p.hash) := hc.set _ _ (by decide)
  apply ExecBlock.consNormal (.letDecl (evalEthSignHash hc))
  apply signatureRecoverSource (old := old) hc' _ _ _ _ _ hbody
  · exact evalLocalValue (by simp [signatureEthFrame, signatureSet, Std.HashMap.getElem?_insert])
  · exact evalEthSignV (by
      simp [signatureEthFrame, signatureSet, Std.HashMap.getElem?_insert, hv]) hl hh
  all_goals simp [signatureEthFrame, signatureSet, Std.HashMap.getElem?_insert, hr, hs, ho]

theorem signatureEthSourceRejected {p : SignatureInput} {f : Frame} {evm : EVM.State}
    {r s v : UInt256} (hc : SignatureCore p f)
    (hr : f.locals["r"]? = some (wordBytes32Value r))
    (hs : f.locals["s"]? = some (wordBytes32Value s))
    (hv : f.locals["v"]? = some (uint256Value v)) (hl : 4 ≤ v.toNat) (hh : v.toNat < 256)
    (hbody : ExecFuncBody config (ecrecoverFrame ⟨ethSignWord p.hash, UInt256.sub v ⟨4⟩, r, s⟩)
      evm ecrecoverAddressFunction.body .reverted) :
    ExecBlock config f evm signatureEthBody .reverted := by
  have hc' : SignatureCore p (signatureEthFrame f p.hash) := hc.set _ _ (by decide)
  apply ExecBlock.consNormal (.letDecl (evalEthSignHash hc))
  apply signatureRecoverSourceRejected hc' _ _ _ _ hbody
  · exact evalLocalValue (by simp [signatureEthFrame, signatureSet, Std.HashMap.getElem?_insert])
  · exact evalEthSignV (by
      simp [signatureEthFrame, signatureSet, Std.HashMap.getElem?_insert, hv]) hl hh
  all_goals simp [signatureEthFrame, signatureSet, Std.HashMap.getElem?_insert, hr, hs]

end Benchmarks.Safe
