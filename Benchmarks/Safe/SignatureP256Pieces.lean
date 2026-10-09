import Benchmarks.Safe.SignatureP256BoundsSource
import Benchmarks.Safe.P256Source
import Benchmarks.Safe.Hashes

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

set_option maxRecDepth 100000

def signatureP256Input (p : SignatureInput) (off : UInt256) : P256Input :=
  ⟨p.hash, calldataWord p.signatures off.toNat, calldataWord p.signatures (off.toNat + 32),
    calldataWord p.signatures (off.toNat + 64), calldataWord p.signatures (off.toNat + 96)⟩

def signatureP256RFrame (f : Frame) (p : P256Input) : Frame :=
  signatureSet f "p256r" (wordBytes32Value p.r)

def signatureP256SFrame (f : Frame) (p : P256Input) : Frame :=
  signatureSet (signatureP256RFrame f p) "p256s" (wordBytes32Value p.s)

def signatureP256XFrame (f : Frame) (p : P256Input) : Frame :=
  signatureSet (signatureP256SFrame f p) "qx" (uint256Value p.qx)

def signatureP256WordsFrame (f : Frame) (p : P256Input) : Frame :=
  signatureSet (signatureP256XFrame f p) "qy" (uint256Value p.qy)

def signatureP256Signer (p : P256Input) : UInt256 :=
  uInt256OfByteArray (KEC (wordBytes [p.qx, p.qy]))

def signatureP256SignerFrame (f : Frame) (p : P256Input) : Frame :=
  signatureSet (signatureP256WordsFrame f p) "signerAddress"
    (.address (AccountAddress.ofUInt256 (signatureP256Signer p)))

theorem SignatureCore.p256Words {p : SignatureInput} {f : Frame}
    (hc : SignatureCore p f) (q : P256Input) : SignatureCore p (signatureP256WordsFrame f q) :=
  (((hc.set _ _ (by decide)).set _ _ (by decide)).set _ _ (by decide)).set _ _ (by decide)

theorem SignatureCore.p256Signer {p : SignatureInput} {f : Frame}
    (hc : SignatureCore p f) (q : P256Input) : SignatureCore p (signatureP256SignerFrame f q) :=
  (hc.p256Words q).set _ _ (by decide)

theorem signatureP256PiecesSource {p : SignatureInput} {f : Frame} {evm : EVM.State}
    {off : UInt256} (hc : SignatureCore p f)
    (hoff : f.locals["p256Offset"]? = some (uint256Value off))
    (hb : off.toNat + 128 ≤ p.signatures.size) :
    ExecBlock config f evm ((signatureP256Body.drop 5).take 4)
      (.ok (signatureP256WordsFrame f (signatureP256Input p off)) evm) := by
  let q := signatureP256Input p off
  have hc₁ := hc.set "p256r" (wordBytes32Value q.r) (by decide)
  have hc₂ := hc₁.set "p256s" (wordBytes32Value q.s) (by decide)
  have hc₃ := hc₂.set "qx" (uint256Value q.qx) (by decide)
  have hsig {g : Frame} (hg : SignatureCore p g) :
      evalExpr? config g evm (.var "signatures") = .ok (.bytes p.signatures) :=
    evalLocalValue hg.signatures
  have hread {g : Frame} (hg : g.locals["p256Offset"]? = some (uint256Value off)) :
      evalExpr? config g evm (.var "p256Offset") = .ok (uint256Value off) := evalLocalValue hg
  have hr := evalSignatureWordAt (hsig hc) (hread hoff) (by omega : off.toNat + 32 ≤ _)
  have hs := evalSignatureWordAt (hsig hc₁) (naturalAddSource
    (hread (by simp [signatureSet, Std.HashMap.getElem?_insert, hoff])) (rhs := .intLit 32)
    (b := 32) (by simp [evalExpr?, pure])) (by omega : off.toNat + 32 + 32 ≤ _)
  have hx := evalSignatureUintAt (hsig hc₂) (naturalAddSource
    (hread (by simp [signatureSet, Std.HashMap.getElem?_insert, hoff])) (rhs := .intLit 64)
    (b := 64) (by simp [evalExpr?, pure])) (by omega : off.toNat + 64 + 32 ≤ _)
  have hy := evalSignatureUintAt (hsig hc₃) (naturalAddSource
    (hread (by simp [signatureSet, Std.HashMap.getElem?_insert, hoff])) (rhs := .intLit 96)
    (b := 96) (by simp [evalExpr?, pure])) (by omega : off.toNat + 96 + 32 ≤ _)
  exact .consNormal (.letDecl hr) (.consNormal (.letDecl hs)
    (.consNormal (.letDecl hx) (.consNormal (.letDecl hy) .nil)))

theorem evalSignatureP256Signer {f : Frame} {evm : EVM.State} {p : P256Input}
    (hx : f.locals["qx"]? = some (uint256Value p.qx))
    (hy : f.locals["qy"]? = some (uint256Value p.qy)) :
    evalExpr? config f evm
      (uint256AsAddress (bytes32AsUint256
        (.keccak256 (.abiEncodePacked [(uint256, .var "qx"), (uint256, .var "qy")])))) =
      .ok (.address (AccountAddress.ofUInt256 (signatureP256Signer p))) := by
  have hargs := evalPackedArgs_cons (evalLocalValue (cfg := config) (evm := evm) hx)
    (encodePacked_uint256 p.qx)
    (evalPackedArgs_single (evalLocalValue hy) (encodePacked_uint256 p.qy))
  change evalPackedArgs? config f evm [(uint256, .var "qx"), (uint256, .var "qy")] = _ at hargs
  have hpacked : evalExpr? config f evm
      (.abiEncodePacked [(uint256, .var "qx"), (uint256, .var "qy")]) =
      .ok (.bytes (wordBytes [p.qx, p.qy])) := by
    rw [evalExpr?, hargs]
    simp only [EvalResult.bind, bind, pure, wordBytes_eq_list,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, byteArray_mk_toArray_eq_toByteArray]
  simpa only [accountAddress_ofUInt256_eq_ofNat_toNat] using
    evalNatAsAddress (evalWordBytesAsUint256 (evalKeccakWord hpacked))

theorem signatureP256SignerSource (f : Frame) (evm : EVM.State) (p : P256Input) :
    ExecStmt config (signatureP256WordsFrame f p) evm signatureP256Body[9]!
      (.ok (signatureP256SignerFrame f p) evm) :=
  .letDecl (evalSignatureP256Signer (by
    simp [signatureP256WordsFrame, signatureP256XFrame, signatureSet,
      Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert]) (by
    simp [signatureP256WordsFrame, signatureSet, Std.HashMap.getElem?_insert]))

end Benchmarks.Safe
