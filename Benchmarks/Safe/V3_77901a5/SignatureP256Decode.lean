import Benchmarks.Safe.V3_77901a5.SignatureP256Source

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.V3_77901a5

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

def signatureP256ReadFrame (f : Frame) (p : P256Input) : Frame :=
  signatureSet (signatureSet (signatureSet (signatureSet f "r" (wordBytes32Value p.r))
    "s" (wordBytes32Value p.s)) "qx" (uint256Value p.qx)) "qy" (uint256Value p.qy)

def signatureP256SignerFrame (f : Frame) (p : P256Input) : Frame :=
  signatureSet (signatureP256ReadFrame f p) "signerAddress"
    (.address (AccountAddress.ofUInt256 (p256SignerWord p)))

theorem evalP256Signer {f : Frame} {evm : EVM.State} {p : P256Input}
    (hx : f.locals["qx"]? = some (uint256Value p.qx))
    (hy : f.locals["qy"]? = some (uint256Value p.qy)) :
    evalExpr? config f evm
      (uint256AsAddress (bytes32AsUint256 (.keccak256
        (.abiEncodePacked [(uint256, .var "qx"), (uint256, .var "qy")])))) =
      .ok (.address (AccountAddress.ofUInt256 (p256SignerWord p))) := by
  rw [accountAddress_ofUInt256_eq_ofNat_toNat]
  apply evalNatAsAddress (n := (p256SignerWord p).toNat)
  apply evalWordBytesAsUint256
  apply evalKeccakWord
  have hp : evalPackedArgs? config f evm [(uint256, .var "qx"), (uint256, .var "qy")] =
      .ok ([p.qx, p.qy].flatMap EVM.Word.toBytesBE) := by
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    apply evalPackedArgs_cons (evalLocalValue hx) (encodePacked_uint256 _)
    exact evalPackedArgs_single (evalLocalValue hy) (encodePacked_uint256 _)
  rw [evalExpr?, hp]
  simp only [bind, EvalResult.bind, pure, wordBytes_eq_list,
    byteArray_mk_toArray_eq_toByteArray]

theorem signatureP256DecodeSource {p : SignatureInput} {f : Frame} {evm : EVM.State}
    {s : UInt256} {oldR oldS : Value} (hc : SignatureCore p f)
    (hr : f.locals["r"]? = some oldR) (hs : f.locals["s"]? = some oldS)
    (hoff : f.locals["p256Offset"]? = some (uint256Value s))
    (hb : s.toNat + 128 ≤ p.signatures.size) :
    ExecBlock fork config f evm ((signatureP256Body.drop 5).take 5)
      (.ok (signatureP256SignerFrame f (signatureP256Input p s)) evm) := by
  let input := signatureP256Input p s
  let f₁ := signatureSet f "r" (wordBytes32Value input.r)
  let f₂ := signatureSet f₁ "s" (wordBytes32Value input.s)
  let f₃ := signatureSet f₂ "qx" (uint256Value input.qx)
  have hc₁ : SignatureCore p f₁ := hc.set _ _ (by decide)
  have hc₂ : SignatureCore p f₂ := hc₁.set _ _ (by decide)
  have hc₃ : SignatureCore p f₃ := hc₂.set _ _ (by decide)
  have hoff₁ : f₁.locals["p256Offset"]? = some (uint256Value s) := by
    simp [f₁, signatureSet, Std.HashMap.getElem?_insert, hoff]
  have hoff₂ : f₂.locals["p256Offset"]? = some (uint256Value s) := by
    simp [f₂, signatureSet, Std.HashMap.getElem?_insert, hoff₁]
  have hoff₃ : f₃.locals["p256Offset"]? = some (uint256Value s) := by
    simp [f₃, signatureSet, Std.HashMap.getElem?_insert, hoff₂]
  have h₁ : ExecStmt fork config f evm signatureP256Body[5]! (.ok f₁ evm) :=
    .assign (hperm := by first | exact Or.inl rfl | assumption | exact Or.inr ‹_›) (evalSignatureWordAt (evalLocalValue hc.signatures) (evalLocalValue hoff) (by omega))
      (assignLocalValue _ hr)
  have h₂ : ExecStmt fork config f₁ evm signatureP256Body[6]! (.ok f₂ evm) :=
    .assign (hperm := by first | exact Or.inl rfl | assumption | exact Or.inr ‹_›) (evalSignatureWordAt (evalLocalValue hc₁.signatures)
      (naturalAddSource (evalLocalValue hoff₁) (by simp [evalExpr?]; rfl)) (by omega))
      (assignLocalValue _ (old := oldS)
        (by simp [f₁, signatureSet, Std.HashMap.getElem?_insert, hs]))
  have h₃ : ExecStmt fork config f₂ evm signatureP256Body[7]! (.ok f₃ evm) :=
    .letDecl (evalSignatureUintAt (evalLocalValue hc₂.signatures)
      (naturalAddSource (evalLocalValue hoff₂) (by simp [evalExpr?]; rfl)) (by omega))
  have h₄ : ExecStmt fork config f₃ evm signatureP256Body[8]!
      (.ok (signatureP256ReadFrame f input) evm) :=
    .letDecl (evalSignatureUintAt (evalLocalValue hc₃.signatures)
      (naturalAddSource (evalLocalValue hoff₃) (by simp [evalExpr?]; rfl)) (by omega))
  have h₅ : ExecStmt fork config (signatureP256ReadFrame f input) evm signatureP256Body[9]!
      (.ok (signatureP256SignerFrame f input) evm) :=
    .letDecl (evalP256Signer (p := input) (by
      simp [signatureP256ReadFrame, signatureSet, Std.HashMap.getElem?_insert,
        Std.HashMap.getElem_insert]) (by
      simp [signatureP256ReadFrame, signatureSet, Std.HashMap.getElem?_insert,
        Std.HashMap.getElem_insert]))
  exact .consNormal h₁ (.consNormal h₂ (.consNormal h₃ (.consNormal h₄ (.consNormal h₅ .nil))))

theorem SignatureContext.p256Decoded {p : SignatureInput} {f : Frame} {i : Nat} {last : UInt256}
    (hc : SignatureContext p f i last) (r s : UInt256) :
    SignatureContext p
      (signatureP256SignerFrame (signatureP256EndFrame f r s) (signatureP256Input p s)) i last :=
  (((((((hc.current r).set _ _ (by decide)).set _ _ (by decide)).set _ _ (by decide)).set _ _
    (by decide)).set _ _ (by decide)).set _ _ (by decide)).set _ _ (by decide)

theorem evalP256SignerMatches {f : Frame} {evm : EVM.State} {owner signer : UInt256}
    (ho : f.locals["currentOwner"]? = some (.address (AccountAddress.ofUInt256 owner)))
    (hs : f.locals["signerAddress"]? = some (.address (AccountAddress.ofUInt256 signer))) :
    evalExpr? config f evm (eqE (.var "currentOwner") (.var "signerAddress")) =
      .ok (.bool (decide
        (UInt256.land solcAddrMask owner = UInt256.land solcAddrMask signer))) := by
  have hm (w : UInt256) : (UInt256.land solcAddrMask w).toNat < EVM.addressModulus := by
    rw [u256_land_comm]
    exact solcAddrMask_result_canonical w
  apply evalAddressEq (hm owner) (hm signer)
  · rw [evalLocalValue ho, accountAddress_ofUInt256_eq_ofNat_toNat,
      addressOfNat_eq_of_masked_word owner, u256_land_comm owner solcAddrMask]
  · rw [evalLocalValue hs, accountAddress_ofUInt256_eq_ofNat_toNat,
      addressOfNat_eq_of_masked_word signer, u256_land_comm signer solcAddrMask]

end Benchmarks.Safe.V3_77901a5
