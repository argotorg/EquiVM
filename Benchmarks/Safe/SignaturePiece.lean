import Benchmarks.Safe.SignatureInput
import Benchmarks.Safe.ByteAtMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

-- LIBRARY CANDIDATE: unbounded natural multiplication in a Solm expression.
theorem naturalMulSource {cfg frame evm lhs rhs} {a b : Nat}
    (ha : evalExpr? cfg frame evm lhs = .ok (.int (Int.ofNat a)))
    (hb : evalExpr? cfg frame evm rhs = .ok (.int (Int.ofNat b))) :
    evalExpr? cfg frame evm (.binary .mul lhs rhs) = .ok (.int (Int.ofNat (a * b))) := by
  simp only [evalExpr?, ha, hb, EvalResult.bind, bind, evalBinaryOp?]
  simp [Int.ofNat_eq_natCast, pure]

def signatureR (bytes : ByteArray) (i : Nat) : UInt256 := calldataWord bytes (65 * i)

def signatureS (bytes : ByteArray) (i : Nat) : UInt256 := calldataWord bytes (65 * i + 32)

def signatureVNat (bytes : ByteArray) (i : Nat) : Nat :=
  fromByteArrayBigEndian (bytes.extract (65 * i + 64) (65 * i + 65))

def signatureV (bytes : ByteArray) (i : Nat) : UInt256 := UInt256.ofNat (signatureVNat bytes i)

theorem signatureVNat_bound (bytes : ByteArray) (i : Nat) : signatureVNat bytes i < 256 := by
  have hb := fromByteArrayBigEndian_lt (bytes.extract (65 * i + 64) (65 * i + 65))
  have hs : (bytes.extract (65 * i + 64) (65 * i + 65)).size ≤ 1 := by
    rw [ByteArray.size_extract]
    omega
  have hp : 2 ^ (8 * (bytes.extract (65 * i + 64) (65 * i + 65)).size) ≤ 256 := by
    calc _ ≤ 2 ^ (8 * 1) := Nat.pow_le_pow_right (by decide) (by omega)
         _ = 256 := by decide
  exact lt_of_lt_of_le hb hp

theorem signatureV_toNat (bytes : ByteArray) (i : Nat) :
    (signatureV bytes i).toNat = signatureVNat bytes i :=
  ulit_toNat' _ (lt_trans (signatureVNat_bound bytes i) (by decide))

def signatureSet (f : Frame) (name : Ident) (value : Value) : Frame :=
  { f with locals := f.locals.insert name value }

structure SignatureCore (p : SignatureInput) (f : Frame) : Prop where
  contract : f.contract = Benchmarks.Safe.contract
  immutables : f.immutables = ∅
  executor : f.locals["executor"]? = some (.address p.executor)
  hash : f.locals["dataHash"]? = some (wordBytes32Value p.hash)
  signatures : f.locals["signatures"]? = some (.bytes p.signatures)
  required : f.locals["requiredSignatures"]? = some (uint256Value p.required)
  requiredBytes : f.locals["requiredBytes"]? = some (.int (Int.ofNat p.requiredBytes))
  owners : f.locals["owners"]? = none
  approvedHashes : f.locals["approvedHashes"]? = none

theorem SignatureCore.set {p : SignatureInput} {f : Frame} (h : SignatureCore p f)
    (name : Ident) (value : Value)
    (hn : name ∉ ["executor", "dataHash", "signatures", "requiredSignatures", "requiredBytes",
      "owners", "approvedHashes"]) :
    SignatureCore p (signatureSet f name value) := by
  rcases h with ⟨hc, hi, he, hh, hs, hr, hb, ho, ha⟩
  simp only [List.mem_cons, List.mem_singleton, not_or] at hn
  constructor
  · exact hc
  · exact hi
  all_goals simp [signatureSet, Std.HashMap.getElem?_insert, hn, he, hh, hs, hr, hb, ho, ha]

theorem SignatureCore.initial (p : SignatureInput) : SignatureCore p p.loopFrame := by
  constructor <;> simp [SignatureInput.loopFrame, SignatureInput.requiredFrame,
    SignatureInput.frame, SignatureInput.args, Std.HashMap.getElem_insert]

def signatureOffsetFrame (f : Frame) (i : Nat) : Frame :=
  signatureSet f "signatureOffset" (.int (Int.ofNat (65 * i)))

def signatureRFrame (f : Frame) (bytes : ByteArray) (i : Nat) : Frame :=
  signatureSet (signatureOffsetFrame f i) "r" (wordBytes32Value (signatureR bytes i))

def signatureSFrame (f : Frame) (bytes : ByteArray) (i : Nat) : Frame :=
  signatureSet (signatureRFrame f bytes i) "s" (wordBytes32Value (signatureS bytes i))

def signatureVFrame (f : Frame) (bytes : ByteArray) (i : Nat) : Frame :=
  signatureSet (signatureSFrame f bytes i) "v" (uint256Value (signatureV bytes i))

theorem signatureSplitSource {p : SignatureInput} {f : Frame} {evm : EVM.State} {i : Nat}
    (hc : SignatureCore p f) (hi : f.locals["i"]? = some (.int (Int.ofNat i)))
    (hin : 65 * i + 65 ≤ p.signatures.size) :
    ExecBlock config f evm (signatureLoopBody.take 4)
      (.ok (signatureVFrame f p.signatures i) evm) := by
  have hoff : evalExpr? config f evm signatureOffsetExpr =
      .ok (.int (Int.ofNat (65 * i))) := by
    apply naturalMulSource (a := 65) (b := i)
    · simp [evalExpr?, pure]
    · exact evalLocalValue hi
  have hsig {g : Frame} (hg : SignatureCore p g) :
      evalExpr? config g evm (.var "signatures") = .ok (.bytes p.signatures) :=
    evalLocalValue hg.signatures
  have h₁ := hc.set "signatureOffset" (.int (Int.ofNat (65 * i))) (by decide)
  have h₂ := h₁.set "r" (wordBytes32Value (signatureR p.signatures i)) (by decide)
  have h₃ := h₂.set "s" (wordBytes32Value (signatureS p.signatures i)) (by decide)
  have ho {g : Frame} (hh : g.locals["signatureOffset"]? =
      some (.int (Int.ofNat (65 * i)))) :
      evalExpr? config g evm (.var "signatureOffset") = .ok (.int (Int.ofNat (65 * i))) :=
    evalLocalValue hh
  have hr := evalSignatureWordAt (hsig h₁) (ho (by simp [signatureSet,
    Std.HashMap.getElem_insert])) (by omega : 65 * i + 32 ≤ p.signatures.size)
  have hs := evalSignatureWordAt (hsig h₂) (naturalAddSource
    (ho (by simp [signatureSet, Std.HashMap.getElem_insert])) (b := 32)
    (rhs := .intLit 32) (by simp [evalExpr?, pure]))
    (by omega : 65 * i + 32 + 32 ≤ p.signatures.size)
  have hv := evalSignatureByteAt (hsig h₃) (naturalAddSource
    (ho (by simp [signatureSet, Std.HashMap.getElem_insert])) (b := 64)
    (rhs := .intLit 64) (by simp [evalExpr?, pure]))
    (by omega : 65 * i + 64 < p.signatures.size)
  have hv' : evalExpr? config (signatureSFrame f p.signatures i) evm
      (signatureByteAt (.var "signatures") (addE (.var "signatureOffset") (.intLit 64))) =
      .ok (uint256Value (signatureV p.signatures i)) := by
    simpa only [uint256Value, signatureV_toNat, signatureVNat, Nat.add_assoc] using hv
  exact .consNormal (.letDecl hoff) (.consNormal (.letDecl hr)
    (.consNormal (.letDecl hs) (.consNormal (.letDecl hv') .nil)))

end Benchmarks.Safe
