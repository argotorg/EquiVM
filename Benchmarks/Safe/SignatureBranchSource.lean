import Benchmarks.Safe.SignaturePiece

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

-- LIBRARY CANDIDATE: cast an evaluated bytes32 word to its unsigned integer value.
theorem evalWordBytesAsUint256 {cfg : Config} {f : Frame} {evm : EVM.State}
    {e : Expr} {w : UInt256}
    (he : evalExpr? cfg f evm e = .ok
      (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE w))) :
    evalExpr? cfg f evm (.cast e (.elem (.int (.uint ⟨256, by decide⟩)))) =
      .ok (.int (Int.ofNat w.toNat)) := by
  simp [evalExpr?, he, castValue?, fixedBytesToNat?, fixedBytesValid, fixedBytesSize,
    word_toBytesBE_length_32, fromBytesBE_word, EvalResult.ofOption, EvalResult.bind, bind]

-- LIBRARY CANDIDATE: cast an evaluated nonnegative integer to an address.
theorem evalNatAsAddress {cfg : Config} {f : Frame} {evm : EVM.State}
    {e : Expr} {n : Nat} (he : evalExpr? cfg f evm e = .ok (.int (Int.ofNat n))) :
    evalExpr? cfg f evm (.cast e (.elem .address)) =
      .ok (.address (AccountAddress.ofNat n)) := by
  have hn : ¬(n : Int) < 0 := by omega
  simp [evalExpr?, he, castValue?, Int.ofNat_eq_natCast, hn,
    EvalResult.ofOption, EvalResult.bind, bind]

-- LIBRARY CANDIDATE: assignment to an existing local variable without changing the EVM state.
theorem assignLocalValue {cfg : Config} {f : Frame} {evm : EVM.State}
    {name : Ident} {old : Value} (value : Value) (hl : f.locals[name]? = some old) :
    assignStorageRef? cfg f evm .localVar { base := name } value =
      .ok ({ f with locals := f.locals.insert name value }, evm) := by
  simp [assignStorageRef?, hl, updateLocalPath?, EvalResult.bind, bind, pure]

def signatureCurrentFrame (f : Frame) (r : UInt256) : Frame :=
  signatureSet f "currentOwner" (.address (AccountAddress.ofUInt256 r))

theorem signatureCurrentSource {f : Frame} {evm : EVM.State} {r : UInt256} {old : Value}
    (hr : f.locals["r"]? = some (wordBytes32Value r))
    (hc : f.locals["currentOwner"]? = some old) :
    ExecStmt config f evm
      (.assign .localVar (varRef "currentOwner")
        (uint256AsAddress (bytes32AsUint256 (.var "r"))))
      (.ok (signatureCurrentFrame f r) evm) := by
  apply ExecStmt.assign
  · simpa only [accountAddress_ofUInt256_eq_ofNat_toNat] using
      evalNatAsAddress (evalWordBytesAsUint256 (evalLocalValue hr))
  · simpa only [signatureCurrentFrame, signatureSet, varRef,
      accountAddress_ofUInt256_eq_ofNat_toNat] using
      assignLocalValue (cfg := config) (evm := evm)
        (.address (AccountAddress.ofNat r.toNat)) hc

theorem SignatureCore.current {p : SignatureInput} {f : Frame}
    (hc : SignatureCore p f) (r : UInt256) : SignatureCore p (signatureCurrentFrame f r) :=
  hc.set _ _ (by decide)

theorem SignatureCore.split {p : SignatureInput} {f : Frame}
    (hc : SignatureCore p f) (i : Nat) : SignatureCore p (signatureVFrame f p.signatures i) :=
  (((hc.set _ _ (by decide)).set _ _ (by decide)).set _ _ (by decide)).set _ _ (by decide)

end Benchmarks.Safe
