import Benchmarks.Safe.SignatureBranchSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

def signatureDynamicFrame (f : Frame) (r s : UInt256) (name : Ident) : Frame :=
  signatureSet (signatureCurrentFrame f r) name (uint256Value s)

def signatureDynamicPrefix (name : Ident) : List Stmt :=
  [ .assign .localVar (varRef "currentOwner")
      (uint256AsAddress (bytes32AsUint256 (.var "r"))),
    .letDecl name (some uint256) (bytes32AsUint256 (.var "s")) ]

theorem signatureDynamicLocals {f : Frame} {evm : EVM.State} {r s : UInt256} {old : Value}
    (name : Ident) (hr : f.locals["r"]? = some (wordBytes32Value r))
    (hs : f.locals["s"]? = some (wordBytes32Value s))
    (ho : f.locals["currentOwner"]? = some old) :
    ExecBlock config f evm (signatureDynamicPrefix name)
      (.ok (signatureDynamicFrame f r s name) evm) := by
  exact .consNormal (signatureCurrentSource hr ho)
    (.consNormal (.letDecl (evalWordBytesAsUint256 (evalLocalValue (by
      simpa only [signatureCurrentFrame, signatureSet, Std.HashMap.getElem?_insert,
        show ("currentOwner" == "s") = false from rfl, if_false] using hs)))) .nil)

theorem evalSignatureOffsetBound {p : SignatureInput} {f : Frame} {evm : EVM.State}
    {r s : UInt256} (name : Ident) (hc : SignatureCore p f) (hn : name ≠ "requiredBytes") :
    evalExpr? config (signatureDynamicFrame f r s name) evm
      (geE (.var name) (.var "requiredBytes")) =
      .ok (.bool (decide (p.requiredBytes ≤ s.toNat))) := by
  apply naturalGeSource
  · exact evalLocalValue (by simp [signatureDynamicFrame, signatureSet,
      Std.HashMap.getElem?_insert])
  · exact evalLocalValue (by simp [signatureDynamicFrame, signatureSet, signatureCurrentFrame,
      Std.HashMap.getElem?_insert, hn, hc.requiredBytes])

end Benchmarks.Safe
