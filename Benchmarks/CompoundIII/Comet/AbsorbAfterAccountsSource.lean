import Benchmarks.CompoundIII.Comet.AbsorbPointsSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def absorbAfterAccountsBlock : List Stmt :=
  .letGas "endGas" ::
    .letDecl "gasUsed" (some (.elem (.int (.uint ⟨256, by decide⟩))))
      (.inRange (.uint ⟨256, by decide⟩) (.binary .sub (.var "startGas") (.var "endGas"))) ::
    absorbPointsBlock

theorem absorbAfterAccounts_source (frame : Frame) (evm : State) (addr : AccountAddress)
    (n startGas endGas : UInt256) (accounts : List Value) (hc : frame.contract = contract)
    (ha : frame.locals.get? "absorber" = some (.address addr))
    (hac : frame.locals.get? "accounts" = some (.array accounts))
    (hg : frame.locals.get? "startGas" = some (.int startGas.toNat))
    (hp : frame.locals.get? "liquidatorPoints" = none)
    (hlen : accounts.length = n.toNat) (hn : n.toNat < 2^64) :
    internalBlockResult config frame evm absorbAfterAccountsBlock
      (absorbAfterAccountsOutcome evm addr n startGas endGas) := by
  let f1 : Frame := { frame with locals := frame.locals.insert "endGas" (.int endGas.toNat) }
  let f2 : Frame :=
    { f1 with locals := f1.locals.insert "gasUsed" (.int (UInt256.sub startGas endGas).toNat) }
  have hstart : evalExpr? config f1 evm (.var "startGas") = .ok (.int startGas.toNat) := by
    have hg1 : f1.locals.get? "startGas" = some (.int startGas.toNat) := by
      simpa only [f1, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using hg
    simp only [evalExpr?, hg1, EvalResult.ofOption]
  have hend : evalExpr? config f1 evm (.var "endGas") = .ok (.int endGas.toNat) := by
    simp only [evalExpr?, f1, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      EvalResult.ofOption]
    rfl
  by_cases hle : endGas.toNat ≤ startGas.toNat
  · rw [absorbAfterAccountsOutcome, if_pos hle]
    have hsub := checkedNarrowSubSourceOk ⟨256, by decide⟩ hstart hend startGas.val.isLt hle
    have ha2 : f2.locals.get? "absorber" = some (.address addr) := by
      simpa only [f2, f1, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using ha
    have hac2 : f2.locals.get? "accounts" = some (.array accounts) := by
      simpa only [f2, f1, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using hac
    have hp2 : f2.locals.get? "liquidatorPoints" = none := by
      simpa only [f2, f1, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using hp
    have hg2 : f2.locals.get? "gasUsed" = some (.int (UInt256.sub startGas endGas).toNat) := by
      simp only [f2, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
      rfl
    exact ((absorbPoints_source f2 evm addr n (UInt256.sub startGas endGas) accounts
      hc ha2 hac2 hg2 hp2 hlen hn).prepend (ExecStmt.letDecl hsub)).prepend (ExecStmt.letGas endGas)
  · rw [absorbAfterAccountsOutcome, if_neg hle]
    exact ExecBlock.consNormal (ExecStmt.letGas endGas) (ExecBlock.consRevert
      (ExecStmt.letDeclRevert (checkedNarrowSubSourceUnderflow ⟨256, by decide⟩
        hstart hend (Nat.lt_of_not_ge hle))))

end Benchmarks.CompoundIII.Comet
