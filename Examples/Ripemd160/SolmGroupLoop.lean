import Examples.Ripemd160.SolmGroupBody

/-!
# RIPEMD-160 Solm compression-line loops

The five authored groups on each parallel line reduce to the pure runtime line functions.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Ripemd160

def leftGroupInit : List Stmt := [.letDecl "groupL" uint256Ty (.intLit 0)]
def leftGroupCond : Expr := .binary .lt (.var "groupL") (.intLit 5)
def leftGroupPost : List Stmt :=
  [.assign .localVar { base := "groupL" } (.binary .add (.var "groupL") (.intLit 1))]
def leftGroupFor : Stmt := .for leftGroupInit leftGroupCond leftGroupPost leftGroupBody

def rightGroupInit : List Stmt := [.letDecl "groupR" uint256Ty (.intLit 0)]
def rightGroupCond : Expr := .binary .lt (.var "groupR") (.intLit 5)
def rightGroupPost : List Stmt :=
  [.assign .localVar { base := "groupR" } (.binary .add (.var "groupR") (.intLit 1))]
def rightGroupFor : Stmt := .for rightGroupInit rightGroupCond rightGroupPost rightGroupBody

theorem leftGroupForReturns {L : Store} (evm : EVM.State) (X : Fin 16 -> UInt256)
    (initial : RuntimeLineState) (chain : RuntimeChain) (p : BlockParams)
    (hX32 : ∀ i, (X i).toNat < 2 ^ 32) (hbound : RuntimeLineBound initial)
    (hmask : L.get? "mask32" = some (wordValue mask32Word))
    (hwords : L.get? "words" = some (.array (roundWords X)))
    (hline : LeftLineAt L initial) (hchain : ChainAt L chain)
    (hparams : BlockParamsAt L p) :
    ∃ L', ExecStmt config { contract := contract, locals := L } evm leftGroupFor
        (.ok { contract := contract, locals := L' } evm) ∧
      LeftLineAt L' (runtimePureLeftLine X 5 initial) ∧
      RuntimeLineBound (runtimePureLeftLine X 5 initial) ∧
      L'.get? "mask32" = some (wordValue mask32Word) ∧
      L'.get? "words" = some (.array (roundWords X)) ∧
      ChainAt L' chain ∧ BlockParamsAt L' p := by
  let P : Nat -> Store -> Prop := fun v S =>
    ∃ group, group + v = 5 ∧
      LeftLineAt S (runtimePureLeftLine X group initial) ∧
      RuntimeLineBound (runtimePureLeftLine X group initial) ∧
      S.get? "groupL" = some (natValue group) ∧
      S.get? "mask32" = some (wordValue mask32Word) ∧
      S.get? "words" = some (.array (roundWords X)) ∧
      ChainAt S chain ∧ BlockParamsAt S p
  have hfalse : ∀ S, P 0 S ->
      evalExpr? config { contract := contract, locals := S } evm leftGroupCond =
        .ok (.bool false) := by
    intro S hP
    rcases hP with ⟨group, hv, _, _, hgroup, _⟩
    have he := evalNatLt (evalNatVar hgroup)
      (show evalExpr? config { contract := contract, locals := S } evm (.intLit 5) =
        .ok (natValue 5) by simp [evalExpr?, natValue, pure])
    have : group = 5 := by omega
    subst group
    simpa [leftGroupCond] using he
  have htrue : ∀ v S, P (v + 1) S ->
      evalExpr? config { contract := contract, locals := S } evm leftGroupCond =
        .ok (.bool true) := by
    intro v S hP
    rcases hP with ⟨group, hv, _, _, hgroup, _⟩
    have he := evalNatLt (evalNatVar hgroup)
      (show evalExpr? config { contract := contract, locals := S } evm (.intLit 5) =
        .ok (natValue 5) by simp [evalExpr?, natValue, pure])
    have hg : group < 5 := by omega
    simpa [leftGroupCond, decide_eq_true hg] using he
  have hstep : ∀ v S, P (v + 1) S ->
      ∃ S1, ExecBlock config { contract := contract, locals := S } evm leftGroupBody
          (.ok { contract := contract, locals := S1 } evm) ∧
        ∃ S', ExecBlock config { contract := contract, locals := S1 } evm leftGroupPost
          (.ok { contract := contract, locals := S' } evm) ∧ P v S' := by
    intro v S hP
    rcases hP with ⟨group, hv, hlineS, hboundS, hgroupS, hmaskS, hwordsS, hchainS,
      hparamsS⟩
    have hg : group < 5 := by omega
    obtain ⟨S1, hbody, hline1, hbound1, hgroup1, hmask1, hwords1, hchain1,
        hparams1⟩ :=
      leftGroupBodyReturns evm X group (runtimePureLeftLine X group initial) chain p hg
        hX32 hboundS hgroupS hmaskS hwordsS hlineS hchainS hparamsS
    let S' := S1.insert "groupL" (natValue (group + 1))
    have hpostEval : evalExpr? config { contract := contract, locals := S1 } evm
        (.binary .add (.var "groupL") (.intLit 1)) = .ok (natValue (group + 1)) :=
      evalNatAdd (evalNatVar hgroup1) (by simp [evalExpr?, natValue, pure])
    have hpost : ExecBlock config { contract := contract, locals := S1 } evm leftGroupPost
        (.ok { contract := contract, locals := S' } evm) :=
      ExecBlock.consNormal (execAssignLocal hgroup1 hpostEval) ExecBlock.nil
    have preserve (name : Ident) (hne : ("groupL" == name) = false) :
        S'.get? name = S1.get? name := by simp only [S']; rw [store_get_ne _ _ hne]
    have hline' : LeftLineAt S' (runtimePureLeftLine X (group + 1) initial) := by
      change LeftLineAt S' (runtimePureLeftGroup X group 16
        (runtimePureLeftLine X group initial))
      rcases hline1 with ⟨ha, hb, hc, hd, he⟩
      exact ⟨by rw [preserve "al" (by decide), ha],
        by rw [preserve "bl" (by decide), hb],
        by rw [preserve "cl" (by decide), hc],
        by rw [preserve "dl" (by decide), hd],
        by rw [preserve "el" (by decide), he]⟩
    have hchain' : ChainAt S' chain := by
      rcases hchain1 with ⟨hh0, hh1, hh2, hh3, hh4⟩
      exact ⟨by rw [preserve "h0" (by decide), hh0],
        by rw [preserve "h1" (by decide), hh1],
        by rw [preserve "h2" (by decide), hh2],
        by rw [preserve "h3" (by decide), hh3],
        by rw [preserve "h4" (by decide), hh4]⟩
    have hparams' : BlockParamsAt S' p := by
      rcases hparams1 with ⟨hd, hb, hp, hn, hblk⟩
      exact ⟨by rw [preserve "data" (by decide), hd],
        by rw [preserve "bitLen" (by decide), hb],
        by rw [preserve "paddedLen" (by decide), hp],
        by rw [preserve "numBlocks" (by decide), hn],
        by rw [preserve "blk" (by decide), hblk]⟩
    refine ⟨S1, hbody, S', hpost, group + 1, by omega, hline', ?_, by simp [S'], ?_⟩
    · simpa only [runtimePureLeftLine] using hbound1
    · exact ⟨by rw [preserve "mask32" (by decide), hmask1],
        by rw [preserve "words" (by decide), hwords1], hchain', hparams'⟩
  let L0 := L.insert "groupL" (natValue 0)
  have hinit : ExecBlock config { contract := contract, locals := L } evm leftGroupInit
      (.ok { contract := contract, locals := L0 } evm) :=
    ExecBlock.consNormal (ExecStmt.letDecl (by simp [evalExpr?, natValue, pure])) ExecBlock.nil
  have preserve0 (name : Ident) (hne : ("groupL" == name) = false) :
      L0.get? name = L.get? name := by simp only [L0]; rw [store_get_ne _ _ hne]
  have hline0 : LeftLineAt L0 initial := by
    rcases hline with ⟨ha, hb, hc, hd, he⟩
    exact ⟨by rw [preserve0 "al" (by decide), ha],
      by rw [preserve0 "bl" (by decide), hb],
      by rw [preserve0 "cl" (by decide), hc],
      by rw [preserve0 "dl" (by decide), hd],
      by rw [preserve0 "el" (by decide), he]⟩
  have hchain0 : ChainAt L0 chain := by
    rcases hchain with ⟨hh0, hh1, hh2, hh3, hh4⟩
    exact ⟨by rw [preserve0 "h0" (by decide), hh0],
      by rw [preserve0 "h1" (by decide), hh1],
      by rw [preserve0 "h2" (by decide), hh2],
      by rw [preserve0 "h3" (by decide), hh3],
      by rw [preserve0 "h4" (by decide), hh4]⟩
  have hparams0 : BlockParamsAt L0 p := by
    rcases hparams with ⟨hd, hb, hp, hn, hblk⟩
    exact ⟨by rw [preserve0 "data" (by decide), hd],
      by rw [preserve0 "bitLen" (by decide), hb],
      by rw [preserve0 "paddedLen" (by decide), hp],
      by rw [preserve0 "numBlocks" (by decide), hn],
      by rw [preserve0 "blk" (by decide), hblk]⟩
  have hP0 : P 5 L0 := ⟨0, by omega, by simpa using hline0, by simpa using hbound,
    by simp [L0], by rw [preserve0 "mask32" (by decide), hmask],
    by rw [preserve0 "words" (by decide), hwords], hchain0, hparams0⟩
  obtain ⟨L', hloop, hfinal⟩ := execFor_var P hfalse htrue hstep 5 L0 hP0
  rcases hfinal with ⟨group, hv, hline', hbound', _, hmask', hwords', hchain', hparams'⟩
  have : group = 5 := by omega
  subst group
  exact ⟨L', ExecStmt.for hinit hloop, hline', hbound', hmask', hwords', hchain',
    hparams'⟩

theorem rightGroupForReturns {L : Store} (evm : EVM.State) (X : Fin 16 -> UInt256)
    (initial left : RuntimeLineState) (chain : RuntimeChain) (p : BlockParams)
    (hX32 : ∀ i, (X i).toNat < 2 ^ 32) (hbound : RuntimeLineBound initial)
    (hmask : L.get? "mask32" = some (wordValue mask32Word))
    (hwords : L.get? "words" = some (.array (roundWords X)))
    (hline : RightLineAt L initial) (hleft : LeftLineAt L left)
    (hchain : ChainAt L chain) (hparams : BlockParamsAt L p) :
    ∃ L', ExecStmt config { contract := contract, locals := L } evm rightGroupFor
        (.ok { contract := contract, locals := L' } evm) ∧
      RightLineAt L' (runtimePureRightLine X 5 initial) ∧
      RuntimeLineBound (runtimePureRightLine X 5 initial) ∧
      L'.get? "mask32" = some (wordValue mask32Word) ∧
      L'.get? "words" = some (.array (roundWords X)) ∧
      LeftLineAt L' left ∧
      ChainAt L' chain ∧ BlockParamsAt L' p := by
  let P : Nat -> Store -> Prop := fun v S =>
    ∃ group, group + v = 5 ∧
      RightLineAt S (runtimePureRightLine X group initial) ∧
      RuntimeLineBound (runtimePureRightLine X group initial) ∧
      S.get? "groupR" = some (natValue group) ∧
      S.get? "mask32" = some (wordValue mask32Word) ∧
      S.get? "words" = some (.array (roundWords X)) ∧
      LeftLineAt S left ∧ ChainAt S chain ∧ BlockParamsAt S p
  have hfalse : ∀ S, P 0 S ->
      evalExpr? config { contract := contract, locals := S } evm rightGroupCond =
        .ok (.bool false) := by
    intro S hP
    rcases hP with ⟨group, hv, _, _, hgroup, _⟩
    have he := evalNatLt (evalNatVar hgroup)
      (show evalExpr? config { contract := contract, locals := S } evm (.intLit 5) =
        .ok (natValue 5) by simp [evalExpr?, natValue, pure])
    have : group = 5 := by omega
    subst group
    simpa [rightGroupCond] using he
  have htrue : ∀ v S, P (v + 1) S ->
      evalExpr? config { contract := contract, locals := S } evm rightGroupCond =
        .ok (.bool true) := by
    intro v S hP
    rcases hP with ⟨group, hv, _, _, hgroup, _⟩
    have he := evalNatLt (evalNatVar hgroup)
      (show evalExpr? config { contract := contract, locals := S } evm (.intLit 5) =
        .ok (natValue 5) by simp [evalExpr?, natValue, pure])
    have hg : group < 5 := by omega
    simpa [rightGroupCond, decide_eq_true hg] using he
  have hstep : ∀ v S, P (v + 1) S ->
      ∃ S1, ExecBlock config { contract := contract, locals := S } evm rightGroupBody
          (.ok { contract := contract, locals := S1 } evm) ∧
        ∃ S', ExecBlock config { contract := contract, locals := S1 } evm rightGroupPost
          (.ok { contract := contract, locals := S' } evm) ∧ P v S' := by
    intro v S hP
    rcases hP with ⟨group, hv, hlineS, hboundS, hgroupS, hmaskS, hwordsS, hleftS,
      hchainS, hparamsS⟩
    have hg : group < 5 := by omega
    obtain ⟨S1, hbody, hline1, hbound1, hgroup1, hmask1, hwords1, hleft1, hchain1,
        hparams1⟩ :=
      rightGroupBodyReturns evm X group (runtimePureRightLine X group initial) left chain p hg
        hX32 hboundS hgroupS hmaskS hwordsS hlineS hleftS hchainS hparamsS
    let S' := S1.insert "groupR" (natValue (group + 1))
    have hpostEval : evalExpr? config { contract := contract, locals := S1 } evm
        (.binary .add (.var "groupR") (.intLit 1)) = .ok (natValue (group + 1)) :=
      evalNatAdd (evalNatVar hgroup1) (by simp [evalExpr?, natValue, pure])
    have hpost : ExecBlock config { contract := contract, locals := S1 } evm rightGroupPost
        (.ok { contract := contract, locals := S' } evm) :=
      ExecBlock.consNormal (execAssignLocal hgroup1 hpostEval) ExecBlock.nil
    have preserve (name : Ident) (hne : ("groupR" == name) = false) :
        S'.get? name = S1.get? name := by simp only [S']; rw [store_get_ne _ _ hne]
    have hline' : RightLineAt S' (runtimePureRightLine X (group + 1) initial) := by
      change RightLineAt S' (runtimePureRightGroup X group 16
        (runtimePureRightLine X group initial))
      rcases hline1 with ⟨ha, hb, hc, hd, he⟩
      exact ⟨by rw [preserve "ar" (by decide), ha],
        by rw [preserve "br" (by decide), hb],
        by rw [preserve "cr" (by decide), hc],
        by rw [preserve "dr" (by decide), hd],
        by rw [preserve "er" (by decide), he]⟩
    have hleft' : LeftLineAt S' left := by
      rcases hleft1 with ⟨ha, hb, hc, hd, he⟩
      exact ⟨by rw [preserve "al" (by decide), ha],
        by rw [preserve "bl" (by decide), hb],
        by rw [preserve "cl" (by decide), hc],
        by rw [preserve "dl" (by decide), hd],
        by rw [preserve "el" (by decide), he]⟩
    have hchain' : ChainAt S' chain := by
      rcases hchain1 with ⟨hh0, hh1, hh2, hh3, hh4⟩
      exact ⟨by rw [preserve "h0" (by decide), hh0],
        by rw [preserve "h1" (by decide), hh1],
        by rw [preserve "h2" (by decide), hh2],
        by rw [preserve "h3" (by decide), hh3],
        by rw [preserve "h4" (by decide), hh4]⟩
    have hparams' : BlockParamsAt S' p := by
      rcases hparams1 with ⟨hd, hb, hp, hn, hblk⟩
      exact ⟨by rw [preserve "data" (by decide), hd],
        by rw [preserve "bitLen" (by decide), hb],
        by rw [preserve "paddedLen" (by decide), hp],
        by rw [preserve "numBlocks" (by decide), hn],
        by rw [preserve "blk" (by decide), hblk]⟩
    refine ⟨S1, hbody, S', hpost, group + 1, by omega, hline', ?_, by simp [S'], ?_⟩
    · simpa only [runtimePureRightLine] using hbound1
    · exact ⟨by rw [preserve "mask32" (by decide), hmask1],
        by rw [preserve "words" (by decide), hwords1], hleft', hchain', hparams'⟩
  let L0 := L.insert "groupR" (natValue 0)
  have hinit : ExecBlock config { contract := contract, locals := L } evm rightGroupInit
      (.ok { contract := contract, locals := L0 } evm) :=
    ExecBlock.consNormal (ExecStmt.letDecl (by simp [evalExpr?, natValue, pure])) ExecBlock.nil
  have preserve0 (name : Ident) (hne : ("groupR" == name) = false) :
      L0.get? name = L.get? name := by simp only [L0]; rw [store_get_ne _ _ hne]
  have hline0 : RightLineAt L0 initial := by
    rcases hline with ⟨ha, hb, hc, hd, he⟩
    exact ⟨by rw [preserve0 "ar" (by decide), ha],
      by rw [preserve0 "br" (by decide), hb],
      by rw [preserve0 "cr" (by decide), hc],
      by rw [preserve0 "dr" (by decide), hd],
      by rw [preserve0 "er" (by decide), he]⟩
  have hleft0 : LeftLineAt L0 left := by
    rcases hleft with ⟨ha, hb, hc, hd, he⟩
    exact ⟨by rw [preserve0 "al" (by decide), ha],
      by rw [preserve0 "bl" (by decide), hb],
      by rw [preserve0 "cl" (by decide), hc],
      by rw [preserve0 "dl" (by decide), hd],
      by rw [preserve0 "el" (by decide), he]⟩
  have hchain0 : ChainAt L0 chain := by
    rcases hchain with ⟨hh0, hh1, hh2, hh3, hh4⟩
    exact ⟨by rw [preserve0 "h0" (by decide), hh0],
      by rw [preserve0 "h1" (by decide), hh1],
      by rw [preserve0 "h2" (by decide), hh2],
      by rw [preserve0 "h3" (by decide), hh3],
      by rw [preserve0 "h4" (by decide), hh4]⟩
  have hparams0 : BlockParamsAt L0 p := by
    rcases hparams with ⟨hd, hb, hp, hn, hblk⟩
    exact ⟨by rw [preserve0 "data" (by decide), hd],
      by rw [preserve0 "bitLen" (by decide), hb],
      by rw [preserve0 "paddedLen" (by decide), hp],
      by rw [preserve0 "numBlocks" (by decide), hn],
      by rw [preserve0 "blk" (by decide), hblk]⟩
  have hP0 : P 5 L0 := ⟨0, by omega, by simpa using hline0, by simpa using hbound,
    by simp [L0], by rw [preserve0 "mask32" (by decide), hmask],
    by rw [preserve0 "words" (by decide), hwords], hleft0, hchain0, hparams0⟩
  obtain ⟨L', hloop, hfinal⟩ := execFor_var P hfalse htrue hstep 5 L0 hP0
  rcases hfinal with ⟨group, hv, hline', hbound', _, hmask', hwords', hleft', hchain',
    hparams'⟩
  have : group = 5 := by omega
  subst group
  exact ⟨L', ExecStmt.for hinit hloop, hline', hbound', hmask', hwords', hleft', hchain',
    hparams'⟩

end Ripemd160
