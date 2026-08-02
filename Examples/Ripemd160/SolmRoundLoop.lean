import Examples.Ripemd160.SolmRightRoundBody

/-!
# RIPEMD-160 Solm inner round loops

The sixteen-round loop for a fixed left compression group.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Ripemd160

def leftRoundInit : List Stmt :=
  [.letDecl "roundL" uint256Ty (.intLit 0)]

def leftRoundCond : Expr := .binary .lt (.var "roundL") (.intLit 16)

def leftRoundPost : List Stmt :=
  [.assign .localVar { base := "roundL" }
    (.binary .add (.var "roundL") (.intLit 1))]

def leftRoundFor : Stmt := .for leftRoundInit leftRoundCond leftRoundPost leftRoundBody

theorem leftConstantWord_lt (group : Nat) (hg : group < 5) :
    (leftConstantWord group).toNat < 2 ^ 32 := by
  interval_cases group <;> native_decide

theorem RuntimeLineBound.leftRound (X : Fin 16 -> UInt256)
    (group round : Nat) (s : RuntimeLineState) (hs : RuntimeLineBound s) :
    RuntimeLineBound (Ripemd160.runtimePureLeftRound X group round s) := by
  let x := X ⟨(runtimeRowEntry (leftWordRowWord group) (UInt256.ofNat round)).toNat,
    runtimeRowEntry_lt_sixteen _ _⟩
  have heq : Ripemd160.sourcePureRound s x round (leftRotationRowWord group)
      (runtimeLeftF group s.b s.c s.d) (leftConstantWord group) =
      Ripemd160.runtimePureLeftRound X group round s := by
    simpa [x, Ripemd160.runtimePureLeftRound] using sourcePureRound_eq_runtime s x round
      (leftWordRowWord group) (leftRotationRowWord group)
      (runtimeLeftF group s.b s.c s.d) (leftConstantWord group)
  rw [← heq]
  exact RuntimeLineBound.sourcePureRound s x round _ _ _ hs

theorem leftRoundForReturns {L : Store} (evm : EVM.State) (X : Fin 16 -> UInt256)
    (group : Nat) (initial : RuntimeLineState) (chain : RuntimeChain) (p : BlockParams)
    (hg : group < 5)
    (hX32 : ∀ i, (X i).toNat < 2 ^ 32) (hbound : RuntimeLineBound initial)
    (hgroup : L.get? "groupL" = some (natValue group))
    (hwordRow : L.get? "wordTableL" = some (wordValue (leftWordRowWord group)))
    (hrotRow : L.get? "rotTableL" = some (wordValue (leftRotationRowWord group)))
    (hconstant : L.get? "kL" = some (wordValue (leftConstantWord group)))
    (hmask : L.get? "mask32" = some (wordValue mask32Word))
    (hwords : L.get? "words" = some (.array (roundWords X)))
    (hline : LeftLineAt L initial) (hchain : ChainAt L chain)
    (hparams : BlockParamsAt L p) :
    ∃ L', ExecStmt config { contract := contract, locals := L } evm leftRoundFor
        (.ok { contract := contract, locals := L' } evm) ∧
      LeftLineAt L' (runtimePureLeftGroup X group 16 initial) ∧
      RuntimeLineBound (runtimePureLeftGroup X group 16 initial) ∧
      L'.get? "groupL" = some (natValue group) ∧
      L'.get? "wordTableL" = some (wordValue (leftWordRowWord group)) ∧
      L'.get? "rotTableL" = some (wordValue (leftRotationRowWord group)) ∧
      L'.get? "kL" = some (wordValue (leftConstantWord group)) ∧
      L'.get? "mask32" = some (wordValue mask32Word) ∧
      L'.get? "words" = some (.array (roundWords X)) ∧
      ChainAt L' chain ∧ BlockParamsAt L' p := by
  let P : Nat -> Store -> Prop := fun v S =>
    ∃ round, round + v = 16 ∧
      LeftLineAt S (runtimePureLeftGroup X group round initial) ∧
      RuntimeLineBound (runtimePureLeftGroup X group round initial) ∧
      S.get? "roundL" = some (natValue round) ∧
      S.get? "groupL" = some (natValue group) ∧
      S.get? "wordTableL" = some (wordValue (leftWordRowWord group)) ∧
      S.get? "rotTableL" = some (wordValue (leftRotationRowWord group)) ∧
      S.get? "kL" = some (wordValue (leftConstantWord group)) ∧
      S.get? "mask32" = some (wordValue mask32Word) ∧
      S.get? "words" = some (.array (roundWords X)) ∧
      ChainAt S chain ∧ BlockParamsAt S p
  have hfalse : ∀ S, P 0 S ->
      evalExpr? config { contract := contract, locals := S } evm leftRoundCond =
        .ok (.bool false) := by
    intro S hP
    rcases hP with ⟨round, hv, _, _, hround, _⟩
    have he := evalNatLt (evalNatVar hround)
      (show evalExpr? config { contract := contract, locals := S } evm (.intLit 16) =
        .ok (natValue 16) by simp [evalExpr?, natValue, pure])
    have : round = 16 := by omega
    subst round
    simpa [leftRoundCond] using he
  have htrue : ∀ v S, P (v + 1) S ->
      evalExpr? config { contract := contract, locals := S } evm leftRoundCond =
        .ok (.bool true) := by
    intro v S hP
    rcases hP with ⟨round, hv, _, _, hround, _⟩
    have he := evalNatLt (evalNatVar hround)
      (show evalExpr? config { contract := contract, locals := S } evm (.intLit 16) =
        .ok (natValue 16) by simp [evalExpr?, natValue, pure])
    have hr : round < 16 := by omega
    simpa [leftRoundCond, decide_eq_true hr] using he
  have hstep : ∀ v S, P (v + 1) S ->
      ∃ S1, ExecBlock config { contract := contract, locals := S } evm leftRoundBody
          (.ok { contract := contract, locals := S1 } evm) ∧
        ∃ S', ExecBlock config { contract := contract, locals := S1 } evm leftRoundPost
          (.ok { contract := contract, locals := S' } evm) ∧ P v S' := by
    intro v S hP
    rcases hP with ⟨round, hv, hlineS, hboundS, hroundS, hgroupS,
      hwordS, hrotS, hkS, hmaskS, hwordsS, hchainS, hparamsS⟩
    have hr : round < 16 := by omega
    let S1 := leftRoundOutputStore S X (runtimePureLeftGroup X group round initial)
      group round (leftWordRowWord group) (leftRotationRowWord group)
      (leftConstantWord group)
    have hbody : ExecBlock config { contract := contract, locals := S } evm leftRoundBody
        (.ok { contract := contract, locals := S1 } evm) := by
      rcases hlineS with ⟨ha, hb, hc, hd, he⟩
      simpa [S1] using leftRoundBodyReturns evm X
        (runtimePureLeftGroup X group round initial) group round
        (leftWordRowWord group) (leftRotationRowWord group) (leftConstantWord group)
        hg hr hboundS hX32 hgroupS hroundS hwordS hrotS hkS
        (leftConstantWord_lt group hg) hmaskS hwordsS ha hb hc hd he
    have hline1 : LeftLineAt S1
        (runtimePureLeftRound X group round
          (runtimePureLeftGroup X group round initial)) := by
      simpa [S1] using leftRoundOutputStore_lineAt S X
        (runtimePureLeftGroup X group round initial) group round
    have hctx := leftRoundOutputStore_context S X
      (runtimePureLeftGroup X group round initial) group round
      (leftWordRowWord group) (leftRotationRowWord group) (leftConstantWord group) hg
    change S1.get? "groupL" = S.get? "groupL" ∧
      S1.get? "roundL" = S.get? "roundL" ∧
      S1.get? "wordTableL" = S.get? "wordTableL" ∧
      S1.get? "rotTableL" = S.get? "rotTableL" ∧
      S1.get? "kL" = S.get? "kL" ∧ S1.get? "mask32" = S.get? "mask32" ∧
      S1.get? "words" = S.get? "words" ∧
      S1.get? "h0" = S.get? "h0" ∧ S1.get? "h1" = S.get? "h1" ∧
      S1.get? "h2" = S.get? "h2" ∧ S1.get? "h3" = S.get? "h3" ∧
      S1.get? "h4" = S.get? "h4" ∧ S1.get? "data" = S.get? "data" ∧
      S1.get? "bitLen" = S.get? "bitLen" ∧ S1.get? "paddedLen" = S.get? "paddedLen" ∧
      S1.get? "numBlocks" = S.get? "numBlocks" ∧ S1.get? "blk" = S.get? "blk" at hctx
    rcases hctx with ⟨hgroup1eq, hround1eq, hword1eq, hrot1eq, hk1eq, hmask1eq,
      hwords1eq, hh0eq, hh1eq, hh2eq, hh3eq, hh4eq, hdataeq, hbiteq, hpadeq,
      hnumeq, hblkeq⟩
    have hround1 : S1.get? "roundL" = some (natValue round) := hround1eq.trans hroundS
    have hgroup1 : S1.get? "groupL" = some (natValue group) := hgroup1eq.trans hgroupS
    have hword1 : S1.get? "wordTableL" = some (wordValue (leftWordRowWord group)) :=
      hword1eq.trans hwordS
    have hrot1 : S1.get? "rotTableL" = some (wordValue (leftRotationRowWord group)) :=
      hrot1eq.trans hrotS
    have hk1 : S1.get? "kL" = some (wordValue (leftConstantWord group)) := hk1eq.trans hkS
    have hmask1 : S1.get? "mask32" = some (wordValue mask32Word) := hmask1eq.trans hmaskS
    have hwords1 : S1.get? "words" = some (.array (roundWords X)) := hwords1eq.trans hwordsS
    have hchain1 : ChainAt S1 chain := by
      rcases hchainS with ⟨hh0, hh1, hh2, hh3, hh4⟩
      exact ⟨hh0eq.trans hh0, hh1eq.trans hh1, hh2eq.trans hh2, hh3eq.trans hh3,
        hh4eq.trans hh4⟩
    have hparams1 : BlockParamsAt S1 p := by
      rcases hparamsS with ⟨hd, hb, hp, hn, hblk⟩
      exact ⟨hdataeq.trans hd, hbiteq.trans hb, hpadeq.trans hp, hnumeq.trans hn,
        hblkeq.trans hblk⟩
    let S' := S1.insert "roundL" (natValue (round + 1))
    have hpostEval : evalExpr? config { contract := contract, locals := S1 } evm
        (.binary .add (.var "roundL") (.intLit 1)) = .ok (natValue (round + 1)) :=
      evalNatAdd (evalNatVar hround1) (by simp [evalExpr?, natValue, pure])
    have hpostStmt := execAssignLocal (evm := evm) hround1 hpostEval
    have hpost : ExecBlock config { contract := contract, locals := S1 } evm leftRoundPost
        (.ok { contract := contract, locals := S' } evm) :=
      ExecBlock.consNormal hpostStmt ExecBlock.nil
    have hline' : LeftLineAt S'
        (runtimePureLeftGroup X group (round + 1) initial) := by
      have heq : runtimePureLeftGroup X group (round + 1) initial =
          runtimePureLeftRound X group round
            (runtimePureLeftGroup X group round initial) := rfl
      rw [heq]
      rcases hline1 with ⟨ha, hb, hc, hd, he⟩
      exact ⟨by simp only [S']; rw [store_get_ne _ _ (by decide), ha],
        by simp only [S']; rw [store_get_ne _ _ (by decide), hb],
        by simp only [S']; rw [store_get_ne _ _ (by decide), hc],
        by simp only [S']; rw [store_get_ne _ _ (by decide), hd],
        by simp only [S']; rw [store_get_ne _ _ (by decide), he]⟩
    have hbound' : RuntimeLineBound (runtimePureLeftGroup X group (round + 1) initial) := by
      change RuntimeLineBound (runtimePureLeftRound X group round
        (runtimePureLeftGroup X group round initial))
      exact hboundS.leftRound X group round _
    have hround' : S'.get? "roundL" = some (natValue (round + 1)) := by simp [S']
    have preservePost (name : Ident) (hne : ("roundL" == name) = false) :
        S'.get? name = S1.get? name := by simp only [S']; rw [store_get_ne _ _ hne]
    have hchain' : ChainAt S' chain := by
      rcases hchain1 with ⟨hh0, hh1, hh2, hh3, hh4⟩
      exact ⟨by rw [preservePost "h0" (by decide), hh0],
        by rw [preservePost "h1" (by decide), hh1],
        by rw [preservePost "h2" (by decide), hh2],
        by rw [preservePost "h3" (by decide), hh3],
        by rw [preservePost "h4" (by decide), hh4]⟩
    have hparams' : BlockParamsAt S' p := by
      rcases hparams1 with ⟨hd, hb, hp, hn, hblk⟩
      exact ⟨by rw [preservePost "data" (by decide), hd],
        by rw [preservePost "bitLen" (by decide), hb],
        by rw [preservePost "paddedLen" (by decide), hp],
        by rw [preservePost "numBlocks" (by decide), hn],
        by rw [preservePost "blk" (by decide), hblk]⟩
    refine ⟨S1, hbody, S', hpost, round + 1, by omega, hline', hbound', hround', ?_⟩
    exact ⟨by rw [preservePost "groupL" (by decide), hgroup1],
      by rw [preservePost "wordTableL" (by decide), hword1],
      by rw [preservePost "rotTableL" (by decide), hrot1],
      by rw [preservePost "kL" (by decide), hk1],
      by rw [preservePost "mask32" (by decide), hmask1],
      by rw [preservePost "words" (by decide), hwords1], hchain', hparams'⟩
  let L0 := L.insert "roundL" (natValue 0)
  have hinit : ExecBlock config { contract := contract, locals := L } evm leftRoundInit
      (.ok { contract := contract, locals := L0 } evm) := by
    exact ExecBlock.consNormal (ExecStmt.letDecl (by simp [evalExpr?, natValue, pure])) ExecBlock.nil
  have preserve0 (name : Ident) (hne : ("roundL" == name) = false) :
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
  have hP0 : P 16 L0 := ⟨0, by omega, by simpa using hline0, by simpa using hbound,
    by simp [L0], by rw [preserve0 "groupL" (by decide), hgroup],
    by rw [preserve0 "wordTableL" (by decide), hwordRow],
    by rw [preserve0 "rotTableL" (by decide), hrotRow],
    by rw [preserve0 "kL" (by decide), hconstant],
    by rw [preserve0 "mask32" (by decide), hmask],
    by rw [preserve0 "words" (by decide), hwords], hchain0, hparams0⟩
  obtain ⟨L', hloop, hfinal⟩ := execFor_var P hfalse htrue hstep 16 L0 hP0
  rcases hfinal with ⟨round, hv, hline', hbound', hround', hgroup', hword',
    hrot', hk', hmask', hwords', hchain', hparams'⟩
  have : round = 16 := by omega
  subst round
  exact ⟨L', ExecStmt.for hinit hloop, hline', hbound', hgroup', hword', hrot', hk',
    hmask', hwords', hchain', hparams'⟩

end Ripemd160
