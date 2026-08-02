import Examples.Ripemd160.SolmRoundLoop

/-!
# RIPEMD-160 Solm right inner round loop

The sixteen-round loop for a fixed right compression group.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Ripemd160

def rightRoundInit : List Stmt :=
  [.letDecl "roundR" uint256Ty (.intLit 0)]

def rightRoundCond : Expr := .binary .lt (.var "roundR") (.intLit 16)

def rightRoundPost : List Stmt :=
  [.assign .localVar { base := "roundR" }
    (.binary .add (.var "roundR") (.intLit 1))]

def rightRoundFor : Stmt := .for rightRoundInit rightRoundCond rightRoundPost rightRoundBody

theorem rightConstantWord_lt (group : Nat) (hg : group < 5) :
    (rightConstantWord group).toNat < 2 ^ 32 := by
  interval_cases group <;> native_decide

theorem RuntimeLineBound.rightRound (X : Fin 16 -> UInt256)
    (group round : Nat) (s : RuntimeLineState) (hs : RuntimeLineBound s) :
    RuntimeLineBound (Ripemd160.runtimePureRightRound X group round s) := by
  let x := X ⟨(runtimeRowEntry (rightWordRowWord group) (UInt256.ofNat round)).toNat,
    runtimeRowEntry_lt_sixteen _ _⟩
  have heq : Ripemd160.sourcePureRound s x round (rightRotationRowWord group)
      (runtimeRightF group s.b s.c s.d) (rightConstantWord group) =
      Ripemd160.runtimePureRightRound X group round s := by
    simpa [x, Ripemd160.runtimePureRightRound] using sourcePureRound_eq_runtime s x round
      (rightWordRowWord group) (rightRotationRowWord group)
      (runtimeRightF group s.b s.c s.d) (rightConstantWord group)
  rw [← heq]
  exact RuntimeLineBound.sourcePureRound s x round _ _ _ hs

theorem rightRoundForReturns {L : Store} (evm : EVM.State) (X : Fin 16 -> UInt256)
    (group : Nat) (initial left : RuntimeLineState) (chain : RuntimeChain) (p : BlockParams)
    (hg : group < 5)
    (hX32 : ∀ i, (X i).toNat < 2 ^ 32) (hbound : RuntimeLineBound initial)
    (hgroup : L.get? "groupR" = some (natValue group))
    (hwordRow : L.get? "wordTableR" = some (wordValue (rightWordRowWord group)))
    (hrotRow : L.get? "rotTableR" = some (wordValue (rightRotationRowWord group)))
    (hconstant : L.get? "kR" = some (wordValue (rightConstantWord group)))
    (hmask : L.get? "mask32" = some (wordValue mask32Word))
    (hwords : L.get? "words" = some (.array (roundWords X)))
    (hline : RightLineAt L initial) (hleft : LeftLineAt L left)
    (hchain : ChainAt L chain) (hparams : BlockParamsAt L p) :
    ∃ L', ExecStmt config { contract := contract, locals := L } evm rightRoundFor
        (.ok { contract := contract, locals := L' } evm) ∧
      RightLineAt L' (runtimePureRightGroup X group 16 initial) ∧
      RuntimeLineBound (runtimePureRightGroup X group 16 initial) ∧
      L'.get? "groupR" = some (natValue group) ∧
      L'.get? "wordTableR" = some (wordValue (rightWordRowWord group)) ∧
      L'.get? "rotTableR" = some (wordValue (rightRotationRowWord group)) ∧
      L'.get? "kR" = some (wordValue (rightConstantWord group)) ∧
      L'.get? "mask32" = some (wordValue mask32Word) ∧
      L'.get? "words" = some (.array (roundWords X)) ∧
      LeftLineAt L' left ∧
      ChainAt L' chain ∧ BlockParamsAt L' p := by
  let P : Nat -> Store -> Prop := fun v S =>
    ∃ round, round + v = 16 ∧
      RightLineAt S (runtimePureRightGroup X group round initial) ∧
      RuntimeLineBound (runtimePureRightGroup X group round initial) ∧
      S.get? "roundR" = some (natValue round) ∧
      S.get? "groupR" = some (natValue group) ∧
      S.get? "wordTableR" = some (wordValue (rightWordRowWord group)) ∧
      S.get? "rotTableR" = some (wordValue (rightRotationRowWord group)) ∧
      S.get? "kR" = some (wordValue (rightConstantWord group)) ∧
      S.get? "mask32" = some (wordValue mask32Word) ∧
      S.get? "words" = some (.array (roundWords X)) ∧
      LeftLineAt S left ∧
      ChainAt S chain ∧ BlockParamsAt S p
  have hfalse : ∀ S, P 0 S ->
      evalExpr? config { contract := contract, locals := S } evm rightRoundCond =
        .ok (.bool false) := by
    intro S hP
    rcases hP with ⟨round, hv, _, _, hround, _⟩
    have he := evalNatLt (evalNatVar hround)
      (show evalExpr? config { contract := contract, locals := S } evm (.intLit 16) =
        .ok (natValue 16) by simp [evalExpr?, natValue, pure])
    have : round = 16 := by omega
    subst round
    simpa [rightRoundCond] using he
  have htrue : ∀ v S, P (v + 1) S ->
      evalExpr? config { contract := contract, locals := S } evm rightRoundCond =
        .ok (.bool true) := by
    intro v S hP
    rcases hP with ⟨round, hv, _, _, hround, _⟩
    have he := evalNatLt (evalNatVar hround)
      (show evalExpr? config { contract := contract, locals := S } evm (.intLit 16) =
        .ok (natValue 16) by simp [evalExpr?, natValue, pure])
    have hr : round < 16 := by omega
    simpa [rightRoundCond, decide_eq_true hr] using he
  have hstep : ∀ v S, P (v + 1) S ->
      ∃ S1, ExecBlock config { contract := contract, locals := S } evm rightRoundBody
          (.ok { contract := contract, locals := S1 } evm) ∧
        ∃ S', ExecBlock config { contract := contract, locals := S1 } evm rightRoundPost
          (.ok { contract := contract, locals := S' } evm) ∧ P v S' := by
    intro v S hP
    rcases hP with ⟨round, hv, hlineS, hboundS, hroundS, hgroupS,
      hwordS, hrotS, hkS, hmaskS, hwordsS, hleftS, hchainS, hparamsS⟩
    have hr : round < 16 := by omega
    let S1 := rightRoundOutputStore S X (runtimePureRightGroup X group round initial)
      group round (rightWordRowWord group) (rightRotationRowWord group)
      (rightConstantWord group)
    have hbody : ExecBlock config { contract := contract, locals := S } evm rightRoundBody
        (.ok { contract := contract, locals := S1 } evm) := by
      rcases hlineS with ⟨ha, hb, hc, hd, he⟩
      simpa [S1] using rightRoundBodyReturns evm X
        (runtimePureRightGroup X group round initial) group round
        (rightWordRowWord group) (rightRotationRowWord group) (rightConstantWord group)
        hg hr hboundS hX32 hgroupS hroundS hwordS hrotS hkS
        (rightConstantWord_lt group hg) hmaskS hwordsS ha hb hc hd he
    have hline1 : RightLineAt S1
        (runtimePureRightRound X group round
          (runtimePureRightGroup X group round initial)) := by
      simpa [S1] using rightRoundOutputStore_lineAt S X
        (runtimePureRightGroup X group round initial) group round
    have hctx := rightRoundOutputStore_context S X
      (runtimePureRightGroup X group round initial) group round
      (rightWordRowWord group) (rightRotationRowWord group) (rightConstantWord group) hg
    change S1.get? "groupR" = S.get? "groupR" ∧
      S1.get? "roundR" = S.get? "roundR" ∧
      S1.get? "wordTableR" = S.get? "wordTableR" ∧
      S1.get? "rotTableR" = S.get? "rotTableR" ∧
      S1.get? "kR" = S.get? "kR" ∧ S1.get? "mask32" = S.get? "mask32" ∧
      S1.get? "words" = S.get? "words" ∧
      S1.get? "h0" = S.get? "h0" ∧ S1.get? "h1" = S.get? "h1" ∧
      S1.get? "h2" = S.get? "h2" ∧ S1.get? "h3" = S.get? "h3" ∧
      S1.get? "h4" = S.get? "h4" ∧
      S1.get? "al" = S.get? "al" ∧ S1.get? "bl" = S.get? "bl" ∧
      S1.get? "cl" = S.get? "cl" ∧ S1.get? "dl" = S.get? "dl" ∧
      S1.get? "el" = S.get? "el" ∧ S1.get? "data" = S.get? "data" ∧
      S1.get? "bitLen" = S.get? "bitLen" ∧ S1.get? "paddedLen" = S.get? "paddedLen" ∧
      S1.get? "numBlocks" = S.get? "numBlocks" ∧ S1.get? "blk" = S.get? "blk" at hctx
    rcases hctx with ⟨hgroup1eq, hround1eq, hword1eq, hrot1eq, hk1eq, hmask1eq,
      hwords1eq, hh0eq, hh1eq, hh2eq, hh3eq, hh4eq, haleq, hbleq, hcleq, hdleq,
      heleq, hdataeq, hbiteq, hpadeq, hnumeq, hblkeq⟩
    have hround1 : S1.get? "roundR" = some (natValue round) := hround1eq.trans hroundS
    have hgroup1 : S1.get? "groupR" = some (natValue group) := hgroup1eq.trans hgroupS
    have hword1 : S1.get? "wordTableR" = some (wordValue (rightWordRowWord group)) :=
      hword1eq.trans hwordS
    have hrot1 : S1.get? "rotTableR" = some (wordValue (rightRotationRowWord group)) :=
      hrot1eq.trans hrotS
    have hk1 : S1.get? "kR" = some (wordValue (rightConstantWord group)) := hk1eq.trans hkS
    have hmask1 : S1.get? "mask32" = some (wordValue mask32Word) := hmask1eq.trans hmaskS
    have hwords1 : S1.get? "words" = some (.array (roundWords X)) := hwords1eq.trans hwordsS
    have hleft1 : LeftLineAt S1 left := by
      rcases hleftS with ⟨ha, hb, hc, hd, he⟩
      exact ⟨haleq.trans ha, hbleq.trans hb, hcleq.trans hc, hdleq.trans hd,
        heleq.trans he⟩
    have hchain1 : ChainAt S1 chain := by
      rcases hchainS with ⟨hh0, hh1, hh2, hh3, hh4⟩
      exact ⟨hh0eq.trans hh0, hh1eq.trans hh1, hh2eq.trans hh2, hh3eq.trans hh3,
        hh4eq.trans hh4⟩
    have hparams1 : BlockParamsAt S1 p := by
      rcases hparamsS with ⟨hd, hb, hp, hn, hblk⟩
      exact ⟨hdataeq.trans hd, hbiteq.trans hb, hpadeq.trans hp, hnumeq.trans hn,
        hblkeq.trans hblk⟩
    let S' := S1.insert "roundR" (natValue (round + 1))
    have hpostEval : evalExpr? config { contract := contract, locals := S1 } evm
        (.binary .add (.var "roundR") (.intLit 1)) = .ok (natValue (round + 1)) :=
      evalNatAdd (evalNatVar hround1) (by simp [evalExpr?, natValue, pure])
    have hpostStmt := execAssignLocal (evm := evm) hround1 hpostEval
    have hpost : ExecBlock config { contract := contract, locals := S1 } evm rightRoundPost
        (.ok { contract := contract, locals := S' } evm) :=
      ExecBlock.consNormal hpostStmt ExecBlock.nil
    have hline' : RightLineAt S'
        (runtimePureRightGroup X group (round + 1) initial) := by
      have heq : runtimePureRightGroup X group (round + 1) initial =
          runtimePureRightRound X group round
            (runtimePureRightGroup X group round initial) := rfl
      rw [heq]
      rcases hline1 with ⟨ha, hb, hc, hd, he⟩
      exact ⟨by simp only [S']; rw [store_get_ne _ _ (by decide), ha],
        by simp only [S']; rw [store_get_ne _ _ (by decide), hb],
        by simp only [S']; rw [store_get_ne _ _ (by decide), hc],
        by simp only [S']; rw [store_get_ne _ _ (by decide), hd],
        by simp only [S']; rw [store_get_ne _ _ (by decide), he]⟩
    have hbound' : RuntimeLineBound (runtimePureRightGroup X group (round + 1) initial) := by
      change RuntimeLineBound (runtimePureRightRound X group round
        (runtimePureRightGroup X group round initial))
      exact hboundS.rightRound X group round _
    have hround' : S'.get? "roundR" = some (natValue (round + 1)) := by simp [S']
    have preservePost (name : Ident) (hne : ("roundR" == name) = false) :
        S'.get? name = S1.get? name := by simp only [S']; rw [store_get_ne _ _ hne]
    have hleft' : LeftLineAt S' left := by
      rcases hleft1 with ⟨ha, hb, hc, hd, he⟩
      exact ⟨by rw [preservePost "al" (by decide), ha],
        by rw [preservePost "bl" (by decide), hb],
        by rw [preservePost "cl" (by decide), hc],
        by rw [preservePost "dl" (by decide), hd],
        by rw [preservePost "el" (by decide), he]⟩
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
    exact ⟨by rw [preservePost "groupR" (by decide), hgroup1],
      by rw [preservePost "wordTableR" (by decide), hword1],
      by rw [preservePost "rotTableR" (by decide), hrot1],
      by rw [preservePost "kR" (by decide), hk1],
      by rw [preservePost "mask32" (by decide), hmask1],
      by rw [preservePost "words" (by decide), hwords1], hleft', hchain', hparams'⟩
  let L0 := L.insert "roundR" (natValue 0)
  have hinit : ExecBlock config { contract := contract, locals := L } evm rightRoundInit
      (.ok { contract := contract, locals := L0 } evm) := by
    exact ExecBlock.consNormal (ExecStmt.letDecl (by simp [evalExpr?, natValue, pure])) ExecBlock.nil
  have preserve0 (name : Ident) (hne : ("roundR" == name) = false) :
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
  have hP0 : P 16 L0 := ⟨0, by omega, by simpa using hline0, by simpa using hbound,
    by simp [L0], by rw [preserve0 "groupR" (by decide), hgroup],
    by rw [preserve0 "wordTableR" (by decide), hwordRow],
    by rw [preserve0 "rotTableR" (by decide), hrotRow],
    by rw [preserve0 "kR" (by decide), hconstant],
    by rw [preserve0 "mask32" (by decide), hmask],
    by rw [preserve0 "words" (by decide), hwords], hleft0, hchain0, hparams0⟩
  obtain ⟨L', hloop, hfinal⟩ := execFor_var P hfalse htrue hstep 16 L0 hP0
  rcases hfinal with ⟨round, hv, hline', hbound', hround', hgroup', hword',
    hrot', hk', hmask', hwords', hleft', hchain', hparams'⟩
  have : round = 16 := by omega
  subst round
  exact ⟨L', ExecStmt.for hinit hloop, hline', hbound', hgroup', hword', hrot', hk',
    hmask', hwords', hleft', hchain', hparams'⟩


end Ripemd160
