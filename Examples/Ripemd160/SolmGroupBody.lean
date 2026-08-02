import Examples.Ripemd160.SolmRightGroupPrelude

/-!
# RIPEMD-160 Solm compression-group bodies

Composition of each table/constant prelude with its sixteen authored rounds.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Ripemd160

def leftGroupBody : List Stmt := leftGroupPrelude ++ [leftRoundFor]

def rightGroupBody : List Stmt := rightGroupPrelude ++ [rightRoundFor]

theorem leftGroupBodyReturns {L : Store} (evm : EVM.State) (X : Fin 16 -> UInt256)
    (group : Nat) (initial : RuntimeLineState) (chain : RuntimeChain) (p : BlockParams)
    (hg : group < 5)
    (hX32 : ∀ i, (X i).toNat < 2 ^ 32) (hbound : RuntimeLineBound initial)
    (hgroup : L.get? "groupL" = some (natValue group))
    (hmask : L.get? "mask32" = some (wordValue mask32Word))
    (hwords : L.get? "words" = some (.array (roundWords X)))
    (hline : LeftLineAt L initial) (hchain : ChainAt L chain)
    (hparams : BlockParamsAt L p) :
    ∃ L', ExecBlock config { contract := contract, locals := L } evm leftGroupBody
        (.ok { contract := contract, locals := L' } evm) ∧
      LeftLineAt L' (runtimePureLeftGroup X group 16 initial) ∧
      RuntimeLineBound (runtimePureLeftGroup X group 16 initial) ∧
      L'.get? "groupL" = some (natValue group) ∧
      L'.get? "mask32" = some (wordValue mask32Word) ∧
      L'.get? "words" = some (.array (roundWords X)) ∧
      ChainAt L' chain ∧ BlockParamsAt L' p := by
  let P := leftGroupPreludeStore L group
  have hpre : ExecBlock config { contract := contract, locals := L } evm leftGroupPrelude
      (.ok { contract := contract, locals := P } evm) := by
    simpa [P] using leftGroupPreludeReturns evm group hg hgroup
  have preserve (name : Ident) (hword : ("wordTableL" == name) = false)
      (hrot : ("rotTableL" == name) = false) (hk : ("kL" == name) = false) :
      P.get? name = L.get? name := by
    simpa [P] using leftGroupPreludeStore_get_original L group name hword hrot hk
  have hlineP : LeftLineAt P initial := by
    rcases hline with ⟨ha, hb, hc, hd, he⟩
    exact ⟨by rw [preserve "al" (by decide) (by decide) (by decide), ha],
      by rw [preserve "bl" (by decide) (by decide) (by decide), hb],
      by rw [preserve "cl" (by decide) (by decide) (by decide), hc],
      by rw [preserve "dl" (by decide) (by decide) (by decide), hd],
      by rw [preserve "el" (by decide) (by decide) (by decide), he]⟩
  have hgroupP : P.get? "groupL" = some (natValue group) := by
    rw [preserve "groupL" (by decide) (by decide) (by decide), hgroup]
  have hmaskP : P.get? "mask32" = some (wordValue mask32Word) := by
    rw [preserve "mask32" (by decide) (by decide) (by decide), hmask]
  have hwordsP : P.get? "words" = some (.array (roundWords X)) := by
    rw [preserve "words" (by decide) (by decide) (by decide), hwords]
  have hchainP : ChainAt P chain := by
    rcases hchain with ⟨hh0, hh1, hh2, hh3, hh4⟩
    exact ⟨by rw [preserve "h0" (by decide) (by decide) (by decide), hh0],
      by rw [preserve "h1" (by decide) (by decide) (by decide), hh1],
      by rw [preserve "h2" (by decide) (by decide) (by decide), hh2],
      by rw [preserve "h3" (by decide) (by decide) (by decide), hh3],
      by rw [preserve "h4" (by decide) (by decide) (by decide), hh4]⟩
  have hparamsP : BlockParamsAt P p := by
    rcases hparams with ⟨hd, hb, hp, hn, hblk⟩
    exact ⟨by rw [preserve "data" (by decide) (by decide) (by decide), hd],
      by rw [preserve "bitLen" (by decide) (by decide) (by decide), hb],
      by rw [preserve "paddedLen" (by decide) (by decide) (by decide), hp],
      by rw [preserve "numBlocks" (by decide) (by decide) (by decide), hn],
      by rw [preserve "blk" (by decide) (by decide) (by decide), hblk]⟩
  have hwordP : P.get? "wordTableL" = some (wordValue (leftWordRowWord group)) := by
    simpa [P] using leftGroupPreludeStore_word L group
  have hrotP : P.get? "rotTableL" = some (wordValue (leftRotationRowWord group)) := by
    simpa [P] using leftGroupPreludeStore_rotation L group
  have hkP : P.get? "kL" = some (wordValue (leftConstantWord group)) := by
    simpa [P] using leftGroupPreludeStore_constant L group
  obtain ⟨L', hrounds, hline', hbound', hgroup', _, _, _, hmask', hwords', hchain',
      hparams'⟩ :=
    leftRoundForReturns evm X group initial chain p hg hX32 hbound hgroupP hwordP hrotP
      hkP hmaskP hwordsP hlineP hchainP hparamsP
  refine ⟨L', ?_, hline', hbound', hgroup', hmask', hwords', hchain', hparams'⟩
  exact execBlock_append hpre (ExecBlock.consNormal hrounds ExecBlock.nil)

theorem rightGroupBodyReturns {L : Store} (evm : EVM.State) (X : Fin 16 -> UInt256)
    (group : Nat) (initial left : RuntimeLineState) (chain : RuntimeChain) (p : BlockParams)
    (hg : group < 5)
    (hX32 : ∀ i, (X i).toNat < 2 ^ 32) (hbound : RuntimeLineBound initial)
    (hgroup : L.get? "groupR" = some (natValue group))
    (hmask : L.get? "mask32" = some (wordValue mask32Word))
    (hwords : L.get? "words" = some (.array (roundWords X)))
    (hline : RightLineAt L initial) (hleft : LeftLineAt L left)
    (hchain : ChainAt L chain) (hparams : BlockParamsAt L p) :
    ∃ L', ExecBlock config { contract := contract, locals := L } evm rightGroupBody
        (.ok { contract := contract, locals := L' } evm) ∧
      RightLineAt L' (runtimePureRightGroup X group 16 initial) ∧
      RuntimeLineBound (runtimePureRightGroup X group 16 initial) ∧
      L'.get? "groupR" = some (natValue group) ∧
      L'.get? "mask32" = some (wordValue mask32Word) ∧
      L'.get? "words" = some (.array (roundWords X)) ∧
      LeftLineAt L' left ∧
      ChainAt L' chain ∧ BlockParamsAt L' p := by
  let P := rightGroupPreludeStore L group
  have hpre : ExecBlock config { contract := contract, locals := L } evm rightGroupPrelude
      (.ok { contract := contract, locals := P } evm) := by
    simpa [P] using rightGroupPreludeReturns evm group hg hgroup
  have preserve (name : Ident) (hword : ("wordTableR" == name) = false)
      (hrot : ("rotTableR" == name) = false) (hk : ("kR" == name) = false) :
      P.get? name = L.get? name := by
    simpa [P] using rightGroupPreludeStore_get_original L group name hword hrot hk
  have hlineP : RightLineAt P initial := by
    rcases hline with ⟨ha, hb, hc, hd, he⟩
    exact ⟨by rw [preserve "ar" (by decide) (by decide) (by decide), ha],
      by rw [preserve "br" (by decide) (by decide) (by decide), hb],
      by rw [preserve "cr" (by decide) (by decide) (by decide), hc],
      by rw [preserve "dr" (by decide) (by decide) (by decide), hd],
      by rw [preserve "er" (by decide) (by decide) (by decide), he]⟩
  have hgroupP : P.get? "groupR" = some (natValue group) := by
    rw [preserve "groupR" (by decide) (by decide) (by decide), hgroup]
  have hmaskP : P.get? "mask32" = some (wordValue mask32Word) := by
    rw [preserve "mask32" (by decide) (by decide) (by decide), hmask]
  have hwordsP : P.get? "words" = some (.array (roundWords X)) := by
    rw [preserve "words" (by decide) (by decide) (by decide), hwords]
  have hleftP : LeftLineAt P left := by
    rcases hleft with ⟨ha, hb, hc, hd, he⟩
    exact ⟨by rw [preserve "al" (by decide) (by decide) (by decide), ha],
      by rw [preserve "bl" (by decide) (by decide) (by decide), hb],
      by rw [preserve "cl" (by decide) (by decide) (by decide), hc],
      by rw [preserve "dl" (by decide) (by decide) (by decide), hd],
      by rw [preserve "el" (by decide) (by decide) (by decide), he]⟩
  have hchainP : ChainAt P chain := by
    rcases hchain with ⟨hh0, hh1, hh2, hh3, hh4⟩
    exact ⟨by rw [preserve "h0" (by decide) (by decide) (by decide), hh0],
      by rw [preserve "h1" (by decide) (by decide) (by decide), hh1],
      by rw [preserve "h2" (by decide) (by decide) (by decide), hh2],
      by rw [preserve "h3" (by decide) (by decide) (by decide), hh3],
      by rw [preserve "h4" (by decide) (by decide) (by decide), hh4]⟩
  have hparamsP : BlockParamsAt P p := by
    rcases hparams with ⟨hd, hb, hp, hn, hblk⟩
    exact ⟨by rw [preserve "data" (by decide) (by decide) (by decide), hd],
      by rw [preserve "bitLen" (by decide) (by decide) (by decide), hb],
      by rw [preserve "paddedLen" (by decide) (by decide) (by decide), hp],
      by rw [preserve "numBlocks" (by decide) (by decide) (by decide), hn],
      by rw [preserve "blk" (by decide) (by decide) (by decide), hblk]⟩
  have hwordP : P.get? "wordTableR" = some (wordValue (rightWordRowWord group)) := by
    simpa [P] using rightGroupPreludeStore_word L group
  have hrotP : P.get? "rotTableR" = some (wordValue (rightRotationRowWord group)) := by
    simpa [P] using rightGroupPreludeStore_rotation L group
  have hkP : P.get? "kR" = some (wordValue (rightConstantWord group)) := by
    simpa [P] using rightGroupPreludeStore_constant L group
  obtain ⟨L', hrounds, hline', hbound', hgroup', _, _, _, hmask', hwords', hleft',
      hchain', hparams'⟩ :=
    rightRoundForReturns evm X group initial left chain p hg hX32 hbound hgroupP hwordP
      hrotP hkP hmaskP hwordsP hlineP hleftP hchainP hparamsP
  refine ⟨L', ?_, hline', hbound', hgroup', hmask', hwords', hleft', hchain',
    hparams'⟩
  exact execBlock_append hpre (ExecBlock.consNormal hrounds ExecBlock.nil)

end Ripemd160
