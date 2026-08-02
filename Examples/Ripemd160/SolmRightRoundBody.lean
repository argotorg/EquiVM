import Examples.Ripemd160.SolmRoundBody

/-!
# RIPEMD-160 Solm complete right round body

Composition of the reversed Boolean selector and the right arithmetic tail.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Ripemd160

def rightRoundBody : List Stmt := rightFSelection ++ rightRoundTail

def rightRoundOutputStore (L : Store) (X : Fin 16 -> UInt256) (s : RuntimeLineState)
    (group round : Nat) (wordRow rotationRow constant : UInt256) : Store :=
  let selected := X ⟨(runtimeRowEntry wordRow (UInt256.ofNat round)).toNat,
    runtimeRowEntry_lt_sixteen _ _⟩
  let boolF := runtimeRightF group s.b s.c s.d
  rightRoundTailStore (rightFSelectionStore L group s.b s.c s.d) s selected round
    wordRow rotationRow boolF constant

theorem rightRoundBodyReturns {L : Store} (evm : EVM.State) (X : Fin 16 -> UInt256)
    (s : RuntimeLineState) (group round : Nat) (wordRow rotationRow constant : UInt256)
    (hg : group < 5) (hr : round < 16) (hs : RuntimeLineBound s)
    (hX32 : ∀ i, (X i).toNat < 2 ^ 32)
    (hgroup : L.get? "groupR" = some (natValue group))
    (hround : L.get? "roundR" = some (natValue round))
    (hwordRow : L.get? "wordTableR" = some (wordValue wordRow))
    (hrotRow : L.get? "rotTableR" = some (wordValue rotationRow))
    (hconstant : L.get? "kR" = some (wordValue constant))
    (hconstant32 : constant.toNat < 2 ^ 32)
    (hmask : L.get? "mask32" = some (wordValue mask32Word))
    (hwords : L.get? "words" = some (.array (roundWords X)))
    (ha : L.get? "ar" = some (wordValue s.a))
    (hb : L.get? "br" = some (wordValue s.b))
    (hc : L.get? "cr" = some (wordValue s.c))
    (hd : L.get? "dr" = some (wordValue s.d))
    (he : L.get? "er" = some (wordValue s.e)) :
    ExecBlock config { contract := contract, locals := L } evm rightRoundBody
      (.ok { contract := contract, locals :=
        rightRoundOutputStore L X s group round wordRow rotationRow constant } evm) := by
  let S := rightFSelectionStore L group s.b s.c s.d
  have hsel : ExecBlock config { contract := contract, locals := L } evm rightFSelection
      (.ok { contract := contract, locals := S } evm) := by
    simpa [S] using rightFSelectionReturns evm group s.b s.c s.d hg hgroup hb hc hd
      hs.2.1 hs.2.2.1 hs.2.2.2.1
  have preserve (name : Ident)
      (hf : ("fR" == name) = false) (hf0 : ("fR0" == name) = false)
      (hf1 : ("fR1" == name) = false) (hf2 : ("fR2" == name) = false)
      (hf3 : ("fR3" == name) = false) (hf4 : ("fR4" == name) = false) :
      S.get? name = L.get? name := by
    exact rightFSelectionStore_get_original L group s.b s.c s.d hg name
      hf hf0 hf1 hf2 hf3 hf4
  have hroundS : S.get? "roundR" = some (natValue round) := by
    rw [preserve "roundR" (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), hround]
  have hwordRowS : S.get? "wordTableR" = some (wordValue wordRow) := by
    rw [preserve "wordTableR" (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), hwordRow]
  have hrotRowS : S.get? "rotTableR" = some (wordValue rotationRow) := by
    rw [preserve "rotTableR" (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), hrotRow]
  have hconstantS : S.get? "kR" = some (wordValue constant) := by
    rw [preserve "kR" (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), hconstant]
  have hmaskS : S.get? "mask32" = some (wordValue mask32Word) := by
    rw [preserve "mask32" (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), hmask]
  have hwordsS : S.get? "words" = some (.array (roundWords X)) := by
    rw [preserve "words" (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), hwords]
  have haS : S.get? "ar" = some (wordValue s.a) := by
    rw [preserve "ar" (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), ha]
  have hbS : S.get? "br" = some (wordValue s.b) := by
    rw [preserve "br" (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), hb]
  have hcS : S.get? "cr" = some (wordValue s.c) := by
    rw [preserve "cr" (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), hc]
  have hdS : S.get? "dr" = some (wordValue s.d) := by
    rw [preserve "dr" (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), hd]
  have heS : S.get? "er" = some (wordValue s.e) := by
    rw [preserve "er" (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), he]
  have hfS : S.get? "fR" = some (wordValue (runtimeRightF group s.b s.c s.d)) := by
    simpa [S] using rightFSelectionStore_fR L group s.b s.c s.d hg
  have htail := rightRoundTailReturns evm X s group round wordRow rotationRow
    (runtimeRightF group s.b s.c s.d) constant hg hr hs hX32 hroundS hwordRowS hrotRowS
    hconstantS hconstant32 hfS hmaskS hwordsS haS hbS hcS hdS heS
  simpa [rightRoundBody, rightRoundOutputStore, S] using execBlock_append hsel htail

theorem rightRoundOutputStore_line (L : Store) (X : Fin 16 -> UInt256)
    (s : RuntimeLineState) (group round : Nat) (wordRow rotationRow constant : UInt256) :
    let out := rightRoundOutputStore L X s group round wordRow rotationRow constant
    let x := X ⟨(runtimeRowEntry wordRow (UInt256.ofNat round)).toNat,
      runtimeRowEntry_lt_sixteen _ _⟩
    out.get? "ar" = some (wordValue s.e) ∧
    out.get? "br" = some (wordValue
      (sourceRoundNext s x round rotationRow (runtimeRightF group s.b s.c s.d) constant)) ∧
    out.get? "cr" = some (wordValue s.b) ∧
    out.get? "dr" = some (wordValue (runtimeRol32 s.c ⟨10⟩)) ∧
    out.get? "er" = some (wordValue s.d) := by
  dsimp only
  simp only [rightRoundOutputStore, rightRoundTailStore]
  repeat' first
    | rw [store_get_self]
    | rw [store_get_ne _ _ (by decide)]
  simp


def RightLineAt (L : Store) (s : RuntimeLineState) : Prop :=
  L.get? "ar" = some (wordValue s.a) ∧
  L.get? "br" = some (wordValue s.b) ∧
  L.get? "cr" = some (wordValue s.c) ∧
  L.get? "dr" = some (wordValue s.d) ∧
  L.get? "er" = some (wordValue s.e)

theorem rightRoundOutputStore_lineAt (L : Store) (X : Fin 16 -> UInt256)
    (s : RuntimeLineState) (group round : Nat) :
    RightLineAt
      (rightRoundOutputStore L X s group round (rightWordRowWord group)
        (rightRotationRowWord group) (rightConstantWord group))
      (runtimePureRightRound X group round s) := by
  have hline := rightRoundOutputStore_line L X s group round (rightWordRowWord group)
    (rightRotationRowWord group) (rightConstantWord group)
  have heq : sourcePureRound s
      (X ⟨(runtimeRowEntry (rightWordRowWord group) (UInt256.ofNat round)).toNat,
        runtimeRowEntry_lt_sixteen _ _⟩)
      round (rightRotationRowWord group) (runtimeRightF group s.b s.c s.d)
      (rightConstantWord group) = runtimePureRightRound X group round s := by
    simpa [runtimePureRightRound] using sourcePureRound_eq_runtime s
      (X ⟨(runtimeRowEntry (rightWordRowWord group) (UInt256.ofNat round)).toNat,
        runtimeRowEntry_lt_sixteen _ _⟩)
      round (rightWordRowWord group) (rightRotationRowWord group)
      (runtimeRightF group s.b s.c s.d) (rightConstantWord group)
  rw [← heq]
  exact hline

theorem rightRoundOutputStore_context (L : Store) (X : Fin 16 -> UInt256)
    (s : RuntimeLineState) (group round : Nat) (wordRow rotationRow constant : UInt256)
    (hg : group < 5) :
    let out := rightRoundOutputStore L X s group round wordRow rotationRow constant
    out.get? "groupR" = L.get? "groupR" ∧
    out.get? "roundR" = L.get? "roundR" ∧
    out.get? "wordTableR" = L.get? "wordTableR" ∧
    out.get? "rotTableR" = L.get? "rotTableR" ∧
    out.get? "kR" = L.get? "kR" ∧
    out.get? "mask32" = L.get? "mask32" ∧
    out.get? "words" = L.get? "words" ∧
    out.get? "h0" = L.get? "h0" ∧
    out.get? "h1" = L.get? "h1" ∧
    out.get? "h2" = L.get? "h2" ∧
    out.get? "h3" = L.get? "h3" ∧
    out.get? "h4" = L.get? "h4" ∧
    out.get? "al" = L.get? "al" ∧
    out.get? "bl" = L.get? "bl" ∧
    out.get? "cl" = L.get? "cl" ∧
    out.get? "dl" = L.get? "dl" ∧
    out.get? "el" = L.get? "el" ∧
    out.get? "data" = L.get? "data" ∧ out.get? "bitLen" = L.get? "bitLen" ∧
    out.get? "paddedLen" = L.get? "paddedLen" ∧
    out.get? "numBlocks" = L.get? "numBlocks" ∧ out.get? "blk" = L.get? "blk" := by
  dsimp only
  constructor
  · simp only [rightRoundOutputStore, rightRoundTailStore]
    repeat' rw [store_get_ne _ _ (by decide)]
    exact rightFSelectionStore_get_original L group s.b s.c s.d hg "groupR"
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  constructor
  · simp only [rightRoundOutputStore, rightRoundTailStore]
    repeat' rw [store_get_ne _ _ (by decide)]
    exact rightFSelectionStore_get_original L group s.b s.c s.d hg "roundR"
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  constructor
  · simp only [rightRoundOutputStore, rightRoundTailStore]
    repeat' rw [store_get_ne _ _ (by decide)]
    exact rightFSelectionStore_get_original L group s.b s.c s.d hg "wordTableR"
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  constructor
  · simp only [rightRoundOutputStore, rightRoundTailStore]
    repeat' rw [store_get_ne _ _ (by decide)]
    exact rightFSelectionStore_get_original L group s.b s.c s.d hg "rotTableR"
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  constructor
  · simp only [rightRoundOutputStore, rightRoundTailStore]
    repeat' rw [store_get_ne _ _ (by decide)]
    exact rightFSelectionStore_get_original L group s.b s.c s.d hg "kR"
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  constructor
  · simp only [rightRoundOutputStore, rightRoundTailStore]
    repeat' rw [store_get_ne _ _ (by decide)]
    exact rightFSelectionStore_get_original L group s.b s.c s.d hg "mask32"
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  constructor
  · simp only [rightRoundOutputStore, rightRoundTailStore]
    repeat' rw [store_get_ne _ _ (by decide)]
    exact rightFSelectionStore_get_original L group s.b s.c s.d hg "words"
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  constructor
  · simp only [rightRoundOutputStore, rightRoundTailStore]
    repeat' rw [store_get_ne _ _ (by decide)]
    exact rightFSelectionStore_get_original L group s.b s.c s.d hg "h0"
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  constructor
  · simp only [rightRoundOutputStore, rightRoundTailStore]
    repeat' rw [store_get_ne _ _ (by decide)]
    exact rightFSelectionStore_get_original L group s.b s.c s.d hg "h1"
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  constructor
  · simp only [rightRoundOutputStore, rightRoundTailStore]
    repeat' rw [store_get_ne _ _ (by decide)]
    exact rightFSelectionStore_get_original L group s.b s.c s.d hg "h2"
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  constructor
  · simp only [rightRoundOutputStore, rightRoundTailStore]
    repeat' rw [store_get_ne _ _ (by decide)]
    exact rightFSelectionStore_get_original L group s.b s.c s.d hg "h3"
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  constructor
  · simp only [rightRoundOutputStore, rightRoundTailStore]
    repeat' rw [store_get_ne _ _ (by decide)]
    exact rightFSelectionStore_get_original L group s.b s.c s.d hg "h4"
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  constructor
  · simp only [rightRoundOutputStore, rightRoundTailStore]
    repeat' rw [store_get_ne _ _ (by decide)]
    exact rightFSelectionStore_get_original L group s.b s.c s.d hg "al"
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  constructor
  · simp only [rightRoundOutputStore, rightRoundTailStore]
    repeat' rw [store_get_ne _ _ (by decide)]
    exact rightFSelectionStore_get_original L group s.b s.c s.d hg "bl"
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  constructor
  · simp only [rightRoundOutputStore, rightRoundTailStore]
    repeat' rw [store_get_ne _ _ (by decide)]
    exact rightFSelectionStore_get_original L group s.b s.c s.d hg "cl"
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  constructor
  · simp only [rightRoundOutputStore, rightRoundTailStore]
    repeat' rw [store_get_ne _ _ (by decide)]
    exact rightFSelectionStore_get_original L group s.b s.c s.d hg "dl"
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  constructor
  · simp only [rightRoundOutputStore, rightRoundTailStore]
    repeat' rw [store_get_ne _ _ (by decide)]
    exact rightFSelectionStore_get_original L group s.b s.c s.d hg "el"
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  constructor
  · simp only [rightRoundOutputStore, rightRoundTailStore]
    repeat' rw [store_get_ne _ _ (by decide)]
    exact rightFSelectionStore_get_original L group s.b s.c s.d hg "data"
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  constructor
  · simp only [rightRoundOutputStore, rightRoundTailStore]
    repeat' rw [store_get_ne _ _ (by decide)]
    exact rightFSelectionStore_get_original L group s.b s.c s.d hg "bitLen"
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  constructor
  · simp only [rightRoundOutputStore, rightRoundTailStore]
    repeat' rw [store_get_ne _ _ (by decide)]
    exact rightFSelectionStore_get_original L group s.b s.c s.d hg "paddedLen"
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  constructor
  · simp only [rightRoundOutputStore, rightRoundTailStore]
    repeat' rw [store_get_ne _ _ (by decide)]
    exact rightFSelectionStore_get_original L group s.b s.c s.d hg "numBlocks"
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · simp only [rightRoundOutputStore, rightRoundTailStore]
    repeat' rw [store_get_ne _ _ (by decide)]
    exact rightFSelectionStore_get_original L group s.b s.c s.d hg "blk"
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

end Ripemd160
