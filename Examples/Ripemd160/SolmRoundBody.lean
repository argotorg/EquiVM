import Examples.Ripemd160.SolmRightRoundStep

/-!
# RIPEMD-160 Solm complete round bodies

Composition of explicit Boolean selection and arithmetic tails for one authored compression round.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Ripemd160

def leftRoundBody : List Stmt := leftFSelection ++ leftRoundTail

def leftRoundOutputStore (L : Store) (X : Fin 16 -> UInt256) (s : RuntimeLineState)
    (group round : Nat) (wordRow rotationRow constant : UInt256) : Store :=
  let selected := X ⟨(runtimeRowEntry wordRow (UInt256.ofNat round)).toNat,
    runtimeRowEntry_lt_sixteen _ _⟩
  let boolF := runtimeLeftF group s.b s.c s.d
  leftRoundTailStore (leftFSelectionStore L group s.b s.c s.d) s selected round
    wordRow rotationRow boolF constant

theorem leftRoundBodyReturns {L : Store} (evm : EVM.State) (X : Fin 16 -> UInt256)
    (s : RuntimeLineState) (group round : Nat) (wordRow rotationRow constant : UInt256)
    (hg : group < 5) (hr : round < 16) (hs : RuntimeLineBound s)
    (hX32 : ∀ i, (X i).toNat < 2 ^ 32)
    (hgroup : L.get? "groupL" = some (natValue group))
    (hround : L.get? "roundL" = some (natValue round))
    (hwordRow : L.get? "wordTableL" = some (wordValue wordRow))
    (hrotRow : L.get? "rotTableL" = some (wordValue rotationRow))
    (hconstant : L.get? "kL" = some (wordValue constant))
    (hconstant32 : constant.toNat < 2 ^ 32)
    (hmask : L.get? "mask32" = some (wordValue mask32Word))
    (hwords : L.get? "words" = some (.array (roundWords X)))
    (ha : L.get? "al" = some (wordValue s.a))
    (hb : L.get? "bl" = some (wordValue s.b))
    (hc : L.get? "cl" = some (wordValue s.c))
    (hd : L.get? "dl" = some (wordValue s.d))
    (he : L.get? "el" = some (wordValue s.e)) :
    ExecBlock config { contract := contract, locals := L } evm leftRoundBody
      (.ok { contract := contract, locals :=
        leftRoundOutputStore L X s group round wordRow rotationRow constant } evm) := by
  let S := leftFSelectionStore L group s.b s.c s.d
  have hsel : ExecBlock config { contract := contract, locals := L } evm leftFSelection
      (.ok { contract := contract, locals := S } evm) := by
    simpa [S] using leftFSelectionReturns evm group s.b s.c s.d hg hgroup hb hc hd
      hs.2.1 hs.2.2.1 hs.2.2.2.1
  have preserve (name : Ident)
      (hf : ("fL" == name) = false) (hf0 : ("fL0" == name) = false)
      (hf1 : ("fL1" == name) = false) (hf2 : ("fL2" == name) = false)
      (hf3 : ("fL3" == name) = false) (hf4 : ("fL4" == name) = false) :
      S.get? name = L.get? name := by
    exact leftFSelectionStore_get_original L group s.b s.c s.d hg name
      hf hf0 hf1 hf2 hf3 hf4
  have hroundS : S.get? "roundL" = some (natValue round) := by
    rw [preserve "roundL" (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), hround]
  have hwordRowS : S.get? "wordTableL" = some (wordValue wordRow) := by
    rw [preserve "wordTableL" (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), hwordRow]
  have hrotRowS : S.get? "rotTableL" = some (wordValue rotationRow) := by
    rw [preserve "rotTableL" (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), hrotRow]
  have hconstantS : S.get? "kL" = some (wordValue constant) := by
    rw [preserve "kL" (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), hconstant]
  have hmaskS : S.get? "mask32" = some (wordValue mask32Word) := by
    rw [preserve "mask32" (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), hmask]
  have hwordsS : S.get? "words" = some (.array (roundWords X)) := by
    rw [preserve "words" (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), hwords]
  have haS : S.get? "al" = some (wordValue s.a) := by
    rw [preserve "al" (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), ha]
  have hbS : S.get? "bl" = some (wordValue s.b) := by
    rw [preserve "bl" (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), hb]
  have hcS : S.get? "cl" = some (wordValue s.c) := by
    rw [preserve "cl" (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), hc]
  have hdS : S.get? "dl" = some (wordValue s.d) := by
    rw [preserve "dl" (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), hd]
  have heS : S.get? "el" = some (wordValue s.e) := by
    rw [preserve "el" (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), he]
  have hfS : S.get? "fL" = some (wordValue (runtimeLeftF group s.b s.c s.d)) := by
    simpa [S] using leftFSelectionStore_fL L group s.b s.c s.d hg
  have htail := leftRoundTailReturns evm X s group round wordRow rotationRow
    (runtimeLeftF group s.b s.c s.d) constant hg hr hs hX32 hroundS hwordRowS hrotRowS
    hconstantS hconstant32 hfS hmaskS hwordsS haS hbS hcS hdS heS
  simpa [leftRoundBody, leftRoundOutputStore, S] using execBlock_append hsel htail

theorem leftRoundOutputStore_line (L : Store) (X : Fin 16 -> UInt256)
    (s : RuntimeLineState) (group round : Nat) (wordRow rotationRow constant : UInt256) :
    let out := leftRoundOutputStore L X s group round wordRow rotationRow constant
    let x := X ⟨(runtimeRowEntry wordRow (UInt256.ofNat round)).toNat,
      runtimeRowEntry_lt_sixteen _ _⟩
    out.get? "al" = some (wordValue s.e) ∧
    out.get? "bl" = some (wordValue
      (sourceRoundNext s x round rotationRow (runtimeLeftF group s.b s.c s.d) constant)) ∧
    out.get? "cl" = some (wordValue s.b) ∧
    out.get? "dl" = some (wordValue (runtimeRol32 s.c ⟨10⟩)) ∧
    out.get? "el" = some (wordValue s.d) := by
  dsimp only
  simp only [leftRoundOutputStore, leftRoundTailStore]
  repeat' first
    | rw [store_get_self]
    | rw [store_get_ne _ _ (by decide)]
  simp

def LeftLineAt (L : Store) (s : RuntimeLineState) : Prop :=
  L.get? "al" = some (wordValue s.a) ∧
  L.get? "bl" = some (wordValue s.b) ∧
  L.get? "cl" = some (wordValue s.c) ∧
  L.get? "dl" = some (wordValue s.d) ∧
  L.get? "el" = some (wordValue s.e)

theorem leftRoundOutputStore_lineAt (L : Store) (X : Fin 16 -> UInt256)
    (s : RuntimeLineState) (group round : Nat) :
    LeftLineAt
      (leftRoundOutputStore L X s group round (leftWordRowWord group)
        (leftRotationRowWord group) (leftConstantWord group))
      (runtimePureLeftRound X group round s) := by
  have hline := leftRoundOutputStore_line L X s group round (leftWordRowWord group)
    (leftRotationRowWord group) (leftConstantWord group)
  have heq : sourcePureRound s
      (X ⟨(runtimeRowEntry (leftWordRowWord group) (UInt256.ofNat round)).toNat,
        runtimeRowEntry_lt_sixteen _ _⟩)
      round (leftRotationRowWord group) (runtimeLeftF group s.b s.c s.d)
      (leftConstantWord group) = runtimePureLeftRound X group round s := by
    simpa [runtimePureLeftRound] using sourcePureRound_eq_runtime s
      (X ⟨(runtimeRowEntry (leftWordRowWord group) (UInt256.ofNat round)).toNat,
        runtimeRowEntry_lt_sixteen _ _⟩)
      round (leftWordRowWord group) (leftRotationRowWord group)
      (runtimeLeftF group s.b s.c s.d) (leftConstantWord group)
  rw [← heq]
  exact hline

theorem leftRoundOutputStore_context (L : Store) (X : Fin 16 -> UInt256)
    (s : RuntimeLineState) (group round : Nat) (wordRow rotationRow constant : UInt256)
    (hg : group < 5) :
    let out := leftRoundOutputStore L X s group round wordRow rotationRow constant
    out.get? "groupL" = L.get? "groupL" ∧
    out.get? "roundL" = L.get? "roundL" ∧
    out.get? "wordTableL" = L.get? "wordTableL" ∧
    out.get? "rotTableL" = L.get? "rotTableL" ∧
    out.get? "kL" = L.get? "kL" ∧
    out.get? "mask32" = L.get? "mask32" ∧
    out.get? "words" = L.get? "words" ∧
    out.get? "h0" = L.get? "h0" ∧
    out.get? "h1" = L.get? "h1" ∧
    out.get? "h2" = L.get? "h2" ∧
    out.get? "h3" = L.get? "h3" ∧
    out.get? "h4" = L.get? "h4" ∧
    out.get? "data" = L.get? "data" ∧ out.get? "bitLen" = L.get? "bitLen" ∧
    out.get? "paddedLen" = L.get? "paddedLen" ∧
    out.get? "numBlocks" = L.get? "numBlocks" ∧ out.get? "blk" = L.get? "blk" := by
  dsimp only
  constructor
  · simp only [leftRoundOutputStore, leftRoundTailStore]
    repeat' rw [store_get_ne _ _ (by decide)]
    exact leftFSelectionStore_get_original L group s.b s.c s.d hg "groupL"
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  constructor
  · simp only [leftRoundOutputStore, leftRoundTailStore]
    repeat' rw [store_get_ne _ _ (by decide)]
    exact leftFSelectionStore_get_original L group s.b s.c s.d hg "roundL"
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  constructor
  · simp only [leftRoundOutputStore, leftRoundTailStore]
    repeat' rw [store_get_ne _ _ (by decide)]
    exact leftFSelectionStore_get_original L group s.b s.c s.d hg "wordTableL"
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  constructor
  · simp only [leftRoundOutputStore, leftRoundTailStore]
    repeat' rw [store_get_ne _ _ (by decide)]
    exact leftFSelectionStore_get_original L group s.b s.c s.d hg "rotTableL"
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  constructor
  · simp only [leftRoundOutputStore, leftRoundTailStore]
    repeat' rw [store_get_ne _ _ (by decide)]
    exact leftFSelectionStore_get_original L group s.b s.c s.d hg "kL"
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  constructor
  · simp only [leftRoundOutputStore, leftRoundTailStore]
    repeat' rw [store_get_ne _ _ (by decide)]
    exact leftFSelectionStore_get_original L group s.b s.c s.d hg "mask32"
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  constructor
  · simp only [leftRoundOutputStore, leftRoundTailStore]
    repeat' rw [store_get_ne _ _ (by decide)]
    exact leftFSelectionStore_get_original L group s.b s.c s.d hg "words"
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  constructor
  · simp only [leftRoundOutputStore, leftRoundTailStore]
    repeat' rw [store_get_ne _ _ (by decide)]
    exact leftFSelectionStore_get_original L group s.b s.c s.d hg "h0"
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  constructor
  · simp only [leftRoundOutputStore, leftRoundTailStore]
    repeat' rw [store_get_ne _ _ (by decide)]
    exact leftFSelectionStore_get_original L group s.b s.c s.d hg "h1"
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  constructor
  · simp only [leftRoundOutputStore, leftRoundTailStore]
    repeat' rw [store_get_ne _ _ (by decide)]
    exact leftFSelectionStore_get_original L group s.b s.c s.d hg "h2"
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  constructor
  · simp only [leftRoundOutputStore, leftRoundTailStore]
    repeat' rw [store_get_ne _ _ (by decide)]
    exact leftFSelectionStore_get_original L group s.b s.c s.d hg "h3"
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  constructor
  · simp only [leftRoundOutputStore, leftRoundTailStore]
    repeat' rw [store_get_ne _ _ (by decide)]
    exact leftFSelectionStore_get_original L group s.b s.c s.d hg "h4"
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  constructor
  · simp only [leftRoundOutputStore, leftRoundTailStore]
    repeat' rw [store_get_ne _ _ (by decide)]
    exact leftFSelectionStore_get_original L group s.b s.c s.d hg "data"
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  constructor
  · simp only [leftRoundOutputStore, leftRoundTailStore]
    repeat' rw [store_get_ne _ _ (by decide)]
    exact leftFSelectionStore_get_original L group s.b s.c s.d hg "bitLen"
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  constructor
  · simp only [leftRoundOutputStore, leftRoundTailStore]
    repeat' rw [store_get_ne _ _ (by decide)]
    exact leftFSelectionStore_get_original L group s.b s.c s.d hg "paddedLen"
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  constructor
  · simp only [leftRoundOutputStore, leftRoundTailStore]
    repeat' rw [store_get_ne _ _ (by decide)]
    exact leftFSelectionStore_get_original L group s.b s.c s.d hg "numBlocks"
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · simp only [leftRoundOutputStore, leftRoundTailStore]
    repeat' rw [store_get_ne _ _ (by decide)]
    exact leftFSelectionStore_get_original L group s.b s.c s.d hg "blk"
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem RuntimeLineBound.sourcePureRound (s : RuntimeLineState) (x : UInt256) (round : Nat)
    (rotationRow boolF constant : UInt256) (hs : RuntimeLineBound s) :
    RuntimeLineBound (sourcePureRound s x round rotationRow boolF constant) := by
  rcases hs with ⟨ha, hb, hc, hd, he⟩
  have hnext : (sourceRoundNext s x round rotationRow boolF constant).toNat < 2 ^ 32 := by
    unfold sourceRoundNext
    rw [u256_land_comm]
    exact runtimeMask32_lt _
  have hrot : (runtimeRol32 s.c ⟨10⟩).toNat < 2 ^ 32 := by
    unfold runtimeRol32
    exact runtimeMask32_lt _
  exact ⟨he, hnext, hb, hrot, hd⟩

end Ripemd160
