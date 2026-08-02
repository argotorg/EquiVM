import Examples.Ripemd160.SolmRecombine

/-!
# RIPEMD-160 Solm compression block

Composition of parsing, both eighty-round compression lines, and chain recombination for one
source-level message block.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Ripemd160

def sourceBlockWords (data : ByteArray) (block : Nat) : Fin 16 -> UInt256 :=
  fun i => UInt256.ofNat (Model.blockWord data block i.val)

theorem sourceBlockWords_bound (data : ByteArray) (block : Nat) :
    ∀ i, (sourceBlockWords data block i).toNat < 2 ^ 32 := by
  intro i
  rw [sourceBlockWords, ulit_toNat']
  · exact modelBlockWord_lt data block i.val
  · exact lt_trans (modelBlockWord_lt data block i.val) (by
      rw [UInt256.size]
      norm_num)

theorem parserWords_zero_eq_roundWords (base : Fin 16 -> UInt256)
    (data : ByteArray) (block : Nat) :
    parserWords base data block 0 = roundWords base := by
  apply List.ext_getElem
  · simp
  · intro i hleft hright
    unfold parserWords roundWords
    simp only [List.getElem_ofFn]
    simp

theorem parserWords_complete_eq_roundWords (base : Fin 16 -> UInt256)
    (data : ByteArray) (block : Nat) :
    parserWords base data block 16 = roundWords (sourceBlockWords data block) := by
  apply List.ext_getElem
  · simp
  · intro i hleft hright
    unfold parserWords roundWords sourceBlockWords
    simp only [List.getElem_ofFn]
    simp [show i < 16 by simpa using hleft]

def compressionBlockBody : List Stmt :=
  [parserFor] ++ (leftLineInit ++ ([leftGroupFor] ++
    (rightLineInit ++ ([rightGroupFor] ++ recombineBody))))

theorem compressionBlockReturns {L : Store} (evm : EVM.State)
    (base : Fin 16 -> UInt256) (data : ByteArray) (block : Nat) (h : RuntimeChain)
    (hsmall : data.size ≤ maxFallbackCalldataSize)
    (hblock : block < Model.paddedLength data.size / 64)
    (hchainBound : RuntimeChainBound h)
    (hdata : L.get? "data" = some (.bytes data))
    (hbit : L.get? "bitLen" = some (natValue (data.size * 8)))
    (hpad : L.get? "paddedLen" = some (natValue (Model.paddedLength data.size)))
    (hnum : L.get? "numBlocks" =
      some (natValue (Model.paddedLength data.size / 64)))
    (hblk : L.get? "blk" = some (natValue block))
    (hwords : L.get? "words" = some (.array (roundWords base)))
    (hmask : L.get? "mask32" = some (wordValue mask32Word))
    (hchain : ChainAt L h) :
    let X := sourceBlockWords data block
    ∃ L', ExecBlock config { contract := contract, locals := L } evm compressionBlockBody
        (.ok { contract := contract, locals := L' } evm) ∧
      ChainAt L' (runtimeCompressChain X h) ∧
      RuntimeChainBound (runtimeCompressChain X h) ∧
      L'.get? "mask32" = some (wordValue mask32Word) ∧
      L'.get? "words" = some (.array (roundWords X)) ∧
      BlockParamsAt L'
        { data := data, blocks := Model.paddedLength data.size / 64, block := block } := by
  dsimp only
  let X := sourceBlockWords data block
  let p : BlockParams :=
    { data := data, blocks := Model.paddedLength data.size / 64, block := block }
  have hwords0 : L.get? "words" = some (.array (parserWords base data block 0)) := by
    rw [parserWords_zero_eq_roundWords, hwords]
  obtain ⟨P, hparse, hdataP, hbitP, hpadP, hnumP, hblkP, hwordsP0,
      hmaskP, hchainP⟩ :=
    parserForReturns evm base data block h hsmall hblock hdata hbit hpad hnum hblk
      hwords0 hmask hchain
  have hwordsP : P.get? "words" = some (.array (roundWords X)) := by
    simpa [X, parserWords_complete_eq_roundWords] using hwordsP0
  have hparamsP : BlockParamsAt P p :=
    ⟨hdataP, hbitP, hpadP, hnumP, hblkP⟩
  obtain ⟨hleftInit, hleft0, hchainP1, hmaskP1, hwordsP1, hparamsP1⟩ :=
    leftLineInitReturns evm h X p hchainP hmaskP hwordsP hparamsP
  let P1 := leftLineInitStore P h
  have hlineBound0 := hchainBound.line h
  obtain ⟨P2, hleftLoop, hleft, hleftBound, hmaskP2, hwordsP2, hchainP2,
      hparamsP2⟩ :=
    leftGroupForReturns evm X (runtimeLineOfChain h) h p
      (sourceBlockWords_bound data block) hlineBound0 hmaskP1 hwordsP1 hleft0
      hchainP1 hparamsP1
  obtain ⟨hrightInit, hright0, hleftP3, hchainP3, hmaskP3, hwordsP3, hparamsP3⟩ :=
    rightLineInitReturns evm h X (runtimePureLeftLine X 5 (runtimeLineOfChain h)) p
      hchainP2 hleft hmaskP2 hwordsP2 hparamsP2
  let P3 := rightLineInitStore P2 h
  obtain ⟨P4, hrightLoop, hright, hrightBound, hmaskP4, hwordsP4, hleftP4,
      hchainP4, hparamsP4⟩ :=
    rightGroupForReturns evm X (runtimeLineOfChain h)
      (runtimePureLeftLine X 5 (runtimeLineOfChain h)) h p
      (sourceBlockWords_bound data block) hlineBound0 hmaskP3 hwordsP3 hright0
      hleftP3 hchainP3 hparamsP3
  let left := runtimePureLeftLine X 5 (runtimeLineOfChain h)
  let right := runtimePureRightLine X 5 (runtimeLineOfChain h)
  obtain ⟨hrecombine, hchainNext, hchainNextBound, hmaskNext, hwordsNext,
      hparamsNext⟩ :=
    recombineReturns evm h left right X p hchainP4 hleftP4 hright hchainBound
      hleftBound hrightBound hmaskP4 hwordsP4 hparamsP4
  let P5 := recombineStore P4 (runtimeRecombineChain h left right)
  have hexec : ExecBlock config { contract := contract, locals := L } evm
      compressionBlockBody (.ok { contract := contract, locals := P5 } evm) := by
    exact execBlock_append (ExecBlock.consNormal hparse ExecBlock.nil) <|
      execBlock_append hleftInit <|
      execBlock_append (ExecBlock.consNormal hleftLoop ExecBlock.nil) <|
      execBlock_append hrightInit <|
      execBlock_append (ExecBlock.consNormal hrightLoop ExecBlock.nil) hrecombine
  refine ⟨P5, hexec, ?_, ?_, hmaskNext, hwordsNext, hparamsNext⟩
  · simpa [P5, left, right, X, runtimeCompressChain] using hchainNext
  · simpa [left, right, X, runtimeCompressChain] using hchainNextBound

end Ripemd160
