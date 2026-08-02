import Examples.Ripemd160.SolmBlock
import Examples.Ripemd160.HashRunPure

/-!
# RIPEMD-160 Solm message-block loop

The source outer loop threads the chaining state across every padded 64-byte block.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Ripemd160

def sourceWordsBefore (data : ByteArray) : Nat -> Fin 16 -> UInt256
  | 0 => fun _ => UInt256.ofNat 0
  | block + 1 => sourceBlockWords data block

def sourceChainRun (data : ByteArray) : Nat -> RuntimeChain -> RuntimeChain
  | 0, h => h
  | block + 1, h =>
      runtimeCompressChain (sourceBlockWords data block) (sourceChainRun data block h)

theorem sourceChainRun_rep (data : ByteArray) (blocks : Nat) :
    RuntimeChainRep (sourceChainRun data blocks runtimeInitialChain)
      (Model.stateAfter data blocks) := by
  induction blocks with
  | zero => exact runtimeInitial_rep
  | succ block ih =>
      have hX : ∀ i, (sourceBlockWords data block i).toNat =
          Model.blockWord data block i.val := by
        intro i
        rw [sourceBlockWords, ulit_toNat']
        exact lt_trans (modelBlockWord_lt data block i.val) (by
          rw [UInt256.size]
          norm_num)
      have hnext := runtimeCompressChain_rep data block (sourceBlockWords data block)
        (sourceChainRun data block runtimeInitialChain) (Model.stateAfter data block)
        hX ih (Model.stateAfter_bound data block)
      simpa [sourceChainRun, Model.stateAfter] using hnext

theorem sourceChainRun_final_rep (data : ByteArray) :
    RuntimeChainRep
      (sourceChainRun data (Model.paddedLength data.size / 64) runtimeInitialChain)
      (Model.finalState data) := by
  rw [← Model.stateAfter_blockCount]
  exact sourceChainRun_rep data _

def blockLoopInit : List Stmt := [.letDecl "blk" uint256Ty (.intLit 0)]
def blockLoopCond : Expr := .binary .lt (.var "blk") (.var "numBlocks")
def blockLoopPost : List Stmt :=
  [.assign .localVar { base := "blk" } (.binary .add (.var "blk") (.intLit 1))]
def compressionBlockFor : Stmt :=
  .for blockLoopInit blockLoopCond blockLoopPost compressionBlockBody

theorem compressionBlockForReturns {L : Store} (evm : EVM.State)
    (data : ByteArray) (initial : RuntimeChain)
    (hsmall : data.size ≤ maxFallbackCalldataSize)
    (hinitialBound : RuntimeChainBound initial)
    (hdata : L.get? "data" = some (.bytes data))
    (hbit : L.get? "bitLen" = some (natValue (data.size * 8)))
    (hpad : L.get? "paddedLen" = some (natValue (Model.paddedLength data.size)))
    (hnum : L.get? "numBlocks" =
      some (natValue (Model.paddedLength data.size / 64)))
    (hwords : L.get? "words" =
      some (.array (roundWords (sourceWordsBefore data 0))))
    (hmask : L.get? "mask32" = some (wordValue mask32Word))
    (hchain : ChainAt L initial) :
    let blocks := Model.paddedLength data.size / 64
    ∃ L', ExecStmt config { contract := contract, locals := L } evm compressionBlockFor
        (.ok { contract := contract, locals := L' } evm) ∧
      ChainAt L' (sourceChainRun data blocks initial) ∧
      RuntimeChainBound (sourceChainRun data blocks initial) ∧
      L'.get? "data" = some (.bytes data) ∧
      L'.get? "bitLen" = some (natValue (data.size * 8)) ∧
      L'.get? "paddedLen" = some (natValue (Model.paddedLength data.size)) ∧
      L'.get? "numBlocks" = some (natValue blocks) ∧
      L'.get? "blk" = some (natValue blocks) ∧
      L'.get? "words" =
        some (.array (roundWords (sourceWordsBefore data blocks))) ∧
      L'.get? "mask32" = some (wordValue mask32Word) := by
  dsimp only
  let blocks := Model.paddedLength data.size / 64
  let P : Nat -> Store -> Prop := fun v S =>
    ∃ block, block + v = blocks ∧
      ChainAt S (sourceChainRun data block initial) ∧
      RuntimeChainBound (sourceChainRun data block initial) ∧
      S.get? "data" = some (.bytes data) ∧
      S.get? "bitLen" = some (natValue (data.size * 8)) ∧
      S.get? "paddedLen" = some (natValue (Model.paddedLength data.size)) ∧
      S.get? "numBlocks" = some (natValue blocks) ∧
      S.get? "blk" = some (natValue block) ∧
      S.get? "words" = some (.array (roundWords (sourceWordsBefore data block))) ∧
      S.get? "mask32" = some (wordValue mask32Word)
  have hfalse : ∀ S, P 0 S ->
      evalExpr? config { contract := contract, locals := S } evm blockLoopCond =
        .ok (.bool false) := by
    intro S hP
    rcases hP with ⟨block, hv, _, _, _, _, _, hnumS, hblkS, _⟩
    have he := evalNatLt (evm := evm) (evalNatVar hblkS) (evalNatVar hnumS)
    have hb : block = blocks := by omega
    simpa [blockLoopCond, hb] using he
  have htrue : ∀ v S, P (v + 1) S ->
      evalExpr? config { contract := contract, locals := S } evm blockLoopCond =
        .ok (.bool true) := by
    intro v S hP
    rcases hP with ⟨block, hv, _, _, _, _, _, hnumS, hblkS, _⟩
    have he := evalNatLt (evm := evm) (evalNatVar hblkS) (evalNatVar hnumS)
    have hb : block < blocks := by omega
    simpa [blockLoopCond, decide_eq_true hb] using he
  have hstep : ∀ v S, P (v + 1) S ->
      ∃ S1, ExecBlock config { contract := contract, locals := S } evm
          compressionBlockBody (.ok { contract := contract, locals := S1 } evm) ∧
        ∃ S', ExecBlock config { contract := contract, locals := S1 } evm
          blockLoopPost (.ok { contract := contract, locals := S' } evm) ∧ P v S' := by
    intro v S hP
    rcases hP with ⟨block, hv, hchainS, hboundS, hdataS, hbitS, hpadS,
      hnumS, hblkS, hwordsS, hmaskS⟩
    have hblock : block < Model.paddedLength data.size / 64 := by
      simpa [blocks] using (show block < blocks by omega)
    obtain ⟨S1, hbody, hchain1, hbound1, hmask1, hwords1, hparams1⟩ :=
      compressionBlockReturns evm (sourceWordsBefore data block) data block
        (sourceChainRun data block initial) hsmall hblock hboundS hdataS hbitS hpadS
        (by simpa [blocks] using hnumS) hblkS hwordsS hmaskS hchainS
    let S' := S1.insert "blk" (natValue (block + 1))
    have hpostEval : evalExpr? config { contract := contract, locals := S1 } evm
        (.binary .add (.var "blk") (.intLit 1)) = .ok (natValue (block + 1)) :=
      evalNatAdd (evalNatVar hparams1.2.2.2.2) (by simp [evalExpr?, natValue, pure])
    have hpost : ExecBlock config { contract := contract, locals := S1 } evm blockLoopPost
        (.ok { contract := contract, locals := S' } evm) :=
      ExecBlock.consNormal (execAssignLocal hparams1.2.2.2.2 hpostEval) ExecBlock.nil
    have preserve (name : Ident) (hne : ("blk" == name) = false) :
        S'.get? name = S1.get? name := by simp only [S']; rw [store_get_ne _ _ hne]
    have hchain' : ChainAt S' (sourceChainRun data (block + 1) initial) := by
      change ChainAt S'
        (runtimeCompressChain (sourceBlockWords data block)
          (sourceChainRun data block initial))
      rcases hchain1 with ⟨hh0, hh1, hh2, hh3, hh4⟩
      exact ⟨by rw [preserve "h0" (by decide), hh0],
        by rw [preserve "h1" (by decide), hh1],
        by rw [preserve "h2" (by decide), hh2],
        by rw [preserve "h3" (by decide), hh3],
        by rw [preserve "h4" (by decide), hh4]⟩
    have hdata' : S'.get? "data" = some (.bytes data) := by
      rw [preserve "data" (by decide), hparams1.1]
    have hbit' : S'.get? "bitLen" = some (natValue (data.size * 8)) := by
      rw [preserve "bitLen" (by decide), hparams1.2.1]
    have hpad' : S'.get? "paddedLen" =
        some (natValue (Model.paddedLength data.size)) := by
      rw [preserve "paddedLen" (by decide), hparams1.2.2.1]
    have hnum' : S'.get? "numBlocks" = some (natValue blocks) := by
      rw [preserve "numBlocks" (by decide), hparams1.2.2.2.1]
    have hwords' : S'.get? "words" =
        some (.array (roundWords (sourceWordsBefore data (block + 1)))) := by
      rw [preserve "words" (by decide)]
      simpa [sourceWordsBefore] using hwords1
    have hmask' : S'.get? "mask32" = some (wordValue mask32Word) := by
      rw [preserve "mask32" (by decide), hmask1]
    refine ⟨S1, hbody, S', hpost, block + 1, by omega, hchain', ?_, hdata',
      hbit', hpad', hnum', by simp [S'], hwords', hmask'⟩
    simpa only [sourceChainRun] using hbound1
  let L0 := L.insert "blk" (natValue 0)
  have hinit : ExecBlock config { contract := contract, locals := L } evm blockLoopInit
      (.ok { contract := contract, locals := L0 } evm) := by
    exact ExecBlock.consNormal (ExecStmt.letDecl
      (show evalExpr? config { contract := contract, locals := L } evm (.intLit 0) =
        .ok (natValue 0) by simp [evalExpr?, natValue, pure])) ExecBlock.nil
  have preserve0 (name : Ident) (hne : ("blk" == name) = false) :
      L0.get? name = L.get? name := by simp only [L0]; rw [store_get_ne _ _ hne]
  have hchain0 : ChainAt L0 (sourceChainRun data 0 initial) := by
    change ChainAt L0 initial
    rcases hchain with ⟨hh0, hh1, hh2, hh3, hh4⟩
    exact ⟨by rw [preserve0 "h0" (by decide), hh0],
      by rw [preserve0 "h1" (by decide), hh1],
      by rw [preserve0 "h2" (by decide), hh2],
      by rw [preserve0 "h3" (by decide), hh3],
      by rw [preserve0 "h4" (by decide), hh4]⟩
  have hP0 : P blocks L0 :=
    ⟨0, by omega, hchain0, by simpa [sourceChainRun] using hinitialBound,
      by rw [preserve0 "data" (by decide), hdata],
      by rw [preserve0 "bitLen" (by decide), hbit],
      by rw [preserve0 "paddedLen" (by decide), hpad],
      by rw [preserve0 "numBlocks" (by decide), hnum],
      by simp [L0], by rw [preserve0 "words" (by decide), hwords],
      by rw [preserve0 "mask32" (by decide), hmask]⟩
  obtain ⟨L', hloop, hfinal⟩ := execFor_var P hfalse htrue hstep blocks L0 hP0
  rcases hfinal with ⟨block, hv, hchain', hbound', hd, hb, hp, hn, hblk',
    hwords', hm⟩
  have hblock : block = blocks := by omega
  subst block
  exact ⟨L', ExecStmt.for hinit hloop, hchain', hbound', hd, hb, hp, hn, hblk',
    hwords', hm⟩

end Ripemd160
