import Examples.Ripemd160.SolmGroupLoop
import Examples.Ripemd160.ParserArithmetic

/-!
# RIPEMD-160 Solm block initialization

Initialization of the two parallel compression lines from the current chaining words.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Ripemd160

def RuntimeChainBound (h : RuntimeChain) : Prop :=
  h.h0.toNat < 2 ^ 32 ∧ h.h1.toNat < 2 ^ 32 ∧ h.h2.toNat < 2 ^ 32 ∧
  h.h3.toNat < 2 ^ 32 ∧ h.h4.toNat < 2 ^ 32

theorem RuntimeChainBound.line (h : RuntimeChain) (hh : RuntimeChainBound h) :
    RuntimeLineBound (runtimeLineOfChain h) := by
  simpa [RuntimeChainBound, RuntimeLineBound, runtimeLineOfChain] using hh

theorem runtimeInitialChain_bound : RuntimeChainBound runtimeInitialChain := by
  change 0x67452301 < 2 ^ 32 ∧ 0xefcdab89 < 2 ^ 32 ∧
    0x98badcfe < 2 ^ 32 ∧ 0x10325476 < 2 ^ 32 ∧ 0xc3d2e1f0 < 2 ^ 32
  norm_num

def leftLineInit : List Stmt :=
  [.letDecl "al" uint256Ty (.var "h0"),
   .letDecl "bl" uint256Ty (.var "h1"),
   .letDecl "cl" uint256Ty (.var "h2"),
   .letDecl "dl" uint256Ty (.var "h3"),
   .letDecl "el" uint256Ty (.var "h4")]

def leftLineInitStore (L : Store) (h : RuntimeChain) : Store :=
  ((((L.insert "al" (wordValue h.h0)).insert "bl" (wordValue h.h1)).insert
    "cl" (wordValue h.h2)).insert "dl" (wordValue h.h3)).insert "el" (wordValue h.h4)

theorem leftLineInitStore_get_original (L : Store) (h : RuntimeChain) (name : Ident)
    (hal : ("al" == name) = false) (hbl : ("bl" == name) = false)
    (hcl : ("cl" == name) = false) (hdl : ("dl" == name) = false)
    (hel : ("el" == name) = false) :
    (leftLineInitStore L h).get? name = L.get? name := by
  simp only [leftLineInitStore]
  rw [store_get_ne _ _ hel, store_get_ne _ _ hdl, store_get_ne _ _ hcl,
    store_get_ne _ _ hbl, store_get_ne _ _ hal]

theorem leftLineInitReturns {L : Store} (evm : EVM.State) (h : RuntimeChain)
    (X : Fin 16 -> UInt256) (p : BlockParams) (hchain : ChainAt L h)
    (hmask : L.get? "mask32" = some (wordValue mask32Word))
    (hwords : L.get? "words" = some (.array (roundWords X)))
    (hparams : BlockParamsAt L p) :
    ExecBlock config { contract := contract, locals := L } evm leftLineInit
      (.ok { contract := contract, locals := leftLineInitStore L h } evm) ∧
    LeftLineAt (leftLineInitStore L h) (runtimeLineOfChain h) ∧
    ChainAt (leftLineInitStore L h) h ∧
    (leftLineInitStore L h).get? "mask32" = some (wordValue mask32Word) ∧
    (leftLineInitStore L h).get? "words" = some (.array (roundWords X)) ∧
    BlockParamsAt (leftLineInitStore L h) p := by
  rcases hchain with ⟨hh0, hh1, hh2, hh3, hh4⟩
  let L1 := L.insert "al" (wordValue h.h0)
  let L2 := L1.insert "bl" (wordValue h.h1)
  let L3 := L2.insert "cl" (wordValue h.h2)
  let L4 := L3.insert "dl" (wordValue h.h3)
  let L5 := L4.insert "el" (wordValue h.h4)
  have h1 : ExecStmt config { contract := contract, locals := L } evm
      (.letDecl "al" uint256Ty (.var "h0"))
      (.ok { contract := contract, locals := L1 } evm) :=
    ExecStmt.letDecl (evalWordVar (evm := evm) hh0)
  have hh1L1 : L1.get? "h1" = some (wordValue h.h1) := by
    simp only [L1]; rw [store_get_ne _ _ (by decide), hh1]
  have h2 : ExecStmt config { contract := contract, locals := L1 } evm
      (.letDecl "bl" uint256Ty (.var "h1"))
      (.ok { contract := contract, locals := L2 } evm) :=
    ExecStmt.letDecl (evalWordVar (evm := evm) hh1L1)
  have hh2L2 : L2.get? "h2" = some (wordValue h.h2) := by
    simp only [L2, L1]; rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), hh2]
  have h3 : ExecStmt config { contract := contract, locals := L2 } evm
      (.letDecl "cl" uint256Ty (.var "h2"))
      (.ok { contract := contract, locals := L3 } evm) :=
    ExecStmt.letDecl (evalWordVar (evm := evm) hh2L2)
  have hh3L3 : L3.get? "h3" = some (wordValue h.h3) := by
    simp only [L3, L2, L1]
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hh3]
  have h4 : ExecStmt config { contract := contract, locals := L3 } evm
      (.letDecl "dl" uint256Ty (.var "h3"))
      (.ok { contract := contract, locals := L4 } evm) :=
    ExecStmt.letDecl (evalWordVar (evm := evm) hh3L3)
  have hh4L4 : L4.get? "h4" = some (wordValue h.h4) := by
    simp only [L4, L3, L2, L1]
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), hh4]
  have h5 : ExecStmt config { contract := contract, locals := L4 } evm
      (.letDecl "el" uint256Ty (.var "h4"))
      (.ok { contract := contract, locals := L5 } evm) :=
    ExecStmt.letDecl (evalWordVar (evm := evm) hh4L4)
  have hexec : ExecBlock config { contract := contract, locals := L } evm leftLineInit
      (.ok { contract := contract, locals := L5 } evm) :=
    ExecBlock.consNormal h1 (ExecBlock.consNormal h2 (ExecBlock.consNormal h3
      (ExecBlock.consNormal h4 (ExecBlock.consNormal h5 ExecBlock.nil))))
  have hline : LeftLineAt L5 (runtimeLineOfChain h) := by
    unfold LeftLineAt runtimeLineOfChain
    constructor
    · simp only [L5, L4, L3, L2, L1]
      rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
        store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]
    constructor
    · simp only [L5, L4, L3, L2]
      rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
        store_get_ne _ _ (by decide), store_get_self]
    constructor
    · simp only [L5, L4, L3]
      rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]
    constructor
    · simp only [L5, L4]
      rw [store_get_ne _ _ (by decide), store_get_self]
    · simp only [L5]
      rw [store_get_self]
  have preserve (name : Ident) (hal : ("al" == name) = false)
      (hbl : ("bl" == name) = false) (hcl : ("cl" == name) = false)
      (hdl : ("dl" == name) = false) (hel : ("el" == name) = false) :
      L5.get? name = L.get? name := by
    simpa [L5, L4, L3, L2, L1] using
      leftLineInitStore_get_original L h name hal hbl hcl hdl hel
  have hchain5 : ChainAt L5 h := ⟨by rw [preserve "h0" (by decide) (by decide)
      (by decide) (by decide) (by decide), hh0],
    by rw [preserve "h1" (by decide) (by decide) (by decide) (by decide) (by decide), hh1],
    by rw [preserve "h2" (by decide) (by decide) (by decide) (by decide) (by decide), hh2],
    by rw [preserve "h3" (by decide) (by decide) (by decide) (by decide) (by decide), hh3],
    by rw [preserve "h4" (by decide) (by decide) (by decide) (by decide) (by decide), hh4]⟩
  refine ⟨by simpa [L5, L4, L3, L2, L1, leftLineInitStore] using hexec,
    by simpa [L5, L4, L3, L2, L1, leftLineInitStore] using hline,
    by simpa [L5, L4, L3, L2, L1, leftLineInitStore] using hchain5, ?_, ?_, ?_⟩
  · rw [leftLineInitStore_get_original L h "mask32" (by decide) (by decide)
      (by decide) (by decide) (by decide), hmask]
  · rw [leftLineInitStore_get_original L h "words" (by decide) (by decide)
      (by decide) (by decide) (by decide), hwords]
  · rcases hparams with ⟨hd, hb, hp, hn, hblk⟩
    exact ⟨by rw [leftLineInitStore_get_original L h "data" (by decide) (by decide)
        (by decide) (by decide) (by decide), hd],
      by rw [leftLineInitStore_get_original L h "bitLen" (by decide) (by decide)
        (by decide) (by decide) (by decide), hb],
      by rw [leftLineInitStore_get_original L h "paddedLen" (by decide) (by decide)
        (by decide) (by decide) (by decide), hp],
      by rw [leftLineInitStore_get_original L h "numBlocks" (by decide) (by decide)
        (by decide) (by decide) (by decide), hn],
      by rw [leftLineInitStore_get_original L h "blk" (by decide) (by decide)
        (by decide) (by decide) (by decide), hblk]⟩

def rightLineInit : List Stmt :=
  [.letDecl "ar" uint256Ty (.var "h0"),
   .letDecl "br" uint256Ty (.var "h1"),
   .letDecl "cr" uint256Ty (.var "h2"),
   .letDecl "dr" uint256Ty (.var "h3"),
   .letDecl "er" uint256Ty (.var "h4")]

def rightLineInitStore (L : Store) (h : RuntimeChain) : Store :=
  ((((L.insert "ar" (wordValue h.h0)).insert "br" (wordValue h.h1)).insert
    "cr" (wordValue h.h2)).insert "dr" (wordValue h.h3)).insert "er" (wordValue h.h4)

theorem rightLineInitStore_get_original (L : Store) (h : RuntimeChain) (name : Ident)
    (har : ("ar" == name) = false) (hbr : ("br" == name) = false)
    (hcr : ("cr" == name) = false) (hdr : ("dr" == name) = false)
    (her : ("er" == name) = false) :
    (rightLineInitStore L h).get? name = L.get? name := by
  simp only [rightLineInitStore]
  rw [store_get_ne _ _ her, store_get_ne _ _ hdr, store_get_ne _ _ hcr,
    store_get_ne _ _ hbr, store_get_ne _ _ har]

theorem rightLineInitReturns {L : Store} (evm : EVM.State) (h : RuntimeChain)
    (X : Fin 16 -> UInt256) (left : RuntimeLineState) (p : BlockParams)
    (hchain : ChainAt L h)
    (hleft : LeftLineAt L left)
    (hmask : L.get? "mask32" = some (wordValue mask32Word))
    (hwords : L.get? "words" = some (.array (roundWords X)))
    (hparams : BlockParamsAt L p) :
    ExecBlock config { contract := contract, locals := L } evm rightLineInit
      (.ok { contract := contract, locals := rightLineInitStore L h } evm) ∧
    RightLineAt (rightLineInitStore L h) (runtimeLineOfChain h) ∧
    LeftLineAt (rightLineInitStore L h) left ∧
    ChainAt (rightLineInitStore L h) h ∧
    (rightLineInitStore L h).get? "mask32" = some (wordValue mask32Word) ∧
    (rightLineInitStore L h).get? "words" = some (.array (roundWords X)) ∧
    BlockParamsAt (rightLineInitStore L h) p := by
  rcases hchain with ⟨hh0, hh1, hh2, hh3, hh4⟩
  let L1 := L.insert "ar" (wordValue h.h0)
  let L2 := L1.insert "br" (wordValue h.h1)
  let L3 := L2.insert "cr" (wordValue h.h2)
  let L4 := L3.insert "dr" (wordValue h.h3)
  let L5 := L4.insert "er" (wordValue h.h4)
  have h1 : ExecStmt config { contract := contract, locals := L } evm
      (.letDecl "ar" uint256Ty (.var "h0"))
      (.ok { contract := contract, locals := L1 } evm) :=
    ExecStmt.letDecl (evalWordVar (evm := evm) hh0)
  have hh1L1 : L1.get? "h1" = some (wordValue h.h1) := by
    simp only [L1]; rw [store_get_ne _ _ (by decide), hh1]
  have h2 : ExecStmt config { contract := contract, locals := L1 } evm
      (.letDecl "br" uint256Ty (.var "h1"))
      (.ok { contract := contract, locals := L2 } evm) :=
    ExecStmt.letDecl (evalWordVar (evm := evm) hh1L1)
  have hh2L2 : L2.get? "h2" = some (wordValue h.h2) := by
    simp only [L2, L1]; rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), hh2]
  have h3 : ExecStmt config { contract := contract, locals := L2 } evm
      (.letDecl "cr" uint256Ty (.var "h2"))
      (.ok { contract := contract, locals := L3 } evm) :=
    ExecStmt.letDecl (evalWordVar (evm := evm) hh2L2)
  have hh3L3 : L3.get? "h3" = some (wordValue h.h3) := by
    simp only [L3, L2, L1]
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hh3]
  have h4 : ExecStmt config { contract := contract, locals := L3 } evm
      (.letDecl "dr" uint256Ty (.var "h3"))
      (.ok { contract := contract, locals := L4 } evm) :=
    ExecStmt.letDecl (evalWordVar (evm := evm) hh3L3)
  have hh4L4 : L4.get? "h4" = some (wordValue h.h4) := by
    simp only [L4, L3, L2, L1]
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), hh4]
  have h5 : ExecStmt config { contract := contract, locals := L4 } evm
      (.letDecl "er" uint256Ty (.var "h4"))
      (.ok { contract := contract, locals := L5 } evm) :=
    ExecStmt.letDecl (evalWordVar (evm := evm) hh4L4)
  have hexec : ExecBlock config { contract := contract, locals := L } evm rightLineInit
      (.ok { contract := contract, locals := L5 } evm) :=
    ExecBlock.consNormal h1 (ExecBlock.consNormal h2 (ExecBlock.consNormal h3
      (ExecBlock.consNormal h4 (ExecBlock.consNormal h5 ExecBlock.nil))))
  have hright : RightLineAt L5 (runtimeLineOfChain h) := by
    unfold RightLineAt runtimeLineOfChain
    constructor
    · simp only [L5, L4, L3, L2, L1]
      rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
        store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]
    constructor
    · simp only [L5, L4, L3, L2]
      rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
        store_get_ne _ _ (by decide), store_get_self]
    constructor
    · simp only [L5, L4, L3]
      rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]
    constructor
    · simp only [L5, L4]
      rw [store_get_ne _ _ (by decide), store_get_self]
    · simp only [L5]
      rw [store_get_self]
  have preserve (name : Ident) (har : ("ar" == name) = false)
      (hbr : ("br" == name) = false) (hcr : ("cr" == name) = false)
      (hdr : ("dr" == name) = false) (her : ("er" == name) = false) :
      L5.get? name = L.get? name := by
    simpa [L5, L4, L3, L2, L1] using
      rightLineInitStore_get_original L h name har hbr hcr hdr her
  have hleft5 : LeftLineAt L5 left := by
    rcases hleft with ⟨ha, hb, hc, hd, he⟩
    exact ⟨by rw [preserve "al" (by decide) (by decide) (by decide) (by decide)
        (by decide), ha],
      by rw [preserve "bl" (by decide) (by decide) (by decide) (by decide) (by decide), hb],
      by rw [preserve "cl" (by decide) (by decide) (by decide) (by decide) (by decide), hc],
      by rw [preserve "dl" (by decide) (by decide) (by decide) (by decide) (by decide), hd],
      by rw [preserve "el" (by decide) (by decide) (by decide) (by decide) (by decide), he]⟩
  have hchain5 : ChainAt L5 h := ⟨by rw [preserve "h0" (by decide) (by decide)
      (by decide) (by decide) (by decide), hh0],
    by rw [preserve "h1" (by decide) (by decide) (by decide) (by decide) (by decide), hh1],
    by rw [preserve "h2" (by decide) (by decide) (by decide) (by decide) (by decide), hh2],
    by rw [preserve "h3" (by decide) (by decide) (by decide) (by decide) (by decide), hh3],
    by rw [preserve "h4" (by decide) (by decide) (by decide) (by decide) (by decide), hh4]⟩
  refine ⟨by simpa [L5, L4, L3, L2, L1, rightLineInitStore] using hexec,
    by simpa [L5, L4, L3, L2, L1, rightLineInitStore] using hright,
    by simpa [L5, L4, L3, L2, L1, rightLineInitStore] using hleft5,
    by simpa [L5, L4, L3, L2, L1, rightLineInitStore] using hchain5, ?_, ?_, ?_⟩
  · rw [rightLineInitStore_get_original L h "mask32" (by decide) (by decide)
      (by decide) (by decide) (by decide), hmask]
  · rw [rightLineInitStore_get_original L h "words" (by decide) (by decide)
      (by decide) (by decide) (by decide), hwords]
  · rcases hparams with ⟨hd, hb, hp, hn, hblk⟩
    exact ⟨by rw [rightLineInitStore_get_original L h "data" (by decide) (by decide)
        (by decide) (by decide) (by decide), hd],
      by rw [rightLineInitStore_get_original L h "bitLen" (by decide) (by decide)
        (by decide) (by decide) (by decide), hb],
      by rw [rightLineInitStore_get_original L h "paddedLen" (by decide) (by decide)
        (by decide) (by decide) (by decide), hp],
      by rw [rightLineInitStore_get_original L h "numBlocks" (by decide) (by decide)
        (by decide) (by decide) (by decide), hn],
      by rw [rightLineInitStore_get_original L h "blk" (by decide) (by decide)
        (by decide) (by decide) (by decide), hblk]⟩

end Ripemd160
