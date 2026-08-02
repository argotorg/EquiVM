import Examples.Ripemd160.SolmBlockInit

/-!
# RIPEMD-160 Solm line recombination

The two completed compression lines are rejoined into the next five chaining words.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Ripemd160

def recombineNextH0 : Stmt := .letDecl "nextH0" uint256Ty
  (.binary .bitAnd
    (.binary .add (.binary .add (.var "h1") (.var "cl")) (.var "dr"))
    (.var "mask32"))
def recombineNextH1 : Stmt := .letDecl "nextH1" uint256Ty
  (.binary .bitAnd
    (.binary .add (.binary .add (.var "h2") (.var "dl")) (.var "er"))
    (.var "mask32"))
def recombineNextH2 : Stmt := .letDecl "nextH2" uint256Ty
  (.binary .bitAnd
    (.binary .add (.binary .add (.var "h3") (.var "el")) (.var "ar"))
    (.var "mask32"))
def recombineNextH3 : Stmt := .letDecl "nextH3" uint256Ty
  (.binary .bitAnd
    (.binary .add (.binary .add (.var "h4") (.var "al")) (.var "br"))
    (.var "mask32"))
def recombineNextH4 : Stmt := .letDecl "nextH4" uint256Ty
  (.binary .bitAnd
    (.binary .add (.binary .add (.var "h0") (.var "bl")) (.var "cr"))
    (.var "mask32"))
def recombineAssignH0 : Stmt :=
  .assign .localVar { base := "h0" } (.var "nextH0")
def recombineAssignH1 : Stmt :=
  .assign .localVar { base := "h1" } (.var "nextH1")
def recombineAssignH2 : Stmt :=
  .assign .localVar { base := "h2" } (.var "nextH2")
def recombineAssignH3 : Stmt :=
  .assign .localVar { base := "h3" } (.var "nextH3")
def recombineAssignH4 : Stmt :=
  .assign .localVar { base := "h4" } (.var "nextH4")

def recombinePrelude : List Stmt :=
  [recombineNextH0, recombineNextH1, recombineNextH2, recombineNextH3,
   recombineNextH4]

def recombineAssignments : List Stmt :=
  [recombineAssignH0, recombineAssignH1, recombineAssignH2, recombineAssignH3,
   recombineAssignH4]

def recombineBody : List Stmt := recombinePrelude ++ recombineAssignments

theorem evalRecombineWord {L : Store} {evm : EVM.State} {a b c mask : Expr}
    {x y z : UInt256}
    (hx : x.toNat < 2 ^ 32) (hy : y.toNat < 2 ^ 32) (hz : z.toNat < 2 ^ 32)
    (ha : evalExpr? config { contract := contract, locals := L } evm a =
      .ok (wordValue x))
    (hb : evalExpr? config { contract := contract, locals := L } evm b =
      .ok (wordValue y))
    (hc : evalExpr? config { contract := contract, locals := L } evm c =
      .ok (wordValue z))
    (hmask : evalExpr? config { contract := contract, locals := L } evm mask =
      .ok (wordValue mask32Word)) :
    evalExpr? config { contract := contract, locals := L } evm
      (.binary .bitAnd (.binary .add (.binary .add a b) c) mask) =
      .ok (wordValue (UInt256.land mask32Word (x + y + z))) := by
  have hxy : x.toNat + y.toNat < UInt256.size := by
    rw [UInt256.size]
    omega
  have hxyNat : (x + y).toNat = x.toNat + y.toNat := by
    rw [uadd_toNat, Nat.mod_eq_of_lt hxy]
  have hxyz : (x + y).toNat + z.toNat < UInt256.size := by
    rw [hxyNat, UInt256.size]
    omega
  exact evalMask32 (evalWordAdd hxyz (evalWordAdd hxy ha hb) hc) hmask

theorem RuntimeChainBound.recombine (h : RuntimeChain) (left right : RuntimeLineState) :
    RuntimeChainBound (runtimeRecombineChain h left right) := by
  unfold RuntimeChainBound runtimeRecombineChain
  exact ⟨runtimeMask32_lt _, runtimeMask32_lt _, runtimeMask32_lt _,
    runtimeMask32_lt _, runtimeMask32_lt _⟩

def NextChainAt (L : Store) (h : RuntimeChain) : Prop :=
  L.get? "nextH0" = some (wordValue h.h0) ∧
  L.get? "nextH1" = some (wordValue h.h1) ∧
  L.get? "nextH2" = some (wordValue h.h2) ∧
  L.get? "nextH3" = some (wordValue h.h3) ∧
  L.get? "nextH4" = some (wordValue h.h4)

def recombinePreludeStore (L : Store) (next : RuntimeChain) : Store :=
  ((((L.insert "nextH0" (wordValue next.h0)).insert "nextH1" (wordValue next.h1)).insert
    "nextH2" (wordValue next.h2)).insert "nextH3" (wordValue next.h3)).insert
    "nextH4" (wordValue next.h4)

def recombineAssignStore (L : Store) (next : RuntimeChain) : Store :=
  ((((L.insert "h0" (wordValue next.h0)).insert "h1" (wordValue next.h1)).insert
    "h2" (wordValue next.h2)).insert "h3" (wordValue next.h3)).insert
    "h4" (wordValue next.h4)

def recombineStore (L : Store) (next : RuntimeChain) : Store :=
  recombineAssignStore (recombinePreludeStore L next) next

theorem recombinePreludeStore_get_original (L : Store) (next : RuntimeChain) (name : Ident)
    (hn0 : ("nextH0" == name) = false) (hn1 : ("nextH1" == name) = false)
    (hn2 : ("nextH2" == name) = false) (hn3 : ("nextH3" == name) = false)
    (hn4 : ("nextH4" == name) = false) :
    (recombinePreludeStore L next).get? name = L.get? name := by
  simp only [recombinePreludeStore]
  rw [store_get_ne _ _ hn4, store_get_ne _ _ hn3, store_get_ne _ _ hn2,
    store_get_ne _ _ hn1, store_get_ne _ _ hn0]

theorem recombineAssignStore_get_original (L : Store) (next : RuntimeChain) (name : Ident)
    (hh0 : ("h0" == name) = false) (hh1 : ("h1" == name) = false)
    (hh2 : ("h2" == name) = false) (hh3 : ("h3" == name) = false)
    (hh4 : ("h4" == name) = false) :
    (recombineAssignStore L next).get? name = L.get? name := by
  simp only [recombineAssignStore]
  rw [store_get_ne _ _ hh4, store_get_ne _ _ hh3, store_get_ne _ _ hh2,
    store_get_ne _ _ hh1, store_get_ne _ _ hh0]

theorem recombineStore_get_context (L : Store) (next : RuntimeChain) (name : Ident)
    (hn0 : ("nextH0" == name) = false) (hn1 : ("nextH1" == name) = false)
    (hn2 : ("nextH2" == name) = false) (hn3 : ("nextH3" == name) = false)
    (hn4 : ("nextH4" == name) = false) (hh0 : ("h0" == name) = false)
    (hh1 : ("h1" == name) = false) (hh2 : ("h2" == name) = false)
    (hh3 : ("h3" == name) = false) (hh4 : ("h4" == name) = false) :
    (recombineStore L next).get? name = L.get? name := by
  rw [recombineStore, recombineAssignStore_get_original _ _ _ hh0 hh1 hh2 hh3 hh4,
    recombinePreludeStore_get_original _ _ _ hn0 hn1 hn2 hn3 hn4]

theorem recombinePreludeStore_next (L : Store) (next : RuntimeChain) :
    NextChainAt (recombinePreludeStore L next) next := by
  unfold NextChainAt
  constructor
  · simp only [recombinePreludeStore]
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]
  constructor
  · simp only [recombinePreludeStore]
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), store_get_self]
  constructor
  · simp only [recombinePreludeStore]
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]
  constructor
  · simp only [recombinePreludeStore]
    rw [store_get_ne _ _ (by decide), store_get_self]
  · simp only [recombinePreludeStore]
    rw [store_get_self]

theorem recombinePreludeReturns {L : Store} (evm : EVM.State) (h : RuntimeChain)
    (left right : RuntimeLineState)
    (hchain : ChainAt L h) (hleft : LeftLineAt L left) (hright : RightLineAt L right)
    (hchainBound : RuntimeChainBound h) (hleftBound : RuntimeLineBound left)
    (hrightBound : RuntimeLineBound right)
    (hmask : L.get? "mask32" = some (wordValue mask32Word)) :
    let next := runtimeRecombineChain h left right
    ExecBlock config { contract := contract, locals := L } evm recombinePrelude
      (.ok { contract := contract, locals := recombinePreludeStore L next } evm) ∧
    NextChainAt (recombinePreludeStore L next) next := by
  dsimp only
  let next := runtimeRecombineChain h left right
  rcases hchain with ⟨hh0, hh1, hh2, hh3, hh4⟩
  rcases hleft with ⟨hal, hbl, hcl, hdl, hel⟩
  rcases hright with ⟨har, hbr, hcr, hdr, her⟩
  rcases hchainBound with ⟨bh0, bh1, bh2, bh3, bh4⟩
  rcases hleftBound with ⟨bal, bbl, bcl, bdl, bel⟩
  rcases hrightBound with ⟨bar, bbr, bcr, bdr, ber⟩
  let L0 := L.insert "nextH0" (wordValue next.h0)
  let L1 := L0.insert "nextH1" (wordValue next.h1)
  let L2 := L1.insert "nextH2" (wordValue next.h2)
  let L3 := L2.insert "nextH3" (wordValue next.h3)
  let L4 := L3.insert "nextH4" (wordValue next.h4)
  have e0 : ExecStmt config { contract := contract, locals := L } evm recombineNextH0
      (.ok { contract := contract, locals := L0 } evm) := by
    exact ExecStmt.letDecl (by
      simpa [next, runtimeRecombineChain] using evalRecombineWord (evm := evm)
        bh1 bcl bdr (evalWordVar hh1) (evalWordVar hcl)
        (evalWordVar hdr) (evalWordVar hmask))
  have from0 (name : Ident) (hne : ("nextH0" == name) = false) :
      L0.get? name = L.get? name := by simp only [L0]; rw [store_get_ne _ _ hne]
  have e1 : ExecStmt config { contract := contract, locals := L0 } evm recombineNextH1
      (.ok { contract := contract, locals := L1 } evm) := by
    exact ExecStmt.letDecl (by
      simpa [next, runtimeRecombineChain] using evalRecombineWord bh2 bdl ber
        (evalWordVar (by rw [from0 "h2" (by decide), hh2]))
        (evalWordVar (by rw [from0 "dl" (by decide), hdl]))
        (evalWordVar (by rw [from0 "er" (by decide), her]))
        (evalWordVar (by rw [from0 "mask32" (by decide), hmask])))
  have from1 (name : Ident) (hne : ("nextH1" == name) = false) :
      L1.get? name = L0.get? name := by simp only [L1]; rw [store_get_ne _ _ hne]
  have e2 : ExecStmt config { contract := contract, locals := L1 } evm recombineNextH2
      (.ok { contract := contract, locals := L2 } evm) := by
    exact ExecStmt.letDecl (by
      simpa [next, runtimeRecombineChain] using evalRecombineWord bh3 bel bar
        (evalWordVar (by rw [from1 "h3" (by decide), from0 "h3" (by decide), hh3]))
        (evalWordVar (by rw [from1 "el" (by decide), from0 "el" (by decide), hel]))
        (evalWordVar (by rw [from1 "ar" (by decide), from0 "ar" (by decide), har]))
        (evalWordVar (by rw [from1 "mask32" (by decide),
          from0 "mask32" (by decide), hmask])))
  have from2 (name : Ident) (hne : ("nextH2" == name) = false) :
      L2.get? name = L1.get? name := by simp only [L2]; rw [store_get_ne _ _ hne]
  have e3 : ExecStmt config { contract := contract, locals := L2 } evm recombineNextH3
      (.ok { contract := contract, locals := L3 } evm) := by
    exact ExecStmt.letDecl (by
      simpa [next, runtimeRecombineChain] using evalRecombineWord bh4 bal bbr
        (evalWordVar (by rw [from2 "h4" (by decide), from1 "h4" (by decide),
          from0 "h4" (by decide), hh4]))
        (evalWordVar (by rw [from2 "al" (by decide), from1 "al" (by decide),
          from0 "al" (by decide), hal]))
        (evalWordVar (by rw [from2 "br" (by decide), from1 "br" (by decide),
          from0 "br" (by decide), hbr]))
        (evalWordVar (by rw [from2 "mask32" (by decide), from1 "mask32" (by decide),
          from0 "mask32" (by decide), hmask])))
  have from3 (name : Ident) (hne : ("nextH3" == name) = false) :
      L3.get? name = L2.get? name := by simp only [L3]; rw [store_get_ne _ _ hne]
  have e4 : ExecStmt config { contract := contract, locals := L3 } evm recombineNextH4
      (.ok { contract := contract, locals := L4 } evm) := by
    exact ExecStmt.letDecl (by
      simpa [next, runtimeRecombineChain] using evalRecombineWord bh0 bbl bcr
        (evalWordVar (by rw [from3 "h0" (by decide), from2 "h0" (by decide),
          from1 "h0" (by decide), from0 "h0" (by decide), hh0]))
        (evalWordVar (by rw [from3 "bl" (by decide), from2 "bl" (by decide),
          from1 "bl" (by decide), from0 "bl" (by decide), hbl]))
        (evalWordVar (by rw [from3 "cr" (by decide), from2 "cr" (by decide),
          from1 "cr" (by decide), from0 "cr" (by decide), hcr]))
        (evalWordVar (by rw [from3 "mask32" (by decide), from2 "mask32" (by decide),
          from1 "mask32" (by decide), from0 "mask32" (by decide), hmask])))
  have hexec : ExecBlock config { contract := contract, locals := L } evm recombinePrelude
      (.ok { contract := contract, locals := L4 } evm) := by
    exact ExecBlock.consNormal e0 <| ExecBlock.consNormal e1 <|
      ExecBlock.consNormal e2 <| ExecBlock.consNormal e3 <|
      ExecBlock.consNormal e4 ExecBlock.nil
  refine ⟨?_, ?_⟩
  · simpa only [recombinePreludeStore] using hexec
  · exact recombinePreludeStore_next L next

theorem recombineAssignmentsReturns {L : Store} (evm : EVM.State)
    (old next : RuntimeChain) (hchain : ChainAt L old) (hnext : NextChainAt L next) :
    ExecBlock config { contract := contract, locals := L } evm recombineAssignments
      (.ok { contract := contract, locals := recombineAssignStore L next } evm) ∧
    ChainAt (recombineAssignStore L next) next := by
  rcases hchain with ⟨hh0, hh1, hh2, hh3, hh4⟩
  rcases hnext with ⟨hn0, hn1, hn2, hn3, hn4⟩
  let L0 := L.insert "h0" (wordValue next.h0)
  let L1 := L0.insert "h1" (wordValue next.h1)
  let L2 := L1.insert "h2" (wordValue next.h2)
  let L3 := L2.insert "h3" (wordValue next.h3)
  let L4 := L3.insert "h4" (wordValue next.h4)
  have e0 : ExecStmt config { contract := contract, locals := L } evm recombineAssignH0
      (.ok { contract := contract, locals := L0 } evm) :=
    execAssignLocal hh0 (evalWordVar hn0)
  have e1 : ExecStmt config { contract := contract, locals := L0 } evm recombineAssignH1
      (.ok { contract := contract, locals := L1 } evm) :=
    execAssignLocal (by simp only [L0]; rw [store_get_ne _ _ (by decide), hh1])
      (evalWordVar (by simp only [L0]; rw [store_get_ne _ _ (by decide), hn1]))
  have e2 : ExecStmt config { contract := contract, locals := L1 } evm recombineAssignH2
      (.ok { contract := contract, locals := L2 } evm) :=
    execAssignLocal (by simp only [L1, L0]; rw [store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hh2])
      (evalWordVar (by simp only [L1, L0]; rw [store_get_ne _ _ (by decide),
        store_get_ne _ _ (by decide), hn2]))
  have e3 : ExecStmt config { contract := contract, locals := L2 } evm recombineAssignH3
      (.ok { contract := contract, locals := L3 } evm) :=
    execAssignLocal (by simp only [L2, L1, L0]; rw [store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), hh3])
      (evalWordVar (by simp only [L2, L1, L0]; rw [store_get_ne _ _ (by decide),
        store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), hn3]))
  have e4 : ExecStmt config { contract := contract, locals := L3 } evm recombineAssignH4
      (.ok { contract := contract, locals := L4 } evm) := by
    have hh4L3 : L3.get? "h4" = some (wordValue old.h4) := by
      simp only [L3, L2, L1, L0]
      rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
        store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), hh4]
    have hn4L3 : L3.get? "nextH4" = some (wordValue next.h4) := by
      simp only [L3, L2, L1, L0]
      rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
        store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), hn4]
    exact execAssignLocal hh4L3 (evalWordVar hn4L3)
  have hexec : ExecBlock config { contract := contract, locals := L } evm recombineAssignments
      (.ok { contract := contract, locals := L4 } evm) :=
    ExecBlock.consNormal e0 <| ExecBlock.consNormal e1 <| ExecBlock.consNormal e2 <|
      ExecBlock.consNormal e3 <| ExecBlock.consNormal e4 ExecBlock.nil
  refine ⟨by simpa only [recombineAssignStore] using hexec, ?_⟩
  unfold ChainAt
  constructor
  · simp only [recombineAssignStore]
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]
  constructor
  · simp only [recombineAssignStore]
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), store_get_self]
  constructor
  · simp only [recombineAssignStore]
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]
  constructor
  · simp only [recombineAssignStore]
    rw [store_get_ne _ _ (by decide), store_get_self]
  · simp only [recombineAssignStore]
    rw [store_get_self]

theorem recombineReturns {L : Store} (evm : EVM.State) (h : RuntimeChain)
    (left right : RuntimeLineState) (X : Fin 16 -> UInt256) (p : BlockParams)
    (hchain : ChainAt L h) (hleft : LeftLineAt L left) (hright : RightLineAt L right)
    (hchainBound : RuntimeChainBound h) (hleftBound : RuntimeLineBound left)
    (hrightBound : RuntimeLineBound right)
    (hmask : L.get? "mask32" = some (wordValue mask32Word))
    (hwords : L.get? "words" = some (.array (roundWords X)))
    (hparams : BlockParamsAt L p) :
    let next := runtimeRecombineChain h left right
    ExecBlock config { contract := contract, locals := L } evm recombineBody
      (.ok { contract := contract, locals := recombineStore L next } evm) ∧
    ChainAt (recombineStore L next) next ∧ RuntimeChainBound next ∧
    (recombineStore L next).get? "mask32" = some (wordValue mask32Word) ∧
    (recombineStore L next).get? "words" = some (.array (roundWords X)) ∧
    BlockParamsAt (recombineStore L next) p := by
  dsimp only
  let next := runtimeRecombineChain h left right
  obtain ⟨hpre, hnext⟩ := recombinePreludeReturns evm h left right hchain hleft hright
    hchainBound hleftBound hrightBound hmask
  let P := recombinePreludeStore L next
  have hchainP : ChainAt P h := by
    rcases hchain with ⟨hh0, hh1, hh2, hh3, hh4⟩
    exact ⟨by rw [recombinePreludeStore_get_original L next "h0" (by decide)
        (by decide) (by decide) (by decide) (by decide), hh0],
      by rw [recombinePreludeStore_get_original L next "h1" (by decide)
        (by decide) (by decide) (by decide) (by decide), hh1],
      by rw [recombinePreludeStore_get_original L next "h2" (by decide)
        (by decide) (by decide) (by decide) (by decide), hh2],
      by rw [recombinePreludeStore_get_original L next "h3" (by decide)
        (by decide) (by decide) (by decide) (by decide), hh3],
      by rw [recombinePreludeStore_get_original L next "h4" (by decide)
        (by decide) (by decide) (by decide) (by decide), hh4]⟩
  obtain ⟨hassign, hchainNext⟩ := recombineAssignmentsReturns evm h next hchainP hnext
  have hexec : ExecBlock config { contract := contract, locals := L } evm recombineBody
      (.ok { contract := contract, locals := recombineStore L next } evm) := by
    exact execBlock_append hpre hassign
  refine ⟨hexec, hchainNext, RuntimeChainBound.recombine h left right, ?_, ?_, ?_⟩
  · rw [recombineStore_get_context L next "mask32" (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), hmask]
  · rw [recombineStore_get_context L next "words" (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), hwords]
  · rcases hparams with ⟨hd, hb, hp, hn, hblk⟩
    exact ⟨by rw [recombineStore_get_context L next "data" (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), hd],
      by rw [recombineStore_get_context L next "bitLen" (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), hb],
      by rw [recombineStore_get_context L next "paddedLen" (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), hp],
      by rw [recombineStore_get_context L next "numBlocks" (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), hn],
      by rw [recombineStore_get_context L next "blk" (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), hblk]⟩

end Ripemd160
