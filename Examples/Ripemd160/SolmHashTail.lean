import Examples.Ripemd160.SolmHashInit

/-!
# RIPEMD-160 Solm hash finalization

Execution of the five byte swaps, digest packing, and `bytes20` return at the end of the authored
hash function.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Ripemd160

abbrev bytes20Width : Fin 32 := ⟨19, by decide⟩
abbrev bytes20Storage : StorageType := .elem (.bytes bytes20Width)

def digestBytes20 (h : RuntimeChain) : Value :=
  .fixedBytes bytes20Width ((EVM.Word.toBytesBE (runtimeDigestPacked h)).drop 12)

def hashSwap0Stmt : Stmt := .internalCall "swap32" [.var "h0"] "r0"
def hashSwap1Stmt : Stmt := .internalCall "swap32" [.var "h1"] "r1"
def hashSwap2Stmt : Stmt := .internalCall "swap32" [.var "h2"] "r2"
def hashSwap3Stmt : Stmt := .internalCall "swap32" [.var "h3"] "r3"
def hashSwap4Stmt : Stmt := .internalCall "swap32" [.var "h4"] "r4"

def hashDigestExpr : Expr :=
  .binary .bitOr
    (.binary .bitOr
      (.binary .bitOr
        (.binary .bitOr
          (.binary .shl (.var "r0") (.intLit 128))
          (.binary .shl (.var "r1") (.intLit 96)))
        (.binary .shl (.var "r2") (.intLit 64)))
      (.binary .shl (.var "r3") (.intLit 32)))
    (.var "r4")

def hashDigestStmt : Stmt := .letDecl "digest" uint256Ty hashDigestExpr
def hashReturnStmt : Stmt := .return [.cast (.var "digest") bytes20Storage]

def hashTail : List Stmt :=
  [hashSwap0Stmt, hashSwap1Stmt, hashSwap2Stmt, hashSwap3Stmt, hashSwap4Stmt,
    hashDigestStmt, hashReturnStmt]

def sourceDigestPacked (h : RuntimeChain) : UInt256 :=
  UInt256.lor
    (UInt256.lor
      (UInt256.lor
        (UInt256.lor
          (UInt256.shiftLeft (runtimeSwap32 h.h0) ⟨128⟩)
          (UInt256.shiftLeft (runtimeSwap32 h.h1) ⟨96⟩))
        (UInt256.shiftLeft (runtimeSwap32 h.h2) ⟨64⟩))
      (UInt256.shiftLeft (runtimeSwap32 h.h3) ⟨32⟩))
    (runtimeSwap32 h.h4)

theorem sourceDigestPacked_eq_runtime (h : RuntimeChain) :
    sourceDigestPacked h = runtimeDigestPacked h := by
  simp only [sourceDigestPacked, runtimeDigestPacked]
  repeat' rw [u256_lor_assoc]

theorem digestBytes20_eq_cast (h : RuntimeChain) :
    castValue? (wordValue (runtimeDigestPacked h)) bytes20Storage =
      some (digestBytes20 h) := by
  simp only [wordValue, bytes20Storage, castValue?, digestBytes20]
  split
  · rename_i hneg
    exact (not_lt_of_ge (Int.natCast_nonneg _) hneg).elim
  · rw [show (Int.ofNat (runtimeDigestPacked h).toNat).toNat =
      (runtimeDigestPacked h).toNat from Int.toNat_natCast _]
    have hw : EVM.Word.ofNat (runtimeDigestPacked h).toNat = runtimeDigestPacked h := by
      exact u256_ofNat_toNat _
    rw [hw]

theorem hashTailReturns {L : Store} (evm : EVM.State) (h : RuntimeChain)
    (hchain : ChainAt L h) (hbound : RuntimeChainBound h) :
    ∃ L', ExecBlock config { contract := contract, locals := L } evm hashTail
        (.returned { contract := contract, locals := L' } evm
          (some [digestBytes20 h])) ∧
      ChainAt L' h := by
  rcases hchain with ⟨hh0, hh1, hh2, hh3, hh4⟩
  rcases hbound with ⟨hb0, hb1, hb2, hb3, hb4⟩
  let L0 := L.insert "r0" (wordValue (runtimeSwap32 h.h0))
  let L1 := L0.insert "r1" (wordValue (runtimeSwap32 h.h1))
  let L2 := L1.insert "r2" (wordValue (runtimeSwap32 h.h2))
  let L3 := L2.insert "r3" (wordValue (runtimeSwap32 h.h3))
  let L4 := L3.insert "r4" (wordValue (runtimeSwap32 h.h4))
  let L5 := L4.insert "digest" (wordValue (runtimeDigestPacked h))
  have e0 : ExecStmt config { contract := contract, locals := L } evm hashSwap0Stmt
      (.ok { contract := contract, locals := L0 } evm) := by
    simpa only [hashSwap0Stmt, L0] using
      swap32Call evm h.h0 hb0 (xExpr := .var "h0") (retVar := "r0")
        (evalWordVar hh0)
  have preserve0 (name : Ident) (hne : ("r0" == name) = false) :
      L0.get? name = L.get? name := by
    simp only [L0]
    rw [store_get_ne _ _ hne]
  have e1 : ExecStmt config { contract := contract, locals := L0 } evm hashSwap1Stmt
      (.ok { contract := contract, locals := L1 } evm) := by
    simpa only [hashSwap1Stmt, L1] using
      swap32Call evm h.h1 hb1 (xExpr := .var "h1") (retVar := "r1")
        (evalWordVar (by rw [preserve0 "h1" (by decide), hh1]))
  have preserve1 (name : Ident) (hne : ("r1" == name) = false) :
      L1.get? name = L0.get? name := by
    simp only [L1]
    rw [store_get_ne _ _ hne]
  have e2 : ExecStmt config { contract := contract, locals := L1 } evm hashSwap2Stmt
      (.ok { contract := contract, locals := L2 } evm) := by
    simpa only [hashSwap2Stmt, L2] using
      swap32Call evm h.h2 hb2 (xExpr := .var "h2") (retVar := "r2")
        (evalWordVar (by rw [preserve1 "h2" (by decide), preserve0 "h2" (by decide), hh2]))
  have preserve2 (name : Ident) (hne : ("r2" == name) = false) :
      L2.get? name = L1.get? name := by
    simp only [L2]
    rw [store_get_ne _ _ hne]
  have e3 : ExecStmt config { contract := contract, locals := L2 } evm hashSwap3Stmt
      (.ok { contract := contract, locals := L3 } evm) := by
    simpa only [hashSwap3Stmt, L3] using
      swap32Call evm h.h3 hb3 (xExpr := .var "h3") (retVar := "r3")
        (evalWordVar (by
          rw [preserve2 "h3" (by decide), preserve1 "h3" (by decide),
            preserve0 "h3" (by decide), hh3]))
  have preserve3 (name : Ident) (hne : ("r3" == name) = false) :
      L3.get? name = L2.get? name := by
    simp only [L3]
    rw [store_get_ne _ _ hne]
  have e4 : ExecStmt config { contract := contract, locals := L3 } evm hashSwap4Stmt
      (.ok { contract := contract, locals := L4 } evm) := by
    simpa only [hashSwap4Stmt, L4] using
      swap32Call evm h.h4 hb4 (xExpr := .var "h4") (retVar := "r4")
        (evalWordVar (by
          rw [preserve3 "h4" (by decide), preserve2 "h4" (by decide),
            preserve1 "h4" (by decide), preserve0 "h4" (by decide), hh4]))
  have preserve4 (name : Ident) (hne : ("r4" == name) = false) :
      L4.get? name = L3.get? name := by
    simp only [L4]
    rw [store_get_ne _ _ hne]
  have hr0 : L4.get? "r0" = some (wordValue (runtimeSwap32 h.h0)) := by
    rw [preserve4 "r0" (by decide), preserve3 "r0" (by decide),
      preserve2 "r0" (by decide), preserve1 "r0" (by decide)]
    simp [L0]
  have hr1 : L4.get? "r1" = some (wordValue (runtimeSwap32 h.h1)) := by
    rw [preserve4 "r1" (by decide), preserve3 "r1" (by decide),
      preserve2 "r1" (by decide)]
    simp [L1]
  have hr2 : L4.get? "r2" = some (wordValue (runtimeSwap32 h.h2)) := by
    rw [preserve4 "r2" (by decide), preserve3 "r2" (by decide)]
    simp [L2]
  have hr3 : L4.get? "r3" = some (wordValue (runtimeSwap32 h.h3)) := by
    rw [preserve4 "r3" (by decide)]
    simp [L3]
  have hr4 : L4.get? "r4" = some (wordValue (runtimeSwap32 h.h4)) := by
    simp [L4]
  have h128 := evalWordLit (L := L4) (evm := evm) 128 (by decide)
  have h96 := evalWordLit (L := L4) (evm := evm) 96 (by decide)
  have h64 := evalWordLit (L := L4) (evm := evm) 64 (by decide)
  have h32 := evalWordLit (L := L4) (evm := evm) 32 (by decide)
  have es0 := evalShl 128 (by decide) (evalWordVar hr0) h128
  have es1 := evalShl 96 (by decide) (evalWordVar hr1) h96
  have es2 := evalShl 64 (by decide) (evalWordVar hr2) h64
  have es3 := evalShl 32 (by decide) (evalWordVar hr3) h32
  have hdigestEval : evalExpr? config { contract := contract, locals := L4 } evm
      hashDigestExpr = .ok (wordValue (runtimeDigestPacked h)) := by
    have hall := evalBitOr (evalBitOr (evalBitOr (evalBitOr es0 es1) es2) es3)
      (evalWordVar hr4)
    change evalExpr? config { contract := contract, locals := L4 } evm hashDigestExpr =
      .ok (wordValue (sourceDigestPacked h)) at hall
    rw [sourceDigestPacked_eq_runtime h] at hall
    exact hall
  have e5 : ExecStmt config { contract := contract, locals := L4 } evm hashDigestStmt
      (.ok { contract := contract, locals := L5 } evm) := by
    exact ExecStmt.letDecl (by simpa only [hashDigestStmt] using hdigestEval)
  have hdigest : L5.get? "digest" = some (wordValue (runtimeDigestPacked h)) := by
    simp [L5]
  have hcast : evalExpr? config { contract := contract, locals := L5 } evm
      (.cast (.var "digest") bytes20Storage) = .ok (digestBytes20 h) := by
    simp only [evalExpr?, EvalResult.ofOption, hdigest, EvalResult.bind, bind]
    rw [digestBytes20_eq_cast]
  have e6 : ExecStmt config { contract := contract, locals := L5 } evm hashReturnStmt
      (.returned { contract := contract, locals := L5 } evm (some [digestBytes20 h])) := by
    apply ExecStmt.return
    simp only [hashReturnStmt, evalExprs?, hcast, EvalResult.bind, bind, pure]
  have hexec : ExecBlock config { contract := contract, locals := L } evm hashTail
      (.returned { contract := contract, locals := L5 } evm (some [digestBytes20 h])) :=
    ExecBlock.consNormal e0 <| ExecBlock.consNormal e1 <| ExecBlock.consNormal e2 <|
      ExecBlock.consNormal e3 <| ExecBlock.consNormal e4 <| ExecBlock.consNormal e5 <|
      ExecBlock.consReturn e6
  refine ⟨L5, hexec, ?_⟩
  have preserve5 (name : Ident) (hne : ("digest" == name) = false) :
      L5.get? name = L4.get? name := by
    simp only [L5]
    rw [store_get_ne _ _ hne]
  exact ⟨by
      rw [preserve5 "h0" (by decide), preserve4 "h0" (by decide),
        preserve3 "h0" (by decide), preserve2 "h0" (by decide),
        preserve1 "h0" (by decide), preserve0 "h0" (by decide), hh0],
    by
      rw [preserve5 "h1" (by decide), preserve4 "h1" (by decide),
        preserve3 "h1" (by decide), preserve2 "h1" (by decide),
        preserve1 "h1" (by decide), preserve0 "h1" (by decide), hh1],
    by
      rw [preserve5 "h2" (by decide), preserve4 "h2" (by decide),
        preserve3 "h2" (by decide), preserve2 "h2" (by decide),
        preserve1 "h2" (by decide), preserve0 "h2" (by decide), hh2],
    by
      rw [preserve5 "h3" (by decide), preserve4 "h3" (by decide),
        preserve3 "h3" (by decide), preserve2 "h3" (by decide),
        preserve1 "h3" (by decide), preserve0 "h3" (by decide), hh3],
    by
      rw [preserve5 "h4" (by decide), preserve4 "h4" (by decide),
        preserve3 "h4" (by decide), preserve2 "h4" (by decide),
        preserve1 "h4" (by decide), preserve0 "h4" (by decide), hh4]⟩

end Ripemd160
