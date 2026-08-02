import Examples.Ripemd160.SolmBlockLoop

/-!
# RIPEMD-160 Solm hash initialization

Execution of the source declarations preceding the outer compression loop.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Ripemd160

def hashMaskStmt : Stmt := .letDecl "mask32" uint256Ty (.intLit 0xffffffff)
def hashDataLenStmt : Stmt := .letDecl "dataLen" uint256Ty
  (.arrayLength .localVar { base := "data" })
def hashBitLenStmt : Stmt := .letDecl "bitLen" uint256Ty
  (.binary .mul (.var "dataLen") (.intLit 8))
def hashPaddedLenStmt : Stmt := .letDecl "paddedLen" uint256Ty
  (.binary .mul
    (.binary .div (.binary .add (.var "dataLen") (.intLit 72)) (.intLit 64))
    (.intLit 64))
def hashNumBlocksStmt : Stmt := .letDecl "numBlocks" uint256Ty
  (.binary .div (.var "paddedLen") (.intLit 64))
def hashH0Stmt : Stmt := .letDecl "h0" uint256Ty (.intLit 0x67452301)
def hashH1Stmt : Stmt := .letDecl "h1" uint256Ty (.intLit 0xefcdab89)
def hashH2Stmt : Stmt := .letDecl "h2" uint256Ty (.intLit 0x98badcfe)
def hashH3Stmt : Stmt := .letDecl "h3" uint256Ty (.intLit 0x10325476)
def hashH4Stmt : Stmt := .letDecl "h4" uint256Ty (.intLit 0xc3d2e1f0)
def hashWordsStmt : Stmt := .letDecl "words" (some (.dynamicArray uint256Ty.get!))
  (.newArray (.elem (.int (.uint ⟨256, by decide⟩))) (.intLit 16))

def hashPrelude : List Stmt :=
  [hashMaskStmt, hashDataLenStmt, hashBitLenStmt, hashPaddedLenStmt,
   hashNumBlocksStmt, hashH0Stmt, hashH1Stmt, hashH2Stmt, hashH3Stmt,
   hashH4Stmt, hashWordsStmt]

def hashPreludeStore (L : Store) (data : ByteArray) : Store :=
  let blocks := Model.paddedLength data.size / 64
  let L0 := L.insert "mask32" (wordValue mask32Word)
  let L1 := L0.insert "dataLen" (natValue data.size)
  let L2 := L1.insert "bitLen" (natValue (data.size * 8))
  let L3 := L2.insert "paddedLen" (natValue (Model.paddedLength data.size))
  let L4 := L3.insert "numBlocks" (natValue blocks)
  let L5 := L4.insert "h0" (wordValue runtimeInitialChain.h0)
  let L6 := L5.insert "h1" (wordValue runtimeInitialChain.h1)
  let L7 := L6.insert "h2" (wordValue runtimeInitialChain.h2)
  let L8 := L7.insert "h3" (wordValue runtimeInitialChain.h3)
  let L9 := L8.insert "h4" (wordValue runtimeInitialChain.h4)
  L9.insert "words" (.array (roundWords (sourceWordsBefore data 0)))

theorem evalLocalBytesLength {L : Store} (evm : EVM.State) (data : ByteArray)
    (hdata : L.get? "data" = some (.bytes data)) :
    evalExpr? config { contract := contract, locals := L } evm
      (.arrayLength .localVar { base := "data" }) = .ok (natValue data.size) := by
  simp only [evalExpr?, hdata, readLocalPath?, EvalResult.bind, bind, pure, natValue]

theorem initialWords_eq_replicate (data : ByteArray) :
    roundWords (sourceWordsBefore data 0) = List.replicate 16 (.int 0) := by
  apply List.ext_getElem
  · simp
  · intro i hleft hright
    unfold roundWords sourceWordsBefore wordValue
    simp only [List.getElem_ofFn, List.getElem_replicate]
    rw [ulit_toNat' 0 (by decide)]
    norm_num

theorem hashPreludeStore_get_original (L : Store) (data : ByteArray) (name : Ident)
    (hm : ("mask32" == name) = false) (hdl : ("dataLen" == name) = false)
    (hbl : ("bitLen" == name) = false) (hpl : ("paddedLen" == name) = false)
    (hnb : ("numBlocks" == name) = false) (hh0 : ("h0" == name) = false)
    (hh1 : ("h1" == name) = false) (hh2 : ("h2" == name) = false)
    (hh3 : ("h3" == name) = false) (hh4 : ("h4" == name) = false)
    (hw : ("words" == name) = false) :
    (hashPreludeStore L data).get? name = L.get? name := by
  simp only [hashPreludeStore]
  rw [store_get_ne _ _ hw, store_get_ne _ _ hh4, store_get_ne _ _ hh3,
    store_get_ne _ _ hh2, store_get_ne _ _ hh1, store_get_ne _ _ hh0,
    store_get_ne _ _ hnb, store_get_ne _ _ hpl, store_get_ne _ _ hbl,
    store_get_ne _ _ hdl, store_get_ne _ _ hm]

theorem hashPreludeReturns {L : Store} (evm : EVM.State) (data : ByteArray)
    (hdata : L.get? "data" = some (.bytes data)) :
    ExecBlock config { contract := contract, locals := L } evm hashPrelude
      (.ok { contract := contract, locals := hashPreludeStore L data } evm) ∧
    ChainAt (hashPreludeStore L data) runtimeInitialChain ∧
    RuntimeChainBound runtimeInitialChain ∧
    (hashPreludeStore L data).get? "data" = some (.bytes data) ∧
    (hashPreludeStore L data).get? "bitLen" = some (natValue (data.size * 8)) ∧
    (hashPreludeStore L data).get? "paddedLen" =
      some (natValue (Model.paddedLength data.size)) ∧
    (hashPreludeStore L data).get? "numBlocks" =
      some (natValue (Model.paddedLength data.size / 64)) ∧
    (hashPreludeStore L data).get? "words" =
      some (.array (roundWords (sourceWordsBefore data 0))) ∧
    (hashPreludeStore L data).get? "mask32" = some (wordValue mask32Word) := by
  let blocks := Model.paddedLength data.size / 64
  let L0 := L.insert "mask32" (wordValue mask32Word)
  let L1 := L0.insert "dataLen" (natValue data.size)
  let L2 := L1.insert "bitLen" (natValue (data.size * 8))
  let L3 := L2.insert "paddedLen" (natValue (Model.paddedLength data.size))
  let L4 := L3.insert "numBlocks" (natValue blocks)
  let L5 := L4.insert "h0" (wordValue runtimeInitialChain.h0)
  let L6 := L5.insert "h1" (wordValue runtimeInitialChain.h1)
  let L7 := L6.insert "h2" (wordValue runtimeInitialChain.h2)
  let L8 := L7.insert "h3" (wordValue runtimeInitialChain.h3)
  let L9 := L8.insert "h4" (wordValue runtimeInitialChain.h4)
  let L10 := L9.insert "words" (.array (roundWords (sourceWordsBefore data 0)))
  have e0 : ExecStmt config { contract := contract, locals := L } evm hashMaskStmt
      (.ok { contract := contract, locals := L0 } evm) := by
    exact ExecStmt.letDecl (by
      simpa [hashMaskStmt, mask32Word] using
        evalWordLit (L := L) (evm := evm) 0xffffffff (by decide))
  have from0 (name : Ident) (hne : ("mask32" == name) = false) :
      L0.get? name = L.get? name := by simp only [L0]; rw [store_get_ne _ _ hne]
  have e1 : ExecStmt config { contract := contract, locals := L0 } evm hashDataLenStmt
      (.ok { contract := contract, locals := L1 } evm) := by
    exact ExecStmt.letDecl (by
      exact evalLocalBytesLength evm data (by rw [from0 "data" (by decide), hdata]))
  have from1 (name : Ident) (hne : ("dataLen" == name) = false) :
      L1.get? name = L0.get? name := by simp only [L1]; rw [store_get_ne _ _ hne]
  have hdataLen1 : L1.get? "dataLen" = some (natValue data.size) := by simp [L1]
  have e2 : ExecStmt config { contract := contract, locals := L1 } evm hashBitLenStmt
      (.ok { contract := contract, locals := L2 } evm) := by
    exact ExecStmt.letDecl (evalNatMul (evalNatVar hdataLen1)
      (by simp [evalExpr?, natValue, pure]))
  have from2 (name : Ident) (hne : ("bitLen" == name) = false) :
      L2.get? name = L1.get? name := by simp only [L2]; rw [store_get_ne _ _ hne]
  have e3 : ExecStmt config { contract := contract, locals := L2 } evm hashPaddedLenStmt
      (.ok { contract := contract, locals := L3 } evm) := by
    have hlen : L2.get? "dataLen" = some (natValue data.size) := by
      rw [from2 "dataLen" (by decide), hdataLen1]
    have hadd := evalNatAdd (evalNatVar hlen) (show evalExpr? config
      { contract := contract, locals := L2 } evm (.intLit 72) = .ok (natValue 72) by
        simp [evalExpr?, natValue, pure])
    have hdiv := evalNatDiv (by decide : (64 : Nat) ≠ 0) hadd
      (show evalExpr? config { contract := contract, locals := L2 } evm (.intLit 64) =
        .ok (natValue 64) by simp [evalExpr?, natValue, pure])
    have hmul := evalNatMul hdiv
      (show evalExpr? config { contract := contract, locals := L2 } evm (.intLit 64) =
        .ok (natValue 64) by simp [evalExpr?, natValue, pure])
    exact ExecStmt.letDecl (by simpa [hashPaddedLenStmt, Model.paddedLength] using hmul)
  have from3 (name : Ident) (hne : ("paddedLen" == name) = false) :
      L3.get? name = L2.get? name := by simp only [L3]; rw [store_get_ne _ _ hne]
  have hpad3 : L3.get? "paddedLen" =
      some (natValue (Model.paddedLength data.size)) := by simp [L3]
  have e4 : ExecStmt config { contract := contract, locals := L3 } evm hashNumBlocksStmt
      (.ok { contract := contract, locals := L4 } evm) := by
    exact ExecStmt.letDecl (by
      simpa [blocks, hashNumBlocksStmt] using evalNatDiv (by decide : (64 : Nat) ≠ 0)
        (evalNatVar hpad3)
        (show evalExpr? config { contract := contract, locals := L3 } evm (.intLit 64) =
          .ok (natValue 64) by simp [evalExpr?, natValue, pure]))
  have from4 (name : Ident) (hne : ("numBlocks" == name) = false) :
      L4.get? name = L3.get? name := by simp only [L4]; rw [store_get_ne _ _ hne]
  have e5 : ExecStmt config { contract := contract, locals := L4 } evm hashH0Stmt
      (.ok { contract := contract, locals := L5 } evm) := by
    exact ExecStmt.letDecl (by
      simpa [hashH0Stmt, runtimeInitialChain] using
        evalWordLit (L := L4) (evm := evm) 0x67452301 (by decide))
  have e6 : ExecStmt config { contract := contract, locals := L5 } evm hashH1Stmt
      (.ok { contract := contract, locals := L6 } evm) := by
    exact ExecStmt.letDecl (by
      simpa [hashH1Stmt, runtimeInitialChain] using
        evalWordLit (L := L5) (evm := evm) 0xefcdab89 (by decide))
  have e7 : ExecStmt config { contract := contract, locals := L6 } evm hashH2Stmt
      (.ok { contract := contract, locals := L7 } evm) := by
    exact ExecStmt.letDecl (by
      simpa [hashH2Stmt, runtimeInitialChain] using
        evalWordLit (L := L6) (evm := evm) 0x98badcfe (by decide))
  have e8 : ExecStmt config { contract := contract, locals := L7 } evm hashH3Stmt
      (.ok { contract := contract, locals := L8 } evm) := by
    exact ExecStmt.letDecl (by
      simpa [hashH3Stmt, runtimeInitialChain] using
        evalWordLit (L := L7) (evm := evm) 0x10325476 (by decide))
  have e9 : ExecStmt config { contract := contract, locals := L8 } evm hashH4Stmt
      (.ok { contract := contract, locals := L9 } evm) := by
    exact ExecStmt.letDecl (by
      simpa [hashH4Stmt, runtimeInitialChain] using
        evalWordLit (L := L8) (evm := evm) 0xc3d2e1f0 (by decide))
  have e10 : ExecStmt config { contract := contract, locals := L9 } evm hashWordsStmt
      (.ok { contract := contract, locals := L10 } evm) := by
    apply ExecStmt.letDecl
    simp only [evalExpr?, EvalResult.bind, bind, pure, defaultValue?]
    norm_num
    rw [initialWords_eq_replicate data]
    change List.replicate 16 (Value.int 0) = List.replicate 16 (Value.int 0)
    rfl
  have hexec : ExecBlock config { contract := contract, locals := L } evm hashPrelude
      (.ok { contract := contract, locals := L10 } evm) :=
    ExecBlock.consNormal e0 <| ExecBlock.consNormal e1 <| ExecBlock.consNormal e2 <|
      ExecBlock.consNormal e3 <| ExecBlock.consNormal e4 <| ExecBlock.consNormal e5 <|
      ExecBlock.consNormal e6 <| ExecBlock.consNormal e7 <| ExecBlock.consNormal e8 <|
      ExecBlock.consNormal e9 <| ExecBlock.consNormal e10 ExecBlock.nil
  have hstore : L10 = hashPreludeStore L data := by rfl
  subst L10
  refine ⟨hexec, ?_, runtimeInitialChain_bound, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold ChainAt
    constructor
    · simp only [hashPreludeStore]
      rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
        store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
        store_get_ne _ _ (by decide), store_get_self]
    constructor
    · simp only [hashPreludeStore]
      rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
        store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]
    constructor
    · simp only [hashPreludeStore]
      rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
        store_get_ne _ _ (by decide), store_get_self]
    constructor
    · simp only [hashPreludeStore]
      rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]
    · simp only [hashPreludeStore]
      rw [store_get_ne _ _ (by decide), store_get_self]
  · rw [hashPreludeStore_get_original L data "data" (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), hdata]
  · simp only [hashPreludeStore]
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]
  · simp only [hashPreludeStore]
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), store_get_self]
  · simp only [hashPreludeStore]
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]
  · simp only [hashPreludeStore]
    rw [store_get_self]
  · simp only [hashPreludeStore]
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]

end Ripemd160
