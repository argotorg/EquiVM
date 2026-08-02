import Examples.Ripemd160.SolmCalls

/-!
# RIPEMD-160 Solm message parser

The inner source loop assembles sixteen little-endian words from calls to `paddedByte`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Ripemd160

def ChainAt (L : Store) (h : RuntimeChain) : Prop :=
  L.get? "h0" = some (wordValue h.h0) ∧
  L.get? "h1" = some (wordValue h.h1) ∧
  L.get? "h2" = some (wordValue h.h2) ∧
  L.get? "h3" = some (wordValue h.h3) ∧
  L.get? "h4" = some (wordValue h.h4)

structure BlockParams where
  data : ByteArray
  blocks : Nat
  block : Nat

def BlockParamsAt (L : Store) (p : BlockParams) : Prop :=
  L.get? "data" = some (.bytes p.data) ∧
  L.get? "bitLen" = some (natValue (p.data.size * 8)) ∧
  L.get? "paddedLen" = some (natValue (Model.paddedLength p.data.size)) ∧
  L.get? "numBlocks" = some (natValue p.blocks) ∧
  L.get? "blk" = some (natValue p.block)

def sourceParsedWord (data : ByteArray) (block wordNo : Nat) : UInt256 :=
  let off := block * 64 + wordNo * 4
  UInt256.lor
    (UInt256.lor
      (UInt256.lor
        (UInt256.ofNat (Model.paddedByte data off))
        (UInt256.shiftLeft (UInt256.ofNat (Model.paddedByte data (off + 1)))
          (UInt256.ofNat 8)))
      (UInt256.shiftLeft (UInt256.ofNat (Model.paddedByte data (off + 2)))
        (UInt256.ofNat 16)))
    (UInt256.shiftLeft (UInt256.ofNat (Model.paddedByte data (off + 3)))
      (UInt256.ofNat 24))

theorem sourceParsedWord_toNat (data : ByteArray) (block wordNo : Nat) :
    (sourceParsedWord data block wordNo).toNat = Model.blockWord data block wordNo := by
  let off := block * 64 + wordNo * 4
  have hb0 := Model.paddedByte_lt data off
  have hb1 := Model.paddedByte_lt data (off + 1)
  have hb2 := Model.paddedByte_lt data (off + 2)
  have hb3 := Model.paddedByte_lt data (off + 3)
  have hs8 : Model.paddedByte data (off + 1) <<< 8 < UInt256.size := by
    rw [Nat.shiftLeft_eq]
    norm_num [UInt256.size]
    omega
  have hs16 : Model.paddedByte data (off + 2) <<< 16 < UInt256.size := by
    rw [Nat.shiftLeft_eq]
    norm_num [UInt256.size]
    omega
  have hs24 : Model.paddedByte data (off + 3) <<< 24 < UInt256.size := by
    rw [Nat.shiftLeft_eq]
    norm_num [UInt256.size]
    omega
  unfold sourceParsedWord Model.blockWord
  dsimp only
  simp only [word_toNat_lor]
  rw [ushl_ofNat_toNat, ushl_ofNat_toNat, ushl_ofNat_toNat] <;> norm_num
  rw [ulit_toNat', ulit_toNat', ulit_toNat', ulit_toNat'] <;>
    try { exact lt_trans (Model.paddedByte_lt _ _) (by decide) }
  rw [Nat.mod_eq_of_lt hs8, Nat.mod_eq_of_lt hs16, Nat.mod_eq_of_lt hs24]
  change ((Model.paddedByte data off ||| Model.paddedByte data (off + 1) <<< 8) |||
      Model.paddedByte data (off + 2) <<< 16) ||| Model.paddedByte data (off + 3) <<< 24 = _
  simpa only [off, Nat.or_assoc, Nat.or_comm]

theorem sourceParsedWord_eq_model (data : ByteArray) (block wordNo : Nat) :
    sourceParsedWord data block wordNo = UInt256.ofNat (Model.blockWord data block wordNo) := by
  apply u256_inj
  rw [sourceParsedWord_toNat]
  rw [ulit_toNat']
  have h0 := Model.paddedByte_lt data (block * 64 + wordNo * 4)
  have h1 := Model.paddedByte_lt data (block * 64 + wordNo * 4 + 1)
  have h2 := Model.paddedByte_lt data (block * 64 + wordNo * 4 + 2)
  have h3 := Model.paddedByte_lt data (block * 64 + wordNo * 4 + 3)
  unfold Model.blockWord
  have hp24 : Model.paddedByte data (block * 64 + wordNo * 4 + 3) <<< 24 < 2 ^ 32 := by
    rw [Nat.shiftLeft_eq]
    norm_num
    omega
  have hp16 : Model.paddedByte data (block * 64 + wordNo * 4 + 2) <<< 16 < 2 ^ 32 := by
    rw [Nat.shiftLeft_eq]
    norm_num
    omega
  have hp8 : Model.paddedByte data (block * 64 + wordNo * 4 + 1) <<< 8 < 2 ^ 32 := by
    rw [Nat.shiftLeft_eq]
    norm_num
    omega
  exact lt_trans (Nat.or_lt_two_pow
    (Nat.or_lt_two_pow hp24 hp16)
    (Nat.or_lt_two_pow hp8 (lt_trans h0 (by norm_num)))) (by decide)

def parserWords (base : Fin 16 -> UInt256) (data : ByteArray)
    (block completed : Nat) : List Value :=
  List.ofFn fun i : Fin 16 =>
    if i.val < completed then
      wordValue (UInt256.ofNat (Model.blockWord data block i.val))
    else wordValue (base i)

@[simp] theorem parserWords_length (base : Fin 16 -> UInt256) (data : ByteArray)
    (block completed : Nat) :
    (parserWords base data block completed).length = 16 := by
  simp [parserWords]

theorem parserWords_get (base : Fin 16 -> UInt256) (data : ByteArray)
    (block completed i : Nat) (hi : i < 16) :
    (parserWords base data block completed)[i] =
      if i < completed then wordValue (UInt256.ofNat (Model.blockWord data block i))
      else wordValue (base ⟨i, hi⟩) := by
  unfold parserWords
  rw [List.getElem_ofFn]

theorem updateNth_eq_set {α : Type u} (xs : List α) (i : Nat) (value : α)
    (hi : i < xs.length) : updateNth? xs i value = some (xs.set i value) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
      cases i with
      | zero => rfl
      | succ i =>
          simp only [updateNth?, List.set]
          rw [ih i (by simpa using hi)]
          rfl

theorem parserWords_set_next (base : Fin 16 -> UInt256) (data : ByteArray)
    (block completed : Nat)
    (hc : completed < 16) :
    (parserWords base data block completed).set completed
      (wordValue (UInt256.ofNat (Model.blockWord data block completed))) =
      parserWords base data block (completed + 1) := by
  apply List.ext_getElem
  · simp
  · intro i hleft hright
    rw [List.getElem_set]
    unfold parserWords
    simp only [List.getElem_ofFn]
    by_cases hi : completed = i
    · subst i
      simp
    · by_cases hlt : i < completed
      · have hnext : i < completed + 1 := by omega
        simp [hi, hlt, hnext]
      · have hgt : completed < i := by omega
        simp [hi, hlt, show ¬i < completed + 1 by omega]

def parserBody : List Stmt :=
  [ .letDecl "off" (some (.elem (.int (.uint ⟨256, by decide⟩))))
      (.binary .add
        (.binary .mul (.var "blk") (.intLit 64))
        (.binary .mul (.var "wordNo") (.intLit 4))),
    .internalCall "paddedByte"
      [.var "data", .var "off", .var "bitLen", .var "paddedLen"] "b0",
    .internalCall "paddedByte"
      [.var "data", .binary .add (.var "off") (.intLit 1),
        .var "bitLen", .var "paddedLen"] "b1",
    .internalCall "paddedByte"
      [.var "data", .binary .add (.var "off") (.intLit 2),
        .var "bitLen", .var "paddedLen"] "b2",
    .internalCall "paddedByte"
      [.var "data", .binary .add (.var "off") (.intLit 3),
        .var "bitLen", .var "paddedLen"] "b3",
    .assign .localVar { base := "words", steps := [.aindex (.var "wordNo")] }
      (.binary .bitOr
        (.binary .bitOr
          (.binary .bitOr (.var "b0") (.binary .shl (.var "b1") (.intLit 8)))
          (.binary .shl (.var "b2") (.intLit 16)))
        (.binary .shl (.var "b3") (.intLit 24))) ]

theorem parserBodyStep {L : Store} (evm : EVM.State) (base : Fin 16 -> UInt256)
    (data : ByteArray) (block wordNo : Nat)
    (hsmall : data.size ≤ maxFallbackCalldataSize)
    (hblock : block < Model.paddedLength data.size / 64)
    (hword : wordNo < 16)
    (hdata : L.get? "data" = some (.bytes data))
    (hbit : L.get? "bitLen" = some (natValue (data.size * 8)))
    (hpad : L.get? "paddedLen" = some (natValue (Model.paddedLength data.size)))
    (hblk : L.get? "blk" = some (natValue block))
    (hwordVar : L.get? "wordNo" = some (natValue wordNo))
    (hwords : L.get? "words" = some (.array (parserWords base data block wordNo))) :
    let Loff := L.insert "off" (natValue (block * 64 + wordNo * 4))
    let L0 := Loff.insert "b0" (natValue
      (Model.paddedByte data (block * 64 + wordNo * 4)))
    let L1 := L0.insert "b1" (natValue
      (Model.paddedByte data (block * 64 + wordNo * 4 + 1)))
    let L2 := L1.insert "b2" (natValue
      (Model.paddedByte data (block * 64 + wordNo * 4 + 2)))
    let L3 := L2.insert "b3" (natValue
      (Model.paddedByte data (block * 64 + wordNo * 4 + 3)))
    let Lout := L3.insert "words" (.array (parserWords base data block (wordNo + 1)))
    ExecBlock config { contract := contract, locals := L } evm parserBody
      (.ok { contract := contract, locals := Lout } evm) := by
  dsimp only
  let off := block * 64 + wordNo * 4
  let Loff := L.insert "off" (natValue off)
  let L0 := Loff.insert "b0" (natValue (Model.paddedByte data off))
  let L1 := L0.insert "b1" (natValue (Model.paddedByte data (off + 1)))
  let L2 := L1.insert "b2" (natValue (Model.paddedByte data (off + 2)))
  let L3 := L2.insert "b3" (natValue (Model.paddedByte data (off + 3)))
  let Lout := L3.insert "words" (.array (parserWords base data block (wordNo + 1)))
  have hoffEval : evalExpr? config { contract := contract, locals := L } evm
      (.binary .add
        (.binary .mul (.var "blk") (.intLit 64))
        (.binary .mul (.var "wordNo") (.intLit 4))) = .ok (natValue off) := by
    exact evalNatAdd
      (evalNatMul (evalNatVar hblk) (by simp [evalExpr?, natValue, pure]))
      (evalNatMul (evalNatVar hwordVar) (by simp [evalExpr?, natValue, pure]))
  have hmod := hashPaddedLength_mod data.size
  have hb : block * 64 < Model.paddedLength data.size := by omega
  have hp0 : off < Model.paddedLength data.size := by dsimp [off]; omega
  have hp1 : off + 1 < Model.paddedLength data.size := by dsimp [off]; omega
  have hp2 : off + 2 < Model.paddedLength data.size := by dsimp [off]; omega
  have hp3 : off + 3 < Model.paddedLength data.size := by dsimp [off]; omega
  have hdataOff : Loff.get? "data" = some (.bytes data) := by
    simp only [Loff]
    rw [store_get_ne _ _ (by decide), hdata]
  have hbitOff : Loff.get? "bitLen" = some (natValue (data.size * 8)) := by
    simp only [Loff]
    rw [store_get_ne _ _ (by decide), hbit]
  have hpadOff : Loff.get? "paddedLen" =
      some (natValue (Model.paddedLength data.size)) := by
    simp only [Loff]
    rw [store_get_ne _ _ (by decide), hpad]
  have hoff : Loff.get? "off" = some (natValue off) := by simp [Loff]
  have hcall0 : ExecStmt config { contract := contract, locals := Loff } evm
      (.internalCall "paddedByte"
        [.var "data", .var "off", .var "bitLen", .var "paddedLen"] "b0")
      (.ok { contract := contract, locals := L0 } evm) := by
    simpa [L0] using paddedByteCall evm data off hsmall hp0 hdataOff
      (evalNatVar hoff) hbitOff hpadOff
  have hdata0 : L0.get? "data" = some (.bytes data) := by
    simp only [L0]
    rw [store_get_ne _ _ (by decide), hdataOff]
  have hbit0 : L0.get? "bitLen" = some (natValue (data.size * 8)) := by
    simp only [L0]
    rw [store_get_ne _ _ (by decide), hbitOff]
  have hpad0 : L0.get? "paddedLen" = some (natValue (Model.paddedLength data.size)) := by
    simp only [L0]
    rw [store_get_ne _ _ (by decide), hpadOff]
  have hoff0 : L0.get? "off" = some (natValue off) := by
    simp only [L0]
    rw [store_get_ne _ _ (by decide), hoff]
  have hcall1 : ExecStmt config { contract := contract, locals := L0 } evm
      (.internalCall "paddedByte"
        [.var "data", .binary .add (.var "off") (.intLit 1),
          .var "bitLen", .var "paddedLen"] "b1")
      (.ok { contract := contract, locals := L1 } evm) := by
    simpa [L1] using paddedByteCall evm data (off + 1) hsmall hp1 hdata0
      (evalNatAdd (evalNatVar hoff0) (by simp [evalExpr?, natValue, pure])) hbit0 hpad0
  have hdata1 : L1.get? "data" = some (.bytes data) := by
    simp only [L1]
    rw [store_get_ne _ _ (by decide), hdata0]
  have hbit1 : L1.get? "bitLen" = some (natValue (data.size * 8)) := by
    simp only [L1]
    rw [store_get_ne _ _ (by decide), hbit0]
  have hpad1 : L1.get? "paddedLen" = some (natValue (Model.paddedLength data.size)) := by
    simp only [L1]
    rw [store_get_ne _ _ (by decide), hpad0]
  have hoff1 : L1.get? "off" = some (natValue off) := by
    simp only [L1]
    rw [store_get_ne _ _ (by decide), hoff0]
  have hcall2 : ExecStmt config { contract := contract, locals := L1 } evm
      (.internalCall "paddedByte"
        [.var "data", .binary .add (.var "off") (.intLit 2),
          .var "bitLen", .var "paddedLen"] "b2")
      (.ok { contract := contract, locals := L2 } evm) := by
    simpa [L2] using paddedByteCall evm data (off + 2) hsmall hp2 hdata1
      (evalNatAdd (evalNatVar hoff1) (by simp [evalExpr?, natValue, pure])) hbit1 hpad1
  have hdata2 : L2.get? "data" = some (.bytes data) := by
    simp only [L2]
    rw [store_get_ne _ _ (by decide), hdata1]
  have hbit2 : L2.get? "bitLen" = some (natValue (data.size * 8)) := by
    simp only [L2]
    rw [store_get_ne _ _ (by decide), hbit1]
  have hpad2 : L2.get? "paddedLen" = some (natValue (Model.paddedLength data.size)) := by
    simp only [L2]
    rw [store_get_ne _ _ (by decide), hpad1]
  have hoff2 : L2.get? "off" = some (natValue off) := by
    simp only [L2]
    rw [store_get_ne _ _ (by decide), hoff1]
  have hcall3 : ExecStmt config { contract := contract, locals := L2 } evm
      (.internalCall "paddedByte"
        [.var "data", .binary .add (.var "off") (.intLit 3),
          .var "bitLen", .var "paddedLen"] "b3")
      (.ok { contract := contract, locals := L3 } evm) := by
    simpa [L3] using paddedByteCall evm data (off + 3) hsmall hp3 hdata2
      (evalNatAdd (evalNatVar hoff2) (by simp [evalExpr?, natValue, pure])) hbit2 hpad2
  have hb0 : L3.get? "b0" = some (natValue (Model.paddedByte data off)) := by
    simp only [L3, L2, L1, L0]
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), store_get_self]
  have hb1 : L3.get? "b1" = some (natValue (Model.paddedByte data (off + 1))) := by
    simp only [L3, L2, L1]
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]
  have hb2 : L3.get? "b2" = some (natValue (Model.paddedByte data (off + 2))) := by
    simp only [L3, L2]
    rw [store_get_ne _ _ (by decide), store_get_self]
  have hb3 : L3.get? "b3" = some (natValue (Model.paddedByte data (off + 3))) := by
    simp only [L3]
    rw [store_get_self]
  have hword3 : L3.get? "wordNo" = some (natValue wordNo) := by
    simp only [L3, L2, L1, L0, Loff]
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hwordVar]
  have hwords3 : L3.get? "words" = some (.array (parserWords base data block wordNo)) := by
    simp only [L3, L2, L1, L0, Loff]
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hwords]
  have asWord (p : Nat) (hp : p < UInt256.size) {name : Ident}
      (hget : L3.get? name = some (natValue p)) :
      evalExpr? config { contract := contract, locals := L3 } evm (.var name) =
        .ok (wordValue (UInt256.ofNat p)) := by
    simpa [wordValue, natValue, ulit_toNat' p hp] using evalNatVar hget
  have hpb0 := Model.paddedByte_lt data off
  have hpb1 := Model.paddedByte_lt data (off + 1)
  have hpb2 := Model.paddedByte_lt data (off + 2)
  have hpb3 := Model.paddedByte_lt data (off + 3)
  have eb0 := asWord _ (lt_trans hpb0 (by decide)) hb0
  have eb1 := asWord _ (lt_trans hpb1 (by decide)) hb1
  have eb2 := asWord _ (lt_trans hpb2 (by decide)) hb2
  have eb3 := asWord _ (lt_trans hpb3 (by decide)) hb3
  have e8 := evalWordLit (L := L3) (evm := evm) 8 (by decide)
  have e16 := evalWordLit (L := L3) (evm := evm) 16 (by decide)
  have e24 := evalWordLit (L := L3) (evm := evm) 24 (by decide)
  have erhs := evalBitOr
    (evalBitOr (evalBitOr eb0 (evalShl 8 (by decide) eb1 e8))
      (evalShl 16 (by decide) eb2 e16))
    (evalShl 24 (by decide) eb3 e24)
  change evalExpr? config { contract := contract, locals := L3 } evm _ =
    .ok (wordValue (sourceParsedWord data block wordNo)) at erhs
  rw [sourceParsedWord_eq_model] at erhs
  have hlookupWord : lookupNth? (parserWords base data block wordNo) wordNo =
      some (wordValue (base ⟨wordNo, hword⟩)) := by
    rw [lookupNth_getElem _ wordNo (by simp [hword])]
    simpa using parserWords_get base data block wordNo wordNo hword
  have hupdateWord : updateNth? (parserWords base data block wordNo) wordNo
      (wordValue (UInt256.ofNat (Model.blockWord data block wordNo))) =
      some (parserWords base data block (wordNo + 1)) := by
    rw [updateNth_eq_set _ wordNo _ (by simp [hword]),
      parserWords_set_next base data block wordNo hword]
  have hupdatePath : updateLocalPath? config { contract := contract, locals := L3 } evm
      (.array (parserWords base data block wordNo)) [.aindex (.var "wordNo")]
      (wordValue (UInt256.ofNat (Model.blockWord data block wordNo))) =
      .ok (.array (parserWords base data block (wordNo + 1))) := by
    simp only [updateLocalPath?]
    rw [evalNatVar hword3]
    simp only [EvalResult.bind, bind]
    rw [if_pos (by simp [parserWords_length, hword])]
    have hnneg : ¬((wordNo : Int) < 0) := not_lt_of_ge (Int.natCast_nonneg _)
    have htoNat : (wordNo : Int).toNat = wordNo := rfl
    simp only [lookupIndex?, intToNat?, Int.ofNat_eq_natCast, if_neg hnneg,
      htoNat, Option.bind_some,
      EvalResult.ofOption, hlookupWord, updateIndex?, hupdateWord, EvalResult.bind, bind, pure]
  have hassign : assignStorageRef? config { contract := contract, locals := L3 } evm
      .localVar { base := "words", steps := [.aindex (.var "wordNo")] }
      (wordValue (UInt256.ofNat (Model.blockWord data block wordNo))) =
      .ok ({ contract := contract, locals := Lout }, evm) := by
    rw [assignStorageRef?, hwords3]
    simp only
    rw [hupdatePath]
    simp only [EvalResult.bind, bind, pure]
    rfl
  apply ExecBlock.consNormal (ExecStmt.letDecl hoffEval)
  apply ExecBlock.consNormal hcall0
  apply ExecBlock.consNormal hcall1
  apply ExecBlock.consNormal hcall2
  apply ExecBlock.consNormal hcall3
  exact ExecBlock.consNormal (ExecStmt.assign erhs hassign) ExecBlock.nil

def parserStepStore (L : Store) (base : Fin 16 -> UInt256) (data : ByteArray)
    (block wordNo : Nat) : Store :=
  let off := block * 64 + wordNo * 4
  (((((L.insert "off" (natValue off)).insert "b0" (natValue (Model.paddedByte data off))).insert
    "b1" (natValue (Model.paddedByte data (off + 1)))).insert
    "b2" (natValue (Model.paddedByte data (off + 2)))).insert
    "b3" (natValue (Model.paddedByte data (off + 3)))).insert
    "words" (.array (parserWords base data block (wordNo + 1)))

theorem parserStepStore_get_ne (L : Store) (base : Fin 16 -> UInt256)
    (data : ByteArray) (block wordNo : Nat)
    (name : Ident)
    (hwords : ("words" == name) = false) (hb3 : ("b3" == name) = false)
    (hb2 : ("b2" == name) = false) (hb1 : ("b1" == name) = false)
    (hb0 : ("b0" == name) = false) (hoff : ("off" == name) = false) :
    (parserStepStore L base data block wordNo).get? name = L.get? name := by
  simp only [parserStepStore]
  rw [store_get_ne _ _ hwords, store_get_ne _ _ hb3, store_get_ne _ _ hb2,
    store_get_ne _ _ hb1, store_get_ne _ _ hb0, store_get_ne _ _ hoff]

@[simp] theorem parserStepStore_words (L : Store) (base : Fin 16 -> UInt256)
    (data : ByteArray)
    (block wordNo : Nat) :
    (parserStepStore L base data block wordNo).get? "words" =
      some (.array (parserWords base data block (wordNo + 1))) := by
  simp only [parserStepStore]
  rw [store_get_self]

def parserPost : List Stmt :=
  [.assign .localVar { base := "wordNo" }
    (.binary .add (.var "wordNo") (.intLit 1))]

def parserCond : Expr := .binary .lt (.var "wordNo") (.intLit 16)

def parserInit : List Stmt :=
  [.letDecl "wordNo" (some (.elem (.int (.uint ⟨256, by decide⟩)))) (.intLit 0)]

def parserFor : Stmt := .for parserInit parserCond parserPost parserBody

theorem parserForReturns {L : Store} (evm : EVM.State) (base : Fin 16 -> UInt256)
    (data : ByteArray) (block : Nat) (chain : RuntimeChain)
    (hsmall : data.size ≤ maxFallbackCalldataSize)
    (hblock : block < Model.paddedLength data.size / 64)
    (hdata : L.get? "data" = some (.bytes data))
    (hbit : L.get? "bitLen" = some (natValue (data.size * 8)))
    (hpad : L.get? "paddedLen" = some (natValue (Model.paddedLength data.size)))
    (hnum : L.get? "numBlocks" = some (natValue (Model.paddedLength data.size / 64)))
    (hblk : L.get? "blk" = some (natValue block))
    (hwords : L.get? "words" = some (.array (parserWords base data block 0)))
    (hmask : L.get? "mask32" = some (wordValue mask32Word))
    (hchain : ChainAt L chain) :
    ∃ L', ExecStmt config { contract := contract, locals := L } evm parserFor
        (.ok { contract := contract, locals := L' } evm) ∧
      L'.get? "data" = some (.bytes data) ∧
      L'.get? "bitLen" = some (natValue (data.size * 8)) ∧
      L'.get? "paddedLen" = some (natValue (Model.paddedLength data.size)) ∧
      L'.get? "numBlocks" = some (natValue (Model.paddedLength data.size / 64)) ∧
      L'.get? "blk" = some (natValue block) ∧
      L'.get? "words" = some (.array (parserWords base data block 16)) ∧
      L'.get? "mask32" = some (wordValue mask32Word) ∧
      ChainAt L' chain := by
  let P : Nat → Store → Prop := fun v S =>
    ∃ wordNo, S.get? "wordNo" = some (natValue wordNo) ∧ wordNo + v = 16 ∧
      S.get? "data" = some (.bytes data) ∧
      S.get? "bitLen" = some (natValue (data.size * 8)) ∧
      S.get? "paddedLen" = some (natValue (Model.paddedLength data.size)) ∧
      S.get? "numBlocks" = some (natValue (Model.paddedLength data.size / 64)) ∧
      S.get? "blk" = some (natValue block) ∧
      S.get? "words" = some (.array (parserWords base data block wordNo)) ∧
      S.get? "mask32" = some (wordValue mask32Word) ∧
      ChainAt S chain
  have hfalse : ∀ S, P 0 S →
      evalExpr? config { contract := contract, locals := S } evm parserCond =
        .ok (.bool false) := by
    intro S hP
    rcases hP with ⟨wordNo, hword, hvar, _⟩
    have he := evalNatLt (evalNatVar hword)
      (show evalExpr? config { contract := contract, locals := S } evm (.intLit 16) =
        .ok (natValue 16) by simp [evalExpr?, natValue, pure])
    have hw : wordNo = 16 := by omega
    simpa [parserCond, hw] using he
  have htrue : ∀ v S, P (v + 1) S →
      evalExpr? config { contract := contract, locals := S } evm parserCond =
        .ok (.bool true) := by
    intro v S hP
    rcases hP with ⟨wordNo, hword, hvar, _⟩
    have he := evalNatLt (evalNatVar hword)
      (show evalExpr? config { contract := contract, locals := S } evm (.intLit 16) =
        .ok (natValue 16) by simp [evalExpr?, natValue, pure])
    have hw : wordNo < 16 := by omega
    simpa [parserCond, decide_eq_true hw] using he
  have hstep : ∀ v S, P (v + 1) S →
      ∃ S1, ExecBlock config { contract := contract, locals := S } evm parserBody
            (.ok { contract := contract, locals := S1 } evm) ∧
        ∃ S', ExecBlock config { contract := contract, locals := S1 } evm parserPost
            (.ok { contract := contract, locals := S' } evm) ∧ P v S' := by
    intro v S hP
    rcases hP with ⟨wordNo, hword, hvar, hd, hbi, hpa, hnumS, hbl, hws, hmaskS,
      hchainS⟩
    have hw : wordNo < 16 := by omega
    let S1 := parserStepStore S base data block wordNo
    have hbody : ExecBlock config { contract := contract, locals := S } evm parserBody
        (.ok { contract := contract, locals := S1 } evm) := by
      simpa [S1, parserStepStore] using
        parserBodyStep evm base data block wordNo hsmall hblock hw hd hbi hpa hbl hword hws
    have preserve (name : Ident)
        (hwordsName : ("words" == name) = false) (hb3 : ("b3" == name) = false)
        (hb2 : ("b2" == name) = false) (hb1 : ("b1" == name) = false)
        (hb0 : ("b0" == name) = false) (hoff : ("off" == name) = false) :
        S1.get? name = S.get? name := by
      simpa [S1] using parserStepStore_get_ne S base data block wordNo name
        hwordsName hb3 hb2 hb1 hb0 hoff
    have hword1 : S1.get? "wordNo" = some (natValue wordNo) := by
      rw [preserve "wordNo" (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), hword]
    have hdata1 : S1.get? "data" = some (.bytes data) := by
      rw [preserve "data" (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), hd]
    have hbit1 : S1.get? "bitLen" = some (natValue (data.size * 8)) := by
      rw [preserve "bitLen" (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), hbi]
    have hpad1 : S1.get? "paddedLen" =
        some (natValue (Model.paddedLength data.size)) := by
      rw [preserve "paddedLen" (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), hpa]
    have hblk1 : S1.get? "blk" = some (natValue block) := by
      rw [preserve "blk" (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), hbl]
    have hnum1 : S1.get? "numBlocks" =
        some (natValue (Model.paddedLength data.size / 64)) := by
      rw [preserve "numBlocks" (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), hnumS]
    have hwords1 : S1.get? "words" =
        some (.array (parserWords base data block (wordNo + 1))) := by
      simpa [S1] using parserStepStore_words S base data block wordNo
    have hmask1 : S1.get? "mask32" = some (wordValue mask32Word) := by
      rw [preserve "mask32" (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), hmaskS]
    have hchain1 : ChainAt S1 chain := by
      rcases hchainS with ⟨hh0, hh1, hh2, hh3, hh4⟩
      exact ⟨by rw [preserve "h0" (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide), hh0],
        by rw [preserve "h1" (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide), hh1],
        by rw [preserve "h2" (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide), hh2],
        by rw [preserve "h3" (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide), hh3],
        by rw [preserve "h4" (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide), hh4]⟩
    let S' := S1.insert "wordNo" (natValue (wordNo + 1))
    have hpostEval : evalExpr? config { contract := contract, locals := S1 } evm
        (.binary .add (.var "wordNo") (.intLit 1)) = .ok (natValue (wordNo + 1)) :=
      evalNatAdd (evalNatVar hword1) (by simp [evalExpr?, natValue, pure])
    have hpostAssign : assignStorageRef? config
        { contract := contract, locals := S1 } evm .localVar { base := "wordNo" }
        (natValue (wordNo + 1)) = .ok ({ contract := contract, locals := S' }, evm) := by
      rw [assignStorageRef?, hword1]
      simp only [updateLocalPath?, EvalResult.bind, bind, pure]
      rfl
    have hpost : ExecBlock config { contract := contract, locals := S1 } evm parserPost
        (.ok { contract := contract, locals := S' } evm) := by
      exact ExecBlock.consNormal (ExecStmt.assign hpostEval hpostAssign) ExecBlock.nil
    have hword' : S'.get? "wordNo" = some (natValue (wordNo + 1)) := by simp [S']
    have hdata' : S'.get? "data" = some (.bytes data) := by
      simp only [S']; rw [store_get_ne _ _ (by decide), hdata1]
    have hbit' : S'.get? "bitLen" = some (natValue (data.size * 8)) := by
      simp only [S']; rw [store_get_ne _ _ (by decide), hbit1]
    have hpad' : S'.get? "paddedLen" =
        some (natValue (Model.paddedLength data.size)) := by
      simp only [S']; rw [store_get_ne _ _ (by decide), hpad1]
    have hblk' : S'.get? "blk" = some (natValue block) := by
      simp only [S']; rw [store_get_ne _ _ (by decide), hblk1]
    have hnum' : S'.get? "numBlocks" =
        some (natValue (Model.paddedLength data.size / 64)) := by
      simp only [S']; rw [store_get_ne _ _ (by decide), hnum1]
    have hwords' : S'.get? "words" =
        some (.array (parserWords base data block (wordNo + 1))) := by
      simp only [S']; rw [store_get_ne _ _ (by decide), hwords1]
    have hmask' : S'.get? "mask32" = some (wordValue mask32Word) := by
      simp only [S']; rw [store_get_ne _ _ (by decide), hmask1]
    have hchain' : ChainAt S' chain := by
      rcases hchain1 with ⟨hh0, hh1, hh2, hh3, hh4⟩
      exact ⟨by simp only [S']; rw [store_get_ne _ _ (by decide), hh0],
        by simp only [S']; rw [store_get_ne _ _ (by decide), hh1],
        by simp only [S']; rw [store_get_ne _ _ (by decide), hh2],
        by simp only [S']; rw [store_get_ne _ _ (by decide), hh3],
        by simp only [S']; rw [store_get_ne _ _ (by decide), hh4]⟩
    refine ⟨S1, hbody, S', hpost, ?_⟩
    exact ⟨wordNo + 1, hword', by omega, hdata', hbit', hpad', hnum', hblk', hwords',
      hmask', hchain'⟩
  let L0 := L.insert "wordNo" (natValue 0)
  have hinit : ExecBlock config { contract := contract, locals := L } evm parserInit
      (.ok { contract := contract, locals := L0 } evm) := by
    have hzero : evalExpr? config { contract := contract, locals := L } evm (.intLit 0) =
        .ok (natValue 0) := by simp [evalExpr?, natValue, pure]
    exact ExecBlock.consNormal (ExecStmt.letDecl hzero) ExecBlock.nil
  have hdata0 : L0.get? "data" = some (.bytes data) := by
    simp only [L0]; rw [store_get_ne _ _ (by decide), hdata]
  have hbit0 : L0.get? "bitLen" = some (natValue (data.size * 8)) := by
    simp only [L0]; rw [store_get_ne _ _ (by decide), hbit]
  have hpad0 : L0.get? "paddedLen" = some (natValue (Model.paddedLength data.size)) := by
    simp only [L0]; rw [store_get_ne _ _ (by decide), hpad]
  have hblk0 : L0.get? "blk" = some (natValue block) := by
    simp only [L0]; rw [store_get_ne _ _ (by decide), hblk]
  have hnum0 : L0.get? "numBlocks" =
      some (natValue (Model.paddedLength data.size / 64)) := by
    simp only [L0]; rw [store_get_ne _ _ (by decide), hnum]
  have hwords0 : L0.get? "words" = some (.array (parserWords base data block 0)) := by
    simp only [L0]; rw [store_get_ne _ _ (by decide), hwords]
  have hmask0 : L0.get? "mask32" = some (wordValue mask32Word) := by
    simp only [L0]; rw [store_get_ne _ _ (by decide), hmask]
  have hchain0 : ChainAt L0 chain := by
    rcases hchain with ⟨hh0, hh1, hh2, hh3, hh4⟩
    exact ⟨by simp only [L0]; rw [store_get_ne _ _ (by decide), hh0],
      by simp only [L0]; rw [store_get_ne _ _ (by decide), hh1],
      by simp only [L0]; rw [store_get_ne _ _ (by decide), hh2],
      by simp only [L0]; rw [store_get_ne _ _ (by decide), hh3],
      by simp only [L0]; rw [store_get_ne _ _ (by decide), hh4]⟩
  have hP0 : P 16 L0 :=
    ⟨0, by simp [L0], by omega, hdata0, hbit0, hpad0, hnum0, hblk0, hwords0,
      hmask0, hchain0⟩
  obtain ⟨L', hloop, hfinal⟩ := execFor_var P hfalse htrue hstep 16 L0 hP0
  rcases hfinal with ⟨wordNo, hword, hvar, hd, hb, hp, hn, hbl, hws, hm, hc⟩
  have hw : wordNo = 16 := by omega
  subst wordNo
  refine ⟨L', ?_, hd, hb, hp, hn, hbl, hws, hm, hc⟩
  exact ExecStmt.for hinit hloop

end Ripemd160
