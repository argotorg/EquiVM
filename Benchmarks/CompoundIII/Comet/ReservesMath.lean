import Benchmarks.CompoundIII.Comet.ReservesStart
import Benchmarks.CompoundIII.Comet.Signed256
import Benchmarks.CompoundIII.Comet.SignedWord

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

def reservesValue (v : CometWithExtendedAssetListImmutables) (w0 w1 time balance : UInt256) : Int :=
  Int.ofNat balance.toNat - Int.ofNat (totalReadWord v w0 w1 time false).toNat +
    Int.ofNat (totalReadWord v w0 w1 time true).toNat

def reservesWord (v : CometWithExtendedAssetListImmutables) (w0 w1 time balance : UInt256) : UInt256 :=
  UInt256.sub balance (totalReadWord v w0 w1 time false) + totalReadWord v w0 w1 time true

def ReservesMathValid (v : CometWithExtendedAssetListImmutables) (w0 w1 time balance : UInt256) : Prop :=
  balance.toNat < 2^255 ∧ reservesValue v w0 w1 time balance < (2^255 : Int)

instance (v : CometWithExtendedAssetListImmutables) (w0 w1 time balance : UInt256) :
    Decidable (ReservesMathValid v w0 w1 time balance) := inferInstanceAs (Decidable (_ ∧ _))

theorem totalReadWord_lt {v w0 w1 time} (hv : CurrentIndicesValid v w0 w1 time) (borrow : Bool) :
    (totalReadWord v w0 w1 time borrow).toNat < 2^168 :=
  presentValueWord_lt (currentIndex_lt hv borrow) (totalsPrincipalWord_lt w1 borrow)

theorem reservesWord_signed {v w0 w1 time balance} (hv : CurrentIndicesValid v w0 w1 time)
    (hm : ReservesMathValid v w0 w1 time balance) :
    signedWord (reservesWord v w0 w1 time balance) = reservesValue v w0 w1 time balance := by
  have hs := totalReadWord_lt hv false
  have hb := totalReadWord_lt hv true
  have hd := signedWord_sub_low hm.1 (lt_trans hs (by decide))
  unfold reservesWord
  rw [signedWord_add_of_range]
  · rw [hd]
    rfl
  · rw [hd]
    simp only [Int.ofNat_eq_natCast]
    omega
  · rw [hd]
    exact hm.2

def reservesPresentBlock : List Stmt :=
  [.internalCall "presentValueSupply" [.var "baseSupplyIndex_", .var "supplyPrincipal"] "totalSupply_",
    .internalCall "presentValueBorrow" [.var "baseBorrowIndex_", .var "borrowPrincipal"] "totalBorrow_"]

def reservesSignedBlock : List Stmt :=
  [.internalCall "signed256" [.var "balance"] "__c5",
    .internalCall "signed256" [.var "totalSupply_"] "__c6",
    .letDecl "netSupply" (some (.elem (.int (.sint ⟨256, by decide⟩))))
      (.inRange (.sint ⟨256, by decide⟩) (.binary .sub (.var "__c5") (.var "__c6"))),
    .internalCall "signed256" [.var "totalBorrow_"] "__c7",
    .return [.inRange (.sint ⟨256, by decide⟩) (.binary .add (.var "netSupply") (.var "__c7"))]]

def reservesBalanceFrame (v : CometWithExtendedAssetListImmutables) (w0 w1 time balance : UInt256) : Frame :=
  { reservesReadyFrame v w0 w1 time with
    locals := (reservesReadyFrame v w0 w1 time).locals.insert "balance" (.int balance.toNat) }

def reservesTotalsFrame (v : CometWithExtendedAssetListImmutables) (w0 w1 time balance : UInt256) : Frame :=
  { reservesBalanceFrame v w0 w1 time balance with
    locals := ((reservesBalanceFrame v w0 w1 time balance).locals.insert
      "totalSupply_" (.int (totalReadWord v w0 w1 time false).toNat)).insert
      "totalBorrow_" (.int (totalReadWord v w0 w1 time true).toNat) }

def reservesFinalFrame (v : CometWithExtendedAssetListImmutables) (w0 w1 time balance : UInt256) : Frame :=
  { reservesTotalsFrame v w0 w1 time balance with
    locals := ((((reservesTotalsFrame v w0 w1 time balance).locals.insert
      "__c5" (.int balance.toNat)).insert
      "__c6" (.int (totalReadWord v w0 w1 time false).toNat)).insert
      "netSupply" (.int (Int.ofNat balance.toNat -
        Int.ofNat (totalReadWord v w0 w1 time false).toNat))).insert
      "__c7" (.int (totalReadWord v w0 w1 time true).toNat) }

theorem reservesPresent_result (v : CometWithExtendedAssetListImmutables)
    (w0 w1 time balance : UInt256) (evm : EVM.State) (hv : CurrentIndicesValid v w0 w1 time) :
    ExecBlock config (reservesBalanceFrame v w0 w1 time balance) evm reservesPresentBlock
      (.ok (reservesTotalsFrame v w0 w1 time balance) evm) := by
  apply ExecBlock.consNormal (presentValue_call _ evm false
    (currentIndex v w0 w1 time false) (totalsPrincipalWord w1 false) _ _ "totalSupply_"
    rfl (currentIndex_lt hv false) (totalsPrincipalWord_lt _ _) (by
      simp only [evalExpr?, reservesBalanceFrame, reservesReadyFrame,
        Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, EvalResult.ofOption]
      rfl) (by
      simp only [evalExpr?, reservesBalanceFrame, reservesReadyFrame, reservesIndicesFrame,
        reservesSnapshotFrame, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
        EvalResult.ofOption]
      rfl))
  apply ExecBlock.consNormal (presentValue_call _ evm true
    (currentIndex v w0 w1 time true) (totalsPrincipalWord w1 true) _ _ "totalBorrow_"
    rfl (currentIndex_lt hv true) (totalsPrincipalWord_lt _ _) (by
      simp only [evalExpr?, reservesBalanceFrame, reservesReadyFrame,
        Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, EvalResult.ofOption]
      rfl) (by
      simp only [evalExpr?, reservesBalanceFrame, reservesReadyFrame, reservesIndicesFrame,
        reservesSnapshotFrame, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
        EvalResult.ofOption]
      rfl))
  exact ExecBlock.nil

theorem reservesSigned_result (v : CometWithExtendedAssetListImmutables)
    (w0 w1 time balance : UInt256) (evm : EVM.State) (hv : CurrentIndicesValid v w0 w1 time) :
    ExecBlock config (reservesTotalsFrame v w0 w1 time balance) evm reservesSignedBlock
      (if ReservesMathValid v w0 w1 time balance then
        .returned (reservesFinalFrame v w0 w1 time balance) evm
          (some [.int (reservesValue v w0 w1 time balance)]) else .reverted) := by
  let supply := totalReadWord v w0 w1 time false
  let borrow := totalReadWord v w0 w1 time true
  have hs : supply.toNat < 2^255 := lt_trans (totalReadWord_lt hv false) (by decide)
  have hb : borrow.toNat < 2^255 := lt_trans (totalReadWord_lt hv true) (by decide)
  let f0 := reservesTotalsFrame v w0 w1 time balance
  let f1 : Frame := { f0 with locals := f0.locals.insert "__c5" (.int balance.toNat) }
  let f2 : Frame := { f1 with locals := f1.locals.insert "__c6" (.int supply.toNat) }
  let net := Int.ofNat balance.toNat - Int.ofNat supply.toNat
  let f3 : Frame := { f2 with locals := f2.locals.insert "netSupply" (.int net) }
  have he : evalExpr? config f0 evm (.var "balance") = .ok (.int balance.toNat) := by
    simp only [evalExpr?, f0, reservesTotalsFrame, reservesBalanceFrame,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl
  by_cases hbal : balance.toNat < 2^255
  · apply ExecBlock.consNormal (signed256_call_ok f0 evm balance _ "__c5" rfl he hbal)
    apply ExecBlock.consNormal (signed256_call_ok f1 evm supply _ "__c6" rfl (by
      simp only [evalExpr?, f1, f0, reservesTotalsFrame,
        Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, EvalResult.ofOption]
      rfl) hs)
    have hn : evalExpr? config f2 evm
        (.binary .sub (.var "__c5") (.var "__c6")) = .ok (.int net) := by
      simp only [evalExpr?, f2, f1, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
        EvalResult.ofOption, bind, EvalResult.bind, evalBinaryOp?]
      rfl
    have hnetlo : -(2^255 : Int) ≤ net := by
      dsimp only [net]
      simp only [Int.ofNat_eq_natCast]
      omega
    have hnethi : net < (2^255 : Int) := by
      dsimp only [net]
      simp only [Int.ofNat_eq_natCast]
      omega
    apply ExecBlock.consNormal (ExecStmt.letDecl (signedRangeSourceOk hn hnetlo hnethi))
    apply ExecBlock.consNormal (signed256_call_ok f3 evm borrow _ "__c7" rfl (by
      simp only [evalExpr?, f3, f2, f1, f0, reservesTotalsFrame,
        Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, EvalResult.ofOption]
      rfl) hb)
    have hadd : evalExpr? config (reservesFinalFrame v w0 w1 time balance) evm
        (.binary .add (.var "netSupply") (.var "__c7")) =
        .ok (.int (reservesValue v w0 w1 time balance)) := by
      simp only [evalExpr?, reservesFinalFrame, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert, EvalResult.ofOption, bind, EvalResult.bind, evalBinaryOp?]
      rfl
    by_cases hi : reservesValue v w0 w1 time balance < (2^255 : Int)
    · rw [if_pos (show ReservesMathValid v w0 w1 time balance from ⟨hbal, hi⟩)]
      apply ABlock.start.returns
      apply signedRangeSourceOk hadd _ hi
      dsimp only [reservesValue]
      simp only [Int.ofNat_eq_natCast]
      have hs' := totalReadWord_lt hv false
      omega
    · rw [if_neg (show ¬ ReservesMathValid v w0 w1 time balance from fun h ↦ hi h.2)]
      apply ExecBlock.consRevert
      apply ExecStmt.returnRevert
      have hr := signedRangeSourceOverflow hadd (le_of_not_gt hi)
      change evalExprs? config (reservesFinalFrame v w0 w1 time balance) evm _ = _
      simp only [evalExprs?, hr, bind, EvalResult.bind]
  · rw [if_neg (show ¬ ReservesMathValid v w0 w1 time balance from fun h ↦ hbal h.1)]
    exact ExecBlock.consRevert (signed256_call_revert f0 evm balance _ "__c5" rfl he hbal)

end Benchmarks.CompoundIII.Comet
