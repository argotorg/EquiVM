import Benchmarks.UniswapV3.Pool.FlashProtocolWords
import Benchmarks.UniswapV3.Pool.CollectProtocolPaymentsSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def flashPaidName (second : Bool) : Ident := if second then "paid1" else "paid0"
def flashProtocolName (second : Bool) : Ident := if second then "feeProtocol1" else "feeProtocol0"
def flashProtocolFeesName (second : Bool) : Ident := if second then "fees1" else "fees0"

def flashProtocolExpr (second : Bool) : Expr :=
  if second then .binary (.shr (.uint ⟨8, by decide⟩))
    (.storage ⟨"slot0", [.field "feeProtocol"]⟩) (.intLit 4)
  else .binary .mod (.storage ⟨"slot0", [.field "feeProtocol"]⟩) (.intLit 16)

def flashProtocolFeesExpr (second : Bool) : Expr :=
  .ite (.binary .eq (.var (flashProtocolName second)) (.intLit 0)) (.intLit 0)
    (.binary .div (.var (flashPaidName second)) (.var (flashProtocolName second)))

def flashProtocolStoreStmt (second : Bool) : Stmt :=
  .ite (.binary .gt (.cast (.var (flashProtocolFeesName second))
    (.elem (.int (.uint ⟨128, by decide⟩)))) (.intLit 0))
    [.assign .storage ⟨"protocolFees", [.field (protocolFeesField second)]⟩
      (.cast (.binary .add (protocolFeesExpr second)
        (.cast (.var (flashProtocolFeesName second)) (.elem (.int (.uint ⟨128, by decide⟩)))))
        (.elem (.int (.uint ⟨128, by decide⟩))))] []

theorem evalFlashProtocol (locals imms : Store) (evm : EVM.State) (second : Bool)
    (hbase : locals.get? "slot0" = none) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (flashProtocolExpr second) =
      .ok (.int (Int.ofNat (poolProtocolDivisor second evm.accountMap evm.executionEnv).toNat)) := by
  have hf := evalSlot0FeeProtocol locals imms evm hbase
  rw [poolProtocolDivisor_toNat]
  cases second
  · have h16 : evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
        (.intLit 16) = .ok (.int (Int.ofNat (⟨16⟩ : UInt256).toNat)) := by
      simp only [evalExpr?, pure]; rfl
    simpa only [flashProtocolExpr, Bool.false_eq_true, ↓reduceIte,
      umod_toNat_of_ne_zero _ (⟨16⟩ : UInt256) (by decide),
      show (⟨16⟩ : UInt256).toNat = 16 from rfl] using
      evalExpr_word_mod hf h16 (by decide)
  · have hsmall : (slot0FieldWord 29 1 evm.accountMap evm.executionEnv).toNat < 256 :=
      u256LandMaskToNatLtOfToNat (bits := 8) _ _ (by decide)
    have hn : normalizeInt (.uint ⟨8, by decide⟩)
        (Int.ofNat (slot0FieldWord 29 1 evm.accountMap evm.executionEnv).toNat) =
        Int.ofNat (slot0FieldWord 29 1 evm.accountMap evm.executionEnv).toNat :=
      normalizeInt_uint_eq_self _ _ (Int.natCast_nonneg _)
        (Int.ofNat_lt.mpr hsmall)
    simpa only [flashProtocolExpr, ↓reduceIte, hn, Int.natCast_ediv] using
      evalExpr_uintShiftRight ⟨8, by decide⟩ _ 4 hf (by decide)

theorem evalFlashProtocolFees (locals imms : Store) (evm : EVM.State) (second : Bool)
    (paid divisor : UInt256)
    (hp : locals.get? (flashPaidName second) = some (.int (Int.ofNat paid.toNat)))
    (hd : locals.get? (flashProtocolName second) = some (.int (Int.ofNat divisor.toNat))) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (flashProtocolFeesExpr second) = .ok (.int (Int.ofNat (poolProtocolFees paid divisor).toNat)) := by
  have he := evalExpr_nat_eq_zero (evalExpr_var_get (cfg := config) (evm := evm)
    (frame := {contract := contract, locals := locals, immutables := imms}) hd)
  by_cases hz : divisor = ⟨0⟩
  · subst divisor
    simp only [poolProtocolFees, ↓reduceIte, flashProtocolFeesExpr, evalExpr?, he,
      bind, EvalResult.bind, pure, show (⟨0⟩ : UInt256).toNat = 0 from rfl, decide_true]
    rfl
  · have hn : divisor.toNat ≠ 0 := fun h ↦ hz (uint256_toNat_eq_zero h)
    have hdiv := evalExpr_word_div (evalExpr_var_get (cfg := config) (evm := evm)
      (frame := {contract := contract, locals := locals, immutables := imms}) hp)
      (evalExpr_var_get hd) hn
    simp only [poolProtocolFees, if_neg hz, flashProtocolFeesExpr, evalExpr?, he,
      bind, EvalResult.bind, hn, decide_false, hdiv]

def flashProtocolState (evm : EVM.State) (second : Bool) (fees : UInt256) : EVM.State :=
  if uint128Word fees = ⟨0⟩ then evm
  else storeProtocolFee evm second (protocolFeesWord second evm.accountMap evm.executionEnv + fees)

theorem flashProtocolStore (locals imms : Store) (evm : EVM.State) (second : Bool)
    (fees : UInt256)
    (hf : locals.get? (flashProtocolFeesName second) = some (.int (Int.ofNat fees.toNat)))
    (hbase : locals.get? "protocolFees" = none) :
    ExecStmt config {contract := contract, locals := locals, immutables := imms} evm
      (flashProtocolStoreStmt second)
      (.ok {contract := contract, locals := locals, immutables := imms}
        (flashProtocolState evm second fees)) := by
  have hfee := evalExpr_var_get (cfg := config) (evm := evm)
    (frame := {contract := contract, locals := locals, immutables := imms}) hf
  have hcast := evalExpr_intCast (.uint ⟨128, by decide⟩) hfee
  rw [normalizeUIntWord_mask ⟨128, by decide⟩ fees (UInt256.ofNat (2 ^ 128 - 1))
    (by decide), u256_land_comm] at hcast
  change evalExpr? config _ evm _ = .ok (.int (Int.ofNat (uint128Word fees).toNat)) at hcast
  have hguard := evalExpr_word_gt hcast
    (show evalExpr? config _ evm (.intLit 0) =
      .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) from by simp only [evalExpr?, pure]; rfl)
  by_cases hz : uint128Word fees = ⟨0⟩
  · rw [flashProtocolState, if_pos hz]
    apply ExecStmt.iteFalse _ ExecBlock.nil
    simpa only [show (⟨0⟩ : UInt256).toNat = 0 from rfl,
      hz, Nat.lt_irrefl, decide_false] using hguard
  · rw [flashProtocolState, if_neg hz]
    have hp : 0 < (uint128Word fees).toNat :=
      Nat.pos_of_ne_zero (fun h ↦ hz (uint256_toNat_eq_zero h))
    refine ExecStmt.iteTrue ?_ ?_
    · simpa only [show (⟨0⟩ : UInt256).toNat = 0 from rfl,
        hp, decide_true] using hguard
    refine ExecBlock.consNormal ?_ ExecBlock.nil
    simpa only [storeProtocolFee_uint128Word] using ExecStmt.assign
      (evalExpr_uint128AddCast (evalProtocolFeesWord locals imms evm second hbase) hfee)
      (assignProtocolFee evm locals imms second
        (uint128Word (protocolFeesWord second evm.accountMap evm.executionEnv + fees)) hbase)

def flashProtocolFrame (locals imms : Store) (second : Bool) (paid divisor : UInt256) : Frame :=
  {contract := contract, immutables := imms,
    locals := (locals.insert (flashProtocolName second) (.int (Int.ofNat divisor.toNat))).insert
      (flashProtocolFeesName second) (.int (Int.ofNat (poolProtocolFees paid divisor).toNat))}

def flashProtocolStmts (second : Bool) : List Stmt :=
  [.letDecl (flashProtocolName second) (some (.elem (.int (.uint ⟨8, by decide⟩))))
      (flashProtocolExpr second),
    .letDecl (flashProtocolFeesName second) (some (.elem (.int (.uint ⟨256, by decide⟩))))
      (flashProtocolFeesExpr second),
    flashProtocolStoreStmt second]

theorem flashProtocolSource (locals imms : Store) (evm : EVM.State) (second : Bool)
    (paid : UInt256)
    (hp : locals.get? (flashPaidName second) = some (.int (Int.ofNat paid.toNat)))
    (hslot : locals.get? "slot0" = none) (hfees : locals.get? "protocolFees" = none) :
    let divisor := poolProtocolDivisor second evm.accountMap evm.executionEnv
    ExecBlock config {contract := contract, locals := locals, immutables := imms} evm
      (flashProtocolStmts second)
      (.ok (flashProtocolFrame locals imms second paid divisor)
        (flashProtocolState evm second (poolProtocolFees paid divisor))) := by
  dsimp only
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalFlashProtocol locals imms evm second hslot)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalFlashProtocolFees _ imms evm second paid
    (poolProtocolDivisor second evm.accountMap evm.executionEnv) ?_ ?_)) ?_
  · cases second <;>
      simpa [flashPaidName, flashProtocolName, Std.HashMap.getElem?_insert] using hp
  · simp [Std.HashMap.getElem?_insert]
  refine ExecBlock.consNormal (flashProtocolStore _ imms evm second _ ?_ ?_) ExecBlock.nil
  · simp [Std.HashMap.getElem?_insert]
  · cases second <;>
      simpa [flashProtocolName, flashProtocolFeesName, Std.HashMap.getElem?_insert] using hfees

end Benchmarks.UniswapV3.Pool
