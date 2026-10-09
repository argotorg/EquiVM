import Benchmarks.CompoundIII.Comet.TokenBalanceCall
import Benchmarks.CompoundIII.Comet.TotalsCollateralStorage
import Benchmarks.CompoundIII.Comet.NarrowArithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

def collateralSupply (evm : EVM.State) (asset : AccountAddress) : UInt256 :=
  low128 (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (totalsCollateralSlot asset))

def collateralReservesValue (evm : EVM.State) (asset : AccountAddress)
    (out : ByteArray) : UInt256 :=
  UInt256.sub (calldataWord out 0) (collateralSupply evm asset)

def CollateralReservesValid (evm : EVM.State) (asset : AccountAddress) (z : Bool)
    (out : ByteArray) : Prop :=
  z = true ∧ 32 ≤ out.size ∧ (collateralSupply evm asset).toNat ≤ (calldataWord out 0).toNat

instance (evm : EVM.State) (asset : AccountAddress) (z : Bool) (out : ByteArray) :
    Decidable (CollateralReservesValid evm asset z out) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def collateralReservesExpr : Expr := .inRange (.uint ⟨256, by decide⟩)
  (.binary .sub (.var "__c0") (.storage ⟨"totalsCollateral",
    [.mindex (.var "asset"), .field "totalSupplyAsset"]⟩))

def collateralReservesCallable : CallableDecl :=
  { params := [⟨"asset", abiAddress⟩], returnType := [abiUInt256], body :=
    [.externalCall (.var "asset") "balanceOf" (.intLit 0) [.env .this] "__c0" (perm := false),
      .return [collateralReservesExpr]] }

theorem collateralReservesCallable_lookup :
    lookupCallable? contract "getCollateralReserves_body" = some collateralReservesCallable := rfl

def collateralReservesEntry (imms : Store) (asset : AccountAddress) : Frame :=
  { contract := contract, locals := (∅ : Store).insert "asset" (.address asset),
    immutables := imms }

def collateralReservesFrame (imms : Store) (asset : AccountAddress) (out : ByteArray) : Frame :=
  let f := collateralReservesEntry imms asset
  { f with locals := f.locals.insert "__c0" (.int (Int.ofNat (calldataWord out 0).toNat)) }

theorem collateralReserves_reads (imms : Store) (asset : AccountAddress) (evm : EVM.State)
    (out : ByteArray) :
    evalExpr? config (collateralReservesFrame imms asset out) evm
      (.storage ⟨"totalsCollateral", [.mindex (.var "asset"), .field "totalSupplyAsset"]⟩) =
      .ok (.int (Int.ofNat (collateralSupply evm asset).toNat)) := by
  exact evalTotalsCollateralFieldVar evm _ imms asset false "asset"
    (by simp only [collateralReservesFrame, collateralReservesEntry,
        Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
        Std.HashMap.getElem?_empty]; rfl)
    (by simp only [collateralReservesFrame, collateralReservesEntry,
        Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]; rfl)

theorem collateralReserves_body_ok (imms : Store) (asset : AccountAddress)
    (evm evm' : EVM.State) (out : ByteArray)
    (hc : callViaEVM evm asset 0 (tokenBalancePayload evm.executionEnv.codeOwner)
      (true, evm', out) false) (hhi : out.size < 2^255)
    (hv : CollateralReservesValid evm' asset true out) :
    ExecFuncBody config (collateralReservesEntry imms asset) evm collateralReservesCallable.body
      (.returned (collateralReservesFrame imms asset out) evm'
        (some [.int (Int.ofNat (collateralReservesValue evm' asset out).toNat)])) := by
  apply ExecFuncBody.execBlockRet
  apply ExecBlock.consNormal (tokenBalance_source_ok ?_ hc hv.2.1 hhi)
  · apply ABlock.start.returns
    exact evalExpr_uint256_sub (by
      simp only [evalExpr?, collateralReservesEntry, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl)
      (collateralReserves_reads imms asset evm' out) hv.2.2
  · simp only [evalExpr?, collateralReservesEntry, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl

theorem collateralReserves_body_revert (imms : Store) (asset : AccountAddress)
    (evm evm' : EVM.State) (out : ByteArray) (z : Bool)
    (hc : callViaEVM evm asset 0 (tokenBalancePayload evm.executionEnv.codeOwner)
      (z, evm', out) false) (hhi : out.size < 2^255)
    (hv : ¬ CollateralReservesValid evm' asset z out) :
    ExecFuncBody config (collateralReservesEntry imms asset) evm collateralReservesCallable.body
      .reverted := by
  apply ExecFuncBody.execBlockRevert
  by_cases hcall : z = true ∧ 32 ≤ out.size
  · rcases hcall with ⟨rfl, hlen⟩
    apply ExecBlock.consNormal (tokenBalance_source_ok ?_ hc hlen hhi)
    · apply ExecBlock.consRevert
      apply ExecStmt.returnRevert
      have hr := checkedNarrowSubSourceUnderflow (lhs := .var "__c0")
        (a := calldataWord out 0) ⟨256, by decide⟩ (by
        simp only [evalExpr?, collateralReservesFrame, collateralReservesEntry,
          Std.HashMap.get?_eq_getElem?,
          Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl)
        (collateralReserves_reads imms asset evm' out)
        (Nat.lt_of_not_ge (fun h ↦ hv ⟨rfl, hlen, h⟩))
      change evalExprs? config (collateralReservesFrame imms asset out) evm'
        [collateralReservesExpr] = .revert
      simp only [evalExprs?, collateralReservesExpr, hr, bind, EvalResult.bind]
    · simp only [evalExpr?, collateralReservesEntry, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert, EvalResult.ofOption]
      rfl
  · exact ExecBlock.consRevert (tokenBalance_source_revert (by
      simp only [evalExpr?, collateralReservesEntry, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl) hc hcall)

theorem collateralReserves_call_ok (frame : Frame) (evm evm' : EVM.State)
    (asset : AccountAddress) (expr : Expr) (ret : Ident) (out : ByteArray)
    (hf : frame.contract = contract)
    (he : evalExpr? config frame evm expr = .ok (.address asset))
    (hc : callViaEVM evm asset 0 (tokenBalancePayload evm.executionEnv.codeOwner)
      (true, evm', out) false) (hhi : out.size < 2^255)
    (hv : CollateralReservesValid evm' asset true out) :
    ExecStmt config frame evm (.internalCall "getCollateralReserves_body" [expr] ret)
      (.ok { frame with locals :=
        frame.locals.insert ret (.int (Int.ofNat (collateralReservesValue evm' asset out).toNat)) }
          evm') := by
  have hb := collateralReserves_body_ok frame.immutables asset evm evm' out hc hhi hv
  exact ExecStmt.internalCallReturn (callee := collateralReservesCallable)
    (locals := (∅ : Store).insert "asset" (.address asset))
    (cfg := config) (solm := frame) (evm := evm) (args := [expr])
    (argVals := [.address asset])
    (by simp only [evalExprs?, he, pure, bind, EvalResult.bind])
    (by rw [hf]; exact collateralReservesCallable_lookup) rfl (by simpa only [hf] using hb)

theorem collateralReserves_call_revert (frame : Frame) (evm evm' : EVM.State)
    (asset : AccountAddress) (expr : Expr) (ret : Ident) (out : ByteArray) (z : Bool)
    (hf : frame.contract = contract)
    (he : evalExpr? config frame evm expr = .ok (.address asset))
    (hc : callViaEVM evm asset 0 (tokenBalancePayload evm.executionEnv.codeOwner)
      (z, evm', out) false) (hhi : out.size < 2^255)
    (hv : ¬ CollateralReservesValid evm' asset z out) :
    ExecStmt config frame evm (.internalCall "getCollateralReserves_body" [expr] ret)
      .reverted := by
  have hb := collateralReserves_body_revert frame.immutables asset evm evm' out z hc hhi hv
  exact ExecStmt.internalCallRevert (callee := collateralReservesCallable)
    (locals := (∅ : Store).insert "asset" (.address asset))
    (cfg := config) (solm := frame) (evm := evm) (args := [expr])
    (argVals := [.address asset])
    (by simp only [evalExprs?, he, pure, bind, EvalResult.bind])
    (by rw [hf]; exact collateralReservesCallable_lookup) rfl (by simpa only [hf] using hb)

end Benchmarks.CompoundIII.Comet
