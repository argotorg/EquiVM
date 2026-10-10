import Benchmarks.Morpho.MetaMorphoV1_1.MarketBalancesSource
import Benchmarks.Morpho.MetaMorphoV1_1.BorrowRateABI

/-! Source execution of the rate-model call and its return-buffer reservation. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

def borrowRateStatement : Stmt :=
  .externalCall (.field (.var "marketParams") "irm") "borrowRateView" (.intLit 0)
    [.var "marketParams", .var "market"] "borrowRate" false

theorem marketAccrualBody_prefix :
    marketAccrualBody = [borrowRateStatement, reserveBytes 32] ++ marketAccrualBody.drop 2 := by
  let reserves := fun name ↦
    if name == "market" then 384 else if name == "borrowRateView" then 32 else 0
  have hsplit (tail : List Stmt) :
      allocationBody marketBalancesAllocationCalls reserves (borrowRateStatement :: tail) =
        [borrowRateStatement, reserveBytes 32] ++
          allocationBody marketBalancesAllocationCalls reserves tail := by
    simp [allocationBody, allocationStatement, borrowRateStatement, reserves]
  have hb := hsplit (marketAccrualSourceBody.drop 1)
  change marketAccrualBody = _ at hb
  rw [hb]
  rfl

def borrowRateFrame (frame : Frame) (rate : UInt256) : Frame :=
  { frame with locals := frame.locals.insert "borrowRate" (uint256Value rate) }

def borrowRateReserveFrame (frame : Frame) (ptr rate : UInt256) : Frame :=
  { borrowRateFrame frame rate with
    locals := (borrowRateFrame frame rate).locals.insert cursorName
      (uint256Value (nextCursor ptr ⟨32⟩)) }

theorem borrowRateSourceTarget {frame : Frame} {evm : State} {p : MarketParamsData}
    (hp : frame.locals.get? "marketParams" = some p.value) :
    evalExpr? config frame evm (.field (.var "marketParams") "irm") = .ok (.address p.irm) :=
  evalExpr_structField
    (show evalExpr? config frame evm (.var "marketParams") = .ok p.value by
      simp only [evalExpr?, hp, EvalResult.ofOption]) rfl

theorem borrowRateSourceArgs {frame : Frame} {evm : State} {p : MarketParamsData}
    {market : ByteArray} (hp : frame.locals.get? "marketParams" = some p.value)
    (hm : frame.locals.get? "market" = some (marketValue market)) :
    evalExprs? config frame evm [.var "marketParams", .var "market"] =
      .ok [p.value, marketValue market] := by
  simp only [evalExprs?, evalExpr?, hp, hm, bind, EvalResult.bind, EvalResult.ofOption, pure]

theorem borrowRateSourceCallReverts {frame : Frame} {evm evm' : State} {p : MarketParamsData}
    {market out : ByteArray} (hp : frame.locals.get? "marketParams" = some p.value)
    (hm : frame.locals.get? "market" = some (marketValue market))
    (hcall : typedCallViaEVM config evm p.irm "borrowRateView" 0 [p.value, marketValue market]
      (false, evm', out) false) :
    ExecBlock config frame evm marketAccrualBody .reverted := by
  rw [marketAccrualBody_prefix]
  exact ExecBlock.consRevert (ExecStmt.externalCallFailure (sendVal := 0) (eth := .intLit 0)
    (borrowRateSourceTarget hp) (by simp only [evalExpr?, pure]) (borrowRateSourceArgs hp hm)
    (by rw [show EVM.address (p.irm : Nat) = p.irm from evm_address_of_address_toNat p.irm]
        exact hcall))

theorem borrowRateSourceDecodeReverts {frame : Frame} {evm evm' : State} {p : MarketParamsData}
    {market out : ByteArray} (hp : frame.locals.get? "marketParams" = some p.value)
    (hm : frame.locals.get? "market" = some (marketValue market))
    (hcall : typedCallViaEVM config evm p.irm "borrowRateView" 0 [p.value, marketValue market]
      (true, evm', out) false) (hshort : out.size < 32) :
    ExecBlock config frame evm marketAccrualBody .reverted := by
  rw [marketAccrualBody_prefix]
  exact ExecBlock.consRevert (ExecStmt.externalCallReturnDecodeRevert (sendVal := 0)
    (eth := .intLit 0) (borrowRateSourceTarget hp) (by simp only [evalExpr?, pure])
    (borrowRateSourceArgs hp hm)
    (by rw [show EVM.address (p.irm : Nat) = p.irm from evm_address_of_address_toNat p.irm]
        exact hcall)
    (by rw [borrowRateDecode (by omega), if_neg (by omega)]))

theorem borrowRateSourceDecodePrefix {frame : Frame} {evm evm' : State} {p : MarketParamsData}
    {market out : ByteArray} (hp : frame.locals.get? "marketParams" = some p.value)
    (hm : frame.locals.get? "market" = some (marketValue market))
    (hcall : typedCallViaEVM config evm p.irm "borrowRateView" 0 [p.value, marketValue market]
      (true, evm', out) false) (hl : 32 ≤ out.size) (hh : out.size < 2 ^ 255)
    {result : ExecResult}
    (htail : ExecBlock config (borrowRateFrame frame (calldataWord out 0)) evm'
      (marketAccrualBody.drop 1) result) :
    ExecBlock config frame evm marketAccrualBody result := by
  rw [marketAccrualBody_prefix] at htail ⊢
  exact ExecBlock.consNormal (ExecStmt.externalCallSuccess (sendVal := 0) (eth := .intLit 0)
    (value := [uint256Value (calldataWord out 0)]) (evm' := evm') (out := out)
    (borrowRateSourceTarget hp) (by simp only [evalExpr?, pure]) (borrowRateSourceArgs hp hm)
    (by rw [show EVM.address (p.irm : Nat) = p.irm from evm_address_of_address_toNat p.irm]
        exact hcall)
    (by rw [borrowRateDecode hh, if_pos hl])) htail

theorem borrowRateFrame_cursor {frame : Frame} {evm : State} {ptr rate : UInt256}
    (hp : frame.locals.get? cursorName = some (uint256Value ptr)) :
    evalExpr? config (borrowRateFrame frame rate) evm (.var cursorName) =
      .ok (uint256Value ptr) := by
  simp only [evalExpr?, borrowRateFrame,
    store_get_ne _ _ (by decide : ("borrowRate" == cursorName) = false), hp, EvalResult.ofOption]

theorem borrowRateSourceAllocationReverts {frame : Frame} {evm evm' : State}
    {p : MarketParamsData} {ptr : UInt256} {market out : ByteArray}
    (hcontract : frame.contract = contract)
    (hp : frame.locals.get? "marketParams" = some p.value)
    (hm : frame.locals.get? "market" = some (marketValue market))
    (hptr : frame.locals.get? cursorName = some (uint256Value ptr))
    (hcall : typedCallViaEVM config evm p.irm "borrowRateView" 0 [p.value, marketValue market]
      (true, evm', out) false) (hl : 32 ≤ out.size) (hh : out.size < 2 ^ 255)
    (halloc : ¬ allocationFits ptr ⟨32⟩) :
    ExecBlock config frame evm marketAccrualBody .reverted := by
  apply borrowRateSourceDecodePrefix hp hm hcall hl hh
  rw [marketAccrualBody_prefix]
  exact ExecBlock.consRevert (allocateCallReverts cursorName
    (by change lookupCallable? frame.contract _ = _; rw [hcontract]; exact allocateFunction_lookup)
    (borrowRateFrame_cursor hptr) (by simp only [evalExpr?, pure]; rfl) halloc)

theorem borrowRateSourcePrefix {frame : Frame} {evm evm' : State} {p : MarketParamsData}
    {ptr : UInt256} {market out : ByteArray} (hcontract : frame.contract = contract)
    (hp : frame.locals.get? "marketParams" = some p.value)
    (hm : frame.locals.get? "market" = some (marketValue market))
    (hptr : frame.locals.get? cursorName = some (uint256Value ptr))
    (hcall : typedCallViaEVM config evm p.irm "borrowRateView" 0 [p.value, marketValue market]
      (true, evm', out) false) (hl : 32 ≤ out.size) (hh : out.size < 2 ^ 255)
    (halloc : allocationFits ptr ⟨32⟩) {result : ExecResult}
    (htail : ExecBlock config (borrowRateReserveFrame frame ptr (calldataWord out 0)) evm'
      (marketAccrualBody.drop 2) result) :
    ExecBlock config frame evm marketAccrualBody result := by
  apply borrowRateSourceDecodePrefix hp hm hcall hl hh
  rw [marketAccrualBody_prefix] at htail ⊢
  exact ExecBlock.consNormal (allocateCallReturns cursorName
    (by change lookupCallable? frame.contract _ = _; rw [hcontract]; exact allocateFunction_lookup)
    (borrowRateFrame_cursor hptr) (by simp only [evalExpr?, pure]; rfl) halloc) htail

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
