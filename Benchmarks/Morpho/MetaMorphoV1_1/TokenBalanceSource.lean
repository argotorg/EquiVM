import Benchmarks.Morpho.MetaMorphoV1_1.TokenBalanceCall
import Benchmarks.Morpho.MetaMorphoV1_1.MarketParamsHashSource
import Benchmarks.Morpho.MetaMorphoV1_1.AllocationSource

/-! Source execution of the loan-token balance call and its return-buffer reservation. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

def tokenBalanceStatement : Stmt :=
  .externalCall (.field (.var "marketParams") "loanToken") "balanceOf" (.intLit 0)
    [.immutable "MORPHO"] "__c0" false

def tokenBalanceFrame (frame : Frame) (balance : UInt256) : Frame :=
  { frame with locals := frame.locals.insert "__c0" (uint256Value balance) }

def tokenBalanceReserveFrame (frame : Frame) (ptr balance : UInt256) : Frame :=
  { tokenBalanceFrame frame balance with
    locals := (tokenBalanceFrame frame balance).locals.insert cursorName
      (uint256Value (nextCursor ptr ⟨32⟩)) }

theorem tokenBalanceSourceTarget {frame : Frame} {evm : State} {p : MarketParamsData}
    (hp : frame.locals.get? "marketParams" = some p.value) :
    evalExpr? config frame evm (.field (.var "marketParams") "loanToken") =
      .ok (.address p.loanToken) :=
  evalExpr_structField
    (show evalExpr? config frame evm (.var "marketParams") = .ok p.value by
      simp only [evalExpr?, hp, EvalResult.ofOption]) rfl

theorem tokenBalanceSourceArgs {frame : Frame} {evm : State} {owner : AccountAddress}
    (ho : frame.immutables.get? "MORPHO" = some (.address owner)) :
    evalExprs? config frame evm [.immutable "MORPHO"] = .ok [.address owner] := by
  simp only [evalExprs?, evalExpr?, ho, bind, EvalResult.bind, EvalResult.ofOption, pure]

theorem tokenBalanceSourceCallReverts {frame : Frame} {evm evm' : State}
    {p : MarketParamsData} {owner : AccountAddress} {out : ByteArray}
    (hp : frame.locals.get? "marketParams" = some p.value)
    (ho : frame.immutables.get? "MORPHO" = some (.address owner))
    (hcall : typedCallViaEVM config evm p.loanToken "balanceOf" 0 [.address owner]
      (false, evm', out) false) :
    ExecStmt config frame evm tokenBalanceStatement .reverted := by
  exact ExecStmt.externalCallFailure (sendVal := 0) (eth := .intLit 0)
    (tokenBalanceSourceTarget hp) (by simp only [evalExpr?, pure]) (tokenBalanceSourceArgs ho)
    (by rw [show EVM.address (p.loanToken : Nat) = p.loanToken from
          evm_address_of_address_toNat p.loanToken]
        exact hcall)

theorem tokenBalanceSourceDecodeReverts {frame : Frame} {evm evm' : State}
    {p : MarketParamsData} {owner : AccountAddress} {out : ByteArray}
    (hp : frame.locals.get? "marketParams" = some p.value)
    (ho : frame.immutables.get? "MORPHO" = some (.address owner))
    (hcall : typedCallViaEVM config evm p.loanToken "balanceOf" 0 [.address owner]
      (true, evm', out) false) (hshort : out.size < 32) :
    ExecStmt config frame evm tokenBalanceStatement .reverted := by
  exact ExecStmt.externalCallReturnDecodeRevert (sendVal := 0) (eth := .intLit 0)
    (tokenBalanceSourceTarget hp) (by simp only [evalExpr?, pure]) (tokenBalanceSourceArgs ho)
    (by rw [show EVM.address (p.loanToken : Nat) = p.loanToken from
          evm_address_of_address_toNat p.loanToken]
        exact hcall)
    (by rw [tokenBalanceDecode (by omega), if_neg (by omega)])

theorem tokenBalanceSourceSuccess {frame : Frame} {evm evm' : State}
    {p : MarketParamsData} {owner : AccountAddress} {out : ByteArray}
    (hp : frame.locals.get? "marketParams" = some p.value)
    (ho : frame.immutables.get? "MORPHO" = some (.address owner))
    (hcall : typedCallViaEVM config evm p.loanToken "balanceOf" 0 [.address owner]
      (true, evm', out) false) (hl : 32 ≤ out.size) (hh : out.size < 2 ^ 255) :
    ExecStmt config frame evm tokenBalanceStatement
      (.ok (tokenBalanceFrame frame (calldataWord out 0)) evm') := by
  exact ExecStmt.externalCallSuccess (sendVal := 0) (eth := .intLit 0)
    (value := [uint256Value (calldataWord out 0)]) (evm' := evm') (out := out)
    (tokenBalanceSourceTarget hp) (by simp only [evalExpr?, pure]) (tokenBalanceSourceArgs ho)
    (by rw [show EVM.address (p.loanToken : Nat) = p.loanToken from
          evm_address_of_address_toNat p.loanToken]
        exact hcall)
    (by rw [tokenBalanceDecode hh, if_pos hl])

theorem tokenBalanceFrame_cursor {frame : Frame} {evm : State} {ptr balance : UInt256}
    (hp : frame.locals.get? cursorName = some (uint256Value ptr)) :
    evalExpr? config (tokenBalanceFrame frame balance) evm (.var cursorName) =
      .ok (uint256Value ptr) := by
  simp only [evalExpr?, tokenBalanceFrame,
    store_get_ne _ _ (by decide : ("__c0" == cursorName) = false), hp, EvalResult.ofOption]

theorem tokenBalanceSourceAllocationReverts {frame : Frame} {evm evm' : State}
    {p : MarketParamsData} {owner : AccountAddress} {ptr : UInt256} {out : ByteArray}
    (hcontract : frame.contract = contract)
    (hp : frame.locals.get? "marketParams" = some p.value)
    (ho : frame.immutables.get? "MORPHO" = some (.address owner))
    (hptr : frame.locals.get? cursorName = some (uint256Value ptr))
    (hcall : typedCallViaEVM config evm p.loanToken "balanceOf" 0 [.address owner]
      (true, evm', out) false) (hl : 32 ≤ out.size) (hh : out.size < 2 ^ 255)
    (halloc : ¬ allocationFits ptr ⟨32⟩) (tail : List Stmt) :
    ExecBlock config frame evm ([tokenBalanceStatement, reserveBytes 32] ++ tail) .reverted := by
  apply ExecBlock.consNormal (tokenBalanceSourceSuccess hp ho hcall hl hh)
  exact ExecBlock.consRevert (allocateCallReverts cursorName
    (by change lookupCallable? frame.contract _ = _; rw [hcontract]; exact allocateFunction_lookup)
    (tokenBalanceFrame_cursor hptr) (by simp only [evalExpr?, pure]; rfl) halloc)

theorem tokenBalanceSourcePrefix {frame : Frame} {evm evm' : State}
    {p : MarketParamsData} {owner : AccountAddress} {ptr : UInt256} {out : ByteArray}
    (hcontract : frame.contract = contract)
    (hp : frame.locals.get? "marketParams" = some p.value)
    (ho : frame.immutables.get? "MORPHO" = some (.address owner))
    (hptr : frame.locals.get? cursorName = some (uint256Value ptr))
    (hcall : typedCallViaEVM config evm p.loanToken "balanceOf" 0 [.address owner]
      (true, evm', out) false) (hl : 32 ≤ out.size) (hh : out.size < 2 ^ 255)
    (halloc : allocationFits ptr ⟨32⟩) {tail : List Stmt} {result : ExecResult}
    (htail : ExecBlock config (tokenBalanceReserveFrame frame ptr (calldataWord out 0)) evm'
      tail result) :
    ExecBlock config frame evm ([tokenBalanceStatement, reserveBytes 32] ++ tail) result := by
  apply ExecBlock.consNormal (tokenBalanceSourceSuccess hp ho hcall hl hh)
  exact ExecBlock.consNormal (allocateCallReturns cursorName
    (by change lookupCallable? frame.contract _ = _; rw [hcontract]; exact allocateFunction_lookup)
    (tokenBalanceFrame_cursor hptr) (by simp only [evalExpr?, pure]; rfl) halloc) htail

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
