import Benchmarks.Morpho.MetaMorphoV1_1.SupplySharesAllocationSource
import Benchmarks.Morpho.MetaMorphoV1_1.MarketParamsAllocationSource
import Benchmarks.Morpho.MetaMorphoV1_1.MarketBalancesAllocationSource

/-! Internal-call boundaries for the three allocated Morpho readers. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

theorem supplySharesReaderCall {evm evm' : State} {locals imms : Store}
    {morpho user : AccountAddress} {id ptr : UInt256} {args : List Expr} {ret : Ident}
    {final : Frame} {values : Option (List Value)}
    (hargs : evalExprs? config { contract := contract, locals := locals, immutables := imms }
      evm args = .ok [.address morpho, wordBytes32Value id, .address user, uint256Value ptr])
    (hbody : ExecFuncBody config (allocatedSupplySharesFrame imms morpho user id ptr)
      evm allocatedSupplySharesFunction.body (.returned final evm' values)) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall allocatedSupplySharesFunction.name args ret)
      (.ok (resumeAfterInternalCall
        { contract := contract, locals := locals, immutables := imms } ret values) evm') :=
  internalCallFunctionReturn (callee := allocatedSupplySharesFunction) hargs
    allocatedSupplySharesFunction_lookup rfl hbody

theorem supplySharesReaderRevert {evm : State} {locals imms : Store}
    {morpho user : AccountAddress} {id ptr : UInt256} {args : List Expr} {ret : Ident}
    (hargs : evalExprs? config { contract := contract, locals := locals, immutables := imms }
      evm args = .ok [.address morpho, wordBytes32Value id, .address user, uint256Value ptr])
    (hbody : ExecFuncBody config (allocatedSupplySharesFrame imms morpho user id ptr)
      evm allocatedSupplySharesFunction.body .reverted) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall allocatedSupplySharesFunction.name args ret) .reverted :=
  internalCallFunctionRevert (callee := allocatedSupplySharesFunction) hargs
    allocatedSupplySharesFunction_lookup rfl hbody

theorem marketParamsReaderCall {evm evm' : State} {locals : Store}
    {v : MetaMorphoV1_1Immutables} {id ptr : UInt256} {args : List Expr} {ret : Ident}
    {final : Frame} {values : Option (List Value)}
    (hargs : evalExprs? config
      { contract := contract, locals := locals, immutables := immStore v }
      evm args = .ok [wordBytes32Value id, uint256Value ptr])
    (hbody : ExecFuncBody config (allocatedMarketParamsFrame v id ptr)
      evm allocatedMarketParamsFunction.body (.returned final evm' values)) :
    ExecStmt config { contract := contract, locals := locals, immutables := immStore v } evm
      (.internalCall allocatedMarketParamsFunction.name args ret)
      (.ok (resumeAfterInternalCall
        { contract := contract, locals := locals, immutables := immStore v } ret values) evm') :=
  internalCallFunctionReturn (callee := allocatedMarketParamsFunction) hargs
    allocatedMarketParamsFunction_lookup rfl hbody

theorem marketParamsReaderRevert {evm : State} {locals : Store}
    {v : MetaMorphoV1_1Immutables} {id ptr : UInt256} {args : List Expr} {ret : Ident}
    (hargs : evalExprs? config
      { contract := contract, locals := locals, immutables := immStore v }
      evm args = .ok [wordBytes32Value id, uint256Value ptr])
    (hbody : ExecFuncBody config (allocatedMarketParamsFrame v id ptr)
      evm allocatedMarketParamsFunction.body .reverted) :
    ExecStmt config { contract := contract, locals := locals, immutables := immStore v } evm
      (.internalCall allocatedMarketParamsFunction.name args ret) .reverted :=
  internalCallFunctionRevert (callee := allocatedMarketParamsFunction) hargs
    allocatedMarketParamsFunction_lookup rfl hbody

theorem marketBalancesReaderCall {evm evm' : State} {locals imms : Store}
    {morpho : AccountAddress} {p : MarketParamsData} {ptr : UInt256}
    {args : List Expr} {ret : Ident} {final : Frame} {values : Option (List Value)}
    (hargs : evalExprs? config { contract := contract, locals := locals, immutables := imms }
      evm args = .ok [.address morpho, p.value, uint256Value ptr])
    (hbody : ExecFuncBody config (allocatedMarketBalancesFrame imms morpho p ptr)
      evm allocatedMarketBalancesFunction.body (.returned final evm' values)) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall allocatedMarketBalancesFunction.name args ret)
      (.ok (resumeAfterInternalCall
        { contract := contract, locals := locals, immutables := imms } ret values) evm') :=
  internalCallFunctionReturn (callee := allocatedMarketBalancesFunction) hargs
    allocatedMarketBalancesFunction_lookup rfl hbody

theorem marketBalancesReaderRevert {evm : State} {locals imms : Store}
    {morpho : AccountAddress} {p : MarketParamsData} {ptr : UInt256}
    {args : List Expr} {ret : Ident}
    (hargs : evalExprs? config { contract := contract, locals := locals, immutables := imms }
      evm args = .ok [.address morpho, p.value, uint256Value ptr])
    (hbody : ExecFuncBody config (allocatedMarketBalancesFrame imms morpho p ptr)
      evm allocatedMarketBalancesFunction.body .reverted) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall allocatedMarketBalancesFunction.name args ret) .reverted :=
  internalCallFunctionRevert (callee := allocatedMarketBalancesFunction) hargs
    allocatedMarketBalancesFunction_lookup rfl hbody

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
