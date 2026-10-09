import Benchmarks.Morpho.MorphoBlue.SafeTransferPair
import Benchmarks.Morpho.MorphoBlue.MarketTransferLocals

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem marketTransfer_args {p assets shares account receiver locals}
    (hl : MarketTransferLocals p assets shares account receiver locals) (imms : Store) (evm : EVM.State) (ptr : UInt256)
    (hget : locals.get? "__memory" = some (.int (Int.ofNat ptr.toNat))) :
    evalExprs? config { contract := contract, locals := locals, immutables := imms } evm
      [.tupleGet (.var "marketParams") 0, .var "receiver", .var "assets", .var "__memory"] =
      .ok (safeTransferArgs false (AccountAddress.ofNat p.loanToken.toNat)
        evm.executionEnv.source (AccountAddress.ofNat receiver.toNat) assets ptr.toNat) := by
  have ht : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.tupleGet (.var "marketParams") 0) = .ok (.address (AccountAddress.ofNat p.loanToken.toNat)) := by
    simp only [evalExpr?, hl.evalParams, MarketParamsWords.value, tupleGetValue?,
      EvalResult.bind, EvalResult.ofOption, bind]
    rfl
  simp only [evalExprs?, ht, hl.evalAssets, hl.evalReceiver, evalExpr?, envValue, hget,
    EvalResult.ofOption, pure, bind, EvalResult.bind]
  rfl

def marketTransferPairBody (retVar : String) : List Stmt :=
  [.internalCall "SafeTransferLib_safeTransfer"
    [.tupleGet (.var "marketParams") 0, .var "receiver", .var "assets", .var "__memory"] retVar,
   .return [.var "assets", .var "shares"]]

theorem morphoMarketTransferPairAt {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {mem out : ByteArray} {aw assets shares account receiver ptr : UInt256} {σ : AccountMap}
    {k C : Nat} (mode : Fin 3) (p : MarketParamsWords) (locals imms : Store) (retVar : String)
    (ha : (retVar == "assets") = false) (hbVar : (retVar == "shares") = false)
    (ht : p.loanToken.toNat < EVM.addressModulus) (hr : receiver.toNat < EVM.addressModulus)
    (hl : MarketTransferLocals p assets shares account receiver locals) (hs : SourceState s0 ee σ evm)
    (hm : MorphoHeap mem ptr 0) (hsize : 128 ≤ mem.size) (hptr : 128 ≤ ptr.toNat)
    (hget : locals.get? "__memory" = some (.int (Int.ofNat ptr.toNat)))
    (hzero : memLoad (UInt256.ofNat 96) mem = UInt256.ofNat 0)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 14666)
      ([p.loanToken, receiver, assets] ++ (transferPairReturnPC mode :: transferPairReturnTail mode assets shares))
      mem aw out σ k C) :
    ReturnBlockRefines config (deployedRuntime v) ee g s0
      { contract := contract, locals := locals, immutables := imms } evm
      (marketTransferPairBody retVar) [abiUInt256, abiUInt256] := by
  have he := marketTransfer_args hl imms evm ptr hget
  rw [hs.env] at he
  apply morphoSafeTransferPairAt (v := v) mode false (AccountAddress.ofNat p.loanToken.toNat) ee.source
    (AccountAddress.ofNat receiver.toNat) locals imms _ retVar ha hbVar hl.assets_eq hl.shares_eq he hs hm hsize hptr hzero
  change RD (deployedRuntime v) ee g s0 (UInt256.ofNat 14666)
    ([UInt256.ofNat (AccountAddress.ofNat p.loanToken.toNat).val,
      UInt256.ofNat (AccountAddress.ofNat receiver.toNat).val, assets] ++
      (transferPairReturnPC mode :: transferPairReturnTail mode assets shares)) mem aw out σ k C
  have ht' : UInt256.ofNat (AccountAddress.ofNat p.loanToken.toNat).val = p.loanToken := addressWord_eq_ofNat_address ht
  have hr' : UInt256.ofNat (AccountAddress.ofNat receiver.toNat).val = receiver := addressWord_eq_ofNat_address hr
  rw [ht', hr']
  exact h

theorem morphoMarketTransferPair {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {mem out : ByteArray} {aw assets shares account receiver ptr : UInt256} {σ : AccountMap}
    {k C : Nat} (p : MarketParamsWords) (locals imms : Store) (retVar : String)
    (ha : (retVar == "assets") = false) (hbVar : (retVar == "shares") = false)
    (ht : p.loanToken.toNat < EVM.addressModulus) (hr : receiver.toNat < EVM.addressModulus)
    (hl : MarketTransferLocals p assets shares account receiver locals) (hs : SourceState s0 ee σ evm)
    (hm : MorphoHeap mem ptr 0) (hsize : 128 ≤ mem.size) (hptr : 128 ≤ ptr.toNat)
    (hget : locals.get? "__memory" = some (.int (Int.ofNat ptr.toNat)))
    (hzero : memLoad (UInt256.ofNat 96) mem = UInt256.ofNat 0)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 14666)
      [p.loanToken, receiver, assets, UInt256.ofNat 2752, shares, assets, UInt256.ofNat 64]
      mem aw out σ k C) :
    ReturnBlockRefines config (deployedRuntime v) ee g s0
      { contract := contract, locals := locals, immutables := imms } evm
      (marketTransferPairBody retVar) [abiUInt256, abiUInt256] := by
  exact morphoMarketTransferPairAt (v := v) ⟨0, by decide⟩ p locals imms retVar ha hbVar ht hr hl hs hm
    hsize hptr hget hzero (by simpa only [transferPairReturnPC, transferPairReturnTail, ↓reduceIte] using h)

end Benchmarks.Morpho.MorphoBlue
