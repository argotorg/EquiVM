import Benchmarks.Morpho.MorphoBlue.ReturnBlockRefines
import Benchmarks.Morpho.MorphoBlue.SupplySourceStart
import Benchmarks.Morpho.MorphoBlue.SafeTransferPair

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem supplyTransfer_args {p assets shares account data locals}
    (hl : SupplyLocals p assets shares account data locals) (imms : Store) (evm : EVM.State) (ptr : UInt256)
    (hget : locals.get? "__memory" = some (.int (Int.ofNat ptr.toNat))) :
    evalExprs? config { contract := contract, locals := locals, immutables := imms } evm
      [.tupleGet (.var "marketParams") 0, .env .caller, .env .this, .var "assets", .var "__memory"] =
      .ok (safeTransferArgs true (AccountAddress.ofNat p.loanToken.toNat)
        evm.executionEnv.source evm.executionEnv.codeOwner assets ptr.toNat) := by
  have ht : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.tupleGet (.var "marketParams") 0) = .ok (.address (AccountAddress.ofNat p.loanToken.toNat)) := by
    simp only [evalExpr?, hl.evalParams, MarketParamsWords.value, tupleGetValue?,
      EvalResult.bind, EvalResult.ofOption, bind]
    rfl
  simp only [evalExprs?, ht, hl.evalAssets, evalExpr?, envValue, hget,
    EvalResult.ofOption, pure, bind, EvalResult.bind]
  rfl

-- LIBRARY CANDIDATE: a token transfer followed by a pair of uint256 return values.
def loanTransferPairBody (retVar : String) : List Stmt :=
  [.internalCall "SafeTransferLib_safeTransferFrom"
    [.tupleGet (.var "marketParams") 0, .env .caller, .env .this, .var "assets", .var "__memory"] retVar,
   .return [.var "assets", .var "shares"]]

theorem morphoLoanTransferPair {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {mem out data : ByteArray} {aw assets shares account ptr : UInt256} {σ : AccountMap}
    {k C : Nat} (p : MarketParamsWords) (locals imms : Store) (retVar : String)
    (ha : (retVar == "assets") = false) (hbVar : (retVar == "shares") = false)
    (hl : SupplyLocals p assets shares account data locals) (hs : SourceState s0 ee σ evm)
    (hm : MorphoHeap mem ptr 0) (hsize : 128 ≤ mem.size) (hptr : 128 ≤ ptr.toNat)
    (hget : locals.get? "__memory" = some (.int (Int.ofNat ptr.toNat)))
    (hzero : memLoad (UInt256.ofNat 96) mem = UInt256.ofNat 0)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 15033)
      [UInt256.ofNat (AccountAddress.ofNat p.loanToken.toNat).val, UInt256.ofNat ee.source.val,
       UInt256.ofNat ee.codeOwner.val, assets, UInt256.ofNat 4208, UInt256.ofNat 32,
       shares, assets, UInt256.ofNat 64] mem aw out σ k C) :
    ReturnBlockRefines config (deployedRuntime v) ee g s0
      { contract := contract, locals := locals, immutables := imms } evm
      (loanTransferPairBody retVar) [abiUInt256, abiUInt256] := by
  have he := supplyTransfer_args hl imms evm ptr hget
  rw [hs.env] at he
  exact morphoSafeTransferPair true (AccountAddress.ofNat p.loanToken.toNat) ee.source ee.codeOwner
    locals imms _ retVar ha hbVar hl.assets_eq hl.shares_eq he hs hm hsize hptr hzero h



-- The compiler shares the transfer routine and pair return across supply and repay.
theorem morphoLoanTransferPairAt {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {mem out data : ByteArray} {aw assets shares account ptr pc x0 x1 x2 : UInt256}
    {σ : AccountMap} {k C : Nat} (p : MarketParamsWords) (locals imms : Store) (retVar : String)
    (ha : (retVar == "assets") = false) (hbVar : (retVar == "shares") = false) (hc : p.Canonical)
    (hl : SupplyLocals p assets shares account data locals) (hs : SourceState s0 ee σ evm)
    (hm : MorphoHeap mem ptr 0) (hsize : 160 ≤ mem.size) (hptr : 160 ≤ ptr.toNat)
    (hget : locals.get? "__memory" = some (.int (Int.ofNat ptr.toNat)))
    (hzero : memLoad (UInt256.ofNat 96) mem = UInt256.ofNat 0)
    (htoken : memLoad (UInt256.ofNat 128) mem = p.loanToken)
    (hpc : pc = UInt256.ofNat 4186 ∨ pc = UInt256.ofNat 10845)
    (h : RD (deployedRuntime v) ee g s0 pc
      [x0, x1, x2, UInt256.ofNat 128, UInt256.ofNat 32, shares, assets, solcAddrMask]
      mem aw out σ k C) :
    ReturnBlockRefines config (deployedRuntime v) ee g s0
      { contract := contract, locals := locals, immutables := imms } evm
      (loanTransferPairBody retVar) [abiUInt256, abiUInt256] := by
  have hr : ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 15033)
      [UInt256.land (memLoad (UInt256.ofNat 128) mem) solcAddrMask, UInt256.ofNat ee.source.val,
       UInt256.ofNat ee.codeOwner.val, assets, UInt256.ofNat 4208, UInt256.ofNat 32,
       shares, assets, UInt256.ofNat 64] mem aw' out σ k' C' := by
    rcases hpc with rfl | rfl
    · exact morphoBlocks.morpho_block_4186_packed (immWords := wordsOf (immStore v))
        (by decide) (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
    · exact morphoBlocks.morpho_block_10845_packed (immWords := wordsOf (immStore v))
        (by decide) (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  obtain ⟨a1, k1, C1, rd1⟩ := hr
  rw [htoken, solcAddrMask_clean hc.1] at rd1
  have hw : UInt256.ofNat (AccountAddress.ofNat p.loanToken.toNat).val = p.loanToken :=
    addressWord_eq_ofNat_address hc.1
  rw [← hw] at rd1
  exact morphoLoanTransferPair p locals imms retVar ha hbVar hl hs hm (by omega) (by omega)
    hget hzero rd1

end Benchmarks.Morpho.MorphoBlue
