import Benchmarks.Morpho.MorphoBlue.ReturnBlockRefines
import Benchmarks.Morpho.MorphoBlue.SafeTransferInternal

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def transferPairReturnPC (mode : Fin 3) : UInt256 :=
  match mode.val with
  | 0 => UInt256.ofNat 2752
  | 1 => UInt256.ofNat 4208
  | _ => UInt256.ofNat 8920

def transferPairReturnTail (mode : Fin 3) (assets shares : UInt256) : List UInt256 :=
  if mode.val = 0 then [shares, assets, UInt256.ofNat 64]
  else if mode.val = 1 then [UInt256.ofNat 32, shares, assets, UInt256.ofNat 64]
  else [UInt256.ofNat 32, shares, assets]

-- Shared continuation for incoming and outgoing token transfers.
theorem morphoSafeTransferPairAt {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {mem out : ByteArray} {aw assets shares ptr : UInt256} {σ : AccountMap}
    {k C : Nat} (mode : Fin 3) (isFrom : Bool) (token sender recipient : AccountAddress)
    (locals imms : Store) (args : List Expr) (retVar : String)
    (ha : (retVar == "assets") = false) (hbVar : (retVar == "shares") = false)
    (haGet : locals.get? "assets" = some (.int (Int.ofNat assets.toNat)))
    (hsGet : locals.get? "shares" = some (.int (Int.ofNat shares.toNat)))
    (he : evalExprs? config { contract := contract, locals := locals, immutables := imms } evm args =
      .ok (safeTransferArgs isFrom token sender recipient assets ptr.toNat))
    (hs : SourceState s0 ee σ evm) (hm : MorphoHeap mem ptr 0)
    (hsize : 128 ≤ mem.size) (hptr : 128 ≤ ptr.toNat)
    (hzero : memLoad (UInt256.ofNat 96) mem = UInt256.ofNat 0)
    (h : RD (deployedRuntime v) ee g s0 (safeTransferEntryPC isFrom)
      (safeTransferEVMArgs isFrom token sender recipient assets ++
        (transferPairReturnPC mode :: transferPairReturnTail mode assets shares)) mem aw out σ k C) :
    ReturnBlockRefines config (deployedRuntime v) ee g s0
      { contract := contract, locals := locals, immutables := imms } evm
      [.internalCall (if isFrom then "SafeTransferLib_safeTransferFrom" else "SafeTransferLib_safeTransfer") args retVar,
       .return [.var "assets", .var "shares"]] [abiUInt256, abiUInt256] := by
  have hf := morphoSafeTransferFunctionRefine (v := v)
    (ret := transferPairReturnPC mode) (R := transferPairReturnTail mode assets shares) isFrom token sender recipient imms
    (by fin_cases mode <;> simp [transferPairReturnTail]) hs hm (by omega) (by omega) hzero
    (by fin_cases mode <;> rw [morphoPatchedValidJumps v] <;> jump_dest) h
  cases hf with
  | reverted hb hr =>
    exact .reverted (ExecBlock.consRevert (morphoSafeTransferInternalRevert isFrom token sender recipient
      assets ptr.toNat locals imms evm _ retVar he hb)) hr
  | @ok frame' evm' σ' mem' ptr' aw' rdata' k' C' hb hs' hm' hpref hsize' hlower' hzero' rd =>
    have he' := morphoSafeTransferInternalOk isFrom token sender recipient assets ptr.toNat
      locals imms evm evm' frame' _ _ retVar he hb
    have hret : ExecBlock config
        { contract := contract, locals := locals.insert retVar (.int (Int.ofNat ptr'.toNat)), immutables := imms }
        evm' [.return [.var "assets", .var "shares"]]
        (.returned { contract := contract, locals := locals.insert retVar (.int (Int.ofNat ptr'.toNat)), immutables := imms }
          evm' (some [.int (Int.ofNat assets.toNat), .int (Int.ofNat shares.toNat)])) := by
      apply ExecBlock.consReturn (ExecStmt.return ?_)
      simp only [evalExprs?, evalExpr?, store_get_ne _ _ ha, store_get_ne _ _ hbVar,
        haGet, hsGet, EvalResult.ofOption, pure, bind, EvalResult.bind]
    have hr : RDret (deployedRuntime v) g s0 σ'
        ((shares.toByteArray.write 0 (assets.toByteArray.write 0 mem' (memLoad (UInt256.ofNat 64) mem').toNat 32)
          (memLoad (UInt256.ofNat 64) mem' + UInt256.ofNat 32).toNat 32).readWithPadding
          (memLoad (UInt256.ofNat 64) mem').toNat 64) := by
      fin_cases mode
      · exact morphoBlocks.morpho_block_2752 (immWords := wordsOf (immStore v)) (by decide) rd
      · exact morphoBlocks.morpho_block_4208 (immWords := wordsOf (immStore v)) (by decide) rd
      · exact morphoBlocks.morpho_block_8920 (immWords := wordsOf (immStore v)) (by decide) rd
    rw [hm'.free] at hr
    have hadd : (ptr' + UInt256.ofNat 32).toNat = ptr'.toNat + 32 :=
      uadd_word_ofNat_toNat _ _ (by have hh := hm'.space; change _ < 2 ^ 256; omega)
    rw [hadd] at hr
    have hr' : RDret (deployedRuntime v) g s0 σ' (returnWordBytes [assets, shares]) := by
      change RDret _ _ _ _ ((writeCascade mem' (returnWordWrites ptr'.toNat [assets, shares])).readWithPadding
        ptr'.toNat (32 * [assets, shares].length)) at hr
      rw [readReturnWords _ _ _ (by have hh := hm'.gap; omega)] at hr
      exact hr
    exact .ok (ExecBlock.consNormal he' hret) hs' (uint256PairReturnEncoding assets shares) hr'

theorem morphoSafeTransferPair {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {mem out : ByteArray} {aw assets shares ptr : UInt256} {σ : AccountMap}
    {k C : Nat} (isFrom : Bool) (token sender recipient : AccountAddress)
    (locals imms : Store) (args : List Expr) (retVar : String)
    (ha : (retVar == "assets") = false) (hbVar : (retVar == "shares") = false)
    (haGet : locals.get? "assets" = some (.int (Int.ofNat assets.toNat)))
    (hsGet : locals.get? "shares" = some (.int (Int.ofNat shares.toNat)))
    (he : evalExprs? config { contract := contract, locals := locals, immutables := imms } evm args =
      .ok (safeTransferArgs isFrom token sender recipient assets ptr.toNat))
    (hs : SourceState s0 ee σ evm) (hm : MorphoHeap mem ptr 0)
    (hsize : 128 ≤ mem.size) (hptr : 128 ≤ ptr.toNat)
    (hzero : memLoad (UInt256.ofNat 96) mem = UInt256.ofNat 0)
    (h : RD (deployedRuntime v) ee g s0 (safeTransferEntryPC isFrom)
      (safeTransferEVMArgs isFrom token sender recipient assets ++
        (if isFrom then [UInt256.ofNat 4208, UInt256.ofNat 32, shares, assets, UInt256.ofNat 64]
         else [UInt256.ofNat 2752, shares, assets, UInt256.ofNat 64])) mem aw out σ k C) :
    ReturnBlockRefines config (deployedRuntime v) ee g s0
      { contract := contract, locals := locals, immutables := imms } evm
      [.internalCall (if isFrom then "SafeTransferLib_safeTransferFrom" else "SafeTransferLib_safeTransfer") args retVar,
       .return [.var "assets", .var "shares"]] [abiUInt256, abiUInt256] := by
  cases isFrom
  · exact morphoSafeTransferPairAt (v := v) ⟨0, by decide⟩ false token sender recipient locals imms args retVar
      ha hbVar haGet hsGet he hs hm hsize hptr hzero (by simpa only [transferPairReturnPC, transferPairReturnTail, ↓reduceIte] using h)
  · exact morphoSafeTransferPairAt (v := v) ⟨1, by decide⟩ true token sender recipient locals imms args retVar
      ha hbVar haGet hsGet he hs hm hsize hptr hzero (by simpa only [transferPairReturnPC, transferPairReturnTail, ↓reduceIte] using h)

end Benchmarks.Morpho.MorphoBlue
