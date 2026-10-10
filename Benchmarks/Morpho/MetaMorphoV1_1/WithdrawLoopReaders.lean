import Benchmarks.Morpho.MetaMorphoV1_1.WithdrawLoopSyntax
import Benchmarks.Morpho.MetaMorphoV1_1.SupplySharesAllocationRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.MarketParamsAllocationRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.MarketParamsDecoded
import Benchmarks.Morpho.MetaMorphoV1_1.MarketBalancesSimulation
import Benchmarks.Morpho.MetaMorphoV1_1.HeapWordWindow
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_072
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_073

/-! The three reader calls in a withdrawal simulation iteration. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem withdrawLoopReadersSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr id assets : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 27 ≤ 1024)
    (hcontract : frame.contract = contract) (himms : frame.immutables = immStore v)
    (hid : frame.locals.get? "id" = some (wordBytes32Value id))
    (hcursor : frame.locals.get? cursorName = some (uint256Value ptr))
    (hcalldata : I.calldata.size < UInt256.size)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hlo : 96 ≤ ptr.toNat)
    (hs : SourceState s0 I σ evm)
    (rd : RD (deployedRuntime v) I g s0 ⟨16116⟩
      ([id, ⟨16034⟩, ⟨16043⟩, ⟨16063⟩, id, ⟨16069⟩, assets,
        UInt256.ofNat v.MORPHO.toNat] ++ R) mem aw rdata σ k C) :
    ((∀ tail, ExecBlock config frame evm (withdrawLoopReaders ++ tail) .reverted) ∧
      RDrev (deployedRuntime v) g s0) ∨
    ∃ (evm' : State) (src ptr1 shares ptr2 ptr3 sa ss ba : UInt256)
      (params market mem' out : ByteArray),
      SourceState s0 I evm'.accountMap evm' ∧
      accountStorageStateEq evm.accountMap evm'.accountMap ∧
      (∀ tail outcome, ExecBlock config
        (withdrawLoopBalancesFrame frame params ptr1 shares ptr2 ptr3
          (marketUpdatedBalancesValue market sa ss ba)) evm' tail outcome →
        ExecBlock config frame evm (withdrawLoopReaders ++ tail) outcome) ∧
      memLoad ⟨64⟩ mem' = ptr3 ∧ 96 ≤ ptr3.toNat ∧ ptr3.toNat < 2 ^ 64 ∧
      ptr3.toNat ≤ mem'.size ∧
      memLoad src mem' = UInt256.ofNat (marketParamsData params).loanToken.toNat ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨16053⟩
        ([calldataWord market 96, ba, ss, sa, shares, ⟨16063⟩, src, ⟨16069⟩, assets,
          UInt256.ofNat v.MORPHO.toNat] ++ R) mem' aw' out evm'.accountMap k' C' := by
  rcases frame with ⟨c, locals, imms⟩
  dsimp only at hcontract himms hid hcursor
  subst c
  subst imms
  let frame : Frame := { contract := contract, locals := locals, immutables := immStore v }
  have haddr (a : AccountAddress) :
      AccountAddress.ofNat (UInt256.ofNat a.val).toNat = a := by
    rw [UInt256.toNat_ofNat_of_lt (lt_of_lt_of_le a.isLt (by decide))]
    exact accountAddress_ofNat_toNat a
  have hargs1 : evalExprs? config frame evm [.var "id", .var cursorName] =
      .ok [wordBytes32Value id, uint256Value ptr] := by
    simp only [evalExprs?, evalExpr?, frame, hid, hcursor, EvalResult.ofOption,
      bind, EvalResult.bind, pure]
  rcases marketParamsAllocationSimulation v (by simp only [List.append, List.length_cons]; omega)
      hfree hlo (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) hs rd with
    ⟨hbad, hrev⟩ | ⟨evm1, final1, params, mem1, src, ptr1, aw1, k1, C1,
      hsource1, hs1, hstore1, hparams, hfree1, hlo1, hhi1, hmem1, hsrc, hspan, hfields, h1⟩
  · exact .inl ⟨fun _ ↦ ExecBlock.consRevert (marketParamsReaderRevert hargs1 hbad), hrev⟩
  have hcall1 := marketParamsReaderCall (ret := slotsAndCursorName) hargs1 hsource1
  let frame1 := withdrawLoopParamsFrame frame params ptr1
  have hid1 : frame1.locals.get? "id" = some (wordBytes32Value id) := by
    rw [show frame1 = cursorResultFrame frame "marketParams" _ ptr1 from rfl,
      cursorResultFrame_preserves _ _ _ _ _ (by decide) (by decide) (by decide)]
    exact hid
  have hcursor1 : frame1.locals.get? cursorName = some (uint256Value ptr1) :=
    cursorResultFrame_cursor _ _ _ _
  have hargs2 : evalExprs? config frame1 evm1
      [.immutable "MORPHO", .var "id", .env .this, .var cursorName] =
      .ok [.address v.MORPHO, wordBytes32Value id, .address I.codeOwner, uint256Value ptr1] := by
    have hm : evalExpr? config frame1 evm1 (.immutable "MORPHO") = .ok (.address v.MORPHO) :=
      evalImmutable_MORPHO _ _ _ _ _
    have he : evalExpr? config frame1 evm1 (.env .this) = .ok (.address I.codeOwner) := by
      simp only [evalExpr?, envValue, hs1.env, pure]
    simp only [evalExprs?, hm, he, evalExpr?, hid1, hcursor1, EvalResult.ofOption,
      bind, EvalResult.bind, pure]
  obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_16034_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.append]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
  rcases supplySharesAllocationSimulation v (immStore v)
      (by simp only [List.append, List.length_cons]; omega) hcalldata hfree1 hlo1
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) hs1 h2 with
    ⟨hbad, hrev⟩ | ⟨evm2, final2, shares, ptr2, mem2, aw3, out2, k3, C3,
      hsource2, hs2, hstore2, hfree2, hlo2, hhi2, hmem2, hprefix2, hmono2, h3⟩
  · simp only [Fin.toNat, haddr] at hbad
    refine .inl ⟨fun tail ↦ ?_, hrev⟩
    apply cursorCallPrefix (by decide) hcall1
    exact ExecBlock.consRevert (supplySharesReaderRevert hargs2 hbad)
  simp only [Fin.toNat, haddr] at hsource2
  have hcall2 := supplySharesReaderCall (ret := slotsAndCursorName) hargs2 hsource2
  let p := marketParamsData params
  have hbytes1 : mem1.readWithPadding src.toNat 160 = p.bytes :=
    marketParamsBytes_of_fields hparams (by omega) (by change _ < 2 ^ 256; omega) hfields
  have hloads1 : MarketParamsLoads mem1 src p := marketParamsLoads_of_fields hparams hfields
  have hsrcfit : src.toNat + 160 < UInt256.size := by change _ < 2 ^ 256; omega
  have hbytes2 : mem2.readWithPadding src.toNat 160 = p.bytes := by
    rw [memoryPrefix_read_words hprefix2 5 src.toNat hsrc hspan (by omega)]
    exact hbytes1
  have hloads2 : MarketParamsLoads mem2 src p :=
    hloads1.prefix hprefix2 hsrc (by omega) hspan hsrcfit
  let frame2 := withdrawLoopSharesFrame frame params ptr1 shares ptr2
  have hparams2 : frame2.locals.get? "marketParams" = some p.value := by
    rw [show frame2 = cursorResultFrame frame1 "supplyShares" _ ptr2 from rfl,
      cursorResultFrame_preserves _ _ _ _ _ (by decide) (by decide) (by decide)]
    exact cursorResultFrame_value _ _ _ _ (by decide)
  have hcursor2 : frame2.locals.get? cursorName = some (uint256Value ptr2) :=
    cursorResultFrame_cursor _ _ _ _
  have hargs3 : evalExprs? config frame2 evm2
      [.immutable "MORPHO", .var "marketParams", .var cursorName] =
      .ok [.address v.MORPHO, p.value, uint256Value ptr2] := by
    have hm : evalExpr? config frame2 evm2 (.immutable "MORPHO") = .ok (.address v.MORPHO) :=
      evalImmutable_MORPHO _ _ _ _ _
    simp only [evalExprs?, hm, evalExpr?, hparams2, hcursor2, EvalResult.ofOption,
      bind, EvalResult.bind, pure]
  obtain ⟨aw4, k4, C4, h4⟩ := metaMorphoV1_1_block_16043_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.append]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h3
  rcases marketBalancesSimulation v p (by simp only [List.append, List.length_cons]; omega)
      hfree2 hlo2 hhi2 hmem2 hsrc (by omega) hbytes2 hloads2 hs2
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h4 with
    ⟨hbad, hrev⟩ | ⟨market, evm3, result, out3, hs3, hstore3, hsource3, hdone⟩
  · simp only [Fin.toNat, haddr] at hbad
    refine .inl ⟨fun tail ↦ ?_, hrev⟩
    apply cursorCallPrefix (by decide) hcall1
    apply cursorCallPrefix (by decide) hcall2
    exact ExecBlock.consRevert (marketBalancesReaderRevert hargs3 hbad)
  simp only [Fin.toNat, haddr] at hsource3
  have hcall3 := marketBalancesReaderCall (ret := slotsAndCursorName) hargs3 hsource3
  have hloads3 : MarketParamsLoads result.memory src p :=
    hloads2.prefix result.preserves hsrc (by omega) (by omega) hsrcfit
  refine .inr ⟨evm3, src, ptr1, shares, ptr2, result.cursor, result.supplyAssets,
    result.supplyShares, result.borrowAssets, params, market, result.memory, out3, hs3,
    accountStorageStateEq_trans hstore1 (accountStorageStateEq_trans hstore2 hstore3),
    ?_, result.free, result.lower, result.upper, result.size, hloads3.1, hdone⟩
  intro tail outcome htail
  apply cursorCallPrefix (by decide) hcall1
  apply cursorCallPrefix (by decide) hcall2
  exact cursorCallPrefix (by decide) hcall3 htail

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
