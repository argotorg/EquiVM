import Benchmarks.Morpho.MetaMorphoV1_1.MaxDepositReadersSource
import Benchmarks.Morpho.MetaMorphoV1_1.SupplySharesAllocationRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.MarketParamsAllocationRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.MarketParamsDecoded
import Benchmarks.Morpho.MetaMorphoV1_1.MarketBalancesSimulation
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_066

/-! The three external reader calls in one max-deposit iteration, with a shared cursor. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem maxDepositReadersSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr id cap total len ret i : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 31 ≤ 1024)
    (hcontract : frame.contract = contract) (himms : frame.immutables = immStore v)
    (hid : frame.locals.get? "id" = some (wordBytes32Value id))
    (hcursor : frame.locals.get? cursorName = some (uint256Value ptr))
    (hcalldata : I.calldata.size < UInt256.size)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hlo : 96 ≤ ptr.toNat)
    (hs : SourceState s0 I σ evm)
    (rd : RD (deployedRuntime v) I g s0 ⟨13998⟩
      ([id, cap, total, UInt256.ofNat v.MORPHO.toNat, len, ret, i] ++ R)
      mem aw rdata σ k C) :
    (∀ tail, ExecBlock config frame evm (maxDepositReaders ++ tail) .reverted) ∧
        RDrev (deployedRuntime v) g s0 ∨
    ∃ (evm' : State) (shares ptr1 ptr2 ptr3 sa ss ba : UInt256)
      (params market mem' out : ByteArray),
      SourceState s0 I evm'.accountMap evm' ∧
      accountStorageStateEq evm.accountMap evm'.accountMap ∧
      (∀ tail outcome, ExecBlock config
        (maxDepositBalancesFrame frame shares ptr1 ptr2 ptr3 params
          (marketUpdatedBalancesValue market sa ss ba)) evm' tail outcome →
        ExecBlock config frame evm (maxDepositReaders ++ tail) outcome) ∧
      memLoad ⟨64⟩ mem' = ptr3 ∧ 96 ≤ ptr3.toNat ∧ ptr3.toNat < 2 ^ 64 ∧
      ptr3.toNat ≤ mem'.size ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨14037⟩
        ([calldataWord market 96, ba, ss, sa, shares, ⟨14045⟩, cap, total,
          ⟨14057⟩, ⟨1⟩, UInt256.ofNat v.MORPHO.toNat, len, ret, i] ++ R)
        mem' aw' out evm'.accountMap k' C' := by
  rcases frame with ⟨c, locals, imms⟩
  dsimp only at hcontract himms hid hcursor
  subst c
  subst imms
  let frame : Frame := { contract := contract, locals := locals, immutables := immStore v }
  have haddr (a : AccountAddress) :
      AccountAddress.ofNat (UInt256.ofNat a.val).toNat = a := by
    rw [UInt256.toNat_ofNat_of_lt (lt_of_lt_of_le a.isLt (by decide))]
    exact accountAddress_ofNat_toNat a
  have hargs : evalExprs? config frame evm
      [.immutable "MORPHO", .var "id", .env .this, .var cursorName] =
      .ok [.address v.MORPHO, wordBytes32Value id, .address I.codeOwner, uint256Value ptr] := by
    have hm : evalExpr? config frame evm (.immutable "MORPHO") = .ok (.address v.MORPHO) :=
      evalImmutable_MORPHO _ _ _ _ _
    have he : evalExpr? config frame evm (.env .this) = .ok (.address I.codeOwner) := by
      simp only [evalExpr?, envValue, hs.env, pure]
    have hd : evalExpr? config frame evm (.var "id") = .ok (wordBytes32Value id) := by
      simp only [evalExpr?, frame, hid, EvalResult.ofOption]
    have hp : evalExpr? config frame evm (.var cursorName) = .ok (uint256Value ptr) := by
      simp only [evalExpr?, frame, hcursor, EvalResult.ofOption]
    simp only [evalExprs?, hm, hd, he, hp, bind, EvalResult.bind, pure]
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_13998_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.append, List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  rcases supplySharesAllocationSimulation v (immStore v)
      (by simp only [List.append, List.length_cons]; omega) hcalldata hfree hlo
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) hs h1 with
    ⟨hbad, hrev⟩ | ⟨evm1, final1, shares, ptr1, mem1, aw2, out1, k2, C2,
      hsource1, hs1, hstore1, hfree1, hlo1, hhi1, hmem1, hprefix1, hmono1, h2⟩
  · simp only [Fin.toNat, haddr] at hbad
    exact .inl ⟨fun _ ↦ ExecBlock.consRevert (supplySharesReaderRevert hargs hbad), hrev⟩
  simp only [Fin.toNat, haddr] at hsource1
  have hcall1 := supplySharesReaderCall (ret := slotsAndCursorName) hargs hsource1
  let frame1 := maxDepositSupplyFrame frame shares ptr1
  have hid1 : frame1.locals.get? "id" = some (wordBytes32Value id) := by
    rw [show frame1 = cursorResultFrame frame "supplyShares" (uint256Value shares) ptr1 from rfl,
      cursorResultFrame_preserves _ _ _ _ _ (by decide) (by decide) (by decide)]
    exact hid
  have hcursor1 : frame1.locals.get? cursorName = some (uint256Value ptr1) :=
    cursorResultFrame_cursor _ _ _ _
  have hargs1 : evalExprs? config frame1 evm1 [.var "id", .var cursorName] =
      .ok [wordBytes32Value id, uint256Value ptr1] := by
    simp only [evalExprs?, evalExpr?, hid1, hcursor1, EvalResult.ofOption,
      bind, EvalResult.bind, pure]
  obtain ⟨aw3, k3, C3, h3⟩ := metaMorphoV1_1_block_14025_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.append, List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
  rcases marketParamsAllocationSimulation v (by simp only [List.append, List.length_cons]; omega)
      hfree1 hlo1 (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) hs1 h3 with
    ⟨hbad, hrev⟩ | ⟨evm2, final2, params, mem2, dst, ptr2, aw4, k4, C4,
      hsource2, hs2, hstore2, hc, hfree2, hlo2, hhi2, hmem2, hdst, hspan, hfields, h4⟩
  · refine .inl ⟨fun tail ↦ ?_, hrev⟩
    apply cursorCallPrefix (by decide) hcall1
    exact ExecBlock.consRevert (marketParamsReaderRevert hargs1 hbad)
  have hcall2 := marketParamsReaderCall (ret := slotsAndCursorName) hargs1 hsource2
  let frame2 := maxDepositParamsFrame frame shares ptr1 ptr2 params
  have hparams2 : frame2.locals.get? "__c1" = some (marketParamsData params).value :=
    cursorResultFrame_value _ _ _ _ (by decide)
  have hcursor2 : frame2.locals.get? cursorName = some (uint256Value ptr2) :=
    cursorResultFrame_cursor _ _ _ _
  have hargs2 : evalExprs? config frame2 evm2
      [.immutable "MORPHO", .var "__c1", .var cursorName] =
      .ok [.address v.MORPHO, (marketParamsData params).value, uint256Value ptr2] := by
    have hm : evalExpr? config frame2 evm2 (.immutable "MORPHO") = .ok (.address v.MORPHO) :=
      evalImmutable_MORPHO _ _ _ _ _
    simp only [evalExprs?, hm, evalExpr?, hparams2, hcursor2, EvalResult.ofOption,
      bind, EvalResult.bind, pure]
  obtain ⟨aw5, k5, C5, h5⟩ := metaMorphoV1_1_block_14031_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.append, List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h4
  rcases marketBalancesSimulation v (marketParamsData params)
      (by simp only [List.append, List.length_cons]; omega) hfree2 hlo2 hhi2 hmem2 hdst hspan
      (marketParamsBytes_of_fields hc (by omega) (by change _ < 2 ^ 256; omega) hfields)
      (marketParamsLoads_of_fields hc hfields) hs2
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h5 with
    ⟨hbad, hrev⟩ | ⟨market, evm3, result, out, hs3, hstore3, hsource3, hdone⟩
  · simp only [Fin.toNat, haddr] at hbad
    refine .inl ⟨fun tail ↦ ?_, hrev⟩
    apply cursorCallPrefix (by decide) hcall1
    apply cursorCallPrefix (by decide) hcall2
    exact ExecBlock.consRevert (marketBalancesReaderRevert hargs2 hbad)
  simp only [Fin.toNat, haddr] at hsource3
  have hcall3 := marketBalancesReaderCall (ret := slotsAndCursorName) hargs2 hsource3
  refine .inr ⟨evm3, shares, ptr1, ptr2, result.cursor, result.supplyAssets,
    result.supplyShares, result.borrowAssets, params, market, result.memory, out,
    hs3, accountStorageStateEq_trans hstore1 (accountStorageStateEq_trans hstore2 hstore3),
    ?_, result.free, result.lower, result.upper, result.size, hdone⟩
  intro tail outcome htail
  apply cursorCallPrefix (by decide) hcall1
  apply cursorCallPrefix (by decide) hcall2
  exact cursorCallPrefix (by decide) hcall3 htail

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
