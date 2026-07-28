import Benchmarks.UniswapV3Pool.Burn

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.UniswapV3Pool

abbrev burnModifyPositionArgValues (I : ExecutionEnv) : List Value :=
  [ .address I.source, burnTickLowerValue I, burnTickUpperValue I, burnLiquidityDeltaValue I ]

abbrev burnModifyPositionStore (I : ExecutionEnv) : Store :=
  ((((∅ : Store).insert "liquidityDelta" (burnLiquidityDeltaValue I))
    |>.insert "tickUpper" (burnTickUpperValue I))
    |>.insert "tickLower" (burnTickLowerValue I))
    |>.insert "owner" (.address I.source)

theorem burnLiquidityDeltaFrame_tickLower {v : PoolImmutables} (I : ExecutionEnv) :
    (burnLiquidityDeltaFrame v I).locals.get? "tickLower" = some (burnTickLowerValue I) := by
  rw [burnLiquidityDeltaFrame, burnStore]
  rw [store_get_ne3 ((∅ : Store).insert "tickLower" (burnTickLowerValue I))
    (k1 := "tickUpper") (k2 := "amount") (k3 := "liquidityDelta")
    (a := "tickLower") (burnTickUpperValue I) (burnAmountValue I)
    (burnLiquidityDeltaValue I) (by native_decide) (by native_decide)
    (by native_decide)]
  exact store_get_self (∅ : Store) "tickLower" (burnTickLowerValue I)

theorem burnLiquidityDeltaFrame_tickUpper {v : PoolImmutables} (I : ExecutionEnv) :
    (burnLiquidityDeltaFrame v I).locals.get? "tickUpper" = some (burnTickUpperValue I) := by
  rw [burnLiquidityDeltaFrame, burnStore]
  rw [store_get_ne2 (((∅ : Store).insert "tickLower" (burnTickLowerValue I))
    |>.insert "tickUpper" (burnTickUpperValue I)) (k1 := "amount") (k2 := "liquidityDelta")
    (a := "tickUpper") (burnAmountValue I) (burnLiquidityDeltaValue I)
    (by native_decide) (by native_decide)]
  exact store_get_self ((∅ : Store).insert "tickLower" (burnTickLowerValue I))
    "tickUpper" (burnTickUpperValue I)

theorem burnLiquidityDeltaFrame_liquidityDelta {v : PoolImmutables} (I : ExecutionEnv) :
    (burnLiquidityDeltaFrame v I).locals.get? "liquidityDelta" =
      some (burnLiquidityDeltaValue I) := by
  rw [burnLiquidityDeltaFrame, burnStore]
  exact store_get_self
    (((∅ : Store).insert "tickLower" (burnTickLowerValue I))
      |>.insert "tickUpper" (burnTickUpperValue I)
      |>.insert "amount" (burnAmountValue I))
    "liquidityDelta" (burnLiquidityDeltaValue I)

theorem uniswapV3PoolLookupModifyPosition (v : PoolImmutables) :
    lookupCallable? (contract v) "modifyPosition" = some (modifyPositionFunction v).toCallable := by
  simp [lookupCallable?, lookupFunction?, contract, functions, getSqrtRatioAtTickFunction,
    getTickAtSqrtRatioFunction, oracleLteFunction, oracleTransformFunction,
    getSurroundingObservationsFunction, observeSingleFunction, observeBodyFunction,
    liquidityAddDeltaFunction, oracleWriteFunction, tickGetFeeGrowthInsideFunction,
    tickUpdateFunction, tickClearFunction, tickBitmapFlipFunction, positionUpdateFunction,
    getAmount0DeltaUnsignedFunction, getAmount1DeltaUnsignedFunction,
    getAmount0DeltaSignedFunction, getAmount1DeltaSignedFunction, modifyPositionFunction]

private theorem uniswapV3PoolBurnSharedTailPatchDisjoint33 {v : PoolImmutables}
    {pc : UInt256}
    (hlo : 16233 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 17313) :
    ∀ p ∈ patches v, pc.toNat + 33 ≤ p.1 ∨ p.1 + 32 ≤ pc.toNat := by
  intro p hp
  simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup] at hp
  rcases hp with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals omega

private theorem uniswapV3PoolBurnSharedTailDecodeEqTemplate {v : PoolImmutables}
    {code : ByteArray} {pc : UInt256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hlo : 16233 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 17313) :
    decode code pc = decode uniswapV3PoolBytecode pc := by
  exact uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch
    (by
      have hsize : 17313 ≤ uniswapV3PoolBytecode.size := by native_decide
      omega)
    (uniswapV3PoolBurnSharedTailPatchDisjoint33 (v := v) (pc := pc) hlo hhi)

theorem uniswapV3PoolBurnNoDelegateCallRevert {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret : UInt256} {R : List UInt256}
    {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨16233⟩
      (⟨128⟩ :: ⟨9737⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        burnAmountCleanWord ee :: burnTickUpperCleanWord ee :: burnTickLowerCleanWord ee ::
        ret :: R)
      (burnModifyPositionMem4 ee) (UInt256.ofNat 8) rdata (cA, σ) k C)
    (hguard : uniswapV3PoolNoDelegateCallGuard v ee = ⟨0⟩)
    (hov : R.length + 19 ≤ 1024) :
    RDrev code g s0 := by
  have hd16233 : decode code ⟨16233⟩ = some (.JUMPDEST, .none) := by
    rw [uniswapV3PoolBurnSharedTailDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd16234 : decode code ⟨16234⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    rw [uniswapV3PoolBurnSharedTailDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd16236 : decode code ⟨16236⟩ = some (.DUP1, .none) := by
    rw [uniswapV3PoolBurnSharedTailDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd16237 : decode code ⟨16237⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    rw [uniswapV3PoolBurnSharedTailDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd16239 : decode code ⟨16239⟩ = some (.Push .PUSH2, some (⟨16246⟩, 2)) := by
    rw [uniswapV3PoolBurnSharedTailDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd16242 : decode code ⟨16242⟩ = some (.Push .PUSH2, some (⟨11248⟩, 2)) := by
    rw [uniswapV3PoolBurnSharedTailDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd16245 : decode code ⟨16245⟩ = some (.JUMP, .none) := by
    rw [uniswapV3PoolBurnSharedTailDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have rd16234 := by
    simpa using h.jumpdest hd16233
      (by simp only [List.length_cons]; omega)
  have rd16236 := by
    simpa using rd16234.push1 ⟨0⟩ hd16234
      (by simp only [List.length_cons]; omega)
  have rd16237 := by
    simpa using rd16236.dup1 hd16236
      (by simp only [List.length_cons]; omega)
  have rd16239 := by
    simpa using rd16237.push1 ⟨0⟩ hd16237
      (by simp only [List.length_cons]; omega)
  have rd16242 := by
    simpa using rd16239.push2 ⟨16246⟩ hd16239
      (by simp only [List.length_cons]; omega)
  have rd16245 := by
    simpa using rd16242.push2 ⟨11248⟩ hd16242
      (by simp only [List.length_cons]; omega)
  have rd11248 := rd16245.jump hd16245 (uniswapV3PoolJumpDestPatched11248 hpatch)
    (by simp only [List.length_cons]; omega)
  exact uniswapV3PoolNoDelegateCallReturnRevert (v := v) (code := code) (ee := ee)
    (g := g) (s0 := s0) (ret := ⟨16246⟩)
    (R := ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
      ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
      burnAmountCleanWord ee :: burnTickUpperCleanWord ee :: burnTickLowerCleanWord ee ::
      ret :: R)
    (mem := burnModifyPositionMem4 ee) (aw := UInt256.ofNat 8) (rdata := rdata)
    (acc := (cA, σ)) hpatch rd11248 hguard
    (by simp only [List.length_cons]; omega)

theorem uniswapV3PoolModifyPositionSourceNoDelegateReverts {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hguard : uniswapV3PoolNoDelegateCallGuard v I = ⟨0⟩) :
    ExecFuncBody (config v) { contract := contract v, locals := burnModifyPositionStore I }
      (initState cA gh bl σ σ₀ g A I) (modifyPositionFunction v).body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [modifyPositionFunction, noDelegateCall] using
    (ExecBlock.consRevert
      (ExecStmt.requireFalse (uniswapV3PoolNoDelegateCallEvalFalse
        (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (L := burnModifyPositionStore I) (g := g) hguard)))

theorem uniswapV3PoolBurnSourceNoDelegateReverts {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hunlocked : burnUnlockedByte σ I ≠ ⟨0⟩)
    (hcanon :
      UInt256.signextend ⟨15⟩ (burnAmountCleanWord I) = burnAmountCleanWord I)
    (hguard : uniswapV3PoolNoDelegateCallGuard v I = ⟨0⟩) :
    ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ σ₀ g A I) (burnStore I)
      burnTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  have hprefix := uniswapV3PoolBurnSourceThroughLiquidityDelta (v := v)
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) hwv hunlocked hcanon
  have hlockState :
      Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I) I.codeOwner ⟨0⟩
          (burnLockedSlotWord σ I) =
        initState cA gh bl
          (sstoreAccountMap I.codeOwner σ ⟨0⟩ (burnLockedSlotWord σ I))
          σ₀ g A I := by
    unfold Solm.EVM.storageStore State.lookupAccount sstoreAccountMap
    cases hlookup : σ.find? I.codeOwner with
    | none =>
        simp [initState, Option.option, hlookup]
    | some _ =>
        simp [initState, State.setAccount, Account.updateStorage, Option.option, hlookup]
  have hstmt :
      ExecStmt (config v) (burnLiquidityDeltaFrame v I)
        (Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I) I.codeOwner ⟨0⟩
          (burnLockedSlotWord σ I))
        (.internalCall "modifyPosition"
          [.env .caller, .var "tickLower", .var "tickUpper", .var "liquidityDelta"]
          "modified")
        .reverted := by
    rw [hlockState]
    refine internalCallFunctionRevert (callee := modifyPositionFunction v)
      (argVals := burnModifyPositionArgValues I) (locals := burnModifyPositionStore I)
      ?_ ?_ ?_ ?_
    · have hLower := burnLiquidityDeltaFrame_tickLower (v := v) I
      have hUpper := burnLiquidityDeltaFrame_tickUpper (v := v) I
      have hDelta := burnLiquidityDeltaFrame_liquidityDelta (v := v) I
      simp only [burnModifyPositionArgValues, evalExprs?, evalExpr?, envValue, initState,
        EvalResult.bind, bind, pure]
      rw [hLower, hUpper, hDelta]
      rfl
    · simpa [burnLiquidityDeltaFrame] using uniswapV3PoolLookupModifyPosition v
    · rfl
    · exact uniswapV3PoolModifyPositionSourceNoDelegateReverts (v := v)
        (cA := cA) (gh := gh) (bl := bl)
        (σ := sstoreAccountMap I.codeOwner σ ⟨0⟩ (burnLockedSlotWord σ I))
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hguard
  simpa [burnTransition, nonpayable, lockPrefix] using
    execBlock_append hprefix (ExecBlock.consRevert hstmt)

end Benchmarks.UniswapV3Pool
