import Examples.UniswapV2Pair.MintFeeAfterRootsRuntime

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair

theorem sqrtLoopNextX_nonneg (y x : Int) (hyNonneg : 0 ≤ y) (hxPos : 0 < x) :
    0 ≤ sqrtLoopNextX y x := by
  unfold sqrtLoopNextX
  have hdivNonneg : 0 ≤ y / x := Int.ediv_nonneg hyNonneg (by omega)
  exact Int.ediv_nonneg (by omega) (by omega)

theorem sqrtLoopNextX_toNat (y x : Int) (hyNonneg : 0 ≤ y) (hxPos : 0 < x) :
    (sqrtLoopNextX y x).toNat = (y.toNat / x.toNat + x.toNat) / 2 := by
  have hnextNonneg := sqrtLoopNextX_nonneg y x hyNonneg hxPos
  have hcastDiv : ((y.toNat / x.toNat : Nat) : Int) = y / x := by
    rw [Int.natCast_ediv]
    · simp [Int.toNat_of_nonneg hyNonneg, Int.toNat_of_nonneg (le_of_lt hxPos)]
  have hcastSum :
      ((y.toNat / x.toNat + x.toNat : Nat) : Int) = y / x + x := by
    rw [Nat.cast_add, hcastDiv]
    simp [Int.toNat_of_nonneg (le_of_lt hxPos)]
  have hcastDiv2 :
      (((y.toNat / x.toNat + x.toNat) / 2 : Nat) : Int) =
        (y / x + x) / 2 := by
    rw [Int.natCast_ediv]
    · rw [hcastSum]
      norm_num
  calc
    (sqrtLoopNextX y x).toNat = ((y / x + x) / 2).toNat := by rfl
    _ = (((y.toNat / x.toNat + x.toNat) / 2 : Nat) : Int).toNat :=
      (congrArg Int.toNat hcastDiv2).symm
    _ = (y.toNat / x.toNat + x.toNat) / 2 := by rw [Int.toNat_natCast]

theorem sqrtLoopNextX_size_of_add_fit
    (y x : Int)
    (hyNonneg : 0 ≤ y)
    (hxPos : 0 < x)
    (haddFit : y.toNat / x.toNat + x.toNat < UInt256.size) :
    (sqrtLoopNextX y x).toNat < UInt256.size := by
  rw [sqrtLoopNextX_toNat y x hyNonneg hxPos]
  exact lt_of_le_of_lt (Nat.div_le_self _ _) haddFit

theorem sqrtLoop_step_add_le_y_of_bounds
    (y x : Nat)
    (hy : 3 < y)
    (hxLow : 2 ≤ x)
    (hxHigh : x ≤ y / 2 + 1) :
    y / x + x ≤ y := by
  by_cases hx2 : x = 2
  · subst x
    omega
  · have hx3 : 3 ≤ x := by omega
    have hdiv3 : y / x ≤ y / 3 := Nat.div_le_div_left (a := y) hx3 (by norm_num)
    omega

theorem sqrtLoop_step_next_low_of_bounds
    (y x : Nat)
    (hy : 3 < y)
    (hxLow : 2 ≤ x)
    (hxHigh : x ≤ y / 2 + 1) :
    2 ≤ (y / x + x) / 2 := by
  by_cases hx2 : x = 2
  · subst x
    omega
  · have hx3 : 3 ≤ x := by omega
    have hxLeY : x ≤ y := by omega
    have hdivPos : 0 < y / x := Nat.div_pos hxLeY (by omega)
    omega

theorem sqrtLoop_step_next_high_of_bounds
    (y x : Nat)
    (hy : 3 < y)
    (hxLow : 2 ≤ x)
    (hxHigh : x ≤ y / 2 + 1) :
    (y / x + x) / 2 ≤ y / 2 + 1 := by
  have hsum := sqrtLoop_step_add_le_y_of_bounds y x hy hxLow hxHigh
  have hdiv : (y / x + x) / 2 ≤ y / 2 := Nat.div_le_div_right hsum
  omega

abbrev sqrtLoopRuntimeInv (y x : Int) : Prop :=
  2 ≤ x.toNat ∧ x.toNat ≤ y.toNat / 2 + 1

theorem sqrtLoopRuntimeInv_step_fit
    (y x z : Int)
    (hy : 3 < y.toNat)
    (hySize : y.toNat < UInt256.size)
    (hP : sqrtLoopRuntimeInv y x)
    (_hxPos : 0 < x)
    (_hzNonneg : 0 ≤ z)
    (_hlt : x < z)
    (_hxSize : x.toNat < UInt256.size)
    (_hzSize : z.toNat < UInt256.size) :
    y.toNat / x.toNat + x.toNat < UInt256.size := by
  exact lt_of_le_of_lt (sqrtLoop_step_add_le_y_of_bounds y.toNat x.toNat hy hP.1 hP.2)
    hySize

theorem sqrtLoopRuntimeInv_step
    (y x z : Int)
    (hy : 3 < y.toNat)
    (hP : sqrtLoopRuntimeInv y x)
    (hxPos : 0 < x)
    (_hzNonneg : 0 ≤ z)
    (_hlt : x < z) :
    sqrtLoopRuntimeInv y (sqrtLoopNextX y x) := by
  change 2 ≤ (sqrtLoopNextX y x).toNat ∧
    (sqrtLoopNextX y x).toNat ≤ y.toNat / 2 + 1
  rw [sqrtLoopNextX_toNat y x (by omega) hxPos]
  constructor
  · exact sqrtLoop_step_next_low_of_bounds y.toNat x.toNat hy hP.1 hP.2
  · exact sqrtLoop_step_next_high_of_bounds y.toNat x.toNat hy hP.1 hP.2

theorem sqrtFunctionInitialX_toNat (y : UInt256) :
    (sqrtFunctionInitialX y).toNat = y.toNat / 2 + 1 := by
  unfold sqrtFunctionInitialX sqrtFunctionYInt
  have hnonneg : 0 ≤ (Int.ofNat y.toNat / 2 + 1 : Int) := by
    have hdiv : 0 ≤ (Int.ofNat y.toNat : Int) / 2 :=
      Int.ediv_nonneg (Int.natCast_nonneg _) (by omega)
    omega
  have hcast : ((y.toNat / 2 + 1 : Nat) : Int) = Int.ofNat y.toNat / 2 + 1 := by
    rw [Nat.cast_add, Int.natCast_ediv]
    · norm_num
  apply Nat.cast_injective (R := Int)
  rw [Int.toNat_of_nonneg hnonneg]
  exact hcast

theorem sqrtFunctionInitialX_size (y : UInt256) :
    (sqrtFunctionInitialX y).toNat < UInt256.size := by
  rw [sqrtFunctionInitialX_toNat]
  have hyLe : y.toNat ≤ UInt256.size - 1 := by
    exact Nat.le_pred_of_lt y.val.isLt
  have hdivLe : y.toNat / 2 ≤ (UInt256.size - 1) / 2 :=
    Nat.div_le_div_right hyLe
  have hbound : (UInt256.size - 1) / 2 + 1 < UInt256.size := by
    norm_num [UInt256.size]
  omega

theorem sqrtFunctionInitialX_word_eq (y : UInt256) :
    UInt256.div y (⟨2⟩ : UInt256) + ⟨1⟩ =
      UInt256.ofNat (sqrtFunctionInitialX y).toNat := by
  apply u256_inj
  rw [uadd_toNat, udiv_toNat, show (⟨2⟩ : UInt256).toNat = 2 from by decide,
    show (⟨1⟩ : UInt256).toNat = 1 from by decide, sqrtFunctionInitialX_toNat]
  rw [ulit_toNat' _ (by
    rw [← sqrtFunctionInitialX_toNat]
    exact sqrtFunctionInitialX_size y)]
  rw [Nat.mod_eq_of_lt (by
    simpa [sqrtFunctionInitialX_toNat] using sqrtFunctionInitialX_size y)]

theorem sqrtFunctionInitialX_runtime_inv (y : UInt256) (hlarge : 3 < y.toNat) :
    sqrtLoopRuntimeInv (sqrtFunctionYInt y) (sqrtFunctionInitialX y) := by
  change 2 ≤ (sqrtFunctionInitialX y).toNat ∧
    (sqrtFunctionInitialX y).toNat ≤ (sqrtFunctionYInt y).toNat / 2 + 1
  rw [sqrtFunctionInitialX_toNat]
  constructor
  · omega
  · unfold sqrtFunctionYInt
    rw [show (Int.ofNat y.toNat).toNat = y.toNat by simp]

theorem sqrtLoopNextX_word_step
    (y x : Int)
    (hyNonneg : 0 ≤ y)
    (hxPos : 0 < x)
    (hySize : y.toNat < UInt256.size)
    (hxSize : x.toNat < UInt256.size)
    (haddFit : y.toNat / x.toNat + x.toNat < UInt256.size) :
    UInt256.div
        (UInt256.div (UInt256.ofNat y.toNat) (UInt256.ofNat x.toNat) +
          UInt256.ofNat x.toNat)
        (⟨2⟩ : UInt256) =
      UInt256.ofNat (sqrtLoopNextX y x).toNat := by
  apply u256_inj
  have hxNatPos : 0 < x.toNat := by
    omega
  have hdivWord :
      (UInt256.div (UInt256.ofNat y.toNat) (UInt256.ofNat x.toNat)).toNat =
        y.toNat / x.toNat := by
    rw [udiv_toNat, ulit_toNat' _ hySize, ulit_toNat' _ hxSize]
  have hsum :
      (UInt256.div (UInt256.ofNat y.toNat) (UInt256.ofNat x.toNat) +
          UInt256.ofNat x.toNat).toNat =
        y.toNat / x.toNat + x.toNat := by
    rw [uadd_toNat, hdivWord, ulit_toNat' _ hxSize, Nat.mod_eq_of_lt haddFit]
  have htwo : (⟨2⟩ : UInt256).toNat = 2 := by decide
  rw [udiv_toNat, hsum, htwo]
  have hnextNonneg : 0 ≤ sqrtLoopNextX y x := by
    have hyPosOrZero : 0 ≤ y := hyNonneg
    have hdivNonneg : 0 ≤ y / x := Int.ediv_nonneg hyPosOrZero (by omega)
    unfold sqrtLoopNextX
    have hsumNonneg : 0 ≤ y / x + x := by omega
    exact Int.ediv_nonneg hsumNonneg (by omega)
  rw [ulit_toNat' _]
  · unfold sqrtLoopNextX
    have hcastDiv : ((y.toNat / x.toNat : Nat) : Int) = y / x := by
      rw [Int.natCast_ediv]
      · simp [Int.toNat_of_nonneg hyNonneg, Int.toNat_of_nonneg (le_of_lt hxPos)]
    have hcastSum :
        ((y.toNat / x.toNat + x.toNat : Nat) : Int) = y / x + x := by
      rw [Nat.cast_add, hcastDiv]
      simp [Int.toNat_of_nonneg (le_of_lt hxPos)]
    have hcastDiv2 :
        (((y.toNat / x.toNat + x.toNat) / 2 : Nat) : Int) =
          (y / x + x) / 2 := by
      rw [Int.natCast_ediv]
      · rw [hcastSum]
        norm_num
    calc
      (y.toNat / x.toNat + x.toNat) / 2 =
          (((y.toNat / x.toNat + x.toNat) / 2 : Nat) : Int).toNat := by
        rw [Int.toNat_natCast]
      _ = ((y / x + x) / 2).toNat := congrArg Int.toNat hcastDiv2
  · have hnextLe :
        (sqrtLoopNextX y x).toNat ≤ (y.toNat / x.toNat + x.toNat) / 2 := by
      unfold sqrtLoopNextX
      have hcastDiv : ((y.toNat / x.toNat : Nat) : Int) = y / x := by
        rw [Int.natCast_ediv]
        · simp [Int.toNat_of_nonneg hyNonneg, Int.toNat_of_nonneg (le_of_lt hxPos)]
      have hcastSum :
          ((y.toNat / x.toNat + x.toNat : Nat) : Int) = y / x + x := by
        rw [Nat.cast_add, hcastDiv]
        simp [Int.toNat_of_nonneg (le_of_lt hxPos)]
      have hcastDiv2 :
          (((y.toNat / x.toNat + x.toNat) / 2 : Nat) : Int) =
            (y / x + x) / 2 := by
        rw [Int.natCast_ediv]
        · rw [hcastSum]
          norm_num
      rw [show ((y / x + x) / 2).toNat =
          (y.toNat / x.toNat + x.toNat) / 2 by
        calc
          ((y / x + x) / 2).toNat =
              (((y.toNat / x.toNat + x.toNat) / 2 : Nat) : Int).toNat :=
            (congrArg Int.toNat hcastDiv2).symm
          _ = (y.toNat / x.toNat + x.toNat) / 2 := by
            rw [Int.toNat_natCast]]
    exact lt_of_le_of_lt hnextLe (lt_of_le_of_lt (Nat.div_le_self _ _) haddFit)

set_option maxHeartbeats 1000000 in
theorem execStmt_sqrtLoopTerminates_runtime
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (evm : EVM.State) (y : Int)
    (hyPos : 0 < y)
    (hySize : y.toNat < UInt256.size)
    (hret : (D_J uniswapV2PairBytecode 0).contains ret = true)
    (hov : R.length + 10 ≤ 1024)
    (P : Int → Int → Prop)
    (hstepFit :
      ∀ x z : Int,
        P x z → 0 < x → 0 ≤ z → x < z → x.toNat < UInt256.size →
          z.toNat < UInt256.size →
          y.toNat / x.toNat + x.toNat < UInt256.size) :
    (hstepInv :
      ∀ x z : Int,
        P x z → 0 < x → 0 ≤ z → x < z → P (sqrtLoopNextX y x) x) →
    ∀ fuel, ∀ locals x z k C,
      z.toNat = fuel → P x z → 0 < x → 0 ≤ z → x.toNat < UInt256.size →
      z.toNat < UInt256.size →
      locals.get? "y" = some (.int y) → locals.get? "x" = some (.int x) →
      locals.get? "z" = some (.int z) →
      RD uniswapV2PairBytecode ee g s0 ⟨8067⟩
        (UInt256.ofNat x.toNat :: UInt256.ofNat z.toNat :: UInt256.ofNat y.toNat ::
          ret :: R)
        mem aw rdata acc k C →
      ∃ locals' result k' C',
        ExecStmt config ({ contract := contract, locals := locals } : Frame) evm
          (.while sqrtLoopCond sqrtLoopBody)
          (.ok (show Frame from { contract := contract, locals := locals' }) evm) ∧
        locals'.get? "z" = some (.int result) ∧
        0 ≤ result ∧ result.toNat ≤ fuel ∧
        RD uniswapV2PairBytecode ee g s0 ret (UInt256.ofNat result.toNat :: R)
          mem aw rdata acc k' C' := by
  intro hstepInv
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
      intro locals x z k C hzFuel hP hxPos hzNonneg hxSize hzSize hyLocal hxLocal hzLocal
        rd8067
      by_cases hlt : x < z
      · have hcond := evalExpr_sqrtLoopCond_true evm locals x z hxLocal hzLocal hlt
        have hbody :=
          execBlock_sqrtLoopBody evm locals y x z hyLocal hxLocal hzLocal (ne_of_gt hxPos)
        have hzPos : 0 < z := by omega
        have hmeasure : x.toNat < fuel := by
          rw [← hzFuel]
          exact (Int.toNat_lt_toNat hzPos).mpr hlt
        have hltWord :
            (UInt256.ofNat x.toNat).toNat < (UInt256.ofNat z.toNat).toNat := by
          rw [ulit_toNat' _ hxSize, ulit_toNat' _ hzSize]
          exact (Int.toNat_lt_toNat hzPos).mpr hlt
        have hxWordNe : UInt256.ofNat x.toNat ≠ (⟨0⟩ : UInt256) := by
          intro hzero
          have hnat := congrArg UInt256.toNat hzero
          rw [ulit_toNat' _ hxSize] at hnat
          have hxNatPos : 0 < x.toNat := by
            have hxCast : (x.toNat : Int) = x := by
              rw [Int.toNat_of_nonneg (le_of_lt hxPos)]
            omega
          have hnat0 : x.toNat = 0 := by
            simpa using hnat
          omega
        obtain ⟨kStep, CStep, rdStepRaw⟩ :=
          uniswapSqrtRuntimeLoopStep rd8067 hltWord hxWordNe hov
        have haddFit := hstepFit x z hP hxPos hzNonneg hlt hxSize hzSize
        have hstepWord :=
          sqrtLoopNextX_word_step y x (le_of_lt hyPos) hxPos hySize hxSize haddFit
        have rdStep :
            RD uniswapV2PairBytecode ee g s0 ⟨8067⟩
              (UInt256.ofNat (sqrtLoopNextX y x).toNat :: UInt256.ofNat x.toNat ::
                UInt256.ofNat y.toNat :: ret :: R)
              mem aw rdata acc kStep CStep := by
          simpa [hstepWord] using rdStepRaw
        have hnextSize :
            (sqrtLoopNextX y x).toNat < UInt256.size :=
          sqrtLoopNextX_size_of_add_fit y x (le_of_lt hyPos) hxPos haddFit
        obtain ⟨locals', result, k', C', hwhile, hzFinal, hresultNonneg, hresultFuel,
          rdRet⟩ :=
          ih x.toNat hmeasure
            (sqrtLoopAfterBodyStore locals y x) (sqrtLoopNextX y x) x kStep CStep rfl
            (hstepInv x z hP hxPos hzNonneg hlt)
            (sqrtLoopNextX_pos y x hyPos hxPos) (by omega) hnextSize hxSize
            (sqrtLoopAfterBodyStore_y locals y x hyLocal)
            (sqrtLoopAfterBodyStore_x locals y x)
            (sqrtLoopAfterBodyStore_z locals y x)
            rdStep
        exact ⟨locals', result, k', C', ExecStmt.whileTrue hcond hbody hwhile,
          hzFinal, hresultNonneg, le_trans hresultFuel (Nat.le_of_lt hmeasure), rdRet⟩
      · have hcond := evalExpr_sqrtLoopCond_false evm locals x z hxLocal hzLocal hlt
        have hnltWord :
            ¬ (UInt256.ofNat x.toNat).toNat < (UInt256.ofNat z.toNat).toNat := by
          intro hword
          rw [ulit_toNat' _ hxSize, ulit_toNat' _ hzSize] at hword
          have hwordInt : (x.toNat : Int) < (z.toNat : Int) := by exact_mod_cast hword
          apply hlt
          simpa [Int.toNat_of_nonneg (le_of_lt hxPos), Int.toNat_of_nonneg hzNonneg]
            using hwordInt
        obtain ⟨k', C', rdRet⟩ :=
          uniswapSqrtRuntimeLoopExit rd8067 hnltWord hret (by omega)
        exact ⟨locals, z, k', C', ExecStmt.whileFalse hcond, hzLocal, hzNonneg,
          by rw [hzFuel], rdRet⟩

set_option maxHeartbeats 1000000 in
theorem uniswapSqrtFunctionBodyRuntime_gt3
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {y ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (evm : EVM.State)
    (rd8046 : RD uniswapV2PairBytecode ee g s0 ⟨8046⟩ (y :: ret :: R)
      mem aw rdata acc k C)
    (hlarge : 3 < y.toNat)
    (hret : (D_J uniswapV2PairBytecode 0).contains ret = true)
    (hov : R.length + 10 ≤ 1024) :
    ∃ locals' result k' C',
      ExecFuncBody config { contract := contract, locals := sqrtFunctionCallStore y } evm
        sqrtFunction.body
        (.returned { contract := contract, locals := locals' } evm (some [.int result])) ∧
      0 ≤ result ∧ result.toNat < UInt256.size ∧
      result.toNat ≤ y.toNat ∧
      RD uniswapV2PairBytecode ee g s0 ret (UInt256.ofNat result.toNat :: R)
        mem aw rdata acc k' C' := by
  obtain ⟨kLoop, CLoop, rdLoopRaw⟩ :=
    uniswapSqrtRuntimeLargePrefix rd8046 hlarge (by omega)
  have rdLoop :
      RD uniswapV2PairBytecode ee g s0 ⟨8067⟩
        (UInt256.ofNat (sqrtFunctionInitialX y).toNat ::
          UInt256.ofNat (sqrtFunctionYInt y).toNat ::
          UInt256.ofNat (sqrtFunctionYInt y).toNat :: ret :: R)
        mem aw rdata acc kLoop CLoop := by
    simpa [sqrtFunctionInitialX_word_eq, sqrtFunctionYInt, u256_ofNat_toNat] using rdLoopRaw
  have hyPos : 0 < sqrtFunctionYInt y := by
    unfold sqrtFunctionYInt
    exact Int.ofNat_lt.mpr (lt_trans (by decide : 0 < 3) hlarge)
  have hySize : (sqrtFunctionYInt y).toNat < UInt256.size := by
    change y.toNat < UInt256.size
    exact y.val.isLt
  have hyLargeInt : 3 < (sqrtFunctionYInt y).toNat := by
    simpa [sqrtFunctionYInt] using hlarge
  obtain ⟨locals', result, k', C', hwhile, hzFinal, hresultNonneg, hresultFuel,
    rdRet⟩ :=
    execStmt_sqrtLoopTerminates_runtime
      (g := g) (s0 := s0) (ee := ee) (ret := ret) (R := R) (mem := mem) (aw := aw)
      (rdata := rdata) (acc := acc)
      evm (sqrtFunctionYInt y) hyPos hySize hret hov
      (fun x _z => sqrtLoopRuntimeInv (sqrtFunctionYInt y) x)
      (fun x z hP hxPos hzNonneg hlt hxSize hzSize =>
        sqrtLoopRuntimeInv_step_fit (sqrtFunctionYInt y) x z hyLargeInt hySize hP
          hxPos hzNonneg hlt hxSize hzSize)
      (fun x z hP hxPos hzNonneg hlt =>
        sqrtLoopRuntimeInv_step (sqrtFunctionYInt y) x z hyLargeInt hP hxPos
          hzNonneg hlt)
      y.toNat (sqrtFunctionAfterInitStore y) (sqrtFunctionInitialX y)
      (sqrtFunctionYInt y) kLoop CLoop
      (by simp [sqrtFunctionYInt])
      (sqrtFunctionInitialX_runtime_inv y hlarge)
      (sqrtFunctionInitialX_pos y)
      (by simp [sqrtFunctionYInt])
      (sqrtFunctionInitialX_size y)
      hySize
      (sqrtFunctionAfterInitStore_y y) (sqrtFunctionAfterInitStore_x y)
      (sqrtFunctionAfterInitStore_z y) rdLoop
  have hresultSize : result.toNat < UInt256.size :=
    lt_of_le_of_lt hresultFuel y.val.isLt
  refine ⟨locals', result, k', C', ?_, hresultNonneg, hresultSize, hresultFuel, rdRet⟩
  refine ExecFuncBody.execBlockRet ?_
  change ExecBlock config { contract := contract, locals := sqrtFunctionCallStore y } evm
    [ .ite (.binary .gt (.var "y") (.intLit 3))
        [ .letDecl "z" (some uint256) (.var "y"),
          .letDecl "x" (some uint256)
            (.binary .add (.binary .div (.var "y") (.intLit 2)) (.intLit 1)),
          .while (.binary .lt (.var "x") (.var "z"))
            [ .assign .localVar { base := "z" } (.var "x"),
              .assign .localVar { base := "x" }
                (.binary .div
                  (.binary .add (.binary .div (.var "y") (.var "x")) (.var "x"))
                  (.intLit 2)) ],
          .return [(.var "z")] ]
        [ .ite (.binary .ne (.var "y") (.intLit 0))
            [ .return [(.intLit 1)] ]
            [ .return [(.intLit 0)] ] ] ]
    (.returned { contract := contract, locals := locals' } evm (some [.int result]))
  refine ExecBlock.consReturn (ExecStmt.iteTrue
    (evalExpr_sqrtFunction_outer_true evm y hlarge) ?_)
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_sqrtFunction_y evm y)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_sqrtFunction_initX evm y)) ?_
  have hwhile' :
      ExecStmt config ({ contract := contract, locals := sqrtFunctionAfterInitStore y } : Frame)
        evm (.while sqrtLoopCond sqrtLoopBody)
        (.ok ({ contract := contract, locals := locals' } : Frame) evm) := by
    simpa using hwhile
  change ExecBlock config ({ contract := contract, locals := sqrtFunctionAfterInitStore y } : Frame)
    evm [ .while sqrtLoopCond sqrtLoopBody, .return [(.var "z")] ]
    (.returned { contract := contract, locals := locals' } evm (some [.int result]))
  refine ExecBlock.consNormal hwhile' ?_
  have hretEval :
      evalExpr? config { contract := contract, locals := locals' } evm (.var "z") =
        .ok (.int result) := by
    simp only [evalExpr?, EvalResult.ofOption]
    rw [hzFinal]
  exact ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hretEval))

set_option maxHeartbeats 1000000 in
theorem uniswapSqrtFunctionCallRuntimeSuccessIntBounded
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {y ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {caller : Frame} {evm : EVM.State} {args : List Expr} {retVar : Ident}
    (hcontract : caller.contract = contract)
    (hargs : evalExprs? config caller evm args = .ok [sqrtFunctionYValue y])
    (rd8046 : RD uniswapV2PairBytecode ee g s0 ⟨8046⟩ (y :: ret :: R)
      mem aw rdata acc k C)
    (hret : (D_J uniswapV2PairBytecode 0).contains ret = true)
    (hov : R.length + 10 ≤ 1024) :
    ∃ result k' C',
      ExecStmt config caller evm (.internalCall "sqrt" args retVar)
        (.ok (resumeAfterInternalCall caller retVar (some [.int result])) evm) ∧
      0 ≤ result ∧ result.toNat < UInt256.size ∧
      RD uniswapV2PairBytecode ee g s0 ret (UInt256.ofNat result.toNat :: R)
        mem aw rdata acc k' C' := by
  by_cases hsmall : y.toNat ≤ 3
  · obtain ⟨k', C', rdRetRaw⟩ := uniswapSqrtRuntimeSmallReturns rd8046 hsmall hret
      (by omega)
    by_cases hyZero : y = ⟨0⟩
    · have hstmt :
          ExecStmt config caller evm (.internalCall "sqrt" args retVar)
            (.ok (resumeAfterInternalCall caller retVar (some [.int 0])) evm) := by
        simpa [sqrtFunctionSmallResultValue, hyZero] using
          uniswapSqrtFunctionCallSuccess_le3 hcontract hsmall hargs
      have rdRet :
          RD uniswapV2PairBytecode ee g s0 ret (UInt256.ofNat 0 :: R)
            mem aw rdata acc k' C' := by
        simpa [hyZero] using rdRetRaw
      refine ⟨0, k', C', hstmt, by omega, ?_, rdRet⟩
      norm_num [UInt256.size]
    · have hyNatNe : y.toNat ≠ 0 := by
        intro hnat
        exact hyZero (uint256_toNat_eq_zero hnat)
      have hstmt :
          ExecStmt config caller evm (.internalCall "sqrt" args retVar)
            (.ok (resumeAfterInternalCall caller retVar (some [.int 1])) evm) := by
        simpa [sqrtFunctionSmallResultValue, hyNatNe] using
          uniswapSqrtFunctionCallSuccess_le3 hcontract hsmall hargs
      have rdRet :
          RD uniswapV2PairBytecode ee g s0 ret (UInt256.ofNat 1 :: R)
            mem aw rdata acc k' C' := by
        simpa [hyZero] using rdRetRaw
      refine ⟨1, k', C', hstmt, by omega, ?_, rdRet⟩
      norm_num [UInt256.size]
  · have hlarge : 3 < y.toNat := by omega
    obtain ⟨locals', result, k', C', hbody, hresultNonneg, hresultSize, _hresultInput,
      rdRet⟩ :=
      uniswapSqrtFunctionBodyRuntime_gt3 evm rd8046 hlarge hret hov
    have hstmt :
        ExecStmt config caller evm (.internalCall "sqrt" args retVar)
          (.ok (resumeAfterInternalCall caller retVar (some [.int result])) evm) := by
      exact internalCallFunctionReturn
        (cfg := config) (caller := caller) (evm := evm) (calleeEvm := evm)
        (name := "sqrt") (retVar := retVar) (args := args)
        (argVals := [sqrtFunctionYValue y])
        (callee := sqrtFunction) (locals := sqrtFunctionCallStore y)
        (calleeSolm := { contract := contract, locals := locals' })
        (value := some [.int result])
        hargs
        (by simpa [hcontract] using uniswapLookupSqrtFunction)
        (bindParams_sqrtFunction_call y)
        (by simpa [hcontract] using hbody)
    exact ⟨result, k', C', hstmt, hresultNonneg, hresultSize, rdRet⟩

set_option maxHeartbeats 1000000 in
theorem uniswapSqrtFunctionCallRuntimeSuccessIntBoundedInput
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {y ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {caller : Frame} {evm : EVM.State} {args : List Expr} {retVar : Ident}
    (hcontract : caller.contract = contract)
    (hargs : evalExprs? config caller evm args = .ok [sqrtFunctionYValue y])
    (rd8046 : RD uniswapV2PairBytecode ee g s0 ⟨8046⟩ (y :: ret :: R)
      mem aw rdata acc k C)
    (hret : (D_J uniswapV2PairBytecode 0).contains ret = true)
    (hov : R.length + 10 ≤ 1024) :
    ∃ result k' C',
      ExecStmt config caller evm (.internalCall "sqrt" args retVar)
        (.ok (resumeAfterInternalCall caller retVar (some [.int result])) evm) ∧
      0 ≤ result ∧ result.toNat < UInt256.size ∧ result.toNat ≤ y.toNat ∧
      RD uniswapV2PairBytecode ee g s0 ret (UInt256.ofNat result.toNat :: R)
        mem aw rdata acc k' C' := by
  by_cases hsmall : y.toNat ≤ 3
  · obtain ⟨k', C', rdRetRaw⟩ := uniswapSqrtRuntimeSmallReturns rd8046 hsmall hret
      (by omega)
    by_cases hyZero : y = ⟨0⟩
    · have hstmt :
          ExecStmt config caller evm (.internalCall "sqrt" args retVar)
            (.ok (resumeAfterInternalCall caller retVar (some [.int 0])) evm) := by
        simpa [sqrtFunctionSmallResultValue, hyZero] using
          uniswapSqrtFunctionCallSuccess_le3 hcontract hsmall hargs
      have rdRet :
          RD uniswapV2PairBytecode ee g s0 ret (UInt256.ofNat 0 :: R)
            mem aw rdata acc k' C' := by
        simpa [hyZero] using rdRetRaw
      refine ⟨0, k', C', hstmt, by omega, ?_, ?_, rdRet⟩
      · norm_num [UInt256.size]
      · rw [hyZero]
        rfl
    · have hyNatNe : y.toNat ≠ 0 := by
        intro hnat
        exact hyZero (uint256_toNat_eq_zero hnat)
      have hstmt :
          ExecStmt config caller evm (.internalCall "sqrt" args retVar)
            (.ok (resumeAfterInternalCall caller retVar (some [.int 1])) evm) := by
        simpa [sqrtFunctionSmallResultValue, hyNatNe] using
          uniswapSqrtFunctionCallSuccess_le3 hcontract hsmall hargs
      have rdRet :
          RD uniswapV2PairBytecode ee g s0 ret (UInt256.ofNat 1 :: R)
            mem aw rdata acc k' C' := by
        simpa [hyZero] using rdRetRaw
      refine ⟨1, k', C', hstmt, by omega, ?_, ?_, rdRet⟩
      · norm_num [UInt256.size]
      · omega
  · have hlarge : 3 < y.toNat := by omega
    obtain ⟨locals', result, k', C', hbody, hresultNonneg, hresultSize, hresultInput,
      rdRet⟩ :=
      uniswapSqrtFunctionBodyRuntime_gt3 evm rd8046 hlarge hret hov
    have hstmt :
        ExecStmt config caller evm (.internalCall "sqrt" args retVar)
          (.ok (resumeAfterInternalCall caller retVar (some [.int result])) evm) := by
      exact internalCallFunctionReturn
        (cfg := config) (caller := caller) (evm := evm) (calleeEvm := evm)
        (name := "sqrt") (retVar := retVar) (args := args)
        (argVals := [sqrtFunctionYValue y])
        (callee := sqrtFunction) (locals := sqrtFunctionCallStore y)
        (calleeSolm := { contract := contract, locals := locals' })
        (value := some [.int result])
        hargs
        (by simpa [hcontract] using uniswapLookupSqrtFunction)
        (bindParams_sqrtFunction_call y)
        (by simpa [hcontract] using hbody)
    exact ⟨result, k', C', hstmt, hresultNonneg, hresultSize, hresultInput, rdRet⟩

set_option maxHeartbeats 1000000 in
theorem mintFeeSqrtPrefixRuntimeBoundedInputOfTail
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {kLast feeToWord reserve0 reserve1 ret : UInt256} {R : List UInt256}
    (evm : EVM.State) (feeTo : AccountAddress)
    (rd8046 : RD uniswapV2PairBytecode I g
      s0 ⟨8046⟩
      (UInt256.mul reserve0 reserve1 :: ⟨7886⟩ :: ⟨0⟩ :: kLast :: feeToWord :: ⟨1⟩ :: reserve1 ::
        reserve0 :: ret :: R)
      mem aw rdata (cAFee, σFee) k C)
    (hfit : mintFeeReserveProductNat reserve0 reserve1 < UInt256.size)
    (hov : R.length + 32 ≤ 1024) :
    ∃ rootK rootKLast k' C',
      ExecBlock config (mintFeeAfterKLastFrame reserve0 reserve1 feeTo true kLast) evm
        [ .internalCall "sqrt" [u256 (.binary .mul (.var "_reserve0") (.var "_reserve1"))]
            "rootK",
          .internalCall "sqrt" [.var "_kLast"] "rootKLast" ]
        (.ok (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo true kLast rootK rootKLast)
          evm) ∧
      0 ≤ rootK ∧ rootK.toNat < UInt256.size ∧
      rootK.toNat ≤ (UInt256.mul reserve0 reserve1).toNat ∧
      0 ≤ rootKLast ∧ rootKLast.toNat < UInt256.size ∧
      RD uniswapV2PairBytecode I g
        s0 ⟨7899⟩
        (UInt256.ofNat rootKLast.toNat :: ⟨0⟩ :: UInt256.ofNat rootK.toNat :: kLast :: feeToWord ::
        ⟨1⟩ :: reserve1 :: reserve0 :: ret :: R)
        mem aw rdata (cAFee, σFee) k' C' := by
  have hprodWord :
      mintFeeReserveProductWord reserve0 reserve1 = UInt256.mul reserve0 reserve1 :=
    mintFeeReserveProductWord_eq_mul reserve0 reserve1 hfit
  have rdFirst :
      RD uniswapV2PairBytecode I g
        s0 ⟨8046⟩
        (mintFeeReserveProductWord reserve0 reserve1 :: ⟨7886⟩ :: ⟨0⟩ :: kLast :: feeToWord :: ⟨1⟩ ::
        reserve1 :: reserve0 :: ret :: R)
        mem aw rdata (cAFee, σFee) k C := by
    simpa [hprodWord] using rd8046
  obtain ⟨rootK, k1, C1, hrootK, hrootKNonneg, hrootKSize, hrootKInput,
      rd7886⟩ :=
    uniswapSqrtFunctionCallRuntimeSuccessIntBoundedInput
      (caller := mintFeeAfterKLastFrame reserve0 reserve1 feeTo true kLast)
      (evm := evm) (y := mintFeeReserveProductWord reserve0 reserve1) (ret := ⟨7886⟩)
      (R := (⟨0⟩ :: kLast :: feeToWord :: ⟨1⟩ :: reserve1 :: reserve0 :: ret :: R))
      rfl
      (evalExprs_mintFee_reserveProductArg evm reserve0 reserve1 feeTo true kLast hfit)
      rdFirst (by jump_dest)
      (by simp only [List.length_cons]; omega)
  have hrootKBound :
      rootK.toNat ≤ (UInt256.mul reserve0 reserve1).toNat := by
    simpa [hprodWord] using hrootKInput
  have hrootK' :
      ExecStmt config (mintFeeAfterKLastFrame reserve0 reserve1 feeTo true kLast) evm
        (.internalCall "sqrt" [u256 (.binary .mul (.var "_reserve0") (.var "_reserve1"))]
          "rootK")
        (.ok (mintFeeAfterRootKFrame reserve0 reserve1 feeTo true kLast rootK) evm) := by
    simpa [mintFeeAfterRootKFrame, mintFeeAfterRootKStore, resumeAfterInternalCall] using
      hrootK
  obtain ⟨kEntry, CEntry, rdSecondEntry⟩ :
      ∃ kEntry CEntry,
      RD uniswapV2PairBytecode I g
        s0 ⟨8046⟩
        (kLast :: ⟨7899⟩ :: ⟨0⟩ :: UInt256.ofNat rootK.toNat :: kLast :: feeToWord :: ⟨1⟩ ::
        reserve1 :: reserve0 :: ret :: R)
        mem aw rdata (cAFee, σFee) kEntry CEntry := by
    exact ⟨_, _, evm_run rd7886 with [
      jumpdest, swap1, pop, push1 ⟨0⟩, push2 ⟨7899⟩, dup4, push2 ⟨8046⟩,
      jump (by jump_dest)]⟩
  obtain ⟨rootKLast, k2, C2, hrootKLast, hrootKLastNonneg, hrootKLastSize,
      rd7899⟩ :=
    uniswapSqrtFunctionCallRuntimeSuccessIntBounded
      (caller := mintFeeAfterRootKFrame reserve0 reserve1 feeTo true kLast rootK)
      (evm := evm) (y := kLast) (ret := ⟨7899⟩)
      (R := (⟨0⟩ :: UInt256.ofNat rootK.toNat :: kLast :: feeToWord :: ⟨1⟩ :: reserve1 :: reserve0 ::
        ret :: R))
      rfl
      (evalExprs_mintFee_kLastArg evm reserve0 reserve1 feeTo true kLast rootK)
      rdSecondEntry (by jump_dest)
      (by simp only [List.length_cons]; omega)
  have hrootKLast' :
      ExecStmt config (mintFeeAfterRootKFrame reserve0 reserve1 feeTo true kLast rootK) evm
        (.internalCall "sqrt" [.var "_kLast"] "rootKLast")
        (.ok (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo true kLast rootK rootKLast)
          evm) := by
    simpa [mintFeeAfterRootKLastFrame, mintFeeAfterRootKLastStore,
      resumeAfterInternalCall] using hrootKLast
  exact ⟨rootK, rootKLast, k2, C2,
    ExecBlock.consNormal hrootK' (ExecBlock.consNormal hrootKLast' ExecBlock.nil),
    hrootKNonneg, hrootKSize, hrootKBound, hrootKLastNonneg, hrootKLastSize, rd7899⟩


set_option maxHeartbeats 1000000 in
theorem mintFeeSqrtPrefixRuntimeBounded
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {kLast feeToWord amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel :
      UInt256}
    (evm : EVM.State) (feeTo : AccountAddress)
    (rd8046 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨8046⟩
      [UInt256.mul reserve0 reserve1, ⟨7886⟩, ⟨0⟩, kLast, feeToWord, ⟨1⟩,
        reserve1, reserve0, ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0,
        reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k C)
    (hfit : mintFeeReserveProductNat reserve0 reserve1 < UInt256.size) :
    ∃ rootK rootKLast k' C',
      ExecBlock config (mintFeeAfterKLastFrame reserve0 reserve1 feeTo true kLast) evm
        [ .internalCall "sqrt" [u256 (.binary .mul (.var "_reserve0") (.var "_reserve1"))]
            "rootK",
          .internalCall "sqrt" [.var "_kLast"] "rootKLast" ]
        (.ok (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo true kLast rootK rootKLast)
          evm) ∧
      0 ≤ rootK ∧ rootK.toNat < UInt256.size ∧
      0 ≤ rootKLast ∧ rootKLast.toNat < UInt256.size ∧
      RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7899⟩
        [UInt256.ofNat rootKLast.toNat, ⟨0⟩, UInt256.ofNat rootK.toNat, kLast,
          feeToWord, ⟨1⟩, reserve1, reserve0, ⟨3701⟩, ⟨0⟩, amount1, amount0,
          balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
        mem aw rdata (cAFee, σFee) k' C' := by
  obtain ⟨rootK, rootKLast, k', C', hsource, hrootK, hrootKSize, _, hrootKLast,
    hrootKLastSize, rd7899⟩ := mintFeeSqrtPrefixRuntimeBoundedInputOfTail evm feeTo rd8046 hfit
      (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨rootK, rootKLast, k', C', hsource, hrootK, hrootKSize, hrootKLast,
    hrootKLastSize, rd7899⟩

set_option maxHeartbeats 1000000 in
theorem mintFeeSqrtPrefixRuntimeBoundedInput
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {kLast feeToWord amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel :
      UInt256}
    (evm : EVM.State) (feeTo : AccountAddress)
    (rd8046 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨8046⟩
      [UInt256.mul reserve0 reserve1, ⟨7886⟩, ⟨0⟩, kLast, feeToWord, ⟨1⟩,
        reserve1, reserve0, ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0,
        reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k C)
    (hfit : mintFeeReserveProductNat reserve0 reserve1 < UInt256.size) :
    ∃ rootK rootKLast k' C',
      ExecBlock config (mintFeeAfterKLastFrame reserve0 reserve1 feeTo true kLast) evm
        [ .internalCall "sqrt" [u256 (.binary .mul (.var "_reserve0") (.var "_reserve1"))]
            "rootK",
          .internalCall "sqrt" [.var "_kLast"] "rootKLast" ]
        (.ok (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo true kLast rootK rootKLast)
          evm) ∧
      0 ≤ rootK ∧ rootK.toNat < UInt256.size ∧
      rootK.toNat ≤ (UInt256.mul reserve0 reserve1).toNat ∧
      0 ≤ rootKLast ∧ rootKLast.toNat < UInt256.size ∧
      RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7899⟩
        [UInt256.ofNat rootKLast.toNat, ⟨0⟩, UInt256.ofNat rootK.toNat, kLast,
          feeToWord, ⟨1⟩, reserve1, reserve0, ⟨3701⟩, ⟨0⟩, amount1, amount0,
          balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
        mem aw rdata (cAFee, σFee) k' C' := by
  exact mintFeeSqrtPrefixRuntimeBoundedInputOfTail evm feeTo rd8046 hfit
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
theorem mintFeeSqrtPrefixRuntimeProductZero
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {kLast feeToWord amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel :
      UInt256}
    (evm : EVM.State) (feeTo : AccountAddress)
    (rd8046 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨8046⟩
      [UInt256.mul reserve0 reserve1, ⟨7886⟩, ⟨0⟩, kLast, feeToWord, ⟨1⟩,
        reserve1, reserve0, ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0,
        reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k C)
    (hfit : mintFeeReserveProductNat reserve0 reserve1 < UInt256.size)
    (hprodZero : UInt256.mul reserve0 reserve1 = ⟨0⟩) :
    ∃ rootKLast k' C',
      ExecBlock config (mintFeeAfterKLastFrame reserve0 reserve1 feeTo true kLast) evm
        [ .internalCall "sqrt" [u256 (.binary .mul (.var "_reserve0") (.var "_reserve1"))]
            "rootK",
          .internalCall "sqrt" [.var "_kLast"] "rootKLast" ]
        (.ok (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo true kLast (0 : Int)
          rootKLast) evm) ∧
      0 ≤ rootKLast ∧ rootKLast.toNat < UInt256.size ∧
      RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7899⟩
        [UInt256.ofNat rootKLast.toNat, ⟨0⟩, ⟨0⟩, kLast, feeToWord, ⟨1⟩,
          reserve1, reserve0, ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0,
          reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
        mem aw rdata (cAFee, σFee) k' C' := by
  have hprodWord :
      mintFeeReserveProductWord reserve0 reserve1 = UInt256.mul reserve0 reserve1 :=
    mintFeeReserveProductWord_eq_mul reserve0 reserve1 hfit
  have hyZero : mintFeeReserveProductWord reserve0 reserve1 = ⟨0⟩ := by
    rw [hprodWord, hprodZero]
  have hprodSmall : (mintFeeReserveProductWord reserve0 reserve1).toNat ≤ 3 := by
    rw [hyZero]
    native_decide
  have rdFirst :
      RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨8046⟩
        [mintFeeReserveProductWord reserve0 reserve1, ⟨7886⟩, ⟨0⟩, kLast,
          feeToWord, ⟨1⟩, reserve1, reserve0, ⟨3701⟩, ⟨0⟩, amount1, amount0,
          balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
        mem aw rdata (cAFee, σFee) k C := by
    simpa [hprodWord] using rd8046
  have hrootK :
      ExecStmt config (mintFeeAfterKLastFrame reserve0 reserve1 feeTo true kLast) evm
        (.internalCall "sqrt" [u256 (.binary .mul (.var "_reserve0") (.var "_reserve1"))]
          "rootK")
        (.ok (mintFeeAfterRootKFrame reserve0 reserve1 feeTo true kLast (0 : Int)) evm) := by
    have hstmt :=
      uniswapSqrtFunctionCallSuccess_le3
        (caller := mintFeeAfterKLastFrame reserve0 reserve1 feeTo true kLast)
        (evm := evm) (y := mintFeeReserveProductWord reserve0 reserve1)
        (retVar := "rootK")
        rfl hprodSmall
        (evalExprs_mintFee_reserveProductArg evm reserve0 reserve1 feeTo true kLast hfit)
    simpa [mintFeeAfterRootKFrame, mintFeeAfterRootKStore, resumeAfterInternalCall,
      sqrtFunctionSmallResultValue, hyZero] using hstmt
  obtain ⟨k7886, C7886, rd7886Raw⟩ := uniswapSqrtRuntimeSmallReturns rdFirst
    hprodSmall (by jump_dest) (by simp only [List.length_cons, List.length_nil]; omega)
  have rd7886 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7886⟩
      [⟨0⟩, ⟨0⟩, kLast, feeToWord, ⟨1⟩, reserve1, reserve0, ⟨3701⟩, ⟨0⟩,
        amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord,
        ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k7886 C7886 := by
    simpa [hyZero] using rd7886Raw
  obtain ⟨kEntry, CEntry, rdSecondEntry⟩ :
      ∃ kEntry CEntry,
      RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨8046⟩
        [kLast, ⟨7899⟩, ⟨0⟩, ⟨0⟩, kLast, feeToWord, ⟨1⟩, reserve1,
          reserve0, ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0,
          reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
        mem aw rdata (cAFee, σFee) kEntry CEntry := by
    exact ⟨_, _, evm_run rd7886 with [
      jumpdest, swap1, pop, push1 ⟨0⟩, push2 ⟨7899⟩, dup4, push2 ⟨8046⟩,
      jump (by jump_dest)]⟩
  obtain ⟨rootKLast, k2, C2, hrootKLast, hrootKLastNonneg, hrootKLastSize,
      rd7899⟩ :=
    uniswapSqrtFunctionCallRuntimeSuccessIntBounded
      (caller := mintFeeAfterRootKFrame reserve0 reserve1 feeTo true kLast (0 : Int))
      (evm := evm) (y := kLast) (ret := ⟨7899⟩)
      (R := [⟨0⟩, ⟨0⟩, kLast, feeToWord, ⟨1⟩, reserve1, reserve0, ⟨3701⟩,
        ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
        toWord, ⟨861⟩, sel])
      rfl
      (evalExprs_mintFee_kLastArg evm reserve0 reserve1 feeTo true kLast (0 : Int))
      rdSecondEntry (by jump_dest)
      (by simp only [List.length_cons, List.length_nil]; omega)
  have hrootKLast' :
      ExecStmt config (mintFeeAfterRootKFrame reserve0 reserve1 feeTo true kLast (0 : Int))
        evm (.internalCall "sqrt" [.var "_kLast"] "rootKLast")
        (.ok (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo true kLast (0 : Int)
          rootKLast) evm) := by
    simpa [mintFeeAfterRootKLastFrame, mintFeeAfterRootKLastStore,
      resumeAfterInternalCall] using hrootKLast
  exact ⟨rootKLast, k2, C2,
    ExecBlock.consNormal hrootK (ExecBlock.consNormal hrootKLast' ExecBlock.nil),
    hrootKLastNonneg, hrootKLastSize, by simpa using rd7899⟩

end UniswapV2Pair
