import Benchmarks.UniswapV3Pool.BurnSourceSuccess
import Benchmarks.UniswapV3Pool.BurnPositionUpdateTokensOwedBridge
import Benchmarks.UniswapV3Pool.BurnZeroDeltaFinish
import Benchmarks.UniswapV3Pool.BurnZeroDeltaSlowToken0
import Benchmarks.UniswapV3Pool.BurnLowerLiquidityAddDeltaRevert

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.UniswapV3Pool

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolBurnBodyCore {v : PoolImmutables}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsel : (uniswapV3PoolSelBytes 17 == I.calldata.extract 0 4) = true) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdispatch := uniswapV3PoolDispatch_burn (v := v) (cd := I.calldata) hsel
  by_cases hsz100 : 100 ≤ I.calldata.size
  · have hdecode := uniswapV3PoolBurnDecodeOk (v := v) (I := I) hsz100
    have hdecoded := uniswapV3PoolBurnExternalLenOk (v := v) (code := code)
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g) hpatch hcode hwv hsz hsz100 hsize hsel
    obtain ⟨_, _, hrdDecoded⟩ := hdecoded
    obtain ⟨_, _, hrdLower⟩ :=
      uniswapV3PoolBurnDecodedReachTickLower (v := v) (code := code) (ee := I)
        (g := Sat256.ofUInt256 g)
        (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (ret := ⟨621⟩) (R := [solcSelectorWord I]) hpatch (by
          simpa using hrdDecoded) (by simp)
    obtain ⟨_, _, hrdUpper⟩ :=
      uniswapV3PoolBurnTickLowerReachTickUpper (v := v) (code := code) (ee := I)
        (g := Sat256.ofUInt256 g)
        (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (ret := ⟨621⟩) (R := [solcSelectorWord I]) hpatch hrdLower (by simp)
    obtain ⟨_, _, hrdModifyPosition⟩ :=
      uniswapV3PoolBurnTickUpperReachModifyPosition (v := v) (code := code) (ee := I)
        (g := Sat256.ofUInt256 g)
        (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (ret := ⟨621⟩) (R := [solcSelectorWord I]) hpatch hrdUpper (by simp)
    by_cases hunlocked : burnUnlockedByte σ_evm I ≠ ⟨0⟩
    · obtain ⟨_, _, hrdAfterLock⟩ :=
        uniswapV3PoolBurnLockEnterOk (v := v) (code := code) (ee := I)
          (g := Sat256.ofUInt256 g)
          (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
          (amount := burnAmountCleanWord I) (upper := burnTickUpperCleanWord I)
          (lower := burnTickLowerCleanWord I) (ret := ⟨621⟩)
          (R := [solcSelectorWord I]) (mem := solcFreePtrMem)
          (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
          (cA := cA) (σ := σ_evm) hpatch hrdModifyPosition _hperm hunlocked
          (by simp only [List.length_cons, List.length_nil]; omega)
      have hunlockedSolm : burnUnlockedByte σ_solm I ≠ ⟨0⟩ := by
        rw [burnUnlockedByte_transport (σ_evm := σ_evm) (σ_solm := σ_solm)
          hAccounts]
        exact hunlocked
      have hsourceLock := uniswapV3PoolBurnSourceLockPrefixExact (v := v)
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hwv hunlockedSolm
      have hlockedWord :
          burnLockedSlotWord σ_solm I = burnLockedSlotWord σ_evm I :=
        burnLockedSlotWord_transport (σ_evm := σ_evm) (σ_solm := σ_solm)
          hAccounts
      let σLockedEvm := sstoreAccountMap I.codeOwner σ_evm ⟨0⟩ (burnLockedSlotWord σ_evm I)
      let σLockedSolm := sstoreAccountMap I.codeOwner σ_solm ⟨0⟩ (burnLockedSlotWord σ_solm I)
      have hAccountsAfterLock :
          accountMapEquiv σLockedEvm σLockedSolm := by
        dsimp [σLockedEvm, σLockedSolm]
        rw [hlockedWord]
        exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨0⟩
          (burnLockedSlotWord σ_evm I) hAccounts
      obtain ⟨_, _, hrdOwnerFrame⟩ :=
        uniswapV3PoolBurnAfterLockWriteOwner (v := v) (code := code) (ee := I)
          (g := Sat256.ofUInt256 g)
          (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
          (amount := burnAmountCleanWord I) (upper := burnTickUpperCleanWord I)
          (lower := burnTickLowerCleanWord I) (ret := ⟨621⟩)
          (R := [solcSelectorWord I]) (rdata := ByteArray.empty) (cA := cA)
          (σ := σLockedEvm)
          hpatch hrdAfterLock
          (by simp only [List.length_cons, List.length_nil]; omega)
      obtain ⟨_, _, hrdTickFrame⟩ :=
        uniswapV3PoolBurnAfterLockWriteTicks (v := v) (code := code) (ee := I)
          (g := Sat256.ofUInt256 g)
          (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
          (ret := ⟨621⟩) (R := [solcSelectorWord I]) (rdata := ByteArray.empty)
          (cA := cA)
          (σ := σLockedEvm)
          hpatch hrdOwnerFrame
          (by simp only [List.length_cons, List.length_nil]; omega)
      obtain ⟨_, _, hrdLiquidityDeltaPrep⟩ :=
        uniswapV3PoolBurnPrepareLiquidityDelta (v := v) (code := code) (ee := I)
          (g := Sat256.ofUInt256 g)
          (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
          (ret := ⟨621⟩) (R := [solcSelectorWord I]) (rdata := ByteArray.empty)
          (cA := cA)
          (σ := σLockedEvm)
          hpatch hrdTickFrame
          (by simp only [List.length_cons, List.length_nil]; omega)
      by_cases hcanon :
          UInt256.signextend ⟨15⟩ (burnAmountCleanWord I) = burnAmountCleanWord I
      · obtain ⟨_, _, hrdLiquidityDeltaClean⟩ :=
          uniswapV3PoolBurnLiquidityDeltaInt128Ok (v := v) (code := code) (ee := I)
            (g := Sat256.ofUInt256 g)
            (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
            (ret := ⟨621⟩) (R := [solcSelectorWord I]) (rdata := ByteArray.empty)
            (cA := cA)
            (σ := σLockedEvm)
            hpatch hrdLiquidityDeltaPrep hcanon
            (by simp only [List.length_cons, List.length_nil]; omega)
        have hsourceLiquidityDelta := uniswapV3PoolBurnSourceThroughLiquidityDelta (v := v)
          (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A)
          (I := I) (g := Sat256.ofUInt256 g) hwv hunlockedSolm hcanon
        obtain ⟨_, _, hrdLiquidityDeltaWritten⟩ :=
          uniswapV3PoolBurnWriteLiquidityDelta (v := v) (code := code) (ee := I)
            (g := Sat256.ofUInt256 g)
            (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
            (ret := ⟨621⟩) (R := [solcSelectorWord I]) (rdata := ByteArray.empty)
            (cA := cA)
            (σ := σLockedEvm)
            hpatch hrdLiquidityDeltaClean
            (by simp only [List.length_cons, List.length_nil]; omega)
        have hrdNoDelegateOfGuard :
            uniswapV3PoolNoDelegateCallGuard v I ≠ ⟨0⟩ →
              ∃ k' C', RD code I (Sat256.ofUInt256 g)
                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨16246⟩
                (⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
                  ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
                  burnAmountCleanWord I :: burnTickUpperCleanWord I ::
                  burnTickLowerCleanWord I :: ⟨621⟩ :: [solcSelectorWord I])
                (burnModifyPositionMem4 I) (UInt256.ofNat 8) ByteArray.empty
                (cA,
                  σLockedEvm) k' C' := by
          intro hnoDelegate
          exact uniswapV3PoolBurnNoDelegateCallOk (v := v) (code := code) (ee := I)
            (g := Sat256.ofUInt256 g)
            (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
            (ret := ⟨621⟩) (R := [solcSelectorWord I]) (rdata := ByteArray.empty)
            (cA := cA)
            (σ := σLockedEvm)
            hpatch hrdLiquidityDeltaWritten hnoDelegate
            (by simp only [List.length_cons, List.length_nil]; omega)
        by_cases hnoDelegate : uniswapV3PoolNoDelegateCallGuard v I ≠ ⟨0⟩
        · obtain ⟨_, _, hrdNoDelegate⟩ := hrdNoDelegateOfGuard hnoDelegate
          obtain ⟨_, _, hrdCheckTicks⟩ :=
            uniswapV3PoolBurnEnterCheckTicks (v := v) (code := code) (ee := I)
              (g := Sat256.ofUInt256 g)
              (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
              (ret := ⟨621⟩) (R := [solcSelectorWord I]) (rdata := ByteArray.empty)
              (cA := cA)
              (σ := σLockedEvm)
              hpatch hrdNoDelegate
              (by simp only [List.length_cons, List.length_nil]; omega)
          have hsourceNoDelegate := uniswapV3PoolModifyPositionSourceNoDelegateOk (v := v)
            (cA := cA) (gh := gh) (bl := bl)
            (σ := σLockedSolm)
            (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hnoDelegate
          obtain ⟨_, _, hrdCheckTicksWords⟩ :
              ∃ k' C', RD code I (Sat256.ofUInt256 g)
                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨17313⟩
                (UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I) ::
                  UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I) :: ⟨16264⟩ ::
                  ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
                  ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
                  burnAmountCleanWord I :: burnTickUpperCleanWord I ::
                  burnTickLowerCleanWord I :: ⟨621⟩ :: [solcSelectorWord I])
                (burnModifyPositionMem4 I) (UInt256.ofNat 8) ByteArray.empty
                (cA,
                  σLockedEvm) k' C' := by
            exact ⟨_, _, by
              simpa [burnModifyPositionTickUpperLoad_eq I,
                burnModifyPositionTickLowerLoad_eq I] using hrdCheckTicks⟩
          have hrdCheckTicksLtOfGuard :
              UInt256.slt
                  (UInt256.signextend ⟨2⟩ (UInt256.signextend ⟨2⟩
                    (burnTickLowerCleanWord I)))
                  (UInt256.signextend ⟨2⟩ (UInt256.signextend ⟨2⟩
                    (burnTickUpperCleanWord I))) ≠ ⟨0⟩ →
                ∃ k' C', RD code I (Sat256.ofUInt256 g)
                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨17377⟩
                  (UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I) ::
                    UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I) :: ⟨16264⟩ ::
                    ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
                    ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
                    burnAmountCleanWord I :: burnTickUpperCleanWord I ::
                    burnTickLowerCleanWord I :: ⟨621⟩ :: [solcSelectorWord I])
                  (burnModifyPositionMem4 I) (UInt256.ofNat 8) ByteArray.empty
                  (cA,
                    σLockedEvm) k' C' := by
            intro hlt
            exact uniswapV3PoolBurnCheckTicksLtOk (v := v) (code := code) (ee := I)
              (g := Sat256.ofUInt256 g)
              (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
              (ret := ⟨16264⟩)
              (R := ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
                ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
                burnAmountCleanWord I :: burnTickUpperCleanWord I ::
                burnTickLowerCleanWord I :: ⟨621⟩ :: [solcSelectorWord I])
              (mem := burnModifyPositionMem4 I) (aw := UInt256.ofNat 8)
              (rdata := ByteArray.empty) (cA := cA)
              (σ := σLockedEvm)
              hpatch hrdCheckTicksWords hlt
              (by simp only [List.length_cons, List.length_nil]; omega)
          by_cases htickLt :
              tickSpacingSint24Value (burnTickLowerWord I) <
                tickSpacingSint24Value (burnTickUpperWord I)
          · have hltGuard := burnTickLtSlt_ne_zero I htickLt
            obtain ⟨_, _, hrdAfterTickLt⟩ := hrdCheckTicksLtOfGuard hltGuard
            by_cases hLowerMin :
                tickSpacingSint24Value (burnTickLowerWord I) < (-887272 : Int)
            · have hltMinGuard := burnTickLowerMinSlt_ne_zero I hLowerMin
              have hrd := uniswapV3PoolBurnCheckTicksLowerRevert (v := v) (code := code)
                (ee := I) (g := Sat256.ofUInt256 g)
                (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                (ret := ⟨16264⟩)
                (R := ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
                  ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
                  burnAmountCleanWord I :: burnTickUpperCleanWord I ::
                  burnTickLowerCleanWord I :: ⟨621⟩ :: [solcSelectorWord I])
                (mem := burnModifyPositionMem4 I) (aw := UInt256.ofNat 8)
                (rdata := ByteArray.empty) (cA := cA)
                (σ := σLockedEvm)
                hpatch hrdAfterTickLt hltMinGuard rfl rfl
                (by simp only [List.length_cons, List.length_nil]; omega)
              have hbody := uniswapV3PoolBurnSourceLowerReverts (v := v)
                (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                (A := A) (I := I) (g := Sat256.ofUInt256 g) hwv hunlockedSolm hcanon
                hnoDelegate htickLt hLowerMin
              exact hrd.reEquivExecutionRevert hcode hdispatch hdecode hbody
            · have hgeMinGuard := burnTickLowerMinSlt_eq_zero I hLowerMin
              obtain ⟨_, _, hrdAfterLower⟩ :=
                uniswapV3PoolBurnCheckTicksLowerOk (v := v) (code := code) (ee := I)
                  (g := Sat256.ofUInt256 g)
                  (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                  (ret := ⟨16264⟩)
                  (R := ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
                    ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
                    burnAmountCleanWord I :: burnTickUpperCleanWord I ::
                    burnTickLowerCleanWord I :: ⟨621⟩ :: [solcSelectorWord I])
                  (mem := burnModifyPositionMem4 I) (aw := UInt256.ofNat 8)
                  (rdata := ByteArray.empty) (cA := cA)
                  (σ := σLockedEvm)
                  hpatch hrdAfterTickLt hgeMinGuard
                  (by simp only [List.length_cons, List.length_nil]; omega)
              have hsourceLower := uniswapV3PoolModifyPositionSourceThroughLowerGe (v := v)
                (cA := cA) (gh := gh) (bl := bl)
                (σ := σLockedSolm)
                (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
                hnoDelegate htickLt hLowerMin
              by_cases hUpperMax :
                  (887272 : Int) < tickSpacingSint24Value (burnTickUpperWord I)
              · have hgtMaxGuard := burnTickUpperMaxSgt_ne_zero I hUpperMax
                have hrd := uniswapV3PoolBurnCheckTicksUpperRevert (v := v) (code := code)
                  (ee := I) (g := Sat256.ofUInt256 g)
                  (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                  (ret := ⟨16264⟩)
                  (R := ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
                    ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
                    burnAmountCleanWord I :: burnTickUpperCleanWord I ::
                    burnTickLowerCleanWord I :: ⟨621⟩ :: [solcSelectorWord I])
                  (mem := burnModifyPositionMem4 I) (aw := UInt256.ofNat 8)
                  (rdata := ByteArray.empty) (cA := cA)
                  (σ := σLockedEvm)
                  hpatch hrdAfterLower hgtMaxGuard rfl rfl
                  (by simp only [List.length_cons, List.length_nil]; omega)
                have hbody := uniswapV3PoolBurnSourceUpperReverts (v := v)
                  (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                  (A := A) (I := I) (g := Sat256.ofUInt256 g) hwv hunlockedSolm hcanon
                  hnoDelegate htickLt hLowerMin hUpperMax
                exact hrd.reEquivExecutionRevert hcode hdispatch hdecode hbody
              · have hleMaxGuard := burnTickUpperMaxSgt_eq_zero I hUpperMax
                obtain ⟨_, _, hrdAfterUpper⟩ :=
                  uniswapV3PoolBurnCheckTicksUpperOk (v := v) (code := code) (ee := I)
                    (g := Sat256.ofUInt256 g)
                    (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                    (ret := ⟨16264⟩)
                    (R := ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
                      ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
                      burnAmountCleanWord I :: burnTickUpperCleanWord I ::
                      burnTickLowerCleanWord I :: ⟨621⟩ :: [solcSelectorWord I])
                    (mem := burnModifyPositionMem4 I) (aw := UInt256.ofNat 8)
                    (rdata := ByteArray.empty) (cA := cA)
                    (σ := σLockedEvm)
                    hpatch hrdAfterLower hleMaxGuard
                    (by simp only [List.length_cons, List.length_nil]; omega)
                have hsourcePositionKey :=
                  uniswapV3PoolModifyPositionSourceThroughPositionKey (v := v)
                  (cA := cA) (gh := gh) (bl := bl)
                  (σ := σLockedSolm)
                  (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
                  hnoDelegate htickLt hLowerMin hUpperMax
                have hsourceFeeGlobals :=
                  uniswapV3PoolModifyPositionSourceThroughFeeGrowthGlobals (v := v)
                  (cA := cA) (gh := gh) (bl := bl)
                  (σ := σLockedSolm)
                  (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
                  hnoDelegate htickLt hLowerMin hUpperMax
                obtain ⟨_, _, hrdAfterCheckTicks⟩ :=
                  uniswapV3PoolBurnCheckTicksReturn (v := v) (code := code) (ee := I)
                    (g := Sat256.ofUInt256 g)
                    (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                    (ret := ⟨16264⟩)
                    (R := ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
                      ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
                      burnAmountCleanWord I :: burnTickUpperCleanWord I ::
                      burnTickLowerCleanWord I :: ⟨621⟩ :: [solcSelectorWord I])
                    (mem := burnModifyPositionMem4 I) (aw := UInt256.ofNat 8)
                    (rdata := ByteArray.empty)
                    (acc := (cA, σLockedEvm))
                    hpatch hrdAfterUpper (uniswapV3PoolJumpDestPatched16264 hpatch)
                    (by simp only [List.length_cons, List.length_nil]; omega)
                obtain ⟨_, _, hrdSlot0Frame⟩ :=
                  uniswapV3PoolBurnAfterCheckTicksSlot0Frame (v := v) (code := code)
                    (ee := I) (g := Sat256.ofUInt256 g)
                    (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                    (ret := ⟨621⟩) (R := [solcSelectorWord I])
                    (rdata := ByteArray.empty) (cA := cA)
                    (σ := σLockedEvm)
                    hpatch hrdAfterCheckTicks
                    (by simp only [List.length_cons, List.length_nil]; omega)
                obtain ⟨_, _, hrdPositionKeyEntry⟩ :=
                  uniswapV3PoolBurnAfterCheckTicksEnterPositionKey (v := v) (code := code)
                    (ee := I) (g := Sat256.ofUInt256 g)
                    (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                    (ret := ⟨621⟩) (R := [solcSelectorWord I])
                    (rdata := ByteArray.empty) (cA := cA)
                    (σ := σLockedEvm)
                    hpatch hrdSlot0Frame
                    (by simp only [List.length_cons, List.length_nil]; omega)
                obtain ⟨_, _, hrdPositionKeyRoutine⟩ :=
                  uniswapV3PoolBurnAfterCheckTicksCallPositionKeyRoutine (v := v)
                    (code := code) (ee := I) (g := Sat256.ofUInt256 g)
                    (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                    (ret := ⟨621⟩) (R := [solcSelectorWord I])
                    (rdata := ByteArray.empty) (cA := cA)
                    (σ := σLockedEvm)
                    hpatch hrdPositionKeyEntry
                    (by simp only [List.length_cons, List.length_nil]; omega)
                obtain ⟨_, _, hrdPositionBaseSlot⟩ :=
                  uniswapV3PoolBurnAfterCheckTicksPositionKeyRoutine (v := v)
                    (code := code) (ee := I) (g := Sat256.ofUInt256 g)
                    (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                    (ret := ⟨621⟩) (R := [solcSelectorWord I])
                    (rdata := ByteArray.empty) (cA := cA)
                    (σ := σLockedEvm)
                    hpatch hrdPositionKeyRoutine
                    (by simp only [List.length_cons, List.length_nil]; omega)
                obtain ⟨_, _, hrdFeeGlobalsBranchTest⟩ :=
                  uniswapV3PoolBurnAfterCheckTicksFeeGlobalsBranchTest (v := v)
                    (code := code) (ee := I) (g := Sat256.ofUInt256 g)
                    (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                    (ret := ⟨621⟩) (R := [solcSelectorWord I])
                    (rdata := ByteArray.empty) (cA := cA)
                    (σ := σLockedEvm)
                    hpatch hrdPositionBaseSlot
                    (by simp only [List.length_cons, List.length_nil]; omega)
                have hsourceZeroBranch := fun hzero =>
                  uniswapV3PoolModifyPositionSourceThroughLiquidityDeltaZeroSkip
                    (v := v) (cA := cA) (gh := gh) (bl := bl)
                    (σ := σLockedSolm)
                    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
                    hnoDelegate htickLt hLowerMin hUpperMax hzero
                have hrdZeroBranch := fun hzero =>
                  uniswapV3PoolBurnAfterFeeGlobalsLiquidityDeltaZeroJump (v := v)
                    (code := code) (ee := I) (g := Sat256.ofUInt256 g)
                    (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                    (ret := ⟨621⟩) (R := [solcSelectorWord I])
                    (rdata := ByteArray.empty) (cA := cA)
                    (σ := σLockedEvm)
                    hpatch (burnLiquidityDeltaZeroJumpCond I hzero)
                    hrdFeeGlobalsBranchTest
                    (by simp only [List.length_cons, List.length_nil]; omega)
                have hrdFeeGrowthInsideEntry := fun hzero =>
                  uniswapV3PoolBurnAfterFeeGlobalsZeroToFeeGrowthInside (v := v)
                    (code := code) (ee := I) (g := Sat256.ofUInt256 g)
                    (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                    (ret := ⟨621⟩) (R := [solcSelectorWord I])
                    (rdata := ByteArray.empty) (cA := cA)
                    (σ := σLockedEvm)
                    hpatch hzero hrdFeeGlobalsBranchTest
                    (by simp only [List.length_cons, List.length_nil]; omega)
                have hrdFeeGrowthInsideJoinOfZero :
                    burnAmountCleanWord I = ⟨0⟩ →
                      ∃ k' C' above1 above0 below1 below0,
                        RD code I (Sat256.ofUInt256 g)
                          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                          ⟨21529⟩
                          (above1 :: above0 :: below1 :: below0 ::
                          burnTickUpperFeeGrowthBaseSlot I ::
                          burnTickLowerFeeGrowthBaseSlot I ::
                          ⟨0⟩ :: ⟨0⟩ ::
                          solcSlotWord
                            (σLockedEvm) I ⟨2⟩ ::
                          solcSlotWord
                            (σLockedEvm) I ⟨1⟩ ::
                          slot0TickReturnWord
                            (σLockedEvm) I ::
                          UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I) ::
                          UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I) ::
                          ⟨5⟩ :: ⟨19510⟩ ::
                          ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
                          solcSlotWord
                            (σLockedEvm) I ⟨2⟩ ::
                          solcSlotWord
                            (σLockedEvm) I ⟨1⟩ ::
                          burnPositionBaseSlotWord
                            (σLockedEvm) I ::
                          slot0TickReturnWord
                            (σLockedEvm) I ::
                          UInt256.signextend ⟨15⟩
                            (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)) ::
                          UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I) ::
                          UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I) ::
                          UInt256.ofNat I.source.val :: ⟨16428⟩ :: ⟨256⟩ ::
                          ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
                          ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
                          burnAmountCleanWord I :: burnTickUpperCleanWord I ::
                          burnTickLowerCleanWord I :: ⟨621⟩ :: [solcSelectorWord I])
                          (burnTickUpperFeeGrowthMem
                          (σLockedEvm) I)
                        (UInt256.ofNat 18) ByteArray.empty
                        (cA,
                          σLockedEvm) k' C' := by
                  intro hzero
                  obtain ⟨_, _, hrdEntry⟩ := hrdFeeGrowthInsideEntry hzero
                  by_cases hCurrentBelow :
                      tickSpacingSint24Value
                          (slot0TickRawWord
                          (σLockedEvm) I) <
                        tickSpacingSint24Value (burnTickLowerWord I)
                  · obtain ⟨_, _, hrdLower⟩ :=
                      uniswapV3PoolBurnFeeGrowthInsideLowerBelowToUpperJoin
                        (v := v) (code := code) (ee := I)
                        (g := Sat256.ofUInt256 g)
                        (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                        (ret := ⟨621⟩) (R := [solcSelectorWord I])
                        (rdata := ByteArray.empty) (cA := cA)
                        (σ := σLockedEvm)
                        hpatch hCurrentBelow hrdEntry
                        (by simp only [List.length_cons, List.length_nil]; omega)
                    have hCurrentUpper :
                        tickSpacingSint24Value
                          (slot0TickRawWord
                            (σLockedEvm) I) <
                          tickSpacingSint24Value (burnTickUpperWord I) :=
                      lt_trans hCurrentBelow htickLt
                    obtain ⟨_, _, hrdUpper⟩ :=
                      uniswapV3PoolBurnFeeGrowthInsideUpperInsideFromJoin
                        (v := v) (code := code) (ee := I)
                        (g := Sat256.ofUInt256 g)
                        (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                        (ret := ⟨621⟩) (R := [solcSelectorWord I])
                        (rdata := ByteArray.empty) (cA := cA)
                        (σ := σLockedEvm)
                        hpatch hCurrentUpper hrdLower
                        (by simp only [List.length_cons, List.length_nil]; omega)
                    exact ⟨_, _, _, _, _, _, hrdUpper⟩
                  · obtain ⟨_, _, hrdLower⟩ :=
                      uniswapV3PoolBurnFeeGrowthInsideLowerNotBelowToUpperJoin
                        (v := v) (code := code) (ee := I)
                        (g := Sat256.ofUInt256 g)
                        (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                        (ret := ⟨621⟩) (R := [solcSelectorWord I])
                        (rdata := ByteArray.empty) (cA := cA)
                        (σ := σLockedEvm)
                        hpatch hCurrentBelow hrdEntry
                        (by simp only [List.length_cons, List.length_nil]; omega)
                    by_cases hCurrentUpper :
                        tickSpacingSint24Value
                          (slot0TickRawWord
                            (σLockedEvm) I) <
                          tickSpacingSint24Value (burnTickUpperWord I)
                    · obtain ⟨_, _, hrdUpper⟩ :=
                        uniswapV3PoolBurnFeeGrowthInsideUpperInsideFromJoin
                          (v := v) (code := code) (ee := I)
                          (g := Sat256.ofUInt256 g)
                          (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                          (ret := ⟨621⟩) (R := [solcSelectorWord I])
                          (rdata := ByteArray.empty) (cA := cA)
                          (σ := σLockedEvm)
                          hpatch hCurrentUpper hrdLower
                          (by simp only [List.length_cons, List.length_nil]; omega)
                      exact ⟨_, _, _, _, _, _, hrdUpper⟩
                    · obtain ⟨_, _, hrdUpper⟩ :=
                        uniswapV3PoolBurnFeeGrowthInsideUpperNotInsideFromJoin
                          (v := v) (code := code) (ee := I)
                          (g := Sat256.ofUInt256 g)
                          (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                          (ret := ⟨621⟩) (R := [solcSelectorWord I])
                          (rdata := ByteArray.empty) (cA := cA)
                          (σ := σLockedEvm)
                          hpatch hCurrentUpper hrdLower
                          (by simp only [List.length_cons, List.length_nil]; omega)
                      exact ⟨_, _, _, _, _, _, hrdUpper⟩
                have hrdFeeGrowthInsideReturnOfZero :
                    burnAmountCleanWord I = ⟨0⟩ →
                      ∃ k' C' feeGrowthInside1 feeGrowthInside0,
                        RD code I (Sat256.ofUInt256 g)
                          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                          ⟨19510⟩
                          (feeGrowthInside1 :: feeGrowthInside0 ::
                          ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
                          solcSlotWord
                            (σLockedEvm) I ⟨2⟩ ::
                          solcSlotWord
                            (σLockedEvm) I ⟨1⟩ ::
                          burnPositionBaseSlotWord
                            (σLockedEvm) I ::
                          slot0TickReturnWord
                            (σLockedEvm) I ::
                          UInt256.signextend ⟨15⟩
                            (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)) ::
                          UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I) ::
                          UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I) ::
                          UInt256.ofNat I.source.val :: ⟨16428⟩ :: ⟨256⟩ ::
                          ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
                          ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
                          burnAmountCleanWord I :: burnTickUpperCleanWord I ::
                          burnTickLowerCleanWord I :: ⟨621⟩ :: [solcSelectorWord I])
                          (burnTickUpperFeeGrowthMem
                          (σLockedEvm) I)
                          (UInt256.ofNat 18) ByteArray.empty
                          (cA,
                          σLockedEvm) k' C' := by
                  intro hzero
                  obtain ⟨_, _, hrdEntry⟩ := hrdFeeGrowthInsideEntry hzero
                  obtain ⟨_, _, hrdReturn⟩ :=
                    uniswapV3PoolBurnFeeGrowthInsideEntryReturnConcrete (v := v) (code := code)
                      (ee := I) (g := Sat256.ofUInt256 g)
                      (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                      (ret := ⟨621⟩) (R := [solcSelectorWord I])
                      (rdata := ByteArray.empty) (cA := cA)
                      (σ := σLockedEvm)
                      hpatch htickLt hrdEntry
                      (by simp only [List.length_cons, List.length_nil]; omega)
                  exact ⟨_, _, _, _, hrdReturn⟩
                have hrdPositionUpdateEntryOfZero :
                    burnAmountCleanWord I = ⟨0⟩ →
                      ∃ k' C' feeGrowthInside1 feeGrowthInside0,
                        RD code I (Sat256.ofUInt256 g)
                          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                          ⟨21559⟩
                          (feeGrowthInside1 :: feeGrowthInside0 ::
                            UInt256.signextend ⟨15⟩
                              (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)) ::
                            burnPositionBaseSlotWord
                              (σLockedEvm) I ::
                            ⟨19527⟩ ::
                            feeGrowthInside1 :: feeGrowthInside0 ::
                            ⟨0⟩ :: ⟨0⟩ ::
                            solcSlotWord
                              (σLockedEvm) I ⟨2⟩ ::
                            solcSlotWord
                              (σLockedEvm) I ⟨1⟩ ::
                            burnPositionBaseSlotWord
                              (σLockedEvm) I ::
                            slot0TickReturnWord
                              (σLockedEvm) I ::
                            UInt256.signextend ⟨15⟩
                              (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)) ::
                            UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I) ::
                            UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I) ::
                            UInt256.ofNat I.source.val :: ⟨16428⟩ :: ⟨256⟩ ::
                            ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
                            ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
                            burnAmountCleanWord I :: burnTickUpperCleanWord I ::
                            burnTickLowerCleanWord I :: ⟨621⟩ :: [solcSelectorWord I])
                          (burnTickUpperFeeGrowthMem
                            (σLockedEvm) I)
                          (UInt256.ofNat 18) ByteArray.empty
                          (cA,
                            σLockedEvm) k' C' := by
                    intro hzero
                    obtain ⟨_, _, feeGrowthInside1, feeGrowthInside0, hrdReturn⟩ :=
                      hrdFeeGrowthInsideReturnOfZero hzero
                    obtain ⟨_, _, hrdEntry⟩ :=
                      uniswapV3PoolBurnFeeGrowthInsideEnterPositionUpdate
                        (v := v) (code := code) (ee := I)
                        (g := Sat256.ofUInt256 g)
                        (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                        (inside1 := feeGrowthInside1) (inside0 := feeGrowthInside0)
                        (z0 := ⟨0⟩) (z1 := ⟨0⟩) (z2 := ⟨0⟩) (z3 := ⟨0⟩)
                        (fee1 := solcSlotWord
                          (σLockedEvm) I ⟨2⟩)
                        (fee0 := solcSlotWord
                          (σLockedEvm) I ⟨1⟩)
                        (posBase := burnPositionBaseSlotWord
                          (σLockedEvm) I)
                        (tick := slot0TickReturnWord
                          (σLockedEvm) I)
                        (delta := UInt256.signextend ⟨15⟩
                          (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)))
                        (upper := UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I))
                        (lower := UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I))
                        (owner := UInt256.ofNat I.source.val) (ret := ⟨16428⟩)
                        (free := ⟨256⟩)
                        (R := ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
                          ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
                          burnAmountCleanWord I :: burnTickUpperCleanWord I ::
                          burnTickLowerCleanWord I :: ⟨621⟩ :: [solcSelectorWord I])
                        hpatch hrdReturn
                        (by simp only [List.length_cons, List.length_nil]; omega)
                    exact ⟨_, _, _, _, hrdEntry⟩
                have hrdPositionUpdateSlot0OfZero :
                    burnAmountCleanWord I = ⟨0⟩ →
                      ∃ k' C' feeGrowthInside1 feeGrowthInside0,
                        RD code I (Sat256.ofUInt256 g)
                          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                          ⟨21572⟩
                          (solcSlotWord
                              (σLockedEvm) I
                              (burnPositionBaseSlotWord
                                (σLockedEvm) I) ::
                            burnPositionKeyNewFreePtrWord :: ⟨64⟩ ::
                            feeGrowthInside1 :: feeGrowthInside0 ::
                            UInt256.signextend ⟨15⟩
                              (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)) ::
                            burnPositionBaseSlotWord
                              (σLockedEvm) I ::
                            ⟨19527⟩ ::
                            feeGrowthInside1 :: feeGrowthInside0 ::
                            ⟨0⟩ :: ⟨0⟩ ::
                            solcSlotWord
                              (σLockedEvm) I ⟨2⟩ ::
                            solcSlotWord
                              (σLockedEvm) I ⟨1⟩ ::
                            burnPositionBaseSlotWord
                              (σLockedEvm) I ::
                            slot0TickReturnWord
                              (σLockedEvm) I ::
                            UInt256.signextend ⟨15⟩
                              (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)) ::
                            UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I) ::
                            UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I) ::
                            UInt256.ofNat I.source.val :: ⟨16428⟩ :: ⟨256⟩ ::
                            ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
                            ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
                            burnAmountCleanWord I :: burnTickUpperCleanWord I ::
                            burnTickLowerCleanWord I :: ⟨621⟩ :: [solcSelectorWord I])
                          (burnPositionUpdateMem0
                            (σLockedEvm) I)
                          (UInt256.ofNat 18) ByteArray.empty
                          (cA,
                            σLockedEvm) k' C' := by
                  intro hzero
                  obtain ⟨_, _, feeGrowthInside1, feeGrowthInside0, hrdEntry⟩ :=
                    hrdPositionUpdateEntryOfZero hzero
                  have hslot0Result :=
                    (uniswapV3PoolBurnPositionUpdateLoadSlot0
                      (v := v) (code := code) (ee := I)
                      (g := Sat256.ofUInt256 g)
                      (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                      (inside1 := feeGrowthInside1) (inside0 := feeGrowthInside0)
                      (delta := UInt256.signextend ⟨15⟩
                        (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)))
                      (posBase := burnPositionBaseSlotWord
                        (σLockedEvm) I)
                      (retPos := ⟨19527⟩)
                      (inside1' := feeGrowthInside1) (inside0' := feeGrowthInside0)
                      (z2 := ⟨0⟩) (z3 := ⟨0⟩)
                      (fee1 := solcSlotWord
                        (σLockedEvm) I ⟨2⟩)
                      (fee0 := solcSlotWord
                        (σLockedEvm) I ⟨1⟩)
                      (posBase' := burnPositionBaseSlotWord
                        (σLockedEvm) I)
                      (tick := slot0TickReturnWord
                        (σLockedEvm) I)
                      (delta' := UInt256.signextend ⟨15⟩
                        (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)))
                      (upper := UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I))
                      (lower := UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I))
                      (owner := UInt256.ofNat I.source.val) (ret := ⟨16428⟩)
                      (free := ⟨256⟩)
                      (R := ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
                        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
                        burnAmountCleanWord I :: burnTickUpperCleanWord I ::
                        burnTickLowerCleanWord I :: ⟨621⟩ :: [solcSelectorWord I])
                      hpatch hrdEntry
                      (by simp only [List.length_cons, List.length_nil]; omega))
                  obtain ⟨_, _, hrdSlot0⟩ := hslot0Result
                  exact ⟨_, _, _, _, hrdSlot0⟩
                have hrdPositionUpdatePackedSlot0OfZero :
                    burnAmountCleanWord I = ⟨0⟩ →
                      ∃ k' C' feeGrowthInside1 feeGrowthInside0,
                        RD code I (Sat256.ofUInt256 g)
                          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                          ⟨21585⟩
                          (burnPositionUpdateSlot0Mask ::
                            burnPositionKeyNewFreePtrWord :: ⟨64⟩ ::
                            feeGrowthInside1 :: feeGrowthInside0 ::
                            UInt256.signextend ⟨15⟩
                              (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)) ::
                            burnPositionBaseSlotWord
                              (σLockedEvm) I ::
                            ⟨19527⟩ ::
                            feeGrowthInside1 :: feeGrowthInside0 ::
                            ⟨0⟩ :: ⟨0⟩ ::
                            solcSlotWord
                              (σLockedEvm) I ⟨2⟩ ::
                            solcSlotWord
                              (σLockedEvm) I ⟨1⟩ ::
                            burnPositionBaseSlotWord
                              (σLockedEvm) I ::
                            slot0TickReturnWord
                              (σLockedEvm) I ::
                            UInt256.signextend ⟨15⟩
                              (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)) ::
                            UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I) ::
                            UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I) ::
                            UInt256.ofNat I.source.val :: ⟨16428⟩ :: ⟨256⟩ ::
                            ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
                            ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
                            burnAmountCleanWord I :: burnTickUpperCleanWord I ::
                            burnTickLowerCleanWord I :: ⟨621⟩ :: [solcSelectorWord I])
                          (burnPositionUpdateMem1
                            (σLockedEvm) I
                            (solcSlotWord
                              (σLockedEvm) I
                              (burnPositionBaseSlotWord
                                (σLockedEvm) I)))
                          (UInt256.ofNat 18) ByteArray.empty
                          (cA,
                            σLockedEvm) k' C' := by
                    intro hzero
                    obtain ⟨_, _, feeGrowthInside1, feeGrowthInside0, hrdSlot0⟩ :=
                      hrdPositionUpdateSlot0OfZero hzero
                    have hpackedResult :=
                      (uniswapV3PoolBurnPositionUpdateStoreSlot0Packed
                        (v := v) (code := code) (ee := I)
                        (g := Sat256.ofUInt256 g)
                        (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                        (pos0 := solcSlotWord
                          (σLockedEvm) I
                          (burnPositionBaseSlotWord
                            (σLockedEvm) I))
                        (inside1 := feeGrowthInside1) (inside0 := feeGrowthInside0)
                        (delta := UInt256.signextend ⟨15⟩
                          (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)))
                        (posBase := burnPositionBaseSlotWord
                          (σLockedEvm) I)
                        (retPos := ⟨19527⟩)
                        (inside1' := feeGrowthInside1) (inside0' := feeGrowthInside0)
                        (z2 := ⟨0⟩) (z3 := ⟨0⟩)
                        (fee1 := solcSlotWord
                          (σLockedEvm) I ⟨2⟩)
                        (fee0 := solcSlotWord
                          (σLockedEvm) I ⟨1⟩)
                        (posBase' := burnPositionBaseSlotWord
                          (σLockedEvm) I)
                        (tick := slot0TickReturnWord
                          (σLockedEvm) I)
                        (delta' := UInt256.signextend ⟨15⟩
                          (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)))
                        (upper := UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I))
                        (lower := UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I))
                        (owner := UInt256.ofNat I.source.val) (ret := ⟨16428⟩)
                        (free := ⟨256⟩)
                        (R := ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
                          ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
                          burnAmountCleanWord I :: burnTickUpperCleanWord I ::
                          burnTickLowerCleanWord I :: ⟨621⟩ :: [solcSelectorWord I])
                        hpatch hrdSlot0
                        (by simp only [List.length_cons, List.length_nil]; omega))
                    obtain ⟨_, _, hrdPacked⟩ := hpackedResult
                    exact ⟨_, _, _, _, hrdPacked⟩
                have hrdPositionUpdateFeeGrowthInside0LastOfZero :
                    burnAmountCleanWord I = ⟨0⟩ →
                      ∃ k' C' feeGrowthInside1 feeGrowthInside0,
                        RD code I (Sat256.ofUInt256 g)
                          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                          ⟨21595⟩
                          (burnPositionUpdateSlot0Mask ::
                            burnPositionKeyNewFreePtrWord :: ⟨64⟩ ::
                            feeGrowthInside1 :: feeGrowthInside0 ::
                            UInt256.signextend ⟨15⟩
                              (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)) ::
                            burnPositionBaseSlotWord
                              (σLockedEvm) I ::
                            ⟨19527⟩ ::
                            feeGrowthInside1 :: feeGrowthInside0 ::
                            ⟨0⟩ :: ⟨0⟩ ::
                            solcSlotWord
                              (σLockedEvm) I ⟨2⟩ ::
                            solcSlotWord
                              (σLockedEvm) I ⟨1⟩ ::
                            burnPositionBaseSlotWord
                              (σLockedEvm) I ::
                            slot0TickReturnWord
                              (σLockedEvm) I ::
                            UInt256.signextend ⟨15⟩
                              (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)) ::
                            UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I) ::
                            UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I) ::
                            UInt256.ofNat I.source.val :: ⟨16428⟩ :: ⟨256⟩ ::
                            ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
                            ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
                            burnAmountCleanWord I :: burnTickUpperCleanWord I ::
                            burnTickLowerCleanWord I :: ⟨621⟩ :: [solcSelectorWord I])
                          (burnPositionUpdateMem2
                            (σLockedEvm) I
                            (solcSlotWord
                              (σLockedEvm) I
                              (burnPositionBaseSlotWord
                                (σLockedEvm) I))
                            (burnPositionBaseSlotWord
                              (σLockedEvm) I))
                          (UInt256.ofNat 19) ByteArray.empty
                          (cA,
                            σLockedEvm) k' C' := by
                  intro hzero
                  obtain ⟨_, _, feeGrowthInside1, feeGrowthInside0, hrdPacked⟩ :=
                    hrdPositionUpdatePackedSlot0OfZero hzero
                  have hfeeGrowthInside0Result :=
                    (uniswapV3PoolBurnPositionUpdateStoreFeeGrowthInside0Last
                      (v := v) (code := code) (ee := I)
                      (g := Sat256.ofUInt256 g)
                      (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                      (inside1 := feeGrowthInside1) (inside0 := feeGrowthInside0)
                      (delta := UInt256.signextend ⟨15⟩
                        (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)))
                      (posBase := burnPositionBaseSlotWord
                        (σLockedEvm) I)
                      (retPos := ⟨19527⟩)
                      (inside1' := feeGrowthInside1) (inside0' := feeGrowthInside0)
                      (z2 := ⟨0⟩) (z3 := ⟨0⟩)
                      (fee1 := solcSlotWord
                        (σLockedEvm) I ⟨2⟩)
                      (fee0 := solcSlotWord
                        (σLockedEvm) I ⟨1⟩)
                      (posBase' := burnPositionBaseSlotWord
                        (σLockedEvm) I)
                      (tick := slot0TickReturnWord
                        (σLockedEvm) I)
                      (delta' := UInt256.signextend ⟨15⟩
                        (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)))
                      (upper := UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I))
                      (lower := UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I))
                      (owner := UInt256.ofNat I.source.val) (ret := ⟨16428⟩)
                      (free := ⟨256⟩)
                      (R := ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
                        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
                        burnAmountCleanWord I :: burnTickUpperCleanWord I ::
                        burnTickLowerCleanWord I :: ⟨621⟩ :: [solcSelectorWord I])
                      hpatch hrdPacked
                      (by simp only [List.length_cons, List.length_nil]; omega))
                  obtain ⟨_, _, hrdFeeGrowthInside0⟩ := hfeeGrowthInside0Result
                  exact ⟨_, _, _, _, hrdFeeGrowthInside0⟩
                have hrdPositionUpdateFeeGrowthInside1LastOfZero :
                    burnAmountCleanWord I = ⟨0⟩ →
                      ∃ k' C' feeGrowthInside1 feeGrowthInside0,
                        RD code I (Sat256.ofUInt256 g)
                          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                          ⟨21607⟩
                          (burnPositionKeyNewFreePtrWord ::
                            burnPositionUpdateSlot0Mask ::
                            feeGrowthInside1 :: feeGrowthInside0 ::
                            UInt256.signextend ⟨15⟩
                              (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)) ::
                            burnPositionBaseSlotWord
                              (σLockedEvm) I ::
                            ⟨19527⟩ ::
                            feeGrowthInside1 :: feeGrowthInside0 ::
                            ⟨0⟩ :: ⟨0⟩ ::
                            solcSlotWord
                              (σLockedEvm) I ⟨2⟩ ::
                            solcSlotWord
                              (σLockedEvm) I ⟨1⟩ ::
                            burnPositionBaseSlotWord
                              (σLockedEvm) I ::
                            slot0TickReturnWord
                              (σLockedEvm) I ::
                            UInt256.signextend ⟨15⟩
                              (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)) ::
                            UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I) ::
                            UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I) ::
                            UInt256.ofNat I.source.val :: ⟨16428⟩ :: ⟨256⟩ ::
                            ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
                            ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
                            burnAmountCleanWord I :: burnTickUpperCleanWord I ::
                            burnTickLowerCleanWord I :: ⟨621⟩ :: [solcSelectorWord I])
                          (burnPositionUpdateMem3
                            (σLockedEvm) I
                            (solcSlotWord
                              (σLockedEvm) I
                              (burnPositionBaseSlotWord
                                (σLockedEvm) I))
                            (burnPositionBaseSlotWord
                              (σLockedEvm) I))
                          (UInt256.ofNat 20) ByteArray.empty
                          (cA,
                            σLockedEvm) k' C' := by
                  intro hzero
                  obtain ⟨_, _, feeGrowthInside1, feeGrowthInside0, hrdFeeGrowthInside0⟩ :=
                    hrdPositionUpdateFeeGrowthInside0LastOfZero hzero
                  have hfeeGrowthInside1Result :=
                    (uniswapV3PoolBurnPositionUpdateStoreFeeGrowthInside1Last
                      (v := v) (code := code) (ee := I)
                      (g := Sat256.ofUInt256 g)
                      (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                      (inside1 := feeGrowthInside1) (inside0 := feeGrowthInside0)
                      (delta := UInt256.signextend ⟨15⟩
                        (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)))
                      (posBase := burnPositionBaseSlotWord
                        (σLockedEvm) I)
                      (retPos := ⟨19527⟩)
                      (inside1' := feeGrowthInside1) (inside0' := feeGrowthInside0)
                      (z2 := ⟨0⟩) (z3 := ⟨0⟩)
                      (fee1 := solcSlotWord
                        (σLockedEvm) I ⟨2⟩)
                      (fee0 := solcSlotWord
                        (σLockedEvm) I ⟨1⟩)
                      (posBase' := burnPositionBaseSlotWord
                        (σLockedEvm) I)
                      (tick := slot0TickReturnWord
                        (σLockedEvm) I)
                      (delta' := UInt256.signextend ⟨15⟩
                        (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)))
                      (upper := UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I))
                      (lower := UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I))
                      (owner := UInt256.ofNat I.source.val) (ret := ⟨16428⟩)
                      (free := ⟨256⟩)
                      (R := ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
                        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
                        burnAmountCleanWord I :: burnTickUpperCleanWord I ::
                        burnTickLowerCleanWord I :: ⟨621⟩ :: [solcSelectorWord I])
                      hpatch hrdFeeGrowthInside0
                      (by simp only [List.length_cons, List.length_nil]; omega))
                  obtain ⟨_, _, hrdFeeGrowthInside1⟩ := hfeeGrowthInside1Result
                  exact ⟨_, _, _, _, hrdFeeGrowthInside1⟩
                have hrdPositionUpdateTokensOwed0OfZero :
                    burnAmountCleanWord I = ⟨0⟩ →
                      ∃ k' C' feeGrowthInside1 feeGrowthInside0,
                        RD code I (Sat256.ofUInt256 g)
                          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                          ⟨21620⟩
                          (solcSlotWord
                            (σLockedEvm) I
                            (burnPositionBaseSlotWord
                              (σLockedEvm) I + (⟨3⟩ : UInt256)) ::
                            burnPositionKeyNewFreePtrWord ::
                            burnPositionUpdateSlot0Mask ::
                            feeGrowthInside1 :: feeGrowthInside0 ::
                            UInt256.signextend ⟨15⟩
                              (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)) ::
                            burnPositionBaseSlotWord
                              (σLockedEvm) I ::
                            ⟨19527⟩ ::
                            feeGrowthInside1 :: feeGrowthInside0 ::
                            ⟨0⟩ :: ⟨0⟩ ::
                            solcSlotWord
                              (σLockedEvm) I ⟨2⟩ ::
                            solcSlotWord
                              (σLockedEvm) I ⟨1⟩ ::
                            burnPositionBaseSlotWord
                              (σLockedEvm) I ::
                            slot0TickReturnWord
                              (σLockedEvm) I ::
                            UInt256.signextend ⟨15⟩
                              (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)) ::
                            UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I) ::
                            UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I) ::
                            UInt256.ofNat I.source.val :: ⟨16428⟩ :: ⟨256⟩ ::
                            ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
                            ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
                            burnAmountCleanWord I :: burnTickUpperCleanWord I ::
                            burnTickLowerCleanWord I :: ⟨621⟩ :: [solcSelectorWord I])
                          (burnPositionUpdateMem4
                            (σLockedEvm) I
                            (solcSlotWord
                              (σLockedEvm) I
                              (burnPositionBaseSlotWord
                                (σLockedEvm) I))
                            (burnPositionBaseSlotWord
                              (σLockedEvm) I))
                          (UInt256.ofNat 21) ByteArray.empty
                          (cA,
                            σLockedEvm) k' C' := by
                  intro hzero
                  obtain ⟨_, _, feeGrowthInside1, feeGrowthInside0, hrdFeeGrowthInside1⟩ :=
                    hrdPositionUpdateFeeGrowthInside1LastOfZero hzero
                  have htokensOwed0Result :=
                    (uniswapV3PoolBurnPositionUpdateStoreTokensOwed0
                      (v := v) (code := code) (ee := I)
                      (g := Sat256.ofUInt256 g)
                      (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                      (inside1 := feeGrowthInside1) (inside0 := feeGrowthInside0)
                      (delta := UInt256.signextend ⟨15⟩
                        (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)))
                      (posBase := burnPositionBaseSlotWord
                        (σLockedEvm) I)
                      (retPos := ⟨19527⟩)
                      (inside1' := feeGrowthInside1) (inside0' := feeGrowthInside0)
                      (z2 := ⟨0⟩) (z3 := ⟨0⟩)
                      (fee1 := solcSlotWord
                        (σLockedEvm) I ⟨2⟩)
                      (fee0 := solcSlotWord
                        (σLockedEvm) I ⟨1⟩)
                      (posBase' := burnPositionBaseSlotWord
                        (σLockedEvm) I)
                      (tick := slot0TickReturnWord
                        (σLockedEvm) I)
                      (delta' := UInt256.signextend ⟨15⟩
                        (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)))
                      (upper := UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I))
                      (lower := UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I))
                      (owner := UInt256.ofNat I.source.val) (ret := ⟨16428⟩)
                      (free := ⟨256⟩)
                      (R := ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
                        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
                        burnAmountCleanWord I :: burnTickUpperCleanWord I ::
                        burnTickLowerCleanWord I :: ⟨621⟩ :: [solcSelectorWord I])
                      hpatch hrdFeeGrowthInside1
                      (by simp only [List.length_cons, List.length_nil]; omega))
                  obtain ⟨_, _, hrdTokensOwed0⟩ := htokensOwed0Result
                  exact ⟨_, _, _, _, hrdTokensOwed0⟩
                have hrdPositionUpdateTokensOwed1OfZero :
                    burnAmountCleanWord I = ⟨0⟩ →
                      ∃ k' C' feeGrowthInside1 feeGrowthInside0,
                        RD code I (Sat256.ofUInt256 g)
                          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                          ⟨21635⟩
                          (burnPositionKeyNewFreePtrWord ::
                            feeGrowthInside1 :: feeGrowthInside0 ::
                            UInt256.signextend ⟨15⟩
                              (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)) ::
                            burnPositionBaseSlotWord
                              (σLockedEvm) I ::
                            ⟨19527⟩ ::
                            feeGrowthInside1 :: feeGrowthInside0 ::
                            ⟨0⟩ :: ⟨0⟩ ::
                            solcSlotWord
                              (σLockedEvm) I ⟨2⟩ ::
                            solcSlotWord
                              (σLockedEvm) I ⟨1⟩ ::
                            burnPositionBaseSlotWord
                              (σLockedEvm) I ::
                            slot0TickReturnWord
                              (σLockedEvm) I ::
                            UInt256.signextend ⟨15⟩
                              (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)) ::
                            UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I) ::
                            UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I) ::
                            UInt256.ofNat I.source.val :: ⟨16428⟩ :: ⟨256⟩ ::
                            ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
                            ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
                            burnAmountCleanWord I :: burnTickUpperCleanWord I ::
                            burnTickLowerCleanWord I :: ⟨621⟩ :: [solcSelectorWord I])
                          (burnPositionUpdateMem5
                            (σLockedEvm) I
                            (solcSlotWord
                              (σLockedEvm) I
                              (burnPositionBaseSlotWord
                                (σLockedEvm) I))
                            (burnPositionBaseSlotWord
                              (σLockedEvm) I))
                          (UInt256.ofNat 22) ByteArray.empty
                          (cA,
                            σLockedEvm) k' C' := by
                  intro hzero
                  obtain ⟨_, _, feeGrowthInside1, feeGrowthInside0, hrdTokensOwed0⟩ :=
                    hrdPositionUpdateTokensOwed0OfZero hzero
                  have htokensOwed1Result :=
                    (uniswapV3PoolBurnPositionUpdateStoreTokensOwed1
                      (v := v) (code := code) (ee := I)
                      (g := Sat256.ofUInt256 g)
                      (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                      (inside1 := feeGrowthInside1) (inside0 := feeGrowthInside0)
                      (delta := UInt256.signextend ⟨15⟩
                        (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)))
                      (posBase := burnPositionBaseSlotWord
                        (σLockedEvm) I)
                      (retPos := ⟨19527⟩)
                      (inside1' := feeGrowthInside1) (inside0' := feeGrowthInside0)
                      (z2 := ⟨0⟩) (z3 := ⟨0⟩)
                      (fee1 := solcSlotWord
                        (σLockedEvm) I ⟨2⟩)
                      (fee0 := solcSlotWord
                        (σLockedEvm) I ⟨1⟩)
                      (posBase' := burnPositionBaseSlotWord
                        (σLockedEvm) I)
                      (tick := slot0TickReturnWord
                        (σLockedEvm) I)
                      (delta' := UInt256.signextend ⟨15⟩
                        (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)))
                      (upper := UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I))
                      (lower := UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I))
                      (owner := UInt256.ofNat I.source.val) (ret := ⟨16428⟩)
                      (free := ⟨256⟩)
                      (R := ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
                        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
                        burnAmountCleanWord I :: burnTickUpperCleanWord I ::
                        burnTickLowerCleanWord I :: ⟨621⟩ :: [solcSelectorWord I])
                      hpatch hrdTokensOwed0
                      (by simp only [List.length_cons, List.length_nil]; omega))
                  obtain ⟨_, _, hrdTokensOwed1⟩ := htokensOwed1Result
                  exact ⟨_, _, _, _, hrdTokensOwed1⟩
                have hrdPositionUpdateDeltaZeroFallthroughOfZero :
                    burnAmountCleanWord I = ⟨0⟩ →
                      ∃ k' C' feeGrowthInside1 feeGrowthInside0,
                        RD code I (Sat256.ofUInt256 g)
                          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                          ⟨21646⟩
                          (⟨0⟩ :: burnPositionKeyNewFreePtrWord ::
                            feeGrowthInside1 :: feeGrowthInside0 ::
                            UInt256.signextend ⟨15⟩
                              (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)) ::
                            burnPositionBaseSlotWord
                              (σLockedEvm) I ::
                            ⟨19527⟩ ::
                            feeGrowthInside1 :: feeGrowthInside0 ::
                            ⟨0⟩ :: ⟨0⟩ ::
                            solcSlotWord
                              (σLockedEvm) I ⟨2⟩ ::
                            solcSlotWord
                              (σLockedEvm) I ⟨1⟩ ::
                            burnPositionBaseSlotWord
                              (σLockedEvm) I ::
                            slot0TickReturnWord
                              (σLockedEvm) I ::
                            UInt256.signextend ⟨15⟩
                              (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)) ::
                            UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I) ::
                            UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I) ::
                            UInt256.ofNat I.source.val :: ⟨16428⟩ :: ⟨256⟩ ::
                            ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
                            ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
                            burnAmountCleanWord I :: burnTickUpperCleanWord I ::
                            burnTickLowerCleanWord I :: ⟨621⟩ :: [solcSelectorWord I])
                          (burnPositionUpdateMem5
                            (σLockedEvm) I
                            (solcSlotWord
                              (σLockedEvm) I
                              (burnPositionBaseSlotWord
                                (σLockedEvm) I))
                            (burnPositionBaseSlotWord
                              (σLockedEvm) I))
                          (UInt256.ofNat 22) ByteArray.empty
                          (cA,
                            σLockedEvm) k' C' := by
                  intro hzero
                  obtain ⟨_, _, feeGrowthInside1, feeGrowthInside0, hrdTokensOwed1⟩ :=
                    hrdPositionUpdateTokensOwed1OfZero hzero
                  have hdelta :
                      UInt256.signextend ⟨15⟩
                          (UInt256.signextend ⟨15⟩
                            (UInt256.sub ⟨0⟩ (burnAmountCleanWord I))) = ⟨0⟩ := by
                    rw [hzero]
                    native_decide
                  have hfallthroughResult :=
                    (uniswapV3PoolBurnPositionUpdateLiquidityDeltaZeroFallthrough
                      (v := v) (code := code) (ee := I)
                      (g := Sat256.ofUInt256 g)
                      (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                      (inside1 := feeGrowthInside1) (inside0 := feeGrowthInside0)
                      (delta := UInt256.signextend ⟨15⟩
                        (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)))
                      (posBase := burnPositionBaseSlotWord
                        (σLockedEvm) I)
                      (retPos := ⟨19527⟩)
                      (inside1' := feeGrowthInside1) (inside0' := feeGrowthInside0)
                      (z2 := ⟨0⟩) (z3 := ⟨0⟩)
                      (fee1 := solcSlotWord
                        (σLockedEvm) I ⟨2⟩)
                      (fee0 := solcSlotWord
                        (σLockedEvm) I ⟨1⟩)
                      (posBase' := burnPositionBaseSlotWord
                        (σLockedEvm) I)
                      (tick := slot0TickReturnWord
                        (σLockedEvm) I)
                      (delta' := UInt256.signextend ⟨15⟩
                        (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)))
                      (upper := UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I))
                      (lower := UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I))
                      (owner := UInt256.ofNat I.source.val) (ret := ⟨16428⟩)
                      (free := ⟨256⟩)
                      (R := ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
                        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
                        burnAmountCleanWord I :: burnTickUpperCleanWord I ::
                        burnTickLowerCleanWord I :: ⟨621⟩ :: [solcSelectorWord I])
                      hpatch hdelta hrdTokensOwed1
                      (by simp only [List.length_cons, List.length_nil]; omega))
                  obtain ⟨_, _, hrdFallthrough⟩ := hfallthroughResult
                  exact ⟨_, _, _, _, hrdFallthrough⟩
                let lockedEvm : AccountMap :=
                  σLockedEvm
                let positionBase : UInt256 := burnPositionBaseSlotWord lockedEvm I
                have hrdPositionUpdateLiquidityZeroFallthroughOfZero :
                    burnAmountCleanWord I = ⟨0⟩ →
                      burnPositionUpdateSlot0Packed
                          (solcSlotWord lockedEvm I positionBase) = ⟨0⟩ →
                        ∃ k' C' feeGrowthInside1 feeGrowthInside0,
                          RD code I (Sat256.ofUInt256 g)
                            (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                            ⟨21661⟩
                            (⟨0⟩ :: burnPositionKeyNewFreePtrWord ::
                              feeGrowthInside1 :: feeGrowthInside0 ::
                              UInt256.signextend ⟨15⟩
                                (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)) ::
                              positionBase :: ⟨19527⟩ ::
                              feeGrowthInside1 :: feeGrowthInside0 ::
                              ⟨0⟩ :: ⟨0⟩ ::
                              solcSlotWord lockedEvm I ⟨2⟩ ::
                              solcSlotWord lockedEvm I ⟨1⟩ ::
                              positionBase ::
                              slot0TickReturnWord lockedEvm I ::
                              UInt256.signextend ⟨15⟩
                                (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)) ::
                              UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I) ::
                              UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I) ::
                              UInt256.ofNat I.source.val :: ⟨16428⟩ :: ⟨256⟩ ::
                              ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
                              ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
                              burnAmountCleanWord I :: burnTickUpperCleanWord I ::
                              burnTickLowerCleanWord I :: ⟨621⟩ ::
                              [solcSelectorWord I])
                            (burnPositionUpdateMem5 lockedEvm I
                              (solcSlotWord lockedEvm I positionBase) positionBase)
                            (UInt256.ofNat 22) ByteArray.empty
                            (cA, lockedEvm) k' C' := by
                  intro hzero hliquidity
                  obtain ⟨_, _, feeGrowthInside1, feeGrowthInside0, hrdFallthrough⟩ :=
                    hrdPositionUpdateDeltaZeroFallthroughOfZero hzero
                  obtain ⟨_, _, hrd21661⟩ :=
                    (uniswapV3PoolBurnPositionUpdateLiquidityZeroFallthrough
                      (v := v) (code := code) (ee := I)
                      (g := Sat256.ofUInt256 g)
                      (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                      (inside1 := feeGrowthInside1) (inside0 := feeGrowthInside0)
                      (delta := UInt256.signextend ⟨15⟩
                        (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)))
                      (posBase := positionBase) (retPos := ⟨19527⟩)
                      (inside1' := feeGrowthInside1) (inside0' := feeGrowthInside0)
                      (z2 := ⟨0⟩) (z3 := ⟨0⟩)
                      (fee1 := solcSlotWord lockedEvm I ⟨2⟩)
                      (fee0 := solcSlotWord lockedEvm I ⟨1⟩)
                      (posBase' := positionBase)
                      (tick := slot0TickReturnWord lockedEvm I)
                      (delta' := UInt256.signextend ⟨15⟩
                        (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)))
                      (upper := UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I))
                      (lower := UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I))
                      (owner := UInt256.ofNat I.source.val) (ret := ⟨16428⟩)
                      (free := ⟨256⟩)
                      (R := ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
                        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
                        burnAmountCleanWord I :: burnTickUpperCleanWord I ::
                        burnTickLowerCleanWord I :: ⟨621⟩ :: [solcSelectorWord I])
                      (σ := lockedEvm)
                      hpatch hliquidity
                      (by simpa [lockedEvm, positionBase] using hrdFallthrough)
                      (by simp only [List.length_cons, List.length_nil]; omega))
                  exact ⟨_, _, feeGrowthInside1, feeGrowthInside0, hrd21661⟩
                have hrdPositionUpdateLiquidityZeroRevertOfZero :
                    burnAmountCleanWord I = ⟨0⟩ →
                      burnPositionUpdateSlot0Packed
                          (solcSlotWord lockedEvm I positionBase) = ⟨0⟩ →
                        RDrev code (Sat256.ofUInt256 g)
                          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
                  intro hzero hliquidity
                  obtain ⟨_, _, feeGrowthInside1, feeGrowthInside0, hrd21661⟩ :=
                    hrdPositionUpdateLiquidityZeroFallthroughOfZero hzero hliquidity
                  exact uniswapV3PoolBurnPositionUpdateNpRevertTail
                    (v := v) (code := code) (ee := I) (g := Sat256.ofUInt256 g)
                    (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                    (pos0 := solcSlotWord lockedEvm I positionBase)
                    (posBase := positionBase)
                    (stk := ⟨0⟩ :: burnPositionKeyNewFreePtrWord ::
                      feeGrowthInside1 :: feeGrowthInside0 ::
                      UInt256.signextend ⟨15⟩
                        (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)) ::
                      positionBase :: ⟨19527⟩ ::
                      feeGrowthInside1 :: feeGrowthInside0 ::
                      ⟨0⟩ :: ⟨0⟩ ::
                      solcSlotWord lockedEvm I ⟨2⟩ ::
                      solcSlotWord lockedEvm I ⟨1⟩ ::
                      positionBase ::
                      slot0TickReturnWord lockedEvm I ::
                      UInt256.signextend ⟨15⟩
                        (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)) ::
                      UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I) ::
                      UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I) ::
                      UInt256.ofNat I.source.val :: ⟨16428⟩ :: ⟨256⟩ ::
                      ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
                      ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
                      burnAmountCleanWord I :: burnTickUpperCleanWord I ::
                      burnTickLowerCleanWord I :: ⟨621⟩ :: [solcSelectorWord I])
                    (rdata := ByteArray.empty) (cA := cA) (σ := lockedEvm)
                    hpatch
                    (by simpa using hrd21661)
                    (by simp only [List.length_cons, List.length_nil]; omega)
                by_cases hzeroLiq :
                    burnAmountCleanWord I = ⟨0⟩ ∧
                      burnPositionUpdateSlot0Packed
                          (solcSlotWord lockedEvm I positionBase) = ⟨0⟩
                · rcases hzeroLiq with ⟨hzero, hliquidity⟩
                  let lockedSolm : AccountMap :=
                    σLockedSolm
                  have hAccountsLocked : accountMapEquiv lockedEvm lockedSolm := by
                    simpa [lockedEvm, lockedSolm] using hAccountsAfterLock
                  have hPositionBase :
                      positionBase = positionsBase (burnPositionKeyKey I) := by
                    simpa [positionBase] using
                      burnPositionBaseSlotWord_eq_positionsBase lockedEvm I
                  have hliqEvm :
                      burnPositionUpdateSlot0Packed
                        (solcSlotWord lockedEvm I (positionsBase (burnPositionKeyKey I))) =
                          ⟨0⟩ := by
                    simpa [hPositionBase] using hliquidity
                  have hslotEq :
                      solcSlotWord lockedSolm I (positionsBase (burnPositionKeyKey I)) =
                        solcSlotWord lockedEvm I (positionsBase (burnPositionKeyKey I)) := by
                    have hslot := accountMapEquiv_storage_findD hAccountsLocked I.codeOwner
                      (positionsBase (burnPositionKeyKey I)) (⟨0⟩ : UInt256)
                    simpa [solcSlotWord] using hslot.symm
                  have hliqSolm :
                      burnPositionUpdateSlot0Packed
                        (solcSlotWord lockedSolm I (positionsBase (burnPositionKeyKey I))) =
                          ⟨0⟩ := by
                    rw [hslotEq]
                    exact hliqEvm
                  have hrd := hrdPositionUpdateLiquidityZeroRevertOfZero hzero hliquidity
                  have hbody :=
                    uniswapV3PoolBurnSourcePositionUpdateLiquidityZeroReverts (v := v)
                      (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                      (A := A) (I := I) (g := Sat256.ofUInt256 g) hwv hunlockedSolm
                      hcanon hnoDelegate htickLt hLowerMin hUpperMax hzero
                      (by simpa [lockedSolm] using hliqSolm)
                  exact hrd.reEquivExecutionRevert hcode hdispatch hdecode hbody
                · let positionUpdateR : List UInt256 :=
                    ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
                    ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
                    burnAmountCleanWord I :: burnTickUpperCleanWord I ::
                    burnTickLowerCleanWord I :: ⟨621⟩ :: [solcSelectorWord I]
                  by_cases hzero : burnAmountCleanWord I = ⟨0⟩
                  · have hliq :
                        burnPositionUpdateSlot0Packed
                            (solcSlotWord lockedEvm I positionBase) ≠ ⟨0⟩ := by
                      intro hliqZero
                      exact hzeroLiq ⟨hzero, hliqZero⟩
                    let feeGrowthInside1 := burnTickGetInside1Word lockedEvm I
                    let feeGrowthInside0 := burnTickGetInside0Word lockedEvm I
                    by_cases hprod0 :
                        uniswapV3PoolFullMathMulDivProd1
                            (UInt256.sub feeGrowthInside0
                              (solcSlotWord lockedEvm I
                                (positionBase + (⟨1⟩ : UInt256))))
                            (burnPositionUpdateSlot0Packed
                              (solcSlotWord lockedEvm I positionBase)) = ⟨0⟩
                    · by_cases hprod1 :
                          uniswapV3PoolFullMathMulDivProd1
                              (UInt256.sub feeGrowthInside1
                                (solcSlotWord lockedEvm I
                                  (positionBase + (⟨2⟩ : UInt256))))
                              (burnPositionUpdateSlot0Packed
                                (solcSlotWord lockedEvm I positionBase)) = ⟨0⟩
                      · obtain ⟨_, _, hrdFeeGrowthEntry⟩ := hrdFeeGrowthInsideEntry hzero
                        obtain ⟨_, _, hrd21861⟩ :=
                          uniswapV3PoolBurnZeroDeltaPositionUpdateToMulDivReturnConcrete
                            (v := v) (code := code) (ee := I)
                            (g := Sat256.ofUInt256 g)
                            (s0 := initState cA gh bl σ_evm σ₀
                              (Sat256.ofUInt256 g) A I)
                            (ret := ⟨621⟩) (R := [solcSelectorWord I])
                            (rdata := ByteArray.empty) (cA := cA) (σ := lockedEvm)
                            hpatch _hperm htickLt hzero
                            (by simpa [positionBase] using hliq)
                            (by simpa [feeGrowthInside0, positionBase] using hprod0)
                            (by simpa [feeGrowthInside1, positionBase] using hprod1)
                            (by simpa [lockedEvm, positionBase] using hrdFeeGrowthEntry)
                            (by simp only [List.length_singleton]; omega)
                        have hmload224 := burnPositionUpdateMem5_mload224 lockedEvm I
                          (solcSlotWord lockedEvm I positionBase) positionBase
                        have hdelta :
                            UInt256.slt
                                (UInt256.signextend ⟨15⟩
                                  (UInt256.signextend ⟨15⟩
                                    (UInt256.sub ⟨0⟩ (burnAmountCleanWord I))))
                                ⟨0⟩ = ⟨0⟩ := by
                          rw [hzero]
                          native_decide
                        have hdest9737 :
                            (D_J code 0).contains (⟨9737⟩ : UInt256) = true := by
                          have hpreserve :
                              D_J_auxPreservesTargetBool uniswapV3PoolBytecode
                                  uniswapV3PoolPatchOffsets (⟨9737⟩ : UInt256) 0 =
                                true := by
                            native_decide
                          exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
                            (uniswapV3PoolPatchOffsetMem v) hpreserve
                        have hrdSuccessCases :=
                          uniswapV3PoolBurnZeroDeltaPositionUpdateToFinalReturnCases
                            (v := v) (code := code) (ee := I) (g := Sat256.ofUInt256 g)
                            (s0 := initState cA gh bl σ_evm σ₀
                              (Sat256.ofUInt256 g) A I)
                            (tokensOwed1 := UInt256.div
                              (uniswapV3PoolFullMathMulDivProd0
                                (UInt256.sub feeGrowthInside1
                                  (solcSlotWord lockedEvm I
                                    (positionBase + (⟨2⟩ : UInt256))))
                                (burnPositionUpdateSlot0Packed
                                  (solcSlotWord lockedEvm I positionBase)))
                              (UInt256.shiftLeft ⟨1⟩ ⟨128⟩))
                            (tokensOwed0 := UInt256.div
                              (uniswapV3PoolFullMathMulDivProd0
                                (UInt256.sub feeGrowthInside0
                                  (solcSlotWord lockedEvm I
                                    (positionBase + (⟨1⟩ : UInt256))))
                                (burnPositionUpdateSlot0Packed
                                  (solcSlotWord lockedEvm I positionBase)))
                              (UInt256.shiftLeft ⟨1⟩ ⟨128⟩))
                            (liquidity := burnPositionUpdateSlot0Packed
                              (solcSlotWord lockedEvm I positionBase))
                            (inside1 := feeGrowthInside1) (inside0 := feeGrowthInside0)
                            (delta := UInt256.signextend ⟨15⟩
                              (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)))
                            (posBase := positionBase)
                            (inside1' := feeGrowthInside1) (inside0' := feeGrowthInside0)
                            (z2 := ⟨0⟩) (z3 := ⟨0⟩)
                            (fee1 := solcSlotWord lockedEvm I ⟨2⟩)
                            (fee0 := solcSlotWord lockedEvm I ⟨1⟩)
                            (tick := slot0TickReturnWord lockedEvm I)
                            (delta' := UInt256.signextend ⟨15⟩
                              (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)))
                            (upper := UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I))
                            (lower := UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I))
                            (owner := UInt256.ofNat I.source.val) (free := ⟨256⟩) (r3 := ⟨0⟩)
                            (amount := burnAmountCleanWord I) (eventUpper := burnTickUpperCleanWord I)
                            (eventLower := burnTickLowerCleanWord I) (R := [solcSelectorWord I])
                            (σmem := lockedEvm) (pos0 := solcSlotWord lockedEvm I positionBase)
                            (rdata := ByteArray.empty) (cA := cA)
                            (σ := sstoreAccountMap I.codeOwner
                              (sstoreAccountMap I.codeOwner lockedEvm
                                (positionBase + (⟨1⟩ : UInt256)) feeGrowthInside0)
                              (positionBase + (⟨2⟩ : UInt256)) feeGrowthInside1)
                            hpatch hdest9737 _hperm hzero hmload224
                            (by simpa [positionUpdateR] using hrd21861) hdelta
                            (by simp only [List.length_singleton]; omega)
                        let tokensOwed0 : UInt256 :=
                          UInt256.div
                            (uniswapV3PoolFullMathMulDivProd0
                              (UInt256.sub feeGrowthInside0
                                (solcSlotWord lockedEvm I
                                  (positionBase + (⟨1⟩ : UInt256))))
                              (burnPositionUpdateSlot0Packed
                                (solcSlotWord lockedEvm I positionBase)))
                            (UInt256.shiftLeft ⟨1⟩ ⟨128⟩)
                        let tokensOwed1 : UInt256 :=
                          UInt256.div
                            (uniswapV3PoolFullMathMulDivProd0
                              (UInt256.sub feeGrowthInside1
                                (solcSlotWord lockedEvm I
                                  (positionBase + (⟨2⟩ : UInt256))))
                              (burnPositionUpdateSlot0Packed
                                (solcSlotWord lockedEvm I positionBase)))
                            (UInt256.shiftLeft ⟨1⟩ ⟨128⟩)
                        have hlow0 :
                            UInt256.land burnPositionUpdateSlot0Mask
                                (UInt256.div
                                  (uniswapV3PoolFullMathMulDivProd0
                                    (UInt256.sub feeGrowthInside0
                                      (solcSlotWord lockedEvm I
                                        (positionBase + (⟨1⟩ : UInt256))))
                                    (burnPositionUpdateSlot0Packed
                                      (solcSlotWord lockedEvm I positionBase)))
                                  (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)) =
                              UInt256.land burnPositionUpdateSlot0Mask tokensOwed0 := by
                          rfl
                        have hlow1 :
                            UInt256.land burnPositionUpdateSlot0Mask
                                (UInt256.div
                                  (uniswapV3PoolFullMathMulDivProd0
                                    (UInt256.sub feeGrowthInside1
                                      (solcSlotWord lockedEvm I
                                        (positionBase + (⟨2⟩ : UInt256))))
                                    (burnPositionUpdateSlot0Packed
                                      (solcSlotWord lockedEvm I positionBase)))
                                  (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)) =
                              UInt256.land burnPositionUpdateSlot0Mask tokensOwed1 := by
                          rfl
                        exact
                          uniswapV3PoolBurnZeroDeltaPositionUpdateFinish
                            (v := v) (cA := cA) (gh := gh) (bl := bl)
                            (σ_evm := σ_evm) (σ_solm := σ_solm) (σ₀ := σ₀)
                            (lockedEvm := lockedEvm) (lockedSolm := σLockedSolm)
                            (A := A) (I := I) (g := g)
                            (tokensOwed0 := tokensOwed0) (tokensOwed1 := tokensOwed1)
                            (feeGrowthInside0 := feeGrowthInside0)
                            (feeGrowthInside1 := feeGrowthInside1)
                            (positionBase := positionBase) (code := code)
                            hcode hdispatch hdecode hwv hunlockedSolm hcanon hnoDelegate
                            htickLt hLowerMin hUpperMax hzero
                            (by simpa [lockedEvm] using hAccountsAfterLock)
                            (by rfl) (by rfl) (by rfl)
                            (by
                              simpa [positionBase] using
                                burnPositionBaseSlotWord_eq_positionsBase lockedEvm I)
                            (by simpa [positionBase] using hliq)
                            hlow0 hlow1
                            (by
                              simpa [tokensOwed0, tokensOwed1, lockedEvm]
                                using hrdSuccessCases)
                      · obtain ⟨_, _, hrdFeeGrowthEntry⟩ := hrdFeeGrowthInsideEntry hzero
                        have hliqBound :
                            (burnPositionUpdateSlot0Packed
                              (solcSlotWord lockedEvm I positionBase)).toNat <
                              2 ^ (128 : Nat) := by
                          change
                            (UInt256.land burnPositionUpdateSlot0Mask
                              (solcSlotWord lockedEvm I positionBase)).toNat <
                              2 ^ (128 : Nat)
                          rw [burnPositionUpdateSlot0Mask_eq_uint128Mask]
                          rw [u256_land_comm]
                          simpa [EVM.twoPow] using
                            uint128Mask_bound (solcSlotWord lockedEvm I positionBase)
                        have hden :
                            UInt256.gt (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)
                              (uniswapV3PoolFullMathMulDivProd1
                                (UInt256.sub feeGrowthInside1
                                  (solcSlotWord lockedEvm I
                                    (positionBase + (⟨2⟩ : UInt256))))
                                (burnPositionUpdateSlot0Packed
                                  (solcSlotWord lockedEvm I positionBase))) ≠ ⟨0⟩ := by
                          exact uniswapV3PoolFullMathMulDivProd1DenGtQ128
                            (UInt256.sub feeGrowthInside1
                              (solcSlotWord lockedEvm I
                                (positionBase + (⟨2⟩ : UInt256))))
                            (burnPositionUpdateSlot0Packed
                              (solcSlotWord lockedEvm I positionBase))
                            hliqBound
                        obtain ⟨_, _, hrd21861⟩ :=
                          uniswapV3PoolBurnZeroDeltaPositionUpdateToMulDivReturnConcreteSlowToken1
                            (v := v) (code := code) (ee := I)
                            (g := Sat256.ofUInt256 g)
                            (s0 := initState cA gh bl σ_evm σ₀
                              (Sat256.ofUInt256 g) A I)
                            (ret := ⟨621⟩) (R := [solcSelectorWord I])
                            (rdata := ByteArray.empty) (cA := cA) (σ := lockedEvm)
                            hpatch _hperm htickLt hzero
                            (by simpa [positionBase] using hliq)
                            (by simpa [feeGrowthInside0, positionBase] using hprod0)
                            (by
                              intro hprod1Zero
                              exact hprod1 (by
                                simpa [feeGrowthInside1, positionBase] using hprod1Zero))
                            (by simpa [feeGrowthInside1, positionBase] using hden)
                            (by simpa [lockedEvm, positionBase] using hrdFeeGrowthEntry)
                            (by simp only [List.length_singleton]; omega)
                        have hmload224 := burnPositionUpdateMem5_mload224 lockedEvm I
                          (solcSlotWord lockedEvm I positionBase) positionBase
                        have hdelta :
                            UInt256.slt
                                (UInt256.signextend ⟨15⟩
                                  (UInt256.signextend ⟨15⟩
                                    (UInt256.sub ⟨0⟩ (burnAmountCleanWord I))))
                                ⟨0⟩ = ⟨0⟩ := by
                          rw [hzero]
                          native_decide
                        have hdest9737 :
                            (D_J code 0).contains (⟨9737⟩ : UInt256) = true := by
                          have hpreserve :
                              D_J_auxPreservesTargetBool uniswapV3PoolBytecode
                                  uniswapV3PoolPatchOffsets (⟨9737⟩ : UInt256) 0 =
                                true := by
                            native_decide
                          exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
                            (uniswapV3PoolPatchOffsetMem v) hpreserve
                        let tokensOwed0 : UInt256 :=
                          UInt256.div
                            (uniswapV3PoolFullMathMulDivProd0
                              (UInt256.sub feeGrowthInside0
                                (solcSlotWord lockedEvm I
                                  (positionBase + (⟨1⟩ : UInt256))))
                              (burnPositionUpdateSlot0Packed
                                (solcSlotWord lockedEvm I positionBase)))
                            (UInt256.shiftLeft ⟨1⟩ ⟨128⟩)
                        let tokensOwed1 : UInt256 :=
                          uniswapV3PoolFullMathMulDivSlowResult
                            (uniswapV3PoolFullMathMulDivProd1
                              (UInt256.sub feeGrowthInside1
                                (solcSlotWord lockedEvm I
                                  (positionBase + (⟨2⟩ : UInt256))))
                              (burnPositionUpdateSlot0Packed
                                (solcSlotWord lockedEvm I positionBase)))
                            (uniswapV3PoolFullMathMulDivProd0
                              (UInt256.sub feeGrowthInside1
                                (solcSlotWord lockedEvm I
                                  (positionBase + (⟨2⟩ : UInt256))))
                              (burnPositionUpdateSlot0Packed
                                (solcSlotWord lockedEvm I positionBase)))
                            (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)
                            (burnPositionUpdateSlot0Packed
                              (solcSlotWord lockedEvm I positionBase))
                            (UInt256.sub feeGrowthInside1
                              (solcSlotWord lockedEvm I
                                (positionBase + (⟨2⟩ : UInt256))))
                        have hrdSuccessCases :=
                          uniswapV3PoolBurnZeroDeltaPositionUpdateToFinalReturnCases
                            (v := v) (code := code) (ee := I) (g := Sat256.ofUInt256 g)
                            (s0 := initState cA gh bl σ_evm σ₀
                              (Sat256.ofUInt256 g) A I)
                            (tokensOwed1 := tokensOwed1) (tokensOwed0 := tokensOwed0)
                            (liquidity := burnPositionUpdateSlot0Packed
                              (solcSlotWord lockedEvm I positionBase))
                            (inside1 := feeGrowthInside1) (inside0 := feeGrowthInside0)
                            (delta := UInt256.signextend ⟨15⟩
                              (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)))
                            (posBase := positionBase)
                            (inside1' := feeGrowthInside1) (inside0' := feeGrowthInside0)
                            (z2 := ⟨0⟩) (z3 := ⟨0⟩)
                            (fee1 := solcSlotWord lockedEvm I ⟨2⟩)
                            (fee0 := solcSlotWord lockedEvm I ⟨1⟩)
                            (tick := slot0TickReturnWord lockedEvm I)
                            (delta' := UInt256.signextend ⟨15⟩
                              (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)))
                            (upper := UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I))
                            (lower := UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I))
                            (owner := UInt256.ofNat I.source.val) (free := ⟨256⟩) (r3 := ⟨0⟩)
                            (amount := burnAmountCleanWord I) (eventUpper := burnTickUpperCleanWord I)
                            (eventLower := burnTickLowerCleanWord I) (R := [solcSelectorWord I])
                            (σmem := lockedEvm) (pos0 := solcSlotWord lockedEvm I positionBase)
                            (rdata := ByteArray.empty) (cA := cA)
                            (σ := sstoreAccountMap I.codeOwner
                              (sstoreAccountMap I.codeOwner lockedEvm
                                (positionBase + (⟨1⟩ : UInt256)) feeGrowthInside0)
                              (positionBase + (⟨2⟩ : UInt256)) feeGrowthInside1)
                            hpatch hdest9737 _hperm hzero hmload224
                            (by simpa [positionUpdateR, tokensOwed0, tokensOwed1] using hrd21861)
                            hdelta
                            (by simp only [List.length_singleton]; omega)
                        have hlow0 :
                            UInt256.land burnPositionUpdateSlot0Mask
                                (UInt256.div
                                  (uniswapV3PoolFullMathMulDivProd0
                                    (UInt256.sub feeGrowthInside0
                                      (solcSlotWord lockedEvm I
                                        (positionBase + (⟨1⟩ : UInt256))))
                                    (burnPositionUpdateSlot0Packed
                                      (solcSlotWord lockedEvm I positionBase)))
                                  (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)) =
                              UInt256.land burnPositionUpdateSlot0Mask tokensOwed0 := by
                          rfl
                        have hlow1 :
                            UInt256.land burnPositionUpdateSlot0Mask
                                (UInt256.div
                                  (uniswapV3PoolFullMathMulDivProd0
                                    (UInt256.sub feeGrowthInside1
                                      (solcSlotWord lockedEvm I
                                        (positionBase + (⟨2⟩ : UInt256))))
                                    (burnPositionUpdateSlot0Packed
                                      (solcSlotWord lockedEvm I positionBase)))
                                  (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)) =
                              UInt256.land burnPositionUpdateSlot0Mask tokensOwed1 := by
                          simpa [tokensOwed1] using
                            (uniswapV3PoolFullMathMulDivSlowResult_low128_eq_prod0Div128
                              (UInt256.sub feeGrowthInside1
                                (solcSlotWord lockedEvm I
                                  (positionBase + (⟨2⟩ : UInt256))))
                              (burnPositionUpdateSlot0Packed
                                (solcSlotWord lockedEvm I positionBase))).symm
                        exact
                          uniswapV3PoolBurnZeroDeltaPositionUpdateFinish
                            (v := v) (cA := cA) (gh := gh) (bl := bl)
                            (σ_evm := σ_evm) (σ_solm := σ_solm) (σ₀ := σ₀)
                            (lockedEvm := lockedEvm) (lockedSolm := σLockedSolm)
                            (A := A) (I := I) (g := g)
                            (tokensOwed0 := tokensOwed0) (tokensOwed1 := tokensOwed1)
                            (feeGrowthInside0 := feeGrowthInside0)
                            (feeGrowthInside1 := feeGrowthInside1)
                            (positionBase := positionBase) (code := code)
                            hcode hdispatch hdecode hwv hunlockedSolm hcanon hnoDelegate
                            htickLt hLowerMin hUpperMax hzero
                            (by simpa [lockedEvm] using hAccountsAfterLock)
                            (by rfl) (by rfl) (by rfl)
                            (by
                              simpa [positionBase] using
                                burnPositionBaseSlotWord_eq_positionsBase lockedEvm I)
                            (by simpa [positionBase] using hliq)
                            hlow0 hlow1
                            (by
                              simpa [tokensOwed0, tokensOwed1, lockedEvm]
                                using hrdSuccessCases)
                    · obtain ⟨_, _, hrdFeeGrowthEntry⟩ := hrdFeeGrowthInsideEntry hzero
                      exact
                        uniswapV3PoolBurnZeroDeltaPositionUpdateSlowToken0Runtime
                          (v := v) (cA := cA) (gh := gh) (bl := bl)
                          (σ_evm := σ_evm) (σ_solm := σ_solm) (σ₀ := σ₀)
                          (lockedEvm := lockedEvm) (lockedSolm := σLockedSolm)
                          (A := A) (I := I) (g := g) (code := code)
                          hpatch hcode _hperm hdispatch hdecode hwv hunlockedSolm
                          hcanon hnoDelegate htickLt hLowerMin hUpperMax hzero
                          (by simpa [lockedEvm] using hAccountsAfterLock)
                          (by rfl)
                          (by simpa [positionBase] using hliq)
                          (by
                            intro hprod0Zero
                            exact hprod0 (by
                              simpa [feeGrowthInside0, positionBase] using hprod0Zero))
                          (by simpa [lockedEvm, positionBase] using hrdFeeGrowthEntry)
                  · have hnonzeroCond :
                        UInt256.isZero
                          (UInt256.signextend ⟨15⟩
                            (UInt256.signextend ⟨15⟩
                              (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)))) = ⟨0⟩ :=
                      burnLiquidityDeltaNonzeroJumpCond I hcanon hzero
                    obtain ⟨_, _, _hrdAfterTimestamp⟩ :=
                      uniswapV3PoolBurnAfterFeeGlobalsNonzeroToTimestampReturn
                        (v := v) (code := code) (ee := I) (g := Sat256.ofUInt256 g)
                        (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                        (ret := ⟨621⟩) (R := [solcSelectorWord I])
                        (rdata := ByteArray.empty) (cA := cA) (σ := σLockedEvm)
                        hpatch hnonzeroCond hrdFeeGlobalsBranchTest
                        (by simp only [List.length_singleton]; omega)
                    obtain ⟨_, _, _hrdSlot0Liquidity⟩ :=
                      uniswapV3PoolBurnAfterFeeGlobalsNonzeroTimestampToSlot0LiquidityLoaded
                        (v := v) (code := code) (ee := I) (g := Sat256.ofUInt256 g)
                        (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                        (ret := ⟨621⟩) (R := [solcSelectorWord I])
                        (rdata := ByteArray.empty) (cA := cA) (σ := σLockedEvm)
                        hpatch _hrdAfterTimestamp
                        (by simp only [List.length_singleton]; omega)
                    obtain ⟨_, _, _hrdObserveSingleEntry⟩ :=
                      uniswapV3PoolBurnAfterFeeGlobalsNonzeroSlot0LiquidityToObserveSingleEntry
                        (v := v) (code := code) (ee := I) (g := Sat256.ofUInt256 g)
                        (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                        (ret := ⟨621⟩) (R := [solcSelectorWord I])
                        (rdata := ByteArray.empty) (cA := cA) (σ := σLockedEvm)
                        hpatch _hrdSlot0Liquidity
                        (by simp only [List.length_singleton]; omega)
                    obtain ⟨_, _, _hrdObserveSingleZero⟩ :=
                      uniswapV3PoolBurnObserveSingleSecondsAgoZeroFallthrough
                        (v := v) (code := code) (ee := I) (g := Sat256.ofUInt256 g)
                        (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                        (memPtr := ⟨8⟩) (ret := ⟨19273⟩)
                        (R :=
                          ⟨0⟩ :: ⟨0⟩ :: UInt256.ofNat I.header.timestamp ::
                          ⟨0⟩ :: ⟨0⟩ ::
                          solcSlotWord σLockedEvm I ⟨2⟩ ::
                          solcSlotWord σLockedEvm I ⟨1⟩ ::
                          burnPositionBaseSlotWord σLockedEvm I ::
                          slot0TickReturnWord σLockedEvm I ::
                          UInt256.signextend ⟨15⟩
                            (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)) ::
                          UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I) ::
                          UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I) ::
                          UInt256.ofNat I.source.val :: ⟨16428⟩ :: ⟨256⟩ ::
                          ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
                          ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
                          burnAmountCleanWord I :: burnTickUpperCleanWord I ::
                          burnTickLowerCleanWord I :: ⟨621⟩ :: [solcSelectorWord I])
                        (mem := burnPositionKeyMappingMem σLockedEvm I)
                        (aw := UInt256.ofNat 18)
                        (rdata := ByteArray.empty) (cA := cA) (σ := σLockedEvm)
                        hpatch _hrdObserveSingleEntry
                        (by simp only [List.length_cons, List.length_nil]; omega)
                    by_cases hobsBound :
                        (slot0ObservationIndexWord σLockedEvm I).toNat < 65535
                    · have hidxLt16 :
                          (slot0ObservationIndexWord σLockedEvm I).toNat < EVM.twoPow 16 := by
                        simpa [slot0ObservationIndexWord] using
                          slot0Uint16Mask_bound
                            (UInt256.div (slot0SlotWord σLockedEvm I) (slot0ShiftBytes 23))
                      have hmaskIndex :
                          UInt256.land (⟨65535⟩ : UInt256)
                              (slot0ObservationIndexWord σLockedEvm I) =
                            slot0ObservationIndexWord σLockedEvm I := by
                        rw [show (⟨65535⟩ : UInt256) = slot0Uint16Mask by native_decide]
                        exact slot0Uint16Mask_clean_left hidxLt16
                      have hlt :
                          UInt256.lt
                              ((⟨65535⟩ : UInt256).land
                                (slot0ObservationIndexWord σLockedEvm I))
                              ⟨65535⟩ = ⟨1⟩ := by
                        rw [hmaskIndex]
                        apply ult_one
                        rw [show (⟨65535⟩ : UInt256).toNat = 65535 by native_decide]
                        exact hobsBound
                      obtain ⟨_, _, _hrdObserveSingleInBounds⟩ :=
                        uniswapV3PoolBurnObserveSingleIndexInBoundsJump
                          (v := v) (code := code) (ee := I)
                          (g := Sat256.ofUInt256 g)
                          (s0 := initState cA gh bl σ_evm σ₀
                            (Sat256.ofUInt256 g) A I)
                          hpatch _hrdObserveSingleZero
                          (by
                            have hlt' :
                                UInt256.lt
                                    ((⟨65535⟩ : UInt256).land
                                      ((⟨65535⟩ : UInt256).land
                                        ((solcSlotWord σLockedEvm I ⟨0⟩).div
                                          ((⟨1⟩ : UInt256).shiftLeft ⟨184⟩))))
                                    ⟨65535⟩ = ⟨1⟩ := by
                              simpa [slot0ObservationIndexWord, slot0SlotWord,
                                slot0Uint16Mask, u256_land_comm] using hlt
                            rw [hlt']
                            decide)
                          (by simp only [List.length_cons, List.length_nil]; omega)
                      obtain ⟨_, _, _hrdObserveSingleLoaded⟩ :=
                        uniswapV3PoolBurnObserveSingleLoadObservation
                          (v := v) (code := code) (ee := I)
                          (g := Sat256.ofUInt256 g)
                          (s0 := initState cA gh bl σ_evm σ₀
                            (Sat256.ofUInt256 g) A I)
                          (σ := σLockedEvm) hpatch _hrdObserveSingleInBounds
                          (by simp only [List.length_cons, List.length_nil]; omega)
                      let obsWord := burnObserveSingleLoadedObsWord σLockedEvm I
                      have hobsWord :
                          obsWord = burnObserveSingleSlotWord σLockedEvm I := by
                        simpa [obsWord] using
                          burnObserveSingleLoadedObsWord_eq σLockedEvm I hidxLt16
                      have hsourceObserveStepOfEq := fun (heq : UInt256.eq
                          (UInt256.land (UInt256.ofNat I.header.timestamp)
                            observationsUint32Mask)
                          (burnObserveSingleDecodedBlockWord obsWord) ≠ ⟨0⟩) =>
                        uniswapV3PoolModifyPositionSourceObserveSingleTimestampEqualStep
                          (v := v) (cA := cA) (gh := gh) (bl := bl)
                          (σ := σLockedSolm) (σ₀ := σ₀) (A := A) (I := I)
                          (g := Sat256.ofUInt256 g)
                          (by
                            rw [← burnObserveSingleObservationIndexWord_transport
                              hAccountsAfterLock]
                            exact hobsBound)
                          (burnObserveSingleSourceTimestampEqOfGuard
                            hAccountsAfterLock hobsWord heq)
                      have hrdLowerTickUpdateEntryOfEq := fun (heq : UInt256.eq
                          (UInt256.land (UInt256.ofNat I.header.timestamp)
                            observationsUint32Mask)
                          (burnObserveSingleDecodedBlockWord obsWord) ≠ ⟨0⟩) =>
                        uniswapV3PoolBurnObserveSingleTimestampEqualToLowerTickUpdate
                          (v := v) (code := code) (ee := I)
                          (g := Sat256.ofUInt256 g)
                          (s0 := initState cA gh bl σ_evm σ₀
                            (Sat256.ofUInt256 g) A I)
                          (obsWord := obsWord)
                          (time := UInt256.ofNat I.header.timestamp)
                          (callerTime := UInt256.ofNat I.header.timestamp)
                          (rdata := ByteArray.empty) (cA := cA) (σ := σLockedEvm)
                          hpatch
                          (by simpa [obsWord, burnObserveSingleLoadedObsWord]
                            using _hrdObserveSingleLoaded)
                          heq
                          (by simp only [List.length_cons, List.length_nil]; omega)
                      have hrdLiquidityAddDeltaEntryOfEq := fun (heq : UInt256.eq
                          (UInt256.land (UInt256.ofNat I.header.timestamp)
                            observationsUint32Mask)
                          (burnObserveSingleDecodedBlockWord obsWord) ≠ ⟨0⟩) =>
                        Exists.elim (hrdLowerTickUpdateEntryOfEq heq) fun _ hk =>
                        Exists.elim hk fun _ hrdLowerTickUpdateEntry =>
                        uniswapV3PoolBurnTickUpdateLowerToLiquidityAddDelta
                          (v := v) (code := code) (ee := I) (g := Sat256.ofUInt256 g)
                          (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                          (rdata := ByteArray.empty) (cA := cA) (σ := σLockedEvm) hpatch hrdLowerTickUpdateEntry
                          (by
                            rw [burnObserveSingleDecodedMem_size σLockedEvm I obsWord]
                            native_decide)
                          (by simp only [List.length_cons, List.length_nil]; omega)
                      exact uniswapV3PoolBurnLowerLiquidityAddDeltaBranch hpatch hcode hwv hdispatch hdecode hunlockedSolm hcanon hnoDelegate htickLt hLowerMin hUpperMax hzero hAccountsAfterLock hobsBound hobsWord hrdLiquidityAddDeltaEntryOfEq
                    · have hoobEvm :
                          65535 ≤ (slot0ObservationIndexWord σLockedEvm I).toNat :=
                        Nat.le_of_not_gt hobsBound
                      have hidxLt16 :
                          (slot0ObservationIndexWord σLockedEvm I).toNat < EVM.twoPow 16 := by
                        simpa [slot0ObservationIndexWord] using
                          slot0Uint16Mask_bound
                            (UInt256.div (slot0SlotWord σLockedEvm I) (slot0ShiftBytes 23))
                      have hmaskIndex :
                          UInt256.land (⟨65535⟩ : UInt256)
                              (slot0ObservationIndexWord σLockedEvm I) =
                            slot0ObservationIndexWord σLockedEvm I := by
                        rw [show (⟨65535⟩ : UInt256) = slot0Uint16Mask by native_decide]
                        exact slot0Uint16Mask_clean_left hidxLt16
                      have hlt :
                          UInt256.lt
                              ((⟨65535⟩ : UInt256).land
                                (slot0ObservationIndexWord σLockedEvm I))
                              ⟨65535⟩ = ⟨0⟩ := by
                        rw [hmaskIndex]
                        apply ult_zero
                        rw [show (⟨65535⟩ : UInt256).toNat = 65535 by native_decide]
                        exact hoobEvm
                      have hinvalidOr :=
                        uniswapV3PoolBurnObserveSingleIndexOobInvalid
                          (v := v) (code := code) (ee := I)
                          (g := Sat256.ofUInt256 g)
                          (s0 := initState cA gh bl σ_evm σ₀
                            (Sat256.ofUInt256 g) A I)
                          hpatch _hrdObserveSingleZero
                          (by
                            simpa [slot0ObservationIndexWord, slot0SlotWord,
                              slot0Uint16Mask, u256_land_comm] using hlt)
                          (by simp only [List.length_cons, List.length_nil]; omega)
                      have hidxEq :
                          slot0ObservationIndexWord σLockedEvm I =
                            slot0ObservationIndexWord σLockedSolm I := by
                        unfold slot0ObservationIndexWord slot0SlotWord
                        rw [solcSlotWord_eq_of_accountMapEquiv hAccountsAfterLock I ⟨0⟩]
                      have hoobSolm :
                          65535 ≤ (slot0ObservationIndexWord σLockedSolm I).toNat := by
                        rw [← hidxEq]
                        exact hoobEvm
                      have hbody := uniswapV3PoolBurnSourceObserveSingleOobReverts
                        (v := v) (cA := cA) (gh := gh) (bl := bl)
                        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                        (g := Sat256.ofUInt256 g) hwv hunlockedSolm hcanon
                        hnoDelegate htickLt hLowerMin hUpperMax hzero
                        (by simpa [σLockedSolm] using hoobSolm)
                      rcases hinvalidOr with hoog | hinvalid
                      · exact reEquiv_outOfGas (Xi_error_of_X (g := g) (by
                          rw [← hcode] at hoog
                          simpa [initState, Sat256.ofUInt256] using hoog))
                      · have hxi :
                            Ξ cA gh bl σ_evm σ₀ g A I =
                              .error .InvalidInstruction :=
                          Xi_error_of_X (g := g) (by
                            rw [← hcode] at hinvalid
                            simpa [initState, Sat256.ofUInt256] using hinvalid)
                        exact reEquiv_execution hdispatch hdecode hbody
                          (execResultsEquiv.invalidHalt hxi rfl)
          · have hzero := burnTickLtSlt_eq_zero I htickLt
            have hrd := uniswapV3PoolBurnCheckTicksLtRevert (v := v) (code := code)
              (ee := I) (g := Sat256.ofUInt256 g)
              (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
              (ret := ⟨16264⟩)
              (R := ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
                ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
                burnAmountCleanWord I :: burnTickUpperCleanWord I ::
                burnTickLowerCleanWord I :: ⟨621⟩ :: [solcSelectorWord I])
              (mem := burnModifyPositionMem4 I) (aw := UInt256.ofNat 8)
              (rdata := ByteArray.empty) (cA := cA)
              (σ := σLockedEvm)
              hpatch hrdCheckTicksWords hzero rfl rfl
              (by simp only [List.length_cons, List.length_nil]; omega)
            have hbody := uniswapV3PoolBurnSourceTickLtReverts (v := v)
              (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
              (A := A) (I := I) (g := Sat256.ofUInt256 g) hwv hunlockedSolm hcanon
              hnoDelegate htickLt
            exact hrd.reEquivExecutionRevert hcode hdispatch hdecode hbody
        · have hnoDelegateZero : uniswapV3PoolNoDelegateCallGuard v I = ⟨0⟩ := by
            by_contra hne
            exact hnoDelegate hne
          have hrd := uniswapV3PoolBurnNoDelegateCallRevert (v := v) (code := code)
            (ee := I) (g := Sat256.ofUInt256 g)
            (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
            (ret := ⟨621⟩) (R := [solcSelectorWord I]) (rdata := ByteArray.empty)
            (cA := cA)
            (σ := σLockedEvm)
            hpatch hrdLiquidityDeltaWritten hnoDelegateZero
            (by simp only [List.length_cons, List.length_nil]; omega)
          have hbody := uniswapV3PoolBurnSourceNoDelegateReverts (v := v)
            (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A)
            (I := I) (g := Sat256.ofUInt256 g) hwv hunlockedSolm hcanon hnoDelegateZero
          exact hrd.reEquivExecutionRevert hcode hdispatch hdecode hbody
      · have hcheck :
            UInt256.eq (burnAmountCleanWord I)
              (UInt256.signextend ⟨15⟩ (burnAmountCleanWord I)) = ⟨0⟩ := by
          apply uInt256_eq_zero_of_ne
          intro heqOne
          exact hcanon (uInt256_eq_one_eq heqOne).symm
        have hrd := uniswapV3PoolBurnLiquidityDeltaInt128Revert (v := v) (code := code)
          (ee := I) (g := Sat256.ofUInt256 g)
          (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
          (ret := ⟨621⟩) (R := [solcSelectorWord I]) (rdata := ByteArray.empty)
          (cA := cA)
          (σ := σLockedEvm)
          hpatch hrdLiquidityDeltaPrep hcheck
          (by simp only [List.length_cons, List.length_nil]; omega)
        have hbody := uniswapV3PoolBurnSourceLiquidityDeltaReverts (v := v)
          (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A)
          (I := I) (g := Sat256.ofUInt256 g) hwv hunlockedSolm hcanon
        exact hrd.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · have hlockedEvm : burnUnlockedByte σ_evm I = ⟨0⟩ := by
        by_contra hne
        exact hunlocked hne
      have hlockedSolm : burnUnlockedByte σ_solm I = ⟨0⟩ := by
        rw [burnUnlockedByte_transport (σ_evm := σ_evm) (σ_solm := σ_solm)
          hAccounts]
        exact hlockedEvm
      have hbody := uniswapV3PoolBurnSourceLockedReverts (v := v)
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hwv hlockedSolm
      have hrd := uniswapV3PoolBurnLockEnterLockedRevert (v := v) (code := code)
        (ee := I) (g := Sat256.ofUInt256 g)
        (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (amount := burnAmountCleanWord I) (upper := burnTickUpperCleanWord I)
        (lower := burnTickLowerCleanWord I) (ret := ⟨621⟩) (R := [solcSelectorWord I])
        (rdata := ByteArray.empty) (cA := cA) (σ := σ_evm)
        hpatch hrdModifyPosition hlockedEvm
        (by simp only [List.length_cons, List.length_nil]; omega)
      exact hrd.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · have hshort : I.calldata.size < 100 := by omega
    have hdecode := uniswapV3PoolBurnDecodeShort (v := v) (I := I) hshort
    have hrd := uniswapV3PoolBurnEvmDecodeShort (v := v) (code := code)
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g) hpatch hcode hwv hsz hsize hsel hshort
    exact hrd.reEquivDecodingFailed hcode hdispatch hdecode

end Benchmarks.UniswapV3Pool
