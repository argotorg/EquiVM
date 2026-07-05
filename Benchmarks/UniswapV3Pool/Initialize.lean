import Benchmarks.UniswapV3Pool.InitializeSourceGetTickPostLog

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.UniswapV3Pool

theorem uniswapV3PoolInitializeBodyCore {v : PoolImmutables}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsel : (uniswapV3PoolSelBytes 25 == I.calldata.extract 0 4) = true) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdispatch := uniswapV3PoolDispatch_initialize (v := v) (cd := I.calldata) hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · have hdecode := uniswapV3PoolInitializeDecodeOk (v := v) (I := I) hsz36
    by_cases hnz : slot0SqrtPriceX96Word σ_evm I ≠ ⟨0⟩
    · have hnzSolm : slot0SqrtPriceX96Word σ_solm I ≠ ⟨0⟩ := by
        rw [slot0SqrtPriceX96Word_transport (σ_evm := σ_evm) (σ_solm := σ_solm)
          hAccounts]
        exact hnz
      have hbody := uniswapV3PoolInitializeSourceAlreadyInitializedReverts (v := v)
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hwv hnzSolm
      have hrd := uniswapV3PoolInitializeEvmAlreadyInitialized (v := v) (code := code)
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hpatch hcode hwv hsz hsize hsel hsz36 hnz
      exact hrd.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · have hzeroEvm : slot0SqrtPriceX96Word σ_evm I = ⟨0⟩ := by
        by_contra hne
        exact hnz hne
      have hzeroSolm : slot0SqrtPriceX96Word σ_solm I = ⟨0⟩ := by
        rw [slot0SqrtPriceX96Word_transport (σ_evm := σ_evm) (σ_solm := σ_solm)
          hAccounts]
        exact hzeroEvm
      have hsourceGuard := uniswapV3PoolInitializeEvalSqrtPriceX96EqZeroTrue (v := v)
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hzeroSolm
      have hreachEntry := uniswapV3PoolInitializeReachEntry (v := v) (code := code)
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hpatch hcode hwv hsz hsize hsel
      obtain ⟨_, _, hlenOk⟩ :=
        uniswapV3PoolInitializeExternalLenOk (v := v) (code := code)
          (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
          (I := I) (g := Sat256.ofUInt256 g) hpatch hreachEntry hsz36 hsize
      obtain ⟨_, _, hbodyEntry⟩ :=
        uniswapV3PoolInitializeDecodedReachRoutine (v := v) (code := code)
          (ee := I) (g := Sat256.ofUInt256 g)
          (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
          (ret := ⟨857⟩) (R := [solcSelectorWord I]) (mem := solcFreePtrMem)
          (aw := UInt256.ofNat 3) (rdata := ByteArray.empty) (acc := (cA, σ_evm))
          hpatch hlenOk (by simp only [List.length_singleton]; omega)
      obtain ⟨_, _, hgetTickEntry⟩ :=
        uniswapV3PoolInitializeReachGetTickAtSqrtRatio (v := v) (code := code)
          (ee := I) (g := Sat256.ofUInt256 g)
          (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
          (ret := ⟨857⟩) (R := [solcSelectorWord I]) (mem := solcFreePtrMem)
          (aw := UInt256.ofNat 3) (rdata := ByteArray.empty) (acc := (cA, σ_evm))
          hpatch hbodyEntry hzeroEvm (by simp only [List.length_singleton]; omega)
      by_cases hlo : (initializeArgWord I).toNat < 4295128739
      · have hbody := uniswapV3PoolInitializeSourceGetTickLowReverts (v := v)
          (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A)
          (I := I) (g := Sat256.ofUInt256 g) hwv hzeroSolm hlo
        have hrd := uniswapV3PoolGetTickAtSqrtRatioLowerRevert (v := v) (code := code)
          (ee := I) (g := Sat256.ofUInt256 g)
          (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
          (ret := ⟨857⟩) (R := [solcSelectorWord I]) (rdata := ByteArray.empty)
          (acc := (cA, σ_evm)) hpatch hgetTickEntry hlo
          (by simp only [List.length_singleton]; omega)
        exact hrd.reEquivExecutionRevert hcode hdispatch hdecode hbody
      · have hloOk : 4295128739 ≤ (initializeArgWord I).toNat := Nat.not_lt.mp hlo
        by_cases hhi :
            1461446703485210103287273052203988822378723970342 ≤
              (initializeArgWord I).toNat
        · have hbody := uniswapV3PoolInitializeSourceGetTickHighReverts (v := v)
            (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A)
            (I := I) (g := Sat256.ofUInt256 g) hwv hzeroSolm hhi
          have hrd := uniswapV3PoolGetTickAtSqrtRatioUpperRevert (v := v) (code := code)
            (ee := I) (g := Sat256.ofUInt256 g)
            (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
            (ret := ⟨857⟩) (R := [solcSelectorWord I]) (rdata := ByteArray.empty)
            (acc := (cA, σ_evm)) hpatch hgetTickEntry hloOk hhi
            (by simp only [List.length_singleton]; omega)
          exact hrd.reEquivExecutionRevert hcode hdispatch hdecode hbody
        · have hhiOk :
              (initializeArgWord I).toNat <
                1461446703485210103287273052203988822378723970342 :=
            Nat.lt_of_not_ge hhi
          have hsourceRange := uniswapV3PoolGetTickAtSqrtRatioEvalRangeTrue (v := v)
            (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (I := I) hloOk hhiOk
          obtain ⟨_, _, hrangeOk⟩ :=
            uniswapV3PoolGetTickAtSqrtRatioRangeOk (v := v) (code := code)
              (ee := I) (g := Sat256.ofUInt256 g)
              (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
              (ret := ⟨857⟩) (R := [solcSelectorWord I]) (rdata := ByteArray.empty)
              (acc := (cA, σ_evm)) hpatch hgetTickEntry hloOk hhiOk
              (by simp only [List.length_singleton]; omega)
          obtain ⟨_, _, hmsb7⟩ :=
            uniswapV3PoolGetTickAtSqrtRatioMsbStep7 (v := v) (code := code)
              (ee := I) (g := Sat256.ofUInt256 g)
              (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
              (ret := ⟨857⟩) (R := [solcSelectorWord I]) (rdata := ByteArray.empty)
              (acc := (cA, σ_evm)) hpatch hrangeOk
              (by simp only [List.length_singleton]; omega)
          obtain ⟨_, _, hmsb6⟩ :=
            uniswapV3PoolGetTickAtSqrtRatioMsbStep6 (v := v) (code := code)
              (ee := I) (g := Sat256.ofUInt256 g)
              (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
              (ret := ⟨857⟩) (R := [solcSelectorWord I]) (rdata := ByteArray.empty)
              (acc := (cA, σ_evm)) hpatch hmsb7
              (by simp only [List.length_singleton]; omega)
          obtain ⟨_, _, hmsb5⟩ :=
            uniswapV3PoolGetTickAtSqrtRatioMsbStep5 (v := v) (code := code)
              (ee := I) (g := Sat256.ofUInt256 g)
              (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
              (ret := ⟨857⟩) (R := [solcSelectorWord I]) (rdata := ByteArray.empty)
              (acc := (cA, σ_evm)) hpatch hmsb6
              (by simp only [List.length_singleton]; omega)
          obtain ⟨_, _, hmsb4⟩ :=
            uniswapV3PoolGetTickAtSqrtRatioMsbStep4 (v := v) (code := code)
              (ee := I) (g := Sat256.ofUInt256 g)
              (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
              (ret := ⟨857⟩) (R := [solcSelectorWord I]) (rdata := ByteArray.empty)
              (acc := (cA, σ_evm)) hpatch hmsb5
              (by simp only [List.length_singleton]; omega)
          obtain ⟨_, _, hmsb3⟩ :=
            uniswapV3PoolGetTickAtSqrtRatioMsbStep3 (v := v) (code := code)
              (ee := I) (g := Sat256.ofUInt256 g)
              (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
              (ret := ⟨857⟩) (R := [solcSelectorWord I]) (rdata := ByteArray.empty)
              (acc := (cA, σ_evm)) hpatch hmsb4
              (by simp only [List.length_singleton]; omega)
          obtain ⟨_, _, hmsb2⟩ :=
            uniswapV3PoolGetTickAtSqrtRatioMsbStep2 (v := v) (code := code)
              (ee := I) (g := Sat256.ofUInt256 g)
              (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
              (ret := ⟨857⟩) (R := [solcSelectorWord I]) (rdata := ByteArray.empty)
              (acc := (cA, σ_evm)) hpatch hmsb3
              (by simp only [List.length_singleton]; omega)
          obtain ⟨_, _, hmsb1⟩ :=
            uniswapV3PoolGetTickAtSqrtRatioMsbStep1 (v := v) (code := code)
              (ee := I) (g := Sat256.ofUInt256 g)
              (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
              (ret := ⟨857⟩) (R := [solcSelectorWord I]) (rdata := ByteArray.empty)
              (acc := (cA, σ_evm)) hpatch hmsb2
              (by simp only [List.length_singleton]; omega)
          obtain ⟨_, _, hmsb⟩ :=
            uniswapV3PoolGetTickAtSqrtRatioMsbCombine (v := v) (code := code)
              (ee := I) (g := Sat256.ofUInt256 g)
              (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
              (ret := ⟨857⟩) (R := [solcSelectorWord I]) (rdata := ByteArray.empty)
              (acc := (cA, σ_evm)) hpatch hmsb1
              (by simp only [List.length_singleton]; omega)
          obtain ⟨_, _, hnormR⟩ :=
            uniswapV3PoolGetTickAtSqrtRatioNormalizeR (v := v) (code := code)
              (ee := I) (g := Sat256.ofUInt256 g)
              (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
              (ret := ⟨857⟩) (R := [solcSelectorWord I]) (rdata := ByteArray.empty)
              (acc := (cA, σ_evm)) hpatch hmsb
              (by simp only [List.length_singleton]; omega)
          obtain ⟨_, _, hlog63⟩ :=
            uniswapV3PoolGetTickAtSqrtRatioLogStep63 (v := v) (code := code)
              (ee := I) (g := Sat256.ofUInt256 g)
              (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
              (ret := ⟨857⟩) (R := [solcSelectorWord I]) (rdata := ByteArray.empty)
              (acc := (cA, σ_evm)) hpatch hnormR
              (by simp only [List.length_singleton]; omega)
          obtain ⟨_, _, hlog62⟩ :=
            uniswapV3PoolGetTickAtSqrtRatioLogStep62 (v := v) (code := code)
              (ee := I) (g := Sat256.ofUInt256 g)
              (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
              (ret := ⟨857⟩) (R := [solcSelectorWord I]) (rdata := ByteArray.empty)
              (acc := (cA, σ_evm)) hpatch hlog63
              (by simp only [List.length_singleton]; omega)
          obtain ⟨_, _, hlog61⟩ :=
            uniswapV3PoolGetTickAtSqrtRatioLogStep61 (v := v) (code := code)
              (ee := I) (g := Sat256.ofUInt256 g)
              (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
              (ret := ⟨857⟩) (R := [solcSelectorWord I]) (rdata := ByteArray.empty)
              (acc := (cA, σ_evm)) hpatch hlog62
              (by simp only [List.length_singleton]; omega)
          obtain ⟨_, _, hlog60⟩ :=
            uniswapV3PoolGetTickAtSqrtRatioLogStep60 (v := v) (code := code)
              (ee := I) (g := Sat256.ofUInt256 g)
              (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
              (ret := ⟨857⟩) (R := [solcSelectorWord I]) (rdata := ByteArray.empty)
              (acc := (cA, σ_evm)) hpatch hlog61
              (by simp only [List.length_singleton]; omega)
          obtain ⟨_, _, hlog59⟩ :=
            uniswapV3PoolGetTickAtSqrtRatioLogStep59 (v := v) (code := code)
              (ee := I) (g := Sat256.ofUInt256 g)
              (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
              (ret := ⟨857⟩) (R := [solcSelectorWord I]) (rdata := ByteArray.empty)
              (acc := (cA, σ_evm)) hpatch hlog60
              (by simp only [List.length_singleton]; omega)
          obtain ⟨_, _, hlog58⟩ :=
            uniswapV3PoolGetTickAtSqrtRatioLogStep58 (v := v) (code := code)
              (ee := I) (g := Sat256.ofUInt256 g)
              (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
              (ret := ⟨857⟩) (R := [solcSelectorWord I]) (rdata := ByteArray.empty)
              (acc := (cA, σ_evm)) hpatch hlog59
              (by simp only [List.length_singleton]; omega)
          obtain ⟨_, _, hlog57⟩ :=
            uniswapV3PoolGetTickAtSqrtRatioLogStep57 (v := v) (code := code)
              (ee := I) (g := Sat256.ofUInt256 g)
              (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
              (ret := ⟨857⟩) (R := [solcSelectorWord I]) (rdata := ByteArray.empty)
              (acc := (cA, σ_evm)) hpatch hlog58
              (by simp only [List.length_singleton]; omega)
          obtain ⟨_, _, hlog56⟩ :=
            uniswapV3PoolGetTickAtSqrtRatioLogStep56 (v := v) (code := code)
              (ee := I) (g := Sat256.ofUInt256 g)
              (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
              (ret := ⟨857⟩) (R := [solcSelectorWord I]) (rdata := ByteArray.empty)
              (acc := (cA, σ_evm)) hpatch hlog57
              (by simp only [List.length_singleton]; omega)
          obtain ⟨_, _, hlog55⟩ :=
            uniswapV3PoolGetTickAtSqrtRatioLogStep55 (v := v) (code := code)
              (ee := I) (g := Sat256.ofUInt256 g)
              (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
              (ret := ⟨857⟩) (R := [solcSelectorWord I]) (rdata := ByteArray.empty)
              (acc := (cA, σ_evm)) hpatch hlog56
              (by simp only [List.length_singleton]; omega)
          obtain ⟨_, _, hlog54⟩ :=
            uniswapV3PoolGetTickAtSqrtRatioLogStep54 (v := v) (code := code)
              (ee := I) (g := Sat256.ofUInt256 g)
              (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
              (ret := ⟨857⟩) (R := [solcSelectorWord I]) (rdata := ByteArray.empty)
              (acc := (cA, σ_evm)) hpatch hlog55
              (by simp only [List.length_singleton]; omega)
          obtain ⟨_, _, hlog53⟩ :=
            uniswapV3PoolGetTickAtSqrtRatioLogStep53 (v := v) (code := code)
              (ee := I) (g := Sat256.ofUInt256 g)
              (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
              (ret := ⟨857⟩) (R := [solcSelectorWord I]) (rdata := ByteArray.empty)
              (acc := (cA, σ_evm)) hpatch hlog54
              (by simp only [List.length_singleton]; omega)
          obtain ⟨_, _, hlog52⟩ :=
            uniswapV3PoolGetTickAtSqrtRatioLogStep52 (v := v) (code := code)
              (ee := I) (g := Sat256.ofUInt256 g)
              (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
              (ret := ⟨857⟩) (R := [solcSelectorWord I]) (rdata := ByteArray.empty)
              (acc := (cA, σ_evm)) hpatch hlog53
              (by simp only [List.length_singleton]; omega)
          obtain ⟨_, _, hlog51⟩ :=
            uniswapV3PoolGetTickAtSqrtRatioLogStep51 (v := v) (code := code)
              (ee := I) (g := Sat256.ofUInt256 g)
              (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
              (ret := ⟨857⟩) (R := [solcSelectorWord I]) (rdata := ByteArray.empty)
              (acc := (cA, σ_evm)) hpatch hlog52
              (by simp only [List.length_singleton]; omega)
          obtain ⟨_, _, hlog2_57⟩ :=
            uniswapV3PoolGetTickAtSqrtRatioLog2Bits63To57 (v := v) (code := code)
              (ee := I) (g := Sat256.ofUInt256 g)
              (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
              (ret := ⟨857⟩) (R := [solcSelectorWord I]) (rdata := ByteArray.empty)
              (acc := (cA, σ_evm)) hpatch hlog51
              (by simp only [List.length_singleton]; omega)
          obtain ⟨_, _, hlog2_50⟩ :=
            uniswapV3PoolGetTickAtSqrtRatioLog2Bits56To50 (v := v) (code := code)
              (ee := I) (g := Sat256.ofUInt256 g)
              (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
              (ret := ⟨857⟩) (R := [solcSelectorWord I]) (rdata := ByteArray.empty)
              (acc := (cA, σ_evm)) hpatch hlog2_57
              (by simp only [List.length_singleton]; omega)
          obtain ⟨_, _, htickSetup⟩ :=
            uniswapV3PoolGetTickAtSqrtRatioTickEstimateSetup (v := v) (code := code)
              (ee := I) (g := Sat256.ofUInt256 g)
              (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
              (ret := ⟨857⟩) (R := [solcSelectorWord I]) (rdata := ByteArray.empty)
              (acc := (cA, σ_evm)) hpatch hlog2_50
              (by simp only [List.length_singleton]; omega)
          have htickEstimateIfSqrtOk :
              getSqrtRatioAbsTickInRangeWord
                  (getSqrtRatioAbsTickBranchWord (getTickHiWord I)) ≠ ⟨0⟩ →
                getSqrtRatioAfterAllBitsWord
                    (getSqrtRatioAbsTickBranchWord (getTickHiWord I))
                    (getSqrtRatioInitialBranchWord
                      (getSqrtRatioAbsTickBranchWord (getTickHiWord I))) ≠ ⟨0⟩ →
                  ∃ k' C', RD code I (Sat256.ofUInt256 g)
                    (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨10793⟩
                    (getTickEstimatedWord I :: ⟨0⟩ :: initializeArgWord I :: ⟨857⟩ ::
                      [solcSelectorWord I])
                    solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k' C' := by
            intro hok hratio
            exact uniswapV3PoolGetTickAtSqrtRatioReturnTickEstimate (v := v)
              (code := code) (ee := I) (g := Sat256.ofUInt256 g)
              (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
              (ret := ⟨857⟩) (R := [solcSelectorWord I]) (rdata := ByteArray.empty)
              (acc := (cA, σ_evm)) hpatch htickSetup hok hratio
              (by simp only [List.length_singleton]; omega)
          have hobsEntryIfSqrtOk :
              getSqrtRatioAbsTickInRangeWord
                  (getSqrtRatioAbsTickBranchWord (getTickHiWord I)) ≠ ⟨0⟩ →
                getSqrtRatioAfterAllBitsWord
                    (getSqrtRatioAbsTickBranchWord (getTickHiWord I))
                    (getSqrtRatioInitialBranchWord
                      (getSqrtRatioAbsTickBranchWord (getTickHiWord I))) ≠ ⟨0⟩ →
                  ∃ k' C', RD code I (Sat256.ofUInt256 g)
                    (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨17514⟩
                    (UInt256.ofNat I.header.timestamp :: ⟨8⟩ :: ⟨10817⟩ :: ⟨0⟩ ::
                      ⟨0⟩ :: getTickEstimatedWord I :: initializeArgWord I :: ⟨857⟩ ::
                        [solcSelectorWord I])
                    solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k' C' := by
            intro hok hratio
            obtain ⟨_, _, htickDone⟩ := htickEstimateIfSqrtOk hok hratio
            exact uniswapV3PoolInitializeReachObservationStore (v := v) (code := code)
              (ee := I) (g := Sat256.ofUInt256 g)
              (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
              (tick := getTickEstimatedWord I) (sqrt := initializeArgWord I) (ret := ⟨857⟩)
              (R := [solcSelectorWord I]) (mem := solcFreePtrMem) (aw := UInt256.ofNat 3)
              (rdata := ByteArray.empty) (acc := (cA, σ_evm)) hpatch htickDone
              (by simp only [List.length_singleton]; omega)
          have hobsStoreIfSqrtOk :
              getSqrtRatioAbsTickInRangeWord
                  (getSqrtRatioAbsTickBranchWord (getTickHiWord I)) ≠ ⟨0⟩ →
                getSqrtRatioAfterAllBitsWord
                    (getSqrtRatioAbsTickBranchWord (getTickHiWord I))
                    (getSqrtRatioInitialBranchWord
                      (getSqrtRatioAbsTickBranchWord (getTickHiWord I))) ≠ ⟨0⟩ →
                  ∃ k' C', RD code I (Sat256.ofUInt256 g)
                    (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨10817⟩
                    (⟨1⟩ :: ⟨1⟩ :: ⟨0⟩ :: ⟨0⟩ :: getTickEstimatedWord I ::
                      initializeArgWord I :: ⟨857⟩ :: [solcSelectorWord I])
                    (initializeObservationStoreMem I) (UInt256.ofNat 8) ByteArray.empty
                    (cA, sstoreAccountMap I.codeOwner σ_evm ⟨8⟩
                      (initializeObservationSstoreWord σ_evm I))
                    k' C' := by
            intro hok hratio
            obtain ⟨_, _, hobsEntry⟩ := hobsEntryIfSqrtOk hok hratio
            exact uniswapV3PoolInitializeObservationStore (v := v) (code := code)
              (ee := I) (g := Sat256.ofUInt256 g)
              (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
              (tick := getTickEstimatedWord I) (sqrt := initializeArgWord I) (ret := ⟨857⟩)
              (R := [solcSelectorWord I]) (rdata := ByteArray.empty) (cA := cA)
              (σ := σ_evm) hpatch hobsEntry _hperm
              (by simp only [List.length_singleton]; omega)
          have hslot0EventSetupIfSqrtOk :
              getSqrtRatioAbsTickInRangeWord
                  (getSqrtRatioAbsTickBranchWord (getTickHiWord I)) ≠ ⟨0⟩ →
                getSqrtRatioAfterAllBitsWord
                    (getSqrtRatioAbsTickBranchWord (getTickHiWord I))
                    (getSqrtRatioInitialBranchWord
                      (getSqrtRatioAbsTickBranchWord (getTickHiWord I))) ≠ ⟨0⟩ →
                  ∃ k' C', RD code I (Sat256.ofUInt256 g)
                    (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨10904⟩
                    (⟨0⟩ :: initializeSlot0ObservationCardinalityEventWord :: ⟨0⟩ ::
                      ⟨32⟩ :: initializeSlot0TickEventWord (getTickEstimatedWord I) ::
                        ⟨2⟩ :: initializeSlot0SqrtEventWord (initializeArgWord I) ::
                          initializeSlot0ObservationCardinalityNextEventWord :: ⟨64⟩ ::
                            ⟨1⟩ :: ⟨1⟩ :: ⟨0⟩ :: ⟨0⟩ :: getTickEstimatedWord I ::
                              initializeArgWord I :: ⟨857⟩ :: [solcSelectorWord I])
                    (initializeSlot0EventMem I (initializeArgWord I) (getTickEstimatedWord I))
                    (UInt256.ofNat 15) ByteArray.empty
                    (cA, sstoreAccountMap I.codeOwner σ_evm ⟨8⟩
                      (initializeObservationSstoreWord σ_evm I))
                    k' C' := by
            intro hok hratio
            obtain ⟨_, _, hobsStore⟩ := hobsStoreIfSqrtOk hok hratio
            exact uniswapV3PoolInitializeSlot0EventSetup (v := v) (code := code)
              (ee := I) (g := Sat256.ofUInt256 g)
              (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
              (tick := getTickEstimatedWord I) (sqrt := initializeArgWord I) (ret := ⟨857⟩)
              (R := [solcSelectorWord I]) (rdata := ByteArray.empty)
              (acc := (cA, sstoreAccountMap I.codeOwner σ_evm ⟨8⟩
                (initializeObservationSstoreWord σ_evm I)))
              hpatch hobsStore (by simp only [List.length_singleton]; omega)
          have hslot0StoreIfSqrtOk :
              getSqrtRatioAbsTickInRangeWord
                  (getSqrtRatioAbsTickBranchWord (getTickHiWord I)) ≠ ⟨0⟩ →
                getSqrtRatioAfterAllBitsWord
                    (getSqrtRatioAbsTickBranchWord (getTickHiWord I))
                    (getSqrtRatioInitialBranchWord
                      (getSqrtRatioAbsTickBranchWord (getTickHiWord I))) ≠ ⟨0⟩ →
                  ∃ k' C', RD code I (Sat256.ofUInt256 g)
                    (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨11075⟩
                    (⟨32⟩ :: initializeSlot0SqrtEventWord (initializeArgWord I) ::
                      initializeSlot0TickEventWord (getTickEstimatedWord I) :: ⟨64⟩ ::
                        ⟨1⟩ :: ⟨1⟩ :: ⟨0⟩ :: ⟨0⟩ :: getTickEstimatedWord I ::
                          initializeArgWord I :: ⟨857⟩ :: [solcSelectorWord I])
                    (initializeSlot0EventMem I (initializeArgWord I) (getTickEstimatedWord I))
                    (UInt256.ofNat 15) ByteArray.empty
                    (cA, sstoreAccountMap I.codeOwner
                      (sstoreAccountMap I.codeOwner σ_evm ⟨8⟩
                        (initializeObservationSstoreWord σ_evm I))
                      ⟨0⟩
                      (initializeSlot0SstoreWord
                        (sstoreAccountMap I.codeOwner σ_evm ⟨8⟩
                          (initializeObservationSstoreWord σ_evm I))
                        I (initializeArgWord I) (getTickEstimatedWord I)))
                    k' C' := by
            intro hok hratio
            obtain ⟨_, _, hslot0EventSetup⟩ := hslot0EventSetupIfSqrtOk hok hratio
            exact uniswapV3PoolInitializeSlot0Store (v := v) (code := code)
              (ee := I) (g := Sat256.ofUInt256 g)
              (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
              (tick := getTickEstimatedWord I) (sqrt := initializeArgWord I) (ret := ⟨857⟩)
              (R := [solcSelectorWord I]) (rdata := ByteArray.empty) (cA := cA)
              (σ := sstoreAccountMap I.codeOwner σ_evm ⟨8⟩
                (initializeObservationSstoreWord σ_evm I))
              hpatch hslot0EventSetup _hperm
              (by simp only [List.length_singleton]; omega)
          have hrdSuccessIfSqrtOk :
              getSqrtRatioAbsTickInRangeWord
                  (getSqrtRatioAbsTickBranchWord (getTickHiWord I)) ≠ ⟨0⟩ →
                getSqrtRatioAfterAllBitsWord
                    (getSqrtRatioAbsTickBranchWord (getTickHiWord I))
                    (getSqrtRatioInitialBranchWord
                      (getSqrtRatioAbsTickBranchWord (getTickHiWord I))) ≠ ⟨0⟩ →
                  RDret code (Sat256.ofUInt256 g)
                    (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                    (cA, sstoreAccountMap I.codeOwner
                      (sstoreAccountMap I.codeOwner σ_evm ⟨8⟩
                        (initializeObservationSstoreWord σ_evm I))
                      ⟨0⟩
                      (initializeSlot0SstoreWord
                        (sstoreAccountMap I.codeOwner σ_evm ⟨8⟩
                          (initializeObservationSstoreWord σ_evm I))
                        I (initializeArgWord I) (getTickEstimatedWord I)))
                    ByteArray.empty := by
            intro hok hratio
            obtain ⟨_, _, hslot0Store⟩ := hslot0StoreIfSqrtOk hok hratio
            exact uniswapV3PoolInitializeSlot0LogAndReturn (v := v) (code := code)
              (ee := I) (g := Sat256.ofUInt256 g)
              (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
              (tick := getTickEstimatedWord I) (sqrt := initializeArgWord I)
              (R := [solcSelectorWord I]) (rdata := ByteArray.empty) (cA := cA)
              (σ := sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner σ_evm ⟨8⟩
                  (initializeObservationSstoreWord σ_evm I))
                ⟨0⟩
                (initializeSlot0SstoreWord
                  (sstoreAccountMap I.codeOwner σ_evm ⟨8⟩
                    (initializeObservationSstoreWord σ_evm I))
                  I (initializeArgWord I) (getTickEstimatedWord I)))
              hpatch hslot0Store _hperm
              (by simp only [List.length_singleton]; omega)
          sorry
  · have hshort : I.calldata.size < 36 := by omega
    have hdecode := uniswapV3PoolInitializeDecodeShort (v := v) (I := I) hshort
    have hrd := uniswapV3PoolInitializeEvmDecodeShort (v := v) (code := code)
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g) hpatch hcode hwv hsz hsize hsel hshort
    exact hrd.reEquivDecodingFailed hcode hdispatch hdecode

end Benchmarks.UniswapV3Pool
