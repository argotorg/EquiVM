import Benchmarks.UniswapV3Pool.BurnTickUpdateTrace

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.UniswapV3Pool

abbrev burnLowerLiquidityAddDeltaTickLower (I : ExecutionEnv) : UInt256 :=
  UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I)

abbrev burnLowerLiquidityAddDeltaTickUpper (I : ExecutionEnv) : UInt256 :=
  UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I)

abbrev burnLowerLiquidityAddDeltaY (I : ExecutionEnv) : UInt256 :=
  UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord I))

abbrev burnLowerLiquidityAddDeltaX (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  burnTickUpdateLowerLiquidityGrossBeforeWordEvm σ I
    (burnLowerLiquidityAddDeltaTickLower I)

noncomputable abbrev burnLowerLiquidityAddDeltaTail (v : PoolImmutables) (σ : AccountMap)
    (I : ExecutionEnv) (obsWord : UInt256) : List UInt256 :=
  burnTickUpdateLowerBaseSlotWord (burnLowerLiquidityAddDeltaTickLower I) ::
  ⟨0⟩ :: EVM.wordOfInt v.maxLiquidityPerTick :: ⟨0⟩ ::
  UInt256.ofNat I.header.timestamp ::
  burnObserveSingleDecodedTickWord obsWord ::
  burnObserveSingleDecodedSecondsWord obsWord ::
  solcSlotWord σ I ⟨2⟩ ::
  solcSlotWord σ I ⟨1⟩ ::
  burnLowerLiquidityAddDeltaY I ::
  slot0TickReturnWord σ I ::
  burnLowerLiquidityAddDeltaTickLower I ::
  ⟨5⟩ :: ⟨19331⟩ ::
  burnObserveSingleDecodedSecondsWord obsWord ::
  burnObserveSingleDecodedTickWord obsWord ::
  UInt256.ofNat I.header.timestamp :: ⟨0⟩ :: ⟨0⟩ ::
  solcSlotWord σ I ⟨2⟩ ::
  solcSlotWord σ I ⟨1⟩ ::
  burnPositionBaseSlotWord σ I ::
  slot0TickReturnWord σ I ::
  burnLowerLiquidityAddDeltaY I ::
  burnLowerLiquidityAddDeltaTickUpper I ::
  burnLowerLiquidityAddDeltaTickLower I ::
  UInt256.ofNat I.source.val :: ⟨16428⟩ :: ⟨256⟩ ::
  ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
  ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
  burnAmountCleanWord I :: burnTickUpperCleanWord I ::
  burnTickLowerCleanWord I :: ⟨621⟩ :: [solcSelectorWord I]

noncomputable abbrev burnLowerLiquidityAddDeltaEntryStack (v : PoolImmutables) (σ : AccountMap)
    (I : ExecutionEnv) (obsWord : UInt256) : List UInt256 :=
  burnLowerLiquidityAddDeltaY I ::
  burnLowerLiquidityAddDeltaX σ I ::
  ⟨20838⟩ :: ⟨0⟩ ::
  burnLowerLiquidityAddDeltaX σ I ::
  burnLowerLiquidityAddDeltaTail v σ I obsWord

noncomputable abbrev burnLowerLiquidityAddDeltaReturnStack (v : PoolImmutables) (σ : AccountMap)
    (I : ExecutionEnv) (obsWord : UInt256) : List UInt256 :=
  UInt256.sub (burnLowerLiquidityAddDeltaX σ I)
    (UInt256.sub ⟨0⟩ (burnLowerLiquidityAddDeltaY I)) ::
  ⟨0⟩ ::
  burnLowerLiquidityAddDeltaX σ I ::
  burnLowerLiquidityAddDeltaTail v σ I obsWord

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolBurnLowerLiquidityAddDeltaRevertBranch
    {v : PoolImmutables} {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {code : ByteArray} {σLockedEvm : AccountMap} {obsWord : UInt256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg (contract v) I.calldata = some burnTransition)
    (hdecode :
      decodeCalldataWithMode (config v).abiDecodeMode
        (List.map Param.name burnTransition.params)
        (transitionSignature burnTransition).paramTypes I.calldata = some (burnStore I))
    (hunlockedSolm : burnUnlockedByte σ_solm I ≠ ⟨0⟩)
    (hcanon :
      UInt256.signextend ⟨15⟩ (burnAmountCleanWord I) = burnAmountCleanWord I)
    (hguard : uniswapV3PoolNoDelegateCallGuard v I ≠ ⟨0⟩)
    (htickLt :
      tickSpacingSint24Value (burnTickLowerWord I) <
        tickSpacingSint24Value (burnTickUpperWord I))
    (hge : ¬ tickSpacingSint24Value (burnTickLowerWord I) < (-887272 : Int))
    (hle : ¬ (887272 : Int) < tickSpacingSint24Value (burnTickUpperWord I))
    (hnonzero : burnAmountCleanWord I ≠ ⟨0⟩)
    (hAccountsAfterLock :
      accountMapEquiv σLockedEvm
        (sstoreAccountMap I.codeOwner σ_solm ⟨0⟩ (burnLockedSlotWord σ_solm I)))
    (hobsBound : (slot0ObservationIndexWord σLockedEvm I).toNat < 65535)
    (hobsWord : obsWord = burnObserveSingleSlotWord σLockedEvm I)
    (hrevert :
      ∃ _heq : UInt256.eq
          (UInt256.land (UInt256.ofNat I.header.timestamp) observationsUint32Mask)
          (burnObserveSingleDecodedBlockWord obsWord) ≠ ⟨0⟩,
        ¬ burnTickUpdateLowerLiquidityGrossAfterSubInt
            (sstoreAccountMap I.codeOwner σ_solm ⟨0⟩ (burnLockedSlotWord σ_solm I)) I <
          burnTickUpdateLowerLiquidityGrossBeforeInt
            (sstoreAccountMap I.codeOwner σ_solm ⟨0⟩ (burnLockedSlotWord σ_solm I)) I)
    (hrdEntryOfEq :
      ∀ _heq : UInt256.eq
          (UInt256.land (UInt256.ofNat I.header.timestamp) observationsUint32Mask)
          (burnObserveSingleDecodedBlockWord obsWord) ≠ ⟨0⟩,
        ∃ k' C',
          RD code I (Sat256.ofUInt256 g)
            (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨13807⟩
            (UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)) ::
              burnTickUpdateLowerLiquidityGrossBeforeWordEvm σLockedEvm I
                (UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I)) ::
              ⟨20838⟩ :: ⟨0⟩ ::
              burnTickUpdateLowerLiquidityGrossBeforeWordEvm σLockedEvm I
                (UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I)) ::
              burnTickUpdateLowerBaseSlotWord
                (UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I)) ::
              ⟨0⟩ :: EVM.wordOfInt v.maxLiquidityPerTick :: ⟨0⟩ ::
              UInt256.ofNat I.header.timestamp ::
              burnObserveSingleDecodedTickWord obsWord ::
              burnObserveSingleDecodedSecondsWord obsWord ::
              solcSlotWord σLockedEvm I ⟨2⟩ ::
              solcSlotWord σLockedEvm I ⟨1⟩ ::
              UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)) ::
              slot0TickReturnWord σLockedEvm I ::
              UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I) ::
              ⟨5⟩ :: ⟨19331⟩ ::
              burnObserveSingleDecodedSecondsWord obsWord ::
              burnObserveSingleDecodedTickWord obsWord ::
              UInt256.ofNat I.header.timestamp :: ⟨0⟩ :: ⟨0⟩ ::
              solcSlotWord σLockedEvm I ⟨2⟩ ::
              solcSlotWord σLockedEvm I ⟨1⟩ ::
              burnPositionBaseSlotWord σLockedEvm I ::
              slot0TickReturnWord σLockedEvm I ::
              UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)) ::
              UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I) ::
              UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I) ::
              UInt256.ofNat I.source.val :: ⟨16428⟩ :: ⟨256⟩ ::
              ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
              ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
              burnAmountCleanWord I :: burnTickUpperCleanWord I ::
              burnTickLowerCleanWord I :: ⟨621⟩ :: [solcSelectorWord I])
            (burnTickUpdateLowerHashMem
              (UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I))
              (burnObserveSingleDecodedMem σLockedEvm I obsWord))
            (UInt256.ofNat 21) ByteArray.empty (cA, σLockedEvm) k' C') :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  rcases hrevert with ⟨heq, hdelta⟩
  have hboundSolm :
      (slot0ObservationIndexWord
        (sstoreAccountMap I.codeOwner σ_solm ⟨0⟩ (burnLockedSlotWord σ_solm I)) I).toNat <
        65535 := by
    rw [← burnObserveSingleObservationIndexWord_transport hAccountsAfterLock]
    exact hobsBound
  have hsame :=
    burnObserveSingleSourceTimestampEqOfGuard hAccountsAfterLock hobsWord heq
  have hbody := uniswapV3PoolBurnSourceLowerLiquidityAddDeltaReverts
    (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hwv hunlockedSolm hcanon hguard htickLt hge hle hnonzero hboundSolm hsame hdelta
  have hiff := burnTickUpdateLowerLiquidityAddDeltaEvmCheck_iff
    (σ_evm := σLockedEvm)
    (σ_solm := sstoreAccountMap I.codeOwner σ_solm ⟨0⟩ (burnLockedSlotWord σ_solm I))
    (I := I) hAccountsAfterLock hcanon hnonzero
  have hevmReqNe :
      ¬ UInt256.lt
          (UInt256.land uint128Mask
            (UInt256.sub
              (burnTickUpdateLowerLiquidityGrossBeforeWordEvm σLockedEvm I
                (UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I)))
              (UInt256.sub ⟨0⟩
                (UInt256.signextend ⟨15⟩
                  (UInt256.sub ⟨0⟩ (burnAmountCleanWord I))))))
          (UInt256.land uint128Mask
            (burnTickUpdateLowerLiquidityGrossBeforeWordEvm σLockedEvm I
              (UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I)))) ≠ ⟨0⟩ := by
    intro hreq
    exact hdelta (hiff.mpr hreq)
  have hevmReqEq :
      UInt256.lt
          (UInt256.land uint128Mask
            (UInt256.sub
              (burnTickUpdateLowerLiquidityGrossBeforeWordEvm σLockedEvm I
                (UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I)))
              (UInt256.sub ⟨0⟩
                (UInt256.signextend ⟨15⟩
                  (UInt256.sub ⟨0⟩ (burnAmountCleanWord I))))))
          (UInt256.land uint128Mask
            (burnTickUpdateLowerLiquidityGrossBeforeWordEvm σLockedEvm I
              (UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I)))) = ⟨0⟩ := by
    by_contra hne
    exact hevmReqNe hne
  have hneg := burnLiquidityDeltaNegativeSltJumpCond I hcanon hnonzero
  rcases hrdEntryOfEq heq with ⟨_, _, hrdEntry⟩
  have hrdRevert := uniswapV3PoolLiquidityAddDeltaNegativeRevert
    (v := v) (code := code) (ee := I) (g := Sat256.ofUInt256 g)
    (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
    (obsWord := obsWord)
    (tickLower := UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I))
    (rdata := ByteArray.empty) (cA := cA) (σ := σLockedEvm)
    hpatch hrdEntry hneg hevmReqEq
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact hrdRevert.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem uniswapV3PoolBurnLowerLiquidityAddDeltaReturnRD
    {v : PoolImmutables} {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {code : ByteArray} {σLockedEvm : AccountMap} {obsWord : UInt256} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcanon :
      UInt256.signextend ⟨15⟩ (burnAmountCleanWord I) = burnAmountCleanWord I)
    (hnonzero : burnAmountCleanWord I ≠ ⟨0⟩)
    (hAccountsAfterLock :
      accountMapEquiv σLockedEvm
        (sstoreAccountMap I.codeOwner σ_solm ⟨0⟩ (burnLockedSlotWord σ_solm I)))
    (hdelta :
      burnTickUpdateLowerLiquidityGrossAfterSubInt
          (sstoreAccountMap I.codeOwner σ_solm ⟨0⟩ (burnLockedSlotWord σ_solm I)) I <
        burnTickUpdateLowerLiquidityGrossBeforeInt
          (sstoreAccountMap I.codeOwner σ_solm ⟨0⟩ (burnLockedSlotWord σ_solm I)) I)
    (hrdEntry :
      RD code I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨13807⟩
        (burnLowerLiquidityAddDeltaEntryStack v σLockedEvm I obsWord)
        (burnTickUpdateLowerHashMem (burnLowerLiquidityAddDeltaTickLower I)
          (burnObserveSingleDecodedMem σLockedEvm I obsWord))
        (UInt256.ofNat 21) ByteArray.empty (cA, σLockedEvm) k C) :
    ∃ k' C',
      RD code I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨20838⟩
        (burnLowerLiquidityAddDeltaReturnStack v σLockedEvm I obsWord)
        (burnTickUpdateLowerHashMem (burnLowerLiquidityAddDeltaTickLower I)
          (burnObserveSingleDecodedMem σLockedEvm I obsWord))
        (UInt256.ofNat 21) ByteArray.empty (cA, σLockedEvm) k' C' := by
  have hiff := burnTickUpdateLowerLiquidityAddDeltaEvmCheck_iff
    (σ_evm := σLockedEvm)
    (σ_solm := sstoreAccountMap I.codeOwner σ_solm ⟨0⟩ (burnLockedSlotWord σ_solm I))
    (I := I) hAccountsAfterLock hcanon hnonzero
  have hreq :
      UInt256.lt
        (UInt256.land uint128Mask
          (UInt256.sub (burnLowerLiquidityAddDeltaX σLockedEvm I)
            (UInt256.sub ⟨0⟩ (burnLowerLiquidityAddDeltaY I))))
        (UInt256.land uint128Mask (burnLowerLiquidityAddDeltaX σLockedEvm I)) ≠
        ⟨0⟩ := by
    simpa [burnLowerLiquidityAddDeltaX, burnLowerLiquidityAddDeltaY,
      burnLowerLiquidityAddDeltaTickLower] using hiff.mp hdelta
  have hneg :
      UInt256.isZero (UInt256.slt
        (UInt256.signextend ⟨15⟩ (burnLowerLiquidityAddDeltaY I)) ⟨0⟩) =
        ⟨0⟩ := by
    simpa [burnLowerLiquidityAddDeltaY] using
      burnLiquidityDeltaNegativeSltJumpCond I hcanon hnonzero
  simpa [burnLowerLiquidityAddDeltaReturnStack] using
    (uniswapV3PoolLiquidityAddDeltaNegativeReturn
      (v := v) (code := code) (ee := I) (g := Sat256.ofUInt256 g)
      (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
      (y := burnLowerLiquidityAddDeltaY I)
      (x := burnLowerLiquidityAddDeltaX σLockedEvm I)
      (ret := ⟨20838⟩) (scratch := ⟨0⟩)
      (xCopy := burnLowerLiquidityAddDeltaX σLockedEvm I)
      (R := burnLowerLiquidityAddDeltaTail v σLockedEvm I obsWord)
      (mem := burnTickUpdateLowerHashMem (burnLowerLiquidityAddDeltaTickLower I)
        (burnObserveSingleDecodedMem σLockedEvm I obsWord))
      (aw := UInt256.ofNat 21) (rdata := ByteArray.empty) (cA := cA)
      (σ := σLockedEvm) hpatch hrdEntry hneg hreq
      (uniswapV3PoolBurnJumpDestPatched20838 hpatch)
      (by simp [burnLowerLiquidityAddDeltaTail]))

theorem uniswapV3PoolBurnLowerMaxLiquidityRevertBranch
    {v : PoolImmutables} {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {code : ByteArray} {σLockedEvm : AccountMap} {obsWord : UInt256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg (contract v) I.calldata = some burnTransition)
    (hdecode :
      decodeCalldataWithMode (config v).abiDecodeMode
        (List.map Param.name burnTransition.params)
        (transitionSignature burnTransition).paramTypes I.calldata = some (burnStore I))
    (hunlockedSolm : burnUnlockedByte σ_solm I ≠ ⟨0⟩)
    (hcanon :
      UInt256.signextend ⟨15⟩ (burnAmountCleanWord I) = burnAmountCleanWord I)
    (hguard : uniswapV3PoolNoDelegateCallGuard v I ≠ ⟨0⟩)
    (htickLt :
      tickSpacingSint24Value (burnTickLowerWord I) <
        tickSpacingSint24Value (burnTickUpperWord I))
    (hge : ¬ tickSpacingSint24Value (burnTickLowerWord I) < (-887272 : Int))
    (hle : ¬ (887272 : Int) < tickSpacingSint24Value (burnTickUpperWord I))
    (hnonzero : burnAmountCleanWord I ≠ ⟨0⟩)
    (hAccountsAfterLock :
      accountMapEquiv σLockedEvm
        (sstoreAccountMap I.codeOwner σ_solm ⟨0⟩ (burnLockedSlotWord σ_solm I)))
    (hobsBound : (slot0ObservationIndexWord σLockedEvm I).toNat < 65535)
    (hobsWord : obsWord = burnObserveSingleSlotWord σLockedEvm I)
    (hrevert :
      ∃ _heq : UInt256.eq
          (UInt256.land (UInt256.ofNat I.header.timestamp) observationsUint32Mask)
          (burnObserveSingleDecodedBlockWord obsWord) ≠ ⟨0⟩,
        burnTickUpdateLowerLiquidityGrossAfterSubInt
            (sstoreAccountMap I.codeOwner σ_solm ⟨0⟩ (burnLockedSlotWord σ_solm I)) I <
          burnTickUpdateLowerLiquidityGrossBeforeInt
            (sstoreAccountMap I.codeOwner σ_solm ⟨0⟩ (burnLockedSlotWord σ_solm I)) I ∧
        ¬ burnTickUpdateLowerLiquidityGrossAfterSubInt
            (sstoreAccountMap I.codeOwner σ_solm ⟨0⟩ (burnLockedSlotWord σ_solm I)) I <=
          v.maxLiquidityPerTick)
    (hrdEntryOfEq :
      ∀ _heq : UInt256.eq
          (UInt256.land (UInt256.ofNat I.header.timestamp) observationsUint32Mask)
          (burnObserveSingleDecodedBlockWord obsWord) ≠ ⟨0⟩,
        ∃ k' C',
          RD code I (Sat256.ofUInt256 g)
            (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨13807⟩
            (burnLowerLiquidityAddDeltaEntryStack v σLockedEvm I obsWord)
            (burnTickUpdateLowerHashMem (burnLowerLiquidityAddDeltaTickLower I)
              (burnObserveSingleDecodedMem σLockedEvm I obsWord))
            (UInt256.ofNat 21) ByteArray.empty (cA, σLockedEvm) k' C') :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  rcases hrevert with ⟨heq, hdelta, hmax⟩
  have hboundSolm :
      (slot0ObservationIndexWord
        (sstoreAccountMap I.codeOwner σ_solm ⟨0⟩ (burnLockedSlotWord σ_solm I)) I).toNat <
        65535 := by
    rw [← burnObserveSingleObservationIndexWord_transport hAccountsAfterLock]
    exact hobsBound
  have hsame :=
    burnObserveSingleSourceTimestampEqOfGuard hAccountsAfterLock hobsWord heq
  have hbody := uniswapV3PoolBurnSourceLowerMaxLiquidityReverts
    (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hwv hunlockedSolm hcanon hguard htickLt hge hle hnonzero hboundSolm hsame hdelta hmax
  rcases hrdEntryOfEq heq with ⟨_, _, hrdEntry⟩
  rcases uniswapV3PoolBurnLowerLiquidityAddDeltaReturnRD
      (v := v) (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
      (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (code := code) (σLockedEvm := σLockedEvm) (obsWord := obsWord)
      hpatch hcanon hnonzero hAccountsAfterLock hdelta hrdEntry with
    ⟨_, _, hrd20838⟩
  have hmaxEvm := burnTickUpdateLowerMaxLiquidityEvmCheck_of_source
    (v := v) (σ_evm := σLockedEvm)
    (σ_solm := sstoreAccountMap I.codeOwner σ_solm ⟨0⟩ (burnLockedSlotWord σ_solm I))
    (I := I) hAccountsAfterLock hcanon hnonzero hdelta hmax
  have hrdRevert := uniswapV3PoolBurnLowerMaxLiquidityRevert
    (v := v) (code := code) (ee := I) (g := Sat256.ofUInt256 g)
    (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
    (obsWord := obsWord) (tickLower := burnLowerLiquidityAddDeltaTickLower I)
    (rdata := ByteArray.empty) (cA := cA) (σ := σLockedEvm) hpatch
    (by
      simpa [burnLowerLiquidityAddDeltaReturnStack, burnLowerLiquidityAddDeltaTail]
        using hrd20838)
    (by
      simpa [burnLowerLiquidityAddDeltaX, burnLowerLiquidityAddDeltaY,
        burnLowerLiquidityAddDeltaTickLower] using hmaxEvm)
    (by simp [burnLowerLiquidityAddDeltaTail])
  exact hrdRevert.reEquivExecutionRevert hcode hdispatch hdecode hbody

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolBurnLowerLiquidityAddDeltaBranch
    {v : PoolImmutables} {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {code : ByteArray} {σLockedEvm : AccountMap} {obsWord : UInt256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg (contract v) I.calldata = some burnTransition)
    (hdecode :
      decodeCalldataWithMode (config v).abiDecodeMode
        (List.map Param.name burnTransition.params)
        (transitionSignature burnTransition).paramTypes I.calldata = some (burnStore I))
    (hunlockedSolm : burnUnlockedByte σ_solm I ≠ ⟨0⟩)
    (hcanon :
      UInt256.signextend ⟨15⟩ (burnAmountCleanWord I) = burnAmountCleanWord I)
    (hguard : uniswapV3PoolNoDelegateCallGuard v I ≠ ⟨0⟩)
    (htickLt :
      tickSpacingSint24Value (burnTickLowerWord I) <
        tickSpacingSint24Value (burnTickUpperWord I))
    (hge : ¬ tickSpacingSint24Value (burnTickLowerWord I) < (-887272 : Int))
    (hle : ¬ (887272 : Int) < tickSpacingSint24Value (burnTickUpperWord I))
    (hnonzero : burnAmountCleanWord I ≠ ⟨0⟩)
    (hAccountsAfterLock :
      accountMapEquiv σLockedEvm
        (sstoreAccountMap I.codeOwner σ_solm ⟨0⟩ (burnLockedSlotWord σ_solm I)))
    (hobsBound : (slot0ObservationIndexWord σLockedEvm I).toNat < 65535)
    (hobsWord : obsWord = burnObserveSingleSlotWord σLockedEvm I)
    (hrdEntryOfEq :
      ∀ _heq : UInt256.eq
          (UInt256.land (UInt256.ofNat I.header.timestamp) observationsUint32Mask)
          (burnObserveSingleDecodedBlockWord obsWord) ≠ ⟨0⟩,
        ∃ k' C',
          RD code I (Sat256.ofUInt256 g)
            (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨13807⟩
            (UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)) ::
              burnTickUpdateLowerLiquidityGrossBeforeWordEvm σLockedEvm I
                (UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I)) ::
              ⟨20838⟩ :: ⟨0⟩ ::
              burnTickUpdateLowerLiquidityGrossBeforeWordEvm σLockedEvm I
                (UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I)) ::
              burnTickUpdateLowerBaseSlotWord
                (UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I)) ::
              ⟨0⟩ :: EVM.wordOfInt v.maxLiquidityPerTick :: ⟨0⟩ ::
              UInt256.ofNat I.header.timestamp ::
              burnObserveSingleDecodedTickWord obsWord ::
              burnObserveSingleDecodedSecondsWord obsWord ::
              solcSlotWord σLockedEvm I ⟨2⟩ ::
              solcSlotWord σLockedEvm I ⟨1⟩ ::
              UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)) ::
              slot0TickReturnWord σLockedEvm I ::
              UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I) ::
              ⟨5⟩ :: ⟨19331⟩ ::
              burnObserveSingleDecodedSecondsWord obsWord ::
              burnObserveSingleDecodedTickWord obsWord ::
              UInt256.ofNat I.header.timestamp :: ⟨0⟩ :: ⟨0⟩ ::
              solcSlotWord σLockedEvm I ⟨2⟩ ::
              solcSlotWord σLockedEvm I ⟨1⟩ ::
              burnPositionBaseSlotWord σLockedEvm I ::
              slot0TickReturnWord σLockedEvm I ::
              UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)) ::
              UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I) ::
              UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I) ::
              UInt256.ofNat I.source.val :: ⟨16428⟩ :: ⟨256⟩ ::
              ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
              ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
              burnAmountCleanWord I :: burnTickUpperCleanWord I ::
              burnTickLowerCleanWord I :: ⟨621⟩ :: [solcSelectorWord I])
            (burnTickUpdateLowerHashMem
              (UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I))
              (burnObserveSingleDecodedMem σLockedEvm I obsWord))
            (UInt256.ofNat 21) ByteArray.empty (cA, σLockedEvm) k' C') :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  by_cases hrevert :
      ∃ heq : UInt256.eq
          (UInt256.land (UInt256.ofNat I.header.timestamp) observationsUint32Mask)
          (burnObserveSingleDecodedBlockWord obsWord) ≠ ⟨0⟩,
        ¬ burnTickUpdateLowerLiquidityGrossAfterSubInt
            (sstoreAccountMap I.codeOwner σ_solm ⟨0⟩ (burnLockedSlotWord σ_solm I)) I <
          burnTickUpdateLowerLiquidityGrossBeforeInt
            (sstoreAccountMap I.codeOwner σ_solm ⟨0⟩ (burnLockedSlotWord σ_solm I)) I
  · exact uniswapV3PoolBurnLowerLiquidityAddDeltaRevertBranch
      (v := v) (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
      (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (code := code) (σLockedEvm := σLockedEvm) (obsWord := obsWord)
      hpatch hcode hwv hdispatch hdecode hunlockedSolm hcanon hguard htickLt hge hle
      hnonzero hAccountsAfterLock hobsBound hobsWord hrevert hrdEntryOfEq
  · by_cases hmaxRevert :
      ∃ heq : UInt256.eq
          (UInt256.land (UInt256.ofNat I.header.timestamp) observationsUint32Mask)
          (burnObserveSingleDecodedBlockWord obsWord) ≠ ⟨0⟩,
        burnTickUpdateLowerLiquidityGrossAfterSubInt
            (sstoreAccountMap I.codeOwner σ_solm ⟨0⟩ (burnLockedSlotWord σ_solm I)) I <
          burnTickUpdateLowerLiquidityGrossBeforeInt
            (sstoreAccountMap I.codeOwner σ_solm ⟨0⟩ (burnLockedSlotWord σ_solm I)) I ∧
        ¬ burnTickUpdateLowerLiquidityGrossAfterSubInt
            (sstoreAccountMap I.codeOwner σ_solm ⟨0⟩ (burnLockedSlotWord σ_solm I)) I <=
          v.maxLiquidityPerTick
    · exact uniswapV3PoolBurnLowerMaxLiquidityRevertBranch
        (v := v) (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
        (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (code := code) (σLockedEvm := σLockedEvm) (obsWord := obsWord)
        hpatch hcode hwv hdispatch hdecode hunlockedSolm hcanon hguard htickLt hge hle
        hnonzero hAccountsAfterLock hobsBound hobsWord hmaxRevert hrdEntryOfEq
    · sorry

end Benchmarks.UniswapV3Pool
