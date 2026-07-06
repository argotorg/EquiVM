import Benchmarks.Dss.Jug.DripBodyCore
import Mathlib.Util.ParseCommand
import Lean.Elab.Tactic

open Lean Elab Tactic
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.Dss.Jug

set_option maxHeartbeats 1000000

private def jugDripFeeZeroScript : String := r#"
by_cases hprevMaxNot :
    ¬ ((dripVatIlksPrevWord out).toNat : Int) ≤ maxInt256
· let locals := dripLocals I
  let evmE :=
    initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
  let evmS :=
    initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hrhoWord : jugSlotWord (fileDutyRhoSlotFor I) σ_evm I =
      jugSlotWord (fileDutyRhoSlotFor I) σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner
      (fileDutyRhoSlotFor I) ⟨0⟩
  have hleSolm :
      (jugSlotWord (fileDutyRhoSlotFor I) σ_solm I).toNat ≤
        (UInt256.ofNat I.header.timestamp).toNat := by
    rw [← hrhoWord]
    exact hle
  have hcodeSizeSolm :
      Reasoning.Theory.uniswapExtCodeSizeWord σ_solm
          (dripVatTargetWord σ_solm I) ≠ ⟨0⟩ :=
    dripVatCodeSize_ne_zero_accountMapEquiv hAccounts hvatCode
  have hvatCodeSolm :
      0 <
        (UInt256.ofNat
          (((initState cA gh bl σ_solm σ₀
            (Sat256.ofUInt256 g) A I).lookupAccount
              (dripVatAddress σ_solm I)).option 0
                (fun acc => acc.code.size))).toNat :=
    dripVatCode_pos_of_codeSize_ne_zero (cA := cA) (gh := gh)
      (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) hcodeSizeSolm
  rcases hΘ with ⟨g'', A', hΘ'⟩
  have hdepthNe : evmE.executionEnv.depth ≠ 1024 := by
    intro hbad
    simp [evmE, initState] at hbad
    rw [hbad] at hdepth
    omega
  have htgtAddr :
      dripVatAddress σ_solm I =
        AccountAddress.ofUInt256 (dripVatTargetWord σ_evm I) := by
    rw [← dripVatAddress_accountMapEquiv hAccounts]
    exact dripVatAddress_eq_target σ_evm I
  have htgt :
      EVM.address (dripVatAddress σ_solm I) =
        AccountAddress.ofUInt256 (dripVatTargetWord σ_evm I) := by
    rw [htgtAddr]
    exact evmAddress_accountAddress _
  have hΘE :
      (cA', σ', g'', A', true, out) =
        Ethereum.EVM.Θ evmE.executionEnv.blobVersionedHashes
          evmE.createdAccounts evmE.genesisBlockHeader
          evmE.blocks evmE.accountMap evmE.σ₀ Ain
          (AccountAddress.ofUInt256
            (UInt256.ofNat evmE.executionEnv.codeOwner))
          evmE.executionEnv.sender
          (AccountAddress.ofUInt256 (dripVatTargetWord σ_evm I))
          (toExecute evmE.accountMap
            (AccountAddress.ofUInt256 (dripVatTargetWord σ_evm I)))
          callGas (UInt256.ofNat evmE.executionEnv.gasPrice)
          ⟨0⟩ ⟨0⟩
          ((dripVatIlksCalldataMem I
            (dripIlkHashMem I)).readWithPadding
              dripVatIlksOutPtr.toNat dripVatIlksInSize.toNat)
          (evmE.executionEnv.depth + 1)
          evmE.executionEnv.header true := by
    simpa [evmE, initState, hperm] using hΘ'
  obtain ⟨σ'_solm, A'_solm, hcallSolm, hAccounts'⟩ :=
    typedCallViaEVM_callMade_accountMapEquiv
      (cfg := config) (evm_evm := evmE) (evm_solm := evmS)
      (tgt := EVM.address (dripVatAddress σ_solm I))
      (targetWord := dripVatTargetWord σ_evm I)
      (name := "ilks")
      (args := [.fixedBytes bytes32Width (fileDutyIlkBytes I)])
      (cA' := cA') (σ' := σ') (A' := A') (A_in := Ain)
      (z := true) (out := out) (g'' := g'')
      (callGas := callGas)
      (mem := dripVatIlksCalldataMem I (dripIlkHashMem I))
      (inOff := dripVatIlksOutPtr) (inSize := dripVatIlksInSize)
      (callPerm := true)
      hdepthNe htgt (dripVatIlksEncode_eq I hsz36) hΘE
      (show accountMapEquiv evmE.accountMap evmS.accountMap from hAccounts)
      (show evmE.σ₀ = evmS.σ₀ from rfl)
      (show evmS.createdAccounts = evmE.createdAccounts from rfl)
      (show evmS.genesisBlockHeader = evmE.genesisBlockHeader from rfl)
      (show evmS.blocks = evmE.blocks from rfl)
      (show evmS.substate = evmE.substate from rfl)
      (show evmS.executionEnv = evmE.executionEnv from rfl)
  have hbaseWord : jugSlotWord ⟨4⟩ σ' I =
      jugSlotWord ⟨4⟩ σ'_solm I :=
    accountMapEquiv_storage_findD hAccounts' I.codeOwner ⟨4⟩ ⟨0⟩
  have hdutyWord : jugSlotWord (fileDutyDutySlotFor I) σ' I =
      jugSlotWord (fileDutyDutySlotFor I) σ'_solm I :=
    accountMapEquiv_storage_findD hAccounts' I.codeOwner
      (fileDutyDutySlotFor I) ⟨0⟩
  have haddNoSolm :
      ¬ UInt256.size ≤ (jugSlotWord ⟨4⟩ σ'_solm I).toNat +
        (jugSlotWord (fileDutyDutySlotFor I) σ'_solm I).toNat := by
    intro hbad
    exact haddOverflow (by
      simpa [hbaseWord, hdutyWord] using hbad)
  have hfeeZeroSolm :
      jugSlotWord ⟨4⟩ σ'_solm I +
          jugSlotWord (fileDutyDutySlotFor I) σ'_solm I =
        ⟨0⟩ := by
    simpa [fee, hbaseWord, hdutyWord] using hfeeZero
  have hrhoPostWord : jugSlotWord (fileDutyRhoSlotFor I) σ' I =
      jugSlotWord (fileDutyRhoSlotFor I) σ'_solm I :=
    accountMapEquiv_storage_findD hAccounts' I.codeOwner
      (fileDutyRhoSlotFor I) ⟨0⟩
  have hageNZSolm :
      UInt256.sub (UInt256.ofNat I.header.timestamp)
          (jugSlotWord (fileDutyRhoSlotFor I) σ'_solm I) ≠
        ⟨0⟩ := by
    intro hbad
    exact hageNZ (by simpa [age, hrhoPostWord] using hbad)
  have hbody :
      ExecTransitionBody config contract evmS locals
        dripTransition.body .reverted := by
    simpa [evmS, locals, initState, jugSlotWord] using
      (jugDripSourceBodyVatIlksDiffYBoundRevertsXZeroNNonzero
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (evmVat :=
          { evmS with
            accountMap := σ'_solm
            substate := A'_solm
            createdAccounts := cA' })
        (out := out) hwv hsz36 hleSolm hvatCodeSolm
        (by simpa [evmS] using hcallSolm) _hdecOut
        (by
          simpa [evmS, initState, jugSlotWord] using
            haddNoSolm)
        (by
          simpa [evmS, initState, jugSlotWord] using
            hfeeZeroSolm)
        (by
          simpa [evmS, initState, jugSlotWord] using
            hageNZSolm)
        hprevMaxNot)
  have hfitZero :
      ((⟨0⟩ : UInt256).toNat *
        (dripVatIlksPrevWord out).toNat) < UInt256.size := by
    norm_num [UInt256.size]
  obtain ⟨_, _, rd1524Zero⟩ :=
    RD.jugDripRpowXZeroNNonzeroReturns
      (R := [⟨1530⟩, dripVatIlksPrevWord out, ⟨0⟩,
        fileDutyIlkWord I, ⟨357⟩, jugSelWord I])
      (by simp) hageNZ
      (by simpa [fee, age, hfeeZero] using _rd2153)
  obtain ⟨_, _, rd1530Raw⟩ :=
    RD.jugDripRmulReturns
      (R := [⟨0⟩, fileDutyIlkWord I, ⟨357⟩, jugSelWord I])
      (by simp) hfitZero rd1524Zero
  have hzeroRate :
      UInt256.div (dripVatIlksPrevWord out * (⟨0⟩ : UInt256))
        jugRay = ⟨0⟩ := by
    apply u256_inj
    simp [u256_mul_op_toNat, udiv_toNat]
  have rd1530 := by
    simpa [hzeroRate] using rd1530Raw
  obtain ⟨_, _, rd2397⟩ := RD.jugDripToDiffRoutine rd1530
  have hzeroMax :
      (((⟨0⟩ : UInt256).toNat : Int) ≤ maxInt256) := by
    norm_num [maxInt256]
  have hrev := RD.jugDiffRevertYBound
    (R := [dripVowTargetWord σ' I, fileDutyIlkWord I,
      dripVatFoldSelectorWord, dripVatTargetWord σ' I,
      dripVatIlksPrevWord out, ⟨0⟩, fileDutyIlkWord I,
      ⟨357⟩, jugSelWord I])
    (g := g) (rate := (⟨0⟩ : UInt256))
    (prev := dripVatIlksPrevWord out)
    (by simp) hzeroMax hprevMaxNot rd2397
  exact hrev.reEquivExecutionRevert hcode hdispatch
    (jugDecode_drip_ok hsz36) hbody
· have hprevMax :
      ((dripVatIlksPrevWord out).toNat : Int) ≤ maxInt256 := by
    by_contra hbad
    exact hprevMaxNot hbad
  by_cases hfoldNoCode :
      Reasoning.Theory.uniswapExtCodeSizeWord σ'
        (dripVatTargetWord σ' I) = ⟨0⟩
  · let locals := dripLocals I
    let evmE :=
      initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
    let evmS :=
      initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    have hrhoWord : jugSlotWord (fileDutyRhoSlotFor I) σ_evm I =
        jugSlotWord (fileDutyRhoSlotFor I) σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner
        (fileDutyRhoSlotFor I) ⟨0⟩
    have hleSolm :
        (jugSlotWord (fileDutyRhoSlotFor I) σ_solm I).toNat ≤
          (UInt256.ofNat I.header.timestamp).toNat := by
      rw [← hrhoWord]
      exact hle
    have hcodeSizeSolm :
        Reasoning.Theory.uniswapExtCodeSizeWord σ_solm
            (dripVatTargetWord σ_solm I) ≠ ⟨0⟩ :=
      dripVatCodeSize_ne_zero_accountMapEquiv hAccounts hvatCode
    have hvatCodeSolm :
        0 <
          (UInt256.ofNat
            (((initState cA gh bl σ_solm σ₀
              (Sat256.ofUInt256 g) A I).lookupAccount
                (dripVatAddress σ_solm I)).option 0
                  (fun acc => acc.code.size))).toNat :=
      dripVatCode_pos_of_codeSize_ne_zero (cA := cA) (gh := gh)
        (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) hcodeSizeSolm
    rcases hΘ with ⟨g'', A', hΘ'⟩
    have hdepthNe : evmE.executionEnv.depth ≠ 1024 := by
      intro hbad
      simp [evmE, initState] at hbad
      rw [hbad] at hdepth
      omega
    have htgtAddr :
        dripVatAddress σ_solm I =
          AccountAddress.ofUInt256 (dripVatTargetWord σ_evm I) := by
      rw [← dripVatAddress_accountMapEquiv hAccounts]
      exact dripVatAddress_eq_target σ_evm I
    have htgt :
        EVM.address (dripVatAddress σ_solm I) =
          AccountAddress.ofUInt256 (dripVatTargetWord σ_evm I) := by
      rw [htgtAddr]
      exact evmAddress_accountAddress _
    have hΘE :
        (cA', σ', g'', A', true, out) =
          Ethereum.EVM.Θ evmE.executionEnv.blobVersionedHashes
            evmE.createdAccounts evmE.genesisBlockHeader
            evmE.blocks evmE.accountMap evmE.σ₀ Ain
            (AccountAddress.ofUInt256
              (UInt256.ofNat evmE.executionEnv.codeOwner))
            evmE.executionEnv.sender
            (AccountAddress.ofUInt256 (dripVatTargetWord σ_evm I))
            (toExecute evmE.accountMap
              (AccountAddress.ofUInt256 (dripVatTargetWord σ_evm I)))
            callGas (UInt256.ofNat evmE.executionEnv.gasPrice)
            ⟨0⟩ ⟨0⟩
            ((dripVatIlksCalldataMem I
              (dripIlkHashMem I)).readWithPadding
                dripVatIlksOutPtr.toNat dripVatIlksInSize.toNat)
            (evmE.executionEnv.depth + 1)
            evmE.executionEnv.header true := by
      simpa [evmE, initState, hperm] using hΘ'
    obtain ⟨σ'_solm, A'_solm, hcallSolm, hAccounts'⟩ :=
      typedCallViaEVM_callMade_accountMapEquiv
        (cfg := config) (evm_evm := evmE) (evm_solm := evmS)
        (tgt := EVM.address (dripVatAddress σ_solm I))
        (targetWord := dripVatTargetWord σ_evm I)
        (name := "ilks")
        (args := [.fixedBytes bytes32Width (fileDutyIlkBytes I)])
        (cA' := cA') (σ' := σ') (A' := A') (A_in := Ain)
        (z := true) (out := out) (g'' := g'')
        (callGas := callGas)
        (mem := dripVatIlksCalldataMem I (dripIlkHashMem I))
        (inOff := dripVatIlksOutPtr) (inSize := dripVatIlksInSize)
        (callPerm := true)
        hdepthNe htgt (dripVatIlksEncode_eq I hsz36) hΘE
        (show accountMapEquiv evmE.accountMap evmS.accountMap from hAccounts)
        (show evmE.σ₀ = evmS.σ₀ from rfl)
        (show evmS.createdAccounts = evmE.createdAccounts from rfl)
        (show evmS.genesisBlockHeader = evmE.genesisBlockHeader from rfl)
        (show evmS.blocks = evmE.blocks from rfl)
        (show evmS.substate = evmE.substate from rfl)
        (show evmS.executionEnv = evmE.executionEnv from rfl)
    have hbaseWord : jugSlotWord ⟨4⟩ σ' I =
        jugSlotWord ⟨4⟩ σ'_solm I :=
      accountMapEquiv_storage_findD hAccounts' I.codeOwner
        ⟨4⟩ ⟨0⟩
    have hdutyWord : jugSlotWord (fileDutyDutySlotFor I) σ' I =
        jugSlotWord (fileDutyDutySlotFor I) σ'_solm I :=
      accountMapEquiv_storage_findD hAccounts' I.codeOwner
        (fileDutyDutySlotFor I) ⟨0⟩
    have haddNoSolm :
        ¬ UInt256.size ≤ (jugSlotWord ⟨4⟩ σ'_solm I).toNat +
          (jugSlotWord (fileDutyDutySlotFor I) σ'_solm I).toNat := by
      intro hbad
      exact haddOverflow (by
        simpa [hbaseWord, hdutyWord] using hbad)
    have hfeeZeroSolm :
        jugSlotWord ⟨4⟩ σ'_solm I +
            jugSlotWord (fileDutyDutySlotFor I) σ'_solm I =
          ⟨0⟩ := by
      simpa [fee, hbaseWord, hdutyWord] using hfeeZero
    have hrhoPostWord : jugSlotWord (fileDutyRhoSlotFor I) σ' I =
        jugSlotWord (fileDutyRhoSlotFor I) σ'_solm I :=
      accountMapEquiv_storage_findD hAccounts' I.codeOwner
        (fileDutyRhoSlotFor I) ⟨0⟩
    have hageNZSolm :
        UInt256.sub (UInt256.ofNat I.header.timestamp)
            (jugSlotWord (fileDutyRhoSlotFor I) σ'_solm I) ≠
          ⟨0⟩ := by
      intro hbad
      exact hageNZ (by simpa [age, hrhoPostWord] using hbad)
    have hfoldCodeSolm :
        Reasoning.Theory.uniswapExtCodeSizeWord σ'_solm
            (dripVatTargetWord σ'_solm I) = ⟨0⟩ :=
      dripVatCodeSize_zero_accountMapEquiv hAccounts' hfoldNoCode
    have hfoldNoCodeSolmRaw :
        (UInt256.ofNat
          ((σ'_solm.find? (dripVatAddress σ'_solm I)).option 0
            (fun acc => acc.code.size))).toNat = 0 :=
      drip_uniswapExtCodeSizeWord_zero_lookup_code_zero
        (σ := σ'_solm) (target := dripVatTargetWord σ'_solm I)
        (addr := dripVatAddress σ'_solm I)
        (dripVatAddress_eq_target σ'_solm I) hfoldCodeSolm
    have hbody :
        ExecTransitionBody config contract evmS locals
          dripTransition.body .reverted := by
      simpa [evmS, locals, initState, jugSlotWord] using
        (jugDripSourceBodyVatFoldNoCodeRevertsXZeroNNonzero
          (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
          (σ₀ := σ₀) (A := A) (I := I) (g := g)
          (evmVat :=
            { evmS with
              accountMap := σ'_solm
              substate := A'_solm
              createdAccounts := cA' })
          (out := out) hwv hsz36 hleSolm hvatCodeSolm
          (by simpa [evmS] using hcallSolm) _hdecOut
          (by
            simpa [evmS, initState, jugSlotWord] using
              haddNoSolm)
          (by
            simpa [evmS, initState, jugSlotWord] using
              hfeeZeroSolm)
          (by
            simpa [evmS, initState, jugSlotWord] using
              hageNZSolm)
          hprevMax
          (by
            simpa [evmS, initState, State.lookupAccount] using
              hfoldNoCodeSolmRaw))
    have hfitZero :
        ((⟨0⟩ : UInt256).toNat *
          (dripVatIlksPrevWord out).toNat) < UInt256.size := by
      norm_num [UInt256.size]
    obtain ⟨_, _, rd1524Zero⟩ :=
      RD.jugDripRpowXZeroNNonzeroReturns
        (R := [⟨1530⟩, dripVatIlksPrevWord out, ⟨0⟩,
          fileDutyIlkWord I, ⟨357⟩, jugSelWord I])
        (by simp) hageNZ
        (by simpa [fee, age, hfeeZero] using _rd2153)
    obtain ⟨_, _, rd1530Raw⟩ :=
      RD.jugDripRmulReturns
        (R := [⟨0⟩, fileDutyIlkWord I, ⟨357⟩, jugSelWord I])
        (by simp) hfitZero rd1524Zero
    have hzeroRate :
        UInt256.div (dripVatIlksPrevWord out * (⟨0⟩ : UInt256))
          jugRay = ⟨0⟩ := by
      apply u256_inj
      simp [u256_mul_op_toNat, udiv_toNat]
    have rd1530 := by
      simpa [hzeroRate] using rd1530Raw
    obtain ⟨_, _, rd2397⟩ := RD.jugDripToDiffRoutine rd1530
    have hzeroMax :
        (((⟨0⟩ : UInt256).toNat : Int) ≤ maxInt256) := by
      norm_num [maxInt256]
    obtain ⟨_, _, rd1570⟩ := RD.jugDiffReturns
      (R := [dripVowTargetWord σ' I, fileDutyIlkWord I,
        dripVatFoldSelectorWord, dripVatTargetWord σ' I,
        dripVatIlksPrevWord out, ⟨0⟩, fileDutyIlkWord I,
        ⟨357⟩, jugSelWord I])
      (g := g) (rate := (⟨0⟩ : UInt256))
      (prev := dripVatIlksPrevWord out)
      (by simp) hzeroMax hprevMax rd2397
    let foldBaseMem :=
      twoWordHashMem (fileDutyIlkWord I) ⟨1⟩
        (twoWordHashMem (fileDutyIlkWord I) ⟨1⟩
          (dripVatIlksPostCallMem I out))
    have hpostSize : (dripVatIlksPostCallMem I out).size = 192 :=
      dripVatIlksPostCallMem_size_long I out hlo hout
    have hpostRead64 :
        (dripVatIlksPostCallMem I out).readWithPadding 64 32 =
          UInt256.toByteArray ⟨128⟩ :=
      dripVatIlksPostCallMem_read64_long I out hlo hout
    have hinnerSize :
        (twoWordHashMem (fileDutyIlkWord I) ⟨1⟩
          (dripVatIlksPostCallMem I out)).size = 192 := by
      rw [drip_twoWordHashMem_size_of_ge64 (fileDutyIlkWord I)
        (⟨1⟩ : UInt256) (by rw [hpostSize]; omega), hpostSize]
    have hinnerRead64 :
        (twoWordHashMem (fileDutyIlkWord I) ⟨1⟩
          (dripVatIlksPostCallMem I out)).readWithPadding 64 32 =
          UInt256.toByteArray ⟨128⟩ :=
      drip_twoWordHashMem_read64_of_ge96 (fileDutyIlkWord I)
        (⟨1⟩ : UInt256) (by rw [hpostSize]; omega) hpostRead64
    have hfoldBaseSize : foldBaseMem.size = 192 := by
      dsimp [foldBaseMem]
      rw [drip_twoWordHashMem_size_of_ge64 (fileDutyIlkWord I)
        (⟨1⟩ : UInt256) (by rw [hinnerSize]; omega), hinnerSize]
    have hfoldBaseRead64 :
        foldBaseMem.readWithPadding 64 32 =
          UInt256.toByteArray ⟨128⟩ := by
      dsimp [foldBaseMem]
      exact drip_twoWordHashMem_read64_of_ge96
        (fileDutyIlkWord I) (⟨1⟩ : UInt256)
        (by rw [hinnerSize]; omega) hinnerRead64
    have hrev := RD.jugDripVatFoldNoCode hfoldBaseSize
      hfoldBaseRead64 hfoldNoCode rd1570
    exact hrev.reEquivExecutionRevert hcode hdispatch
      (jugDecode_drip_ok hsz36) hbody
  · let locals := dripLocals I
    let evmE :=
      initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
    let evmS :=
      initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let foldBaseMem :=
      twoWordHashMem (fileDutyIlkWord I) ⟨1⟩
        (twoWordHashMem (fileDutyIlkWord I) ⟨1⟩
          (dripVatIlksPostCallMem I out))
    have hpostSize : (dripVatIlksPostCallMem I out).size = 192 :=
      dripVatIlksPostCallMem_size_long I out hlo hout
    have hpostRead64 :
        (dripVatIlksPostCallMem I out).readWithPadding 64 32 =
          UInt256.toByteArray ⟨128⟩ :=
      dripVatIlksPostCallMem_read64_long I out hlo hout
    have hinnerSize :
        (twoWordHashMem (fileDutyIlkWord I) ⟨1⟩
          (dripVatIlksPostCallMem I out)).size = 192 := by
      rw [drip_twoWordHashMem_size_of_ge64 (fileDutyIlkWord I)
        (⟨1⟩ : UInt256) (by rw [hpostSize]; omega), hpostSize]
    have hinnerRead64 :
        (twoWordHashMem (fileDutyIlkWord I) ⟨1⟩
          (dripVatIlksPostCallMem I out)).readWithPadding 64 32 =
          UInt256.toByteArray ⟨128⟩ :=
      drip_twoWordHashMem_read64_of_ge96 (fileDutyIlkWord I)
        (⟨1⟩ : UInt256) (by rw [hpostSize]; omega) hpostRead64
    have hfoldBaseSize : foldBaseMem.size = 192 := by
      dsimp [foldBaseMem]
      rw [drip_twoWordHashMem_size_of_ge64 (fileDutyIlkWord I)
        (⟨1⟩ : UInt256) (by rw [hinnerSize]; omega), hinnerSize]
    have hfoldBaseRead64 :
        foldBaseMem.readWithPadding 64 32 =
          UInt256.toByteArray ⟨128⟩ := by
      dsimp [foldBaseMem]
      exact drip_twoWordHashMem_read64_of_ge96
        (fileDutyIlkWord I) (⟨1⟩ : UInt256)
        (by rw [hinnerSize]; omega) hinnerRead64
    have hfitZero :
        ((⟨0⟩ : UInt256).toNat *
          (dripVatIlksPrevWord out).toNat) < UInt256.size := by
      norm_num [UInt256.size]
    obtain ⟨_, _, rd1524Zero⟩ :=
      RD.jugDripRpowXZeroNNonzeroReturns
        (R := [⟨1530⟩, dripVatIlksPrevWord out, ⟨0⟩,
          fileDutyIlkWord I, ⟨357⟩, jugSelWord I])
        (by simp) hageNZ
        (by simpa [fee, age, hfeeZero] using _rd2153)
    obtain ⟨_, _, rd1530Raw⟩ :=
      RD.jugDripRmulReturns
        (R := [⟨0⟩, fileDutyIlkWord I, ⟨357⟩, jugSelWord I])
        (by simp) hfitZero rd1524Zero
    have hzeroRate :
        UInt256.div (dripVatIlksPrevWord out * (⟨0⟩ : UInt256))
          jugRay = ⟨0⟩ := by
      apply u256_inj
      simp [u256_mul_op_toNat, udiv_toNat]
    have rd1530 := by
      simpa [hzeroRate] using rd1530Raw
    obtain ⟨_, _, rd2397⟩ := RD.jugDripToDiffRoutine rd1530
    have hzeroMax :
        (((⟨0⟩ : UInt256).toNat : Int) ≤ maxInt256) := by
      norm_num [maxInt256]
    obtain ⟨_, _, rd1570⟩ := RD.jugDiffReturns
      (R := [dripVowTargetWord σ' I, fileDutyIlkWord I,
        dripVatFoldSelectorWord, dripVatTargetWord σ' I,
        dripVatIlksPrevWord out, ⟨0⟩, fileDutyIlkWord I,
        ⟨357⟩, jugSelWord I])
      (g := g) (rate := (⟨0⟩ : UInt256))
      (prev := dripVatIlksPrevWord out)
      (by simp) hzeroMax hprevMax rd2397
    obtain ⟨gasWord, _, _, rd1650⟩ :=
      RD.jugDripVatFoldCallReady hfoldBaseSize hfoldBaseRead64
        hfoldNoCode rd1570
    obtain
      ⟨cA'', σ'', z, foldOut, AinFold, callGasFold, _, _,
        hΘFold, rd1651, hfoldOutSize⟩ :=
      RD.jugDripVatFoldPostCall rd1650 hdepth
    cases z
    · rcases hΘFold with ⟨gFold'', AFold', hΘFold'⟩
      have hrhoWord :
          jugSlotWord (fileDutyRhoSlotFor I) σ_evm I =
            jugSlotWord (fileDutyRhoSlotFor I) σ_solm I :=
        accountMapEquiv_storage_findD hAccounts I.codeOwner
          (fileDutyRhoSlotFor I) ⟨0⟩
      have hleSolm :
          (jugSlotWord (fileDutyRhoSlotFor I) σ_solm I).toNat ≤
            (UInt256.ofNat I.header.timestamp).toNat := by
        rw [← hrhoWord]
        exact hle
      have hcodeSizeSolm :
          Reasoning.Theory.uniswapExtCodeSizeWord σ_solm
              (dripVatTargetWord σ_solm I) ≠ ⟨0⟩ :=
        dripVatCodeSize_ne_zero_accountMapEquiv hAccounts hvatCode
      have hvatCodeSolm :
          0 <
            (UInt256.ofNat
              (((initState cA gh bl σ_solm σ₀
                (Sat256.ofUInt256 g) A I).lookupAccount
                  (dripVatAddress σ_solm I)).option 0
                    (fun acc => acc.code.size))).toNat :=
        dripVatCode_pos_of_codeSize_ne_zero (cA := cA) (gh := gh)
          (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A)
          (I := I) (g := g) hcodeSizeSolm
      rcases hΘ with ⟨g'', A', hΘ'⟩
      have hdepthNe : evmE.executionEnv.depth ≠ 1024 := by
        intro hbad
        simp [evmE, initState] at hbad
        rw [hbad] at hdepth
        omega
      have htgtAddr :
          dripVatAddress σ_solm I =
            AccountAddress.ofUInt256 (dripVatTargetWord σ_evm I) := by
        rw [← dripVatAddress_accountMapEquiv hAccounts]
        exact dripVatAddress_eq_target σ_evm I
      have htgt :
          EVM.address (dripVatAddress σ_solm I) =
            AccountAddress.ofUInt256 (dripVatTargetWord σ_evm I) := by
        rw [htgtAddr]
        exact evmAddress_accountAddress _
      have hΘE :
          (cA', σ', g'', A', true, out) =
            Ethereum.EVM.Θ evmE.executionEnv.blobVersionedHashes
              evmE.createdAccounts evmE.genesisBlockHeader
              evmE.blocks evmE.accountMap evmE.σ₀ Ain
              (AccountAddress.ofUInt256
                (UInt256.ofNat evmE.executionEnv.codeOwner))
              evmE.executionEnv.sender
              (AccountAddress.ofUInt256 (dripVatTargetWord σ_evm I))
              (toExecute evmE.accountMap
                (AccountAddress.ofUInt256 (dripVatTargetWord σ_evm I)))
              callGas (UInt256.ofNat evmE.executionEnv.gasPrice)
              ⟨0⟩ ⟨0⟩
              ((dripVatIlksCalldataMem I
                (dripIlkHashMem I)).readWithPadding
                  dripVatIlksOutPtr.toNat dripVatIlksInSize.toNat)
              (evmE.executionEnv.depth + 1)
              evmE.executionEnv.header true := by
        simpa [evmE, initState, hperm] using hΘ'
      obtain ⟨σ'_solm, A'_solm, hcallSolm, hAccounts'⟩ :=
        typedCallViaEVM_callMade_accountMapEquiv
          (cfg := config) (evm_evm := evmE) (evm_solm := evmS)
          (tgt := EVM.address (dripVatAddress σ_solm I))
          (targetWord := dripVatTargetWord σ_evm I)
          (name := "ilks")
          (args := [.fixedBytes bytes32Width (fileDutyIlkBytes I)])
          (cA' := cA') (σ' := σ') (A' := A') (A_in := Ain)
          (z := true) (out := out) (g'' := g'')
          (callGas := callGas)
          (mem := dripVatIlksCalldataMem I (dripIlkHashMem I))
          (inOff := dripVatIlksOutPtr) (inSize := dripVatIlksInSize)
          (callPerm := true)
          hdepthNe htgt (dripVatIlksEncode_eq I hsz36) hΘE
          (show accountMapEquiv evmE.accountMap evmS.accountMap from hAccounts)
          (show evmE.σ₀ = evmS.σ₀ from rfl)
          (show evmS.createdAccounts = evmE.createdAccounts from rfl)
          (show evmS.genesisBlockHeader = evmE.genesisBlockHeader from rfl)
          (show evmS.blocks = evmE.blocks from rfl)
          (show evmS.substate = evmE.substate from rfl)
          (show evmS.executionEnv = evmE.executionEnv from rfl)
      let evmVatE :=
        { evmE with
          accountMap := σ',
          substate := A'_solm,
          createdAccounts := cA' }
      let evmVatS :=
        { evmS with
          accountMap := σ'_solm,
          substate := A'_solm,
          createdAccounts := cA' }
      have hfoldDepthNe : evmVatE.executionEnv.depth ≠ 1024 := by
        simpa [evmVatE] using hdepthNe
      have hfoldTargetAddr :
          dripVatAddress σ'_solm I =
            AccountAddress.ofUInt256 (dripVatTargetWord σ' I) := by
        rw [← dripVatAddress_accountMapEquiv hAccounts']
        exact dripVatAddress_eq_target σ' I
      have hfoldTarget :
          EVM.address (dripVatAddress σ'_solm I) =
            AccountAddress.ofUInt256 (dripVatTargetWord σ' I) := by
        rw [hfoldTargetAddr]
        exact evmAddress_accountAddress _
      have hvowWord :
          dripVowTargetWord σ'_solm I = dripVowTargetWord σ' I :=
        (dripVowTargetWord_accountMapEquiv hAccounts').symm
      have hfoldEncode :
          config.externalABI.encode? "fold"
              [.fixedBytes bytes32Width (fileDutyIlkBytes I),
                .address (AccountAddress.ofUInt256
                  (dripVowTargetWord σ'_solm I)),
                .int (((⟨0⟩ : UInt256).toNat : Int) -
                  ((dripVatIlksPrevWord out).toNat : Int))] =
            some ((dripVatFoldCalldataMem σ' I
              (UInt256.sub (⟨0⟩ : UInt256)
                (dripVatIlksPrevWord out)) foldBaseMem).readWithPadding
                  dripVatFoldOutPtr.toNat dripVatFoldInSize.toNat) := by
        rw [hvowWord]
        exact dripVatFoldEncode_signed_eq σ' I (⟨0⟩ : UInt256)
          (dripVatIlksPrevWord out)
          (UInt256.sub (⟨0⟩ : UInt256) (dripVatIlksPrevWord out))
          hfoldBaseSize hsz36 hzeroMax hprevMax rfl
      have hΘFoldE :
          (cA'', σ'', gFold'', AFold', false, foldOut) =
            Ethereum.EVM.Θ evmVatE.executionEnv.blobVersionedHashes
              evmVatE.createdAccounts evmVatE.genesisBlockHeader
              evmVatE.blocks evmVatE.accountMap evmVatE.σ₀ AinFold
              (AccountAddress.ofUInt256
                (UInt256.ofNat evmVatE.executionEnv.codeOwner))
              evmVatE.executionEnv.sender
              (AccountAddress.ofUInt256 (dripVatTargetWord σ' I))
              (toExecute evmVatE.accountMap
                (AccountAddress.ofUInt256 (dripVatTargetWord σ' I)))
              callGasFold
              (UInt256.ofNat evmVatE.executionEnv.gasPrice)
              ⟨0⟩ ⟨0⟩
              ((dripVatFoldCalldataMem σ' I
                (UInt256.sub (⟨0⟩ : UInt256)
                  (dripVatIlksPrevWord out)) foldBaseMem).readWithPadding
                    dripVatFoldOutPtr.toNat dripVatFoldInSize.toNat)
              (evmVatE.executionEnv.depth + 1)
              evmVatE.executionEnv.header true := by
        simpa [evmVatE, evmE, initState, hperm, foldBaseMem] using
          hΘFold'
      obtain ⟨σ''_solm, A''_solm, hfoldCallSolm, _hAccounts''⟩ :=
        typedCallViaEVM_callMade_accountMapEquiv
          (cfg := config) (evm_evm := evmVatE) (evm_solm := evmVatS)
          (tgt := EVM.address (dripVatAddress σ'_solm I))
          (targetWord := dripVatTargetWord σ' I)
          (name := "fold")
          (args :=
            [.fixedBytes bytes32Width (fileDutyIlkBytes I),
              .address (AccountAddress.ofUInt256
                (dripVowTargetWord σ'_solm I)),
              .int (((⟨0⟩ : UInt256).toNat : Int) -
                ((dripVatIlksPrevWord out).toNat : Int))])
          (cA' := cA'') (σ' := σ'') (A' := AFold')
          (A_in := AinFold) (z := false) (out := foldOut)
          (g'' := gFold'') (callGas := callGasFold)
          (mem := dripVatFoldCalldataMem σ' I
            (UInt256.sub (⟨0⟩ : UInt256)
              (dripVatIlksPrevWord out)) foldBaseMem)
          (inOff := dripVatFoldOutPtr) (inSize := dripVatFoldInSize)
          (callPerm := true)
          hfoldDepthNe hfoldTarget hfoldEncode hΘFoldE
          (show accountMapEquiv evmVatE.accountMap evmVatS.accountMap from hAccounts')
          (show evmVatE.σ₀ = evmVatS.σ₀ from rfl)
          (show evmVatS.createdAccounts = evmVatE.createdAccounts from rfl)
          (show evmVatS.genesisBlockHeader = evmVatE.genesisBlockHeader from rfl)
          (show evmVatS.blocks = evmVatE.blocks from rfl)
          (show evmVatS.substate = evmVatE.substate from rfl)
          (show evmVatS.executionEnv = evmVatE.executionEnv from rfl)
      have hbaseWord : jugSlotWord ⟨4⟩ σ' I =
          jugSlotWord ⟨4⟩ σ'_solm I :=
        accountMapEquiv_storage_findD hAccounts' I.codeOwner
          ⟨4⟩ ⟨0⟩
      have hdutyWord :
          jugSlotWord (fileDutyDutySlotFor I) σ' I =
            jugSlotWord (fileDutyDutySlotFor I) σ'_solm I :=
        accountMapEquiv_storage_findD hAccounts' I.codeOwner
          (fileDutyDutySlotFor I) ⟨0⟩
      have haddNoSolm :
          ¬ UInt256.size ≤ (jugSlotWord ⟨4⟩ σ'_solm I).toNat +
            (jugSlotWord (fileDutyDutySlotFor I) σ'_solm I).toNat := by
        intro hbad
        exact haddOverflow (by
          simpa [hbaseWord, hdutyWord] using hbad)
      have hfeeZeroSolm :
          jugSlotWord ⟨4⟩ σ'_solm I +
              jugSlotWord (fileDutyDutySlotFor I) σ'_solm I =
            ⟨0⟩ := by
        simpa [fee, hbaseWord, hdutyWord] using hfeeZero
      have hrhoPostWord :
          jugSlotWord (fileDutyRhoSlotFor I) σ' I =
            jugSlotWord (fileDutyRhoSlotFor I) σ'_solm I :=
        accountMapEquiv_storage_findD hAccounts' I.codeOwner
          (fileDutyRhoSlotFor I) ⟨0⟩
      have hageNZSolm :
          UInt256.sub (UInt256.ofNat I.header.timestamp)
              (jugSlotWord (fileDutyRhoSlotFor I) σ'_solm I) ≠
            ⟨0⟩ := by
        intro hbad
        exact hageNZ (by simpa [age, hrhoPostWord] using hbad)
      have hfoldCodeSolmNe :
          Reasoning.Theory.uniswapExtCodeSizeWord σ'_solm
              (dripVatTargetWord σ'_solm I) ≠ ⟨0⟩ :=
        dripVatCodeSize_ne_zero_accountMapEquiv hAccounts'
          hfoldNoCode
      have hfoldCodeSolm :
          0 <
            (UInt256.ofNat
              ((evmVatS.lookupAccount
                (dripVatAddress evmVatS.accountMap
                  evmVatS.executionEnv)).option 0
                    (fun acc => acc.code.size))).toNat := by
        simpa [evmVatS, evmS, initState] using
          (dripVatCode_pos_of_codeSize_ne_zero (cA := cA')
            (gh := gh) (bl := bl) (σ := σ'_solm) (σ₀ := σ₀)
            (A := A'_solm) (I := I) (g := g) hfoldCodeSolmNe)
      have hbody :
          ExecTransitionBody config contract evmS locals
            dripTransition.body .reverted := by
        simpa [evmS, evmVatS, locals, initState, jugSlotWord] using
          (jugDripSourceBodyVatFoldCallFailedRevertsXZeroNNonzero
            (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
            (σ₀ := σ₀) (A := A) (I := I) (g := g)
            (evmVat := evmVatS)
            (evmFold :=
              { evmVatS with
                accountMap := σ''_solm,
                substate := A''_solm,
                createdAccounts := cA'' })
            (out := out) (foldOut := foldOut)
            hwv hsz36 hleSolm hvatCodeSolm
            (by simpa [evmS, evmVatS] using hcallSolm)
            _hdecOut
            (by
              simpa [evmVatS, evmS, initState, jugSlotWord] using
                haddNoSolm)
            (by
              simpa [evmVatS, evmS, initState, jugSlotWord] using
                hfeeZeroSolm)
            (by
              simpa [evmVatS, evmS, initState, jugSlotWord] using
                hageNZSolm)
            hprevMax hfoldCodeSolm
            (by simpa [evmVatS] using hfoldCallSolm))
      have hrev := RD.jugDripVatFoldCallFailed
        (targetWord := dripVatTargetWord σ' I) rd1651 hfoldOutSize
      exact hrev.reEquivExecutionRevert hcode hdispatch
        (jugDecode_drip_ok hsz36) hbody
    · rcases hΘFold with ⟨gFold'', AFold', hΘFold'⟩
      have hfoldCallMemSize :
          (dripVatFoldCalldataMem σ' I
            (UInt256.sub (⟨0⟩ : UInt256)
              (dripVatIlksPrevWord out)) foldBaseMem).size = 228 :=
        dripVatFoldCalldataMem_size σ' I
          (UInt256.sub (⟨0⟩ : UInt256)
            (dripVatIlksPrevWord out)) hfoldBaseSize
      have hfoldCallMemRead64 :
          (dripVatFoldCalldataMem σ' I
            (UInt256.sub (⟨0⟩ : UInt256)
              (dripVatIlksPrevWord out)) foldBaseMem).readWithPadding
              64 32 = UInt256.toByteArray ⟨128⟩ :=
        dripVatFoldCalldataMem_read64 σ' I
          (UInt256.sub (⟨0⟩ : UInt256)
            (dripVatIlksPrevWord out)) hfoldBaseSize
          hfoldBaseRead64
      have hrhoWord :
          jugSlotWord (fileDutyRhoSlotFor I) σ_evm I =
            jugSlotWord (fileDutyRhoSlotFor I) σ_solm I :=
        accountMapEquiv_storage_findD hAccounts I.codeOwner
          (fileDutyRhoSlotFor I) ⟨0⟩
      have hleSolm :
          (jugSlotWord (fileDutyRhoSlotFor I) σ_solm I).toNat ≤
            (UInt256.ofNat I.header.timestamp).toNat := by
        rw [← hrhoWord]
        exact hle
      have hcodeSizeSolm :
          Reasoning.Theory.uniswapExtCodeSizeWord σ_solm
              (dripVatTargetWord σ_solm I) ≠ ⟨0⟩ :=
        dripVatCodeSize_ne_zero_accountMapEquiv hAccounts hvatCode
      have hvatCodeSolm :
          0 <
            (UInt256.ofNat
              (((initState cA gh bl σ_solm σ₀
                (Sat256.ofUInt256 g) A I).lookupAccount
                  (dripVatAddress σ_solm I)).option 0
                    (fun acc => acc.code.size))).toNat :=
        dripVatCode_pos_of_codeSize_ne_zero (cA := cA) (gh := gh)
          (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A)
          (I := I) (g := g) hcodeSizeSolm
      rcases hΘ with ⟨g'', A', hΘ'⟩
      have hdepthNe : evmE.executionEnv.depth ≠ 1024 := by
        intro hbad
        simp [evmE, initState] at hbad
        rw [hbad] at hdepth
        omega
      have htgtAddr :
          dripVatAddress σ_solm I =
            AccountAddress.ofUInt256 (dripVatTargetWord σ_evm I) := by
        rw [← dripVatAddress_accountMapEquiv hAccounts]
        exact dripVatAddress_eq_target σ_evm I
      have htgt :
          EVM.address (dripVatAddress σ_solm I) =
            AccountAddress.ofUInt256 (dripVatTargetWord σ_evm I) := by
        rw [htgtAddr]
        exact evmAddress_accountAddress _
      have hΘE :
          (cA', σ', g'', A', true, out) =
            Ethereum.EVM.Θ evmE.executionEnv.blobVersionedHashes
              evmE.createdAccounts evmE.genesisBlockHeader
              evmE.blocks evmE.accountMap evmE.σ₀ Ain
              (AccountAddress.ofUInt256
                (UInt256.ofNat evmE.executionEnv.codeOwner))
              evmE.executionEnv.sender
              (AccountAddress.ofUInt256 (dripVatTargetWord σ_evm I))
              (toExecute evmE.accountMap
                (AccountAddress.ofUInt256 (dripVatTargetWord σ_evm I)))
              callGas (UInt256.ofNat evmE.executionEnv.gasPrice)
              ⟨0⟩ ⟨0⟩
              ((dripVatIlksCalldataMem I
                (dripIlkHashMem I)).readWithPadding
                  dripVatIlksOutPtr.toNat dripVatIlksInSize.toNat)
              (evmE.executionEnv.depth + 1)
              evmE.executionEnv.header true := by
        simpa [evmE, initState, hperm] using hΘ'
      obtain ⟨σ'_solm, A'_solm, hcallSolm, hAccounts'⟩ :=
        typedCallViaEVM_callMade_accountMapEquiv
          (cfg := config) (evm_evm := evmE) (evm_solm := evmS)
          (tgt := EVM.address (dripVatAddress σ_solm I))
          (targetWord := dripVatTargetWord σ_evm I)
          (name := "ilks")
          (args := [.fixedBytes bytes32Width (fileDutyIlkBytes I)])
          (cA' := cA') (σ' := σ') (A' := A') (A_in := Ain)
          (z := true) (out := out) (g'' := g'')
          (callGas := callGas)
          (mem := dripVatIlksCalldataMem I (dripIlkHashMem I))
          (inOff := dripVatIlksOutPtr) (inSize := dripVatIlksInSize)
          (callPerm := true)
          hdepthNe htgt (dripVatIlksEncode_eq I hsz36) hΘE
          (show accountMapEquiv evmE.accountMap evmS.accountMap from hAccounts)
          (show evmE.σ₀ = evmS.σ₀ from rfl)
          (show evmS.createdAccounts = evmE.createdAccounts from rfl)
          (show evmS.genesisBlockHeader = evmE.genesisBlockHeader from rfl)
          (show evmS.blocks = evmE.blocks from rfl)
          (show evmS.substate = evmE.substate from rfl)
          (show evmS.executionEnv = evmE.executionEnv from rfl)
      let evmVatE :=
        { evmE with
          accountMap := σ',
          substate := A'_solm,
          createdAccounts := cA' }
      let evmVatS :=
        { evmS with
          accountMap := σ'_solm,
          substate := A'_solm,
          createdAccounts := cA' }
      have hfoldDepthNe : evmVatE.executionEnv.depth ≠ 1024 := by
        simpa [evmVatE] using hdepthNe
      have hfoldTargetAddr :
          dripVatAddress σ'_solm I =
            AccountAddress.ofUInt256 (dripVatTargetWord σ' I) := by
        rw [← dripVatAddress_accountMapEquiv hAccounts']
        exact dripVatAddress_eq_target σ' I
      have hfoldTarget :
          EVM.address (dripVatAddress σ'_solm I) =
            AccountAddress.ofUInt256 (dripVatTargetWord σ' I) := by
        rw [hfoldTargetAddr]
        exact evmAddress_accountAddress _
      have hvowWord :
          dripVowTargetWord σ'_solm I = dripVowTargetWord σ' I :=
        (dripVowTargetWord_accountMapEquiv hAccounts').symm
      have hfoldEncode :
          config.externalABI.encode? "fold"
              [.fixedBytes bytes32Width (fileDutyIlkBytes I),
                .address (AccountAddress.ofUInt256
                  (dripVowTargetWord σ'_solm I)),
                .int (((⟨0⟩ : UInt256).toNat : Int) -
                  ((dripVatIlksPrevWord out).toNat : Int))] =
            some ((dripVatFoldCalldataMem σ' I
              (UInt256.sub (⟨0⟩ : UInt256)
                (dripVatIlksPrevWord out)) foldBaseMem).readWithPadding
                  dripVatFoldOutPtr.toNat dripVatFoldInSize.toNat) := by
        rw [hvowWord]
        exact dripVatFoldEncode_signed_eq σ' I (⟨0⟩ : UInt256)
          (dripVatIlksPrevWord out)
          (UInt256.sub (⟨0⟩ : UInt256) (dripVatIlksPrevWord out))
          hfoldBaseSize hsz36 hzeroMax hprevMax rfl
      have hΘFoldE :
          (cA'', σ'', gFold'', AFold', true, foldOut) =
            Ethereum.EVM.Θ evmVatE.executionEnv.blobVersionedHashes
              evmVatE.createdAccounts evmVatE.genesisBlockHeader
              evmVatE.blocks evmVatE.accountMap evmVatE.σ₀ AinFold
              (AccountAddress.ofUInt256
                (UInt256.ofNat evmVatE.executionEnv.codeOwner))
              evmVatE.executionEnv.sender
              (AccountAddress.ofUInt256 (dripVatTargetWord σ' I))
              (toExecute evmVatE.accountMap
                (AccountAddress.ofUInt256 (dripVatTargetWord σ' I)))
              callGasFold
              (UInt256.ofNat evmVatE.executionEnv.gasPrice)
              ⟨0⟩ ⟨0⟩
              ((dripVatFoldCalldataMem σ' I
                (UInt256.sub (⟨0⟩ : UInt256)
                  (dripVatIlksPrevWord out)) foldBaseMem).readWithPadding
                    dripVatFoldOutPtr.toNat dripVatFoldInSize.toNat)
              (evmVatE.executionEnv.depth + 1)
              evmVatE.executionEnv.header true := by
        simpa [evmVatE, evmE, initState, hperm, foldBaseMem] using
          hΘFold'
      obtain ⟨σ''_solm, A''_solm, hfoldCallSolm, hAccounts''⟩ :=
        typedCallViaEVM_callMade_accountMapEquiv
          (cfg := config) (evm_evm := evmVatE) (evm_solm := evmVatS)
          (tgt := EVM.address (dripVatAddress σ'_solm I))
          (targetWord := dripVatTargetWord σ' I)
          (name := "fold")
          (args :=
            [.fixedBytes bytes32Width (fileDutyIlkBytes I),
              .address (AccountAddress.ofUInt256
                (dripVowTargetWord σ'_solm I)),
              .int (((⟨0⟩ : UInt256).toNat : Int) -
                ((dripVatIlksPrevWord out).toNat : Int))])
          (cA' := cA'') (σ' := σ'') (A' := AFold')
          (A_in := AinFold) (z := true) (out := foldOut)
          (g'' := gFold'') (callGas := callGasFold)
          (mem := dripVatFoldCalldataMem σ' I
            (UInt256.sub (⟨0⟩ : UInt256)
              (dripVatIlksPrevWord out)) foldBaseMem)
          (inOff := dripVatFoldOutPtr) (inSize := dripVatFoldInSize)
          (callPerm := true)
          hfoldDepthNe hfoldTarget hfoldEncode hΘFoldE
          (show accountMapEquiv evmVatE.accountMap evmVatS.accountMap from hAccounts')
          (show evmVatE.σ₀ = evmVatS.σ₀ from rfl)
          (show evmVatS.createdAccounts = evmVatE.createdAccounts from rfl)
          (show evmVatS.genesisBlockHeader = evmVatE.genesisBlockHeader from rfl)
          (show evmVatS.blocks = evmVatE.blocks from rfl)
          (show evmVatS.substate = evmVatE.substate from rfl)
          (show evmVatS.executionEnv = evmVatE.executionEnv from rfl)
      have hbaseWord : jugSlotWord ⟨4⟩ σ' I =
          jugSlotWord ⟨4⟩ σ'_solm I :=
        accountMapEquiv_storage_findD hAccounts' I.codeOwner
          ⟨4⟩ ⟨0⟩
      have hdutyWord :
          jugSlotWord (fileDutyDutySlotFor I) σ' I =
            jugSlotWord (fileDutyDutySlotFor I) σ'_solm I :=
        accountMapEquiv_storage_findD hAccounts' I.codeOwner
          (fileDutyDutySlotFor I) ⟨0⟩
      have haddNoSolm :
          ¬ UInt256.size ≤ (jugSlotWord ⟨4⟩ σ'_solm I).toNat +
            (jugSlotWord (fileDutyDutySlotFor I) σ'_solm I).toNat := by
        intro hbad
        exact haddOverflow (by
          simpa [hbaseWord, hdutyWord] using hbad)
      have hfeeZeroSolm :
          jugSlotWord ⟨4⟩ σ'_solm I +
              jugSlotWord (fileDutyDutySlotFor I) σ'_solm I =
            ⟨0⟩ := by
        simpa [fee, hbaseWord, hdutyWord] using hfeeZero
      have hrhoPostWord :
          jugSlotWord (fileDutyRhoSlotFor I) σ' I =
            jugSlotWord (fileDutyRhoSlotFor I) σ'_solm I :=
        accountMapEquiv_storage_findD hAccounts' I.codeOwner
          (fileDutyRhoSlotFor I) ⟨0⟩
      have hageNZSolm :
          UInt256.sub (UInt256.ofNat I.header.timestamp)
              (jugSlotWord (fileDutyRhoSlotFor I) σ'_solm I) ≠
            ⟨0⟩ := by
        intro hbad
        exact hageNZ (by simpa [age, hrhoPostWord] using hbad)
      have hfoldCodeSolmNe :
          Reasoning.Theory.uniswapExtCodeSizeWord σ'_solm
              (dripVatTargetWord σ'_solm I) ≠ ⟨0⟩ :=
        dripVatCodeSize_ne_zero_accountMapEquiv hAccounts'
          hfoldNoCode
      have hfoldCodeSolm :
          0 <
            (UInt256.ofNat
              ((evmVatS.lookupAccount
                (dripVatAddress evmVatS.accountMap
                  evmVatS.executionEnv)).option 0
                    (fun acc => acc.code.size))).toNat := by
        simpa [evmVatS, evmS, initState] using
          (dripVatCode_pos_of_codeSize_ne_zero (cA := cA')
            (gh := gh) (bl := bl) (σ := σ'_solm) (σ₀ := σ₀)
            (A := A'_solm) (I := I) (g := g) hfoldCodeSolmNe)
      let evmFoldS :=
        { evmVatS with
          accountMap := σ''_solm,
          substate := A''_solm,
          createdAccounts := cA'' }
      let finalLocals :=
        (dripDeltaLocalsInt I out
          (jugSlotWord ⟨4⟩ evmVatS.accountMap evmVatS.executionEnv +
            jugSlotWord (fileDutyDutySlotFor I) evmVatS.accountMap
              evmVatS.executionEnv)
          ⟨0⟩ ⟨0⟩
          (((⟨0⟩ : UInt256).toNat : Int) -
            ((dripVatIlksPrevWord out).toNat : Int))).insert
              "_foldRet" .unit
      let evmRhoS :=
        Solm.EVM.storageStore evmFoldS evmFoldS.executionEnv.codeOwner
          (fileDutyRhoSlotFor I)
          (UInt256.ofNat evmFoldS.executionEnv.header.timestamp)
      have hbody :
          ExecTransitionBody config contract evmS locals
            dripTransition.body
            (.returned { contract := contract, locals := finalLocals }
              evmRhoS
              (some [.int (Int.ofNat (⟨0⟩ : UInt256).toNat)])) := by
        simpa [evmS, evmVatS, evmFoldS, finalLocals, evmRhoS,
          locals, initState, jugSlotWord] using
          (jugDripSourceBodyVatFoldCallSucceededReturnsXZeroNNonzero
            (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
            (σ₀ := σ₀) (A := A) (I := I) (g := g)
            (evmVat := evmVatS) (evmFold := evmFoldS)
            (out := out) (foldOut := foldOut)
            hwv hsz36 hleSolm hvatCodeSolm
            (by simpa [evmS, evmVatS] using hcallSolm)
            _hdecOut
            (by
              simpa [evmVatS, evmS, initState, jugSlotWord] using
                haddNoSolm)
            (by
              simpa [evmVatS, evmS, initState, jugSlotWord] using
                hfeeZeroSolm)
            (by
              simpa [evmVatS, evmS, initState, jugSlotWord] using
                hageNZSolm)
            hprevMax hfoldCodeSolm
            (by simpa [evmVatS] using hfoldCallSolm))
      obtain ⟨_, _, rd1669⟩ :=
        RD.jugDripVatFoldCallSucceeded
          (targetWord := dripVatTargetWord σ' I) rd1651
      have hret := RD.jugDripVatFoldStoreRhoReturns
        (targetWord := dripVatTargetWord σ' I)
        hsz36 hperm hfoldCallMemSize hfoldCallMemRead64 rd1669
      exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch
        (jugDecode_drip_ok hsz36) hbody
        (by simp [evmRhoS, evmFoldS, storageStore_createdAccounts])
        (by
          simpa [evmRhoS, evmFoldS, storageStore_accountMap] using
            accountMapEquiv_sstoreAccountMap I.codeOwner
              (fileDutyRhoSlotFor I)
              (UInt256.ofNat I.header.timestamp) hAccounts'')
        (by
          rw [show dripTransition.returnType = [uint256] by rfl]
          exact returnEquiv_of_encode
            (by simpa [uint256] using
              uint256ReturnEncoding (⟨0⟩ : UInt256)))
"#

elab "jug_drip_fee_zero_tac" : tactic => do
  let tacSeq ← match Mathlib.GuardExceptions.parseAsTacticSeq (← getEnv) jugDripFeeZeroScript with
    | .ok tacSeq => pure tacSeq
    | .error err => throwError "failed to parse jug_drip_fee_zero_tac:
{err}"
  evalTactic (← `(tactic| ($tacSeq:tacticSeq)))

end Benchmarks.Dss.Jug
