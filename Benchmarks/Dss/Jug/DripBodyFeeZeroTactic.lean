import Benchmarks.Dss.Jug.DripBodyCore
import Mathlib.Util.ParseCommand
import Lean.Elab.Tactic

open Lean Elab Tactic
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Jug

set_option maxHeartbeats 1000000

private def jugDripFeeZeroScript : String := r#"
by_cases hprevMaxNot :
    ¬ ((dripVatIlksPrevWord out).toNat : Int) ≤ maxInt256
· let locals := dripLocals I
  let evm :=
    initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hvatCodeSolm :
      0 <
        (UInt256.ofNat
          (((initState σ σ₀
            (Sat256.ofUInt256 g) A I).lookupAccount
              (dripVatAddress σ I)).option 0
                (fun acc => acc.code.size))).toNat :=
    dripVatCode_pos_of_codeSize_ne_zero
      (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) hvatCode
  rcases hΘ with ⟨g'', A', hΘ'⟩
  have hdepthNe : evm.executionEnv.depth ≠ 1024 := by
    intro hbad
    simp [evm, initState] at hbad
    rw [hbad] at hdepth
    omega
  have htgtAddr :
      dripVatAddress σ I =
        AccountAddress.ofUInt256 (dripVatTargetWord σ I) :=
    dripVatAddress_eq_target σ I
  have htgt :
      EVM.address (dripVatAddress σ I) =
        AccountAddress.ofUInt256 (dripVatTargetWord σ I) := by
    rw [htgtAddr]
    exact evmAddress_accountAddress _
  have hΘE :
      (σ', g'', A', true, out) =
        Ethereum.EVM.Θ evm.accountMap evm.σ₀ Ain
          (AccountAddress.ofUInt256
            (UInt256.ofNat evm.executionEnv.codeOwner))
          evm.executionEnv.sender
          (AccountAddress.ofUInt256 (dripVatTargetWord σ I))
          (toExecute evm.accountMap
            (AccountAddress.ofUInt256 (dripVatTargetWord σ I)))
          callGas (UInt256.ofNat evm.executionEnv.gasPrice)
          ⟨0⟩ ⟨0⟩
          ((dripVatIlksCalldataMem I
            (dripIlkHashMem I)).readWithPadding
              dripVatIlksOutPtr.toNat dripVatIlksInSize.toNat)
          (evm.executionEnv.depth + 1)
          (evm.executionEnv.header) (evm.executionEnv.blobVersionedHashes) (evm.executionEnv.blocks) true := by
    simpa [evm, initState, hperm] using hΘ'
  have hcall :
      typedCallViaEVM config evm (EVM.address (dripVatAddress σ I)) "ilks" 0
        [.fixedBytes bytes32Width (fileDutyIlkBytes I)]
        (true, { evm with accountMap := σ', substate := A' }, out) true :=
    callCoincides hdepthNe htgt (dripVatIlksEncode_eq I hsz36) hΘE
  have hbody :
      ExecTransitionBody config contract evm locals
        dripTransition.body .reverted := by
    simpa [evm, locals, initState, jugSlotWord] using
      (jugDripSourceBodyVatIlksDiffYBoundRevertsXZeroNNonzero
        (σ := σ)
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (evmVat := { evm with accountMap := σ', substate := A' })
        (out := out) hwv hsz36 hle hvatCodeSolm
        (by simpa [evm] using hcall) _hdecOut
        (by
          simpa [evm, initState, jugSlotWord] using
            haddOverflow)
        (by
          simpa [evm, initState, jugSlotWord, fee] using
            hfeeZero)
        (by
          simpa [evm, initState, jugSlotWord, age] using
            hageNZ)
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
      Reasoning.Theory.extCodeSizeWord σ'
        (dripVatTargetWord σ' I) = ⟨0⟩
  · let locals := dripLocals I
    let evm :=
      initState σ σ₀ (Sat256.ofUInt256 g) A I
    have hvatCodeSolm :
        0 <
          (UInt256.ofNat
            (((initState σ σ₀
              (Sat256.ofUInt256 g) A I).lookupAccount
                (dripVatAddress σ I)).option 0
                  (fun acc => acc.code.size))).toNat :=
      dripVatCode_pos_of_codeSize_ne_zero
        (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) hvatCode
    rcases hΘ with ⟨g'', A', hΘ'⟩
    have hdepthNe : evm.executionEnv.depth ≠ 1024 := by
      intro hbad
      simp [evm, initState] at hbad
      rw [hbad] at hdepth
      omega
    have htgtAddr :
        dripVatAddress σ I =
          AccountAddress.ofUInt256 (dripVatTargetWord σ I) := by
      exact dripVatAddress_eq_target σ I
    have htgt :
        EVM.address (dripVatAddress σ I) =
          AccountAddress.ofUInt256 (dripVatTargetWord σ I) := by
      rw [htgtAddr]
      exact evmAddress_accountAddress _
    have hΘE :
        (σ', g'', A', true, out) =
          Ethereum.EVM.Θ evm.accountMap evm.σ₀ Ain
            (AccountAddress.ofUInt256
              (UInt256.ofNat evm.executionEnv.codeOwner))
            evm.executionEnv.sender
            (AccountAddress.ofUInt256 (dripVatTargetWord σ I))
            (toExecute evm.accountMap
              (AccountAddress.ofUInt256 (dripVatTargetWord σ I)))
            callGas (UInt256.ofNat evm.executionEnv.gasPrice)
            ⟨0⟩ ⟨0⟩
            ((dripVatIlksCalldataMem I
              (dripIlkHashMem I)).readWithPadding
                dripVatIlksOutPtr.toNat dripVatIlksInSize.toNat)
            (evm.executionEnv.depth + 1)
            (evm.executionEnv.header) (evm.executionEnv.blobVersionedHashes) (evm.executionEnv.blocks) true := by
      simpa [evm, initState, hperm] using hΘ'
    have hcall :
        typedCallViaEVM config evm (EVM.address (dripVatAddress σ I)) "ilks" 0
          [.fixedBytes bytes32Width (fileDutyIlkBytes I)]
          (true, { evm with accountMap := σ', substate := A' }, out) true :=
      callCoincides hdepthNe htgt (dripVatIlksEncode_eq I hsz36) hΘE
    have hfoldNoCodeSolmRaw :
        (UInt256.ofNat
          ((σ'.get? (dripVatAddress σ' I)).option 0
            (fun acc => acc.code.size))).toNat = 0 :=
      drip_extCodeSizeWord_zero_lookup_code_zero
        (σ := σ') (target := dripVatTargetWord σ' I)
        (addr := dripVatAddress σ' I)
        (dripVatAddress_eq_target σ' I) hfoldNoCode
    have hbody :
        ExecTransitionBody config contract evm locals
          dripTransition.body .reverted := by
      simpa [evm, locals, initState, jugSlotWord] using
        (jugDripSourceBodyVatFoldNoCodeRevertsXZeroNNonzero
          (σ := σ)
          (σ₀ := σ₀) (A := A) (I := I) (g := g)
          (evmVat := { evm with accountMap := σ', substate := A' })
          (out := out) hwv hsz36 hle hvatCodeSolm
          (by simpa [evm] using hcall) _hdecOut
          (by
            simpa [evm, initState, jugSlotWord] using
              haddOverflow)
          (by
            simpa [evm, initState, jugSlotWord, fee] using
              hfeeZero)
          (by
            simpa [evm, initState, jugSlotWord, age] using
              hageNZ)
          hprevMax
          (by
            simpa [evm, initState, State.lookupAccount] using
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
    let evm :=
      initState σ σ₀ (Sat256.ofUInt256 g) A I
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
      ⟨σ'', z, foldOut, AinFold, callGasFold, _, _,
        hΘFold, rd1651, hfoldOutSize⟩ :=
      RD.jugDripVatFoldPostCall rd1650 hdepth
    cases z
    · rcases hΘFold with ⟨gFold'', AFold', hΘFold'⟩
      have hvatCodeSolm :
          0 <
            (UInt256.ofNat
              (((initState σ σ₀
                (Sat256.ofUInt256 g) A I).lookupAccount
                  (dripVatAddress σ I)).option 0
                    (fun acc => acc.code.size))).toNat :=
        dripVatCode_pos_of_codeSize_ne_zero
          (σ := σ) (σ₀ := σ₀) (A := A)
          (I := I) (g := g) hvatCode
      rcases hΘ with ⟨g'', A', hΘ'⟩
      have hdepthNe : evm.executionEnv.depth ≠ 1024 := by
        intro hbad
        simp [evm, initState] at hbad
        rw [hbad] at hdepth
        omega
      have htgtAddr :
          dripVatAddress σ I =
            AccountAddress.ofUInt256 (dripVatTargetWord σ I) := by
        exact dripVatAddress_eq_target σ I
      have htgt :
          EVM.address (dripVatAddress σ I) =
            AccountAddress.ofUInt256 (dripVatTargetWord σ I) := by
        rw [htgtAddr]
        exact evmAddress_accountAddress _
      have hΘE :
          (σ', g'', A', true, out) =
            Ethereum.EVM.Θ evm.accountMap evm.σ₀ Ain
              (AccountAddress.ofUInt256
                (UInt256.ofNat evm.executionEnv.codeOwner))
              evm.executionEnv.sender
              (AccountAddress.ofUInt256 (dripVatTargetWord σ I))
              (toExecute evm.accountMap
                (AccountAddress.ofUInt256 (dripVatTargetWord σ I)))
              callGas (UInt256.ofNat evm.executionEnv.gasPrice)
              ⟨0⟩ ⟨0⟩
              ((dripVatIlksCalldataMem I
                (dripIlkHashMem I)).readWithPadding
                  dripVatIlksOutPtr.toNat dripVatIlksInSize.toNat)
              (evm.executionEnv.depth + 1)
              (evm.executionEnv.header) (evm.executionEnv.blobVersionedHashes) (evm.executionEnv.blocks) true := by
        simpa [evm, initState, hperm] using hΘ'
      have hcall :
          typedCallViaEVM config evm (EVM.address (dripVatAddress σ I)) "ilks" 0
            [.fixedBytes bytes32Width (fileDutyIlkBytes I)]
            (true, { evm with accountMap := σ', substate := A' }, out) true :=
        callCoincides hdepthNe htgt (dripVatIlksEncode_eq I hsz36) hΘE
      let evmVat := { evm with accountMap := σ', substate := A' }
      have hfoldDepthNe : evmVat.executionEnv.depth ≠ 1024 := by
        simpa [evmVat] using hdepthNe
      have hfoldTargetAddr :
          dripVatAddress σ' I =
            AccountAddress.ofUInt256 (dripVatTargetWord σ' I) :=
        dripVatAddress_eq_target σ' I
      have hfoldTarget :
          EVM.address (dripVatAddress σ' I) =
            AccountAddress.ofUInt256 (dripVatTargetWord σ' I) := by
        rw [hfoldTargetAddr]
        exact evmAddress_accountAddress _
      have hfoldEncode :
          config.externalABI.encode? "fold"
              [.fixedBytes bytes32Width (fileDutyIlkBytes I),
                .address (AccountAddress.ofUInt256
                  (dripVowTargetWord σ' I)),
                .int (((⟨0⟩ : UInt256).toNat : Int) -
                  ((dripVatIlksPrevWord out).toNat : Int))] =
            some ((dripVatFoldCalldataMem σ' I
              (UInt256.sub (⟨0⟩ : UInt256)
                (dripVatIlksPrevWord out)) foldBaseMem).readWithPadding
                  dripVatFoldOutPtr.toNat dripVatFoldInSize.toNat) :=
        dripVatFoldEncode_signed_eq σ' I (⟨0⟩ : UInt256)
          (dripVatIlksPrevWord out)
          (UInt256.sub (⟨0⟩ : UInt256) (dripVatIlksPrevWord out))
          hfoldBaseSize hsz36 hzeroMax hprevMax rfl
      have hΘFoldE :
          (σ'', gFold'', AFold', false, foldOut) =
            Ethereum.EVM.Θ evmVat.accountMap evmVat.σ₀ AinFold
              (AccountAddress.ofUInt256
                (UInt256.ofNat evmVat.executionEnv.codeOwner))
              evmVat.executionEnv.sender
              (AccountAddress.ofUInt256 (dripVatTargetWord σ' I))
              (toExecute evmVat.accountMap
                (AccountAddress.ofUInt256 (dripVatTargetWord σ' I)))
              callGasFold
              (UInt256.ofNat evmVat.executionEnv.gasPrice)
              ⟨0⟩ ⟨0⟩
              ((dripVatFoldCalldataMem σ' I
                (UInt256.sub (⟨0⟩ : UInt256)
                  (dripVatIlksPrevWord out)) foldBaseMem).readWithPadding
                    dripVatFoldOutPtr.toNat dripVatFoldInSize.toNat)
              (evmVat.executionEnv.depth + 1)
              (evmVat.executionEnv.header) (evmVat.executionEnv.blobVersionedHashes) (evmVat.executionEnv.blocks) true := by
        simpa [evmVat, evm, initState, hperm, foldBaseMem] using
          hΘFold'
      have hfoldCall :
          typedCallViaEVM config evmVat (EVM.address (dripVatAddress σ' I))
            "fold" 0
            [.fixedBytes bytes32Width (fileDutyIlkBytes I),
              .address (AccountAddress.ofUInt256 (dripVowTargetWord σ' I)),
              .int (((⟨0⟩ : UInt256).toNat : Int) -
                ((dripVatIlksPrevWord out).toNat : Int))]
            (false, { evmVat with accountMap := σ'', substate := AFold' }, foldOut)
            true :=
        callCoincides hfoldDepthNe hfoldTarget hfoldEncode hΘFoldE
      have hfoldCodeSolm :
          0 <
            (UInt256.ofNat
              ((evmVat.lookupAccount
                (dripVatAddress evmVat.accountMap
                  evmVat.executionEnv)).option 0
                    (fun acc => acc.code.size))).toNat := by
        simpa [evmVat, evm, initState] using
              (dripVatCode_pos_of_codeSize_ne_zero
            (σ := σ') (σ₀ := σ₀)
            (A := A') (I := I) (g := g) hfoldNoCode)
      have hbody :
          ExecTransitionBody config contract evm locals
            dripTransition.body .reverted := by
        simpa [evm, evmVat, locals, initState, jugSlotWord] using
          (jugDripSourceBodyVatFoldCallFailedRevertsXZeroNNonzero
            (σ := σ)
            (σ₀ := σ₀) (A := A) (I := I) (g := g)
            (evmVat := evmVat)
            (evmFold :=
              { evmVat with
                accountMap := σ'',
                substate := AFold' })
            (out := out) (foldOut := foldOut)
            hwv hsz36 hle hvatCodeSolm
            (by simpa [evm, evmVat] using hcall)
            _hdecOut
            (by
              simpa [evmVat, evm, initState, jugSlotWord] using
                haddOverflow)
            (by
              simpa [evmVat, evm, initState, jugSlotWord] using
                (by simpa [fee] using hfeeZero))
            (by
              simpa [evmVat, evm, initState, jugSlotWord] using
                (by simpa [age] using hageNZ))
            hprevMax hfoldCodeSolm
            (by simpa [evmVat] using hfoldCall))
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
      have hvatCodeSolm :
          0 <
            (UInt256.ofNat
              (((initState σ σ₀
                (Sat256.ofUInt256 g) A I).lookupAccount
                  (dripVatAddress σ I)).option 0
                    (fun acc => acc.code.size))).toNat :=
        dripVatCode_pos_of_codeSize_ne_zero
          (σ := σ) (σ₀ := σ₀) (A := A)
          (I := I) (g := g) hvatCode
      rcases hΘ with ⟨g'', A', hΘ'⟩
      have hdepthNe : evm.executionEnv.depth ≠ 1024 := by
        intro hbad
        simp [evm, initState] at hbad
        rw [hbad] at hdepth
        omega
      have htgtAddr :
          dripVatAddress σ I =
            AccountAddress.ofUInt256 (dripVatTargetWord σ I) := by
        exact dripVatAddress_eq_target σ I
      have htgt :
          EVM.address (dripVatAddress σ I) =
            AccountAddress.ofUInt256 (dripVatTargetWord σ I) := by
        rw [htgtAddr]
        exact evmAddress_accountAddress _
      have hΘE :
          (σ', g'', A', true, out) =
            Ethereum.EVM.Θ evm.accountMap evm.σ₀ Ain
              (AccountAddress.ofUInt256
                (UInt256.ofNat evm.executionEnv.codeOwner))
              evm.executionEnv.sender
              (AccountAddress.ofUInt256 (dripVatTargetWord σ I))
              (toExecute evm.accountMap
                (AccountAddress.ofUInt256 (dripVatTargetWord σ I)))
              callGas (UInt256.ofNat evm.executionEnv.gasPrice)
              ⟨0⟩ ⟨0⟩
              ((dripVatIlksCalldataMem I
                (dripIlkHashMem I)).readWithPadding
                  dripVatIlksOutPtr.toNat dripVatIlksInSize.toNat)
              (evm.executionEnv.depth + 1)
              (evm.executionEnv.header) (evm.executionEnv.blobVersionedHashes) (evm.executionEnv.blocks) true := by
        simpa [evm, initState, hperm] using hΘ'
      have hcall :
          typedCallViaEVM config evm (EVM.address (dripVatAddress σ I)) "ilks" 0
            [.fixedBytes bytes32Width (fileDutyIlkBytes I)]
            (true, { evm with accountMap := σ', substate := A' }, out) true :=
        callCoincides hdepthNe htgt (dripVatIlksEncode_eq I hsz36) hΘE
      let evmVat := { evm with accountMap := σ', substate := A' }
      have hfoldDepthNe : evmVat.executionEnv.depth ≠ 1024 := by
        simpa [evmVat] using hdepthNe
      have hfoldTargetAddr :
          dripVatAddress σ' I =
            AccountAddress.ofUInt256 (dripVatTargetWord σ' I) :=
        dripVatAddress_eq_target σ' I
      have hfoldTarget :
          EVM.address (dripVatAddress σ' I) =
            AccountAddress.ofUInt256 (dripVatTargetWord σ' I) := by
        rw [hfoldTargetAddr]
        exact evmAddress_accountAddress _
      have hfoldEncode :
          config.externalABI.encode? "fold"
              [.fixedBytes bytes32Width (fileDutyIlkBytes I),
                .address (AccountAddress.ofUInt256
                  (dripVowTargetWord σ' I)),
                .int (((⟨0⟩ : UInt256).toNat : Int) -
                  ((dripVatIlksPrevWord out).toNat : Int))] =
            some ((dripVatFoldCalldataMem σ' I
              (UInt256.sub (⟨0⟩ : UInt256)
                (dripVatIlksPrevWord out)) foldBaseMem).readWithPadding
                  dripVatFoldOutPtr.toNat dripVatFoldInSize.toNat) :=
        dripVatFoldEncode_signed_eq σ' I (⟨0⟩ : UInt256)
          (dripVatIlksPrevWord out)
          (UInt256.sub (⟨0⟩ : UInt256) (dripVatIlksPrevWord out))
          hfoldBaseSize hsz36 hzeroMax hprevMax rfl
      have hΘFoldE :
          (σ'', gFold'', AFold', true, foldOut) =
            Ethereum.EVM.Θ evmVat.accountMap evmVat.σ₀ AinFold
              (AccountAddress.ofUInt256
                (UInt256.ofNat evmVat.executionEnv.codeOwner))
              evmVat.executionEnv.sender
              (AccountAddress.ofUInt256 (dripVatTargetWord σ' I))
              (toExecute evmVat.accountMap
                (AccountAddress.ofUInt256 (dripVatTargetWord σ' I)))
              callGasFold
              (UInt256.ofNat evmVat.executionEnv.gasPrice)
              ⟨0⟩ ⟨0⟩
              ((dripVatFoldCalldataMem σ' I
                (UInt256.sub (⟨0⟩ : UInt256)
                  (dripVatIlksPrevWord out)) foldBaseMem).readWithPadding
                    dripVatFoldOutPtr.toNat dripVatFoldInSize.toNat)
              (evmVat.executionEnv.depth + 1)
              (evmVat.executionEnv.header) (evmVat.executionEnv.blobVersionedHashes) (evmVat.executionEnv.blocks) true := by
        simpa [evmVat, evm, initState, hperm, foldBaseMem] using
          hΘFold'
      have hfoldCall :
          typedCallViaEVM config evmVat (EVM.address (dripVatAddress σ' I))
            "fold" 0
            [.fixedBytes bytes32Width (fileDutyIlkBytes I),
              .address (AccountAddress.ofUInt256 (dripVowTargetWord σ' I)),
              .int (((⟨0⟩ : UInt256).toNat : Int) -
                ((dripVatIlksPrevWord out).toNat : Int))]
            (true, { evmVat with accountMap := σ'', substate := AFold' }, foldOut)
            true :=
        callCoincides hfoldDepthNe hfoldTarget hfoldEncode hΘFoldE
      have hfoldCodeSolm :
          0 <
            (UInt256.ofNat
              ((evmVat.lookupAccount
                (dripVatAddress evmVat.accountMap
                  evmVat.executionEnv)).option 0
                    (fun acc => acc.code.size))).toNat := by
        simpa [evmVat, evm, initState] using
              (dripVatCode_pos_of_codeSize_ne_zero
            (σ := σ') (σ₀ := σ₀)
            (A := A') (I := I) (g := g) hfoldNoCode)
      let evmFoldS :=
        { evmVat with
          accountMap := σ'',
          substate := AFold' }
      let finalLocals :=
        (dripDeltaLocalsInt I out
          (jugSlotWord ⟨4⟩ evmVat.accountMap evmVat.executionEnv +
            jugSlotWord (fileDutyDutySlotFor I) evmVat.accountMap
              evmVat.executionEnv)
          ⟨0⟩ ⟨0⟩
          (((⟨0⟩ : UInt256).toNat : Int) -
            ((dripVatIlksPrevWord out).toNat : Int))).insert
              "_foldRet" .unit
      let evmRhoS :=
        Solm.EVM.storageStore evmFoldS evmFoldS.executionEnv.codeOwner
          (fileDutyRhoSlotFor I)
          (UInt256.ofNat evmFoldS.executionEnv.header.timestamp)
      have hbody :
          ExecTransitionBody config contract evm locals
            dripTransition.body
            (.returned { contract := contract, locals := finalLocals }
              evmRhoS
              (some [.int (Int.ofNat (⟨0⟩ : UInt256).toNat)])) := by
        simpa [evm, evmVat, evmFoldS, finalLocals, evmRhoS,
          locals, initState, jugSlotWord] using
          (jugDripSourceBodyVatFoldCallSucceededReturnsXZeroNNonzero
            (σ := σ)
            (σ₀ := σ₀) (A := A) (I := I) (g := g)
            (evmVat := evmVat) (evmFold := evmFoldS)
            (out := out) (foldOut := foldOut)
            hwv hsz36 hle hvatCodeSolm
            (by simpa [evm, evmVat] using hcall)
            _hdecOut
            (by
              simpa [evmVat, evm, initState, jugSlotWord] using
                haddOverflow)
            (by
              simpa [evmVat, evm, initState, jugSlotWord] using
                (by simpa [fee] using hfeeZero))
            (by
              simpa [evmVat, evm, initState, jugSlotWord] using
                (by simpa [age] using hageNZ))
            hprevMax hfoldCodeSolm
            (by simpa [evmVat] using hfoldCall))
      obtain ⟨_, _, rd1669⟩ :=
        RD.jugDripVatFoldCallSucceeded
          (targetWord := dripVatTargetWord σ' I) rd1651
      have hret := RD.jugDripVatFoldStoreRhoReturns
        (targetWord := dripVatTargetWord σ' I)
        hsz36 hperm hfoldCallMemSize hfoldCallMemRead64 rd1669
      exact hret.reEquivExecutionGen hcode hdispatch
        (jugDecode_drip_ok hsz36) hbody
        (by simp [evmRhoS, evmFoldS, evmVat, evm, initState,
          storageStore_accountMap])
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
