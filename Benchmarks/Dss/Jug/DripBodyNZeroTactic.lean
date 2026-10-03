import Benchmarks.Dss.Jug.DripBodyFeeZeroTactic
import Benchmarks.Dss.Jug.DripBodyAgeOneTactic
import Mathlib.Util.ParseCommand
import Lean.Elab.Tactic

open Lean Elab Tactic
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Jug

set_option maxHeartbeats 1000000

private def jugDripNZeroScript : String := r#"
by_cases hRmulOverflowNZero :
    age = ⟨0⟩ ∧
      ¬ jugRay.toNat * (dripVatIlksPrevWord out).toNat < UInt256.size
· rcases hRmulOverflowNZero with ⟨hage0, hfitRmulNot⟩
  have hRmulOverflow :
      UInt256.size ≤ jugRay.toNat * (dripVatIlksPrevWord out).toNat := by
    omega
  let locals := dripLocals I
  let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hrhoWord : jugSlotWord (fileDutyRhoSlotFor I) σ I =
      jugSlotWord (fileDutyRhoSlotFor I) σ I := rfl
  have hleSolm :
      (jugSlotWord (fileDutyRhoSlotFor I) σ I).toNat ≤
        (UInt256.ofNat I.header.timestamp).toNat := by
    rw [← hrhoWord]
    exact hle
  have hcodeSizeSolm :
      Reasoning.Theory.extCodeSizeWord σ
          (dripVatTargetWord σ I) ≠ ⟨0⟩ := hvatCode
  have hvatCodeSolm :
      0 <
        (UInt256.ofNat
          (((initState σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
            (dripVatAddress σ I)).option 0
              (fun acc => acc.code.size))).toNat :=
    dripVatCode_pos_of_codeSize_ne_zero
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcodeSizeSolm
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
          (AccountAddress.ofUInt256 (UInt256.ofNat evm.executionEnv.codeOwner))
          evm.executionEnv.sender
          (AccountAddress.ofUInt256 (dripVatTargetWord σ I))
          (toExecute evm.accountMap
            (AccountAddress.ofUInt256 (dripVatTargetWord σ I)))
          callGas (UInt256.ofNat evm.executionEnv.gasPrice) ⟨0⟩ ⟨0⟩
          ((dripVatIlksCalldataMem I (dripIlkHashMem I)).readWithPadding
            dripVatIlksOutPtr.toNat dripVatIlksInSize.toNat)
          (evm.executionEnv.depth + 1) evm.executionEnv.header
          evm.executionEnv.blobVersionedHashes evm.executionEnv.blocks true := by
    simpa [evm, initState, hperm] using hΘ'
  let σ'_solm := σ'
  let A'_solm := A'
  have hcallSolm :
      typedCallViaEVM config evm (EVM.address (dripVatAddress σ I)) "ilks" 0
        [.fixedBytes bytes32Width (fileDutyIlkBytes I)]
        (true, { evm with accountMap := σ', substate := A' }, out) true := by
    simpa [evm] using
      callCoincides hdepthNe htgt (dripVatIlksEncode_eq I hsz36) hΘE
  have hbaseWord : jugSlotWord ⟨4⟩ σ' I = jugSlotWord ⟨4⟩ σ'_solm I := by rfl
  have hdutyWord : jugSlotWord (fileDutyDutySlotFor I) σ' I = jugSlotWord (fileDutyDutySlotFor I) σ'_solm I := by rfl
  have haddNoSolm :
      ¬ UInt256.size ≤ (jugSlotWord ⟨4⟩ σ'_solm I).toNat +
        (jugSlotWord (fileDutyDutySlotFor I) σ'_solm I).toNat := by
    intro hbad
    exact haddOverflow (by
      simpa [hbaseWord, hdutyWord] using hbad)
  have hrhoPostWord : jugSlotWord (fileDutyRhoSlotFor I) σ' I = jugSlotWord (fileDutyRhoSlotFor I) σ'_solm I := by rfl
  have hage0Evm :
      UInt256.sub (UInt256.ofNat I.header.timestamp)
        (jugSlotWord (fileDutyRhoSlotFor I) σ' I) = ⟨0⟩ := by
    simpa [age] using hage0
  have hage0Solm :
      UInt256.sub (UInt256.ofNat I.header.timestamp)
        (jugSlotWord (fileDutyRhoSlotFor I) σ'_solm I) = ⟨0⟩ := by
    rw [← hrhoPostWord]
    exact hage0Evm
  have hbody :
      ExecTransitionBody config contract evm locals dripTransition.body .reverted := by
    simpa [evm, locals, initState, jugSlotWord] using
      (jugDripSourceBodyVatIlksRmulOverflowReverts
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
        (g := g)
        (evmVat :=
          { evm with
            accountMap := σ'_solm
            substate := A'_solm })
        (out := out) hwv hsz36 hleSolm hvatCodeSolm
        (by simpa [evm] using hcallSolm) _hdecOut
        (by simpa [evm, initState, jugSlotWord] using haddNoSolm)
        (by simpa [evm, initState, jugSlotWord] using hage0Solm)
        hRmulOverflow)
  obtain ⟨_, _, rd1524⟩ := _rpowNZeroProgress hage0
  have hrev := RD.jugDripRmulRayOverflowReverts
    (R := [⟨0⟩, fileDutyIlkWord I, ⟨357⟩, jugSelWord I])
    (by simp) hRmulOverflow rd1524
  exact hrev.reEquivExecutionRevert hcode hdispatch
    (jugDecode_drip_ok hsz36) hbody
· by_cases hFoldNoCodeNZero :
      age = ⟨0⟩ ∧
        jugRay.toNat * (dripVatIlksPrevWord out).toNat < UInt256.size ∧
        ((dripVatIlksPrevWord out).toNat : Int) ≤ maxInt256 ∧
        Reasoning.Theory.extCodeSizeWord σ'
          (dripVatTargetWord σ' I) = ⟨0⟩
  · rcases hFoldNoCodeNZero with
      ⟨hage0, hfitRmul, hprevMax, hfoldCode⟩
    let locals := dripLocals I
    let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
    have hrhoWord : jugSlotWord (fileDutyRhoSlotFor I) σ I =
        jugSlotWord (fileDutyRhoSlotFor I) σ I :=
      rfl
    have hleSolm :
        (jugSlotWord (fileDutyRhoSlotFor I) σ I).toNat ≤
          (UInt256.ofNat I.header.timestamp).toNat := by
      rw [← hrhoWord]
      exact hle
    have hcodeSizeSolm :
        Reasoning.Theory.extCodeSizeWord σ
            (dripVatTargetWord σ I) ≠ ⟨0⟩ :=
      hvatCode
    have hvatCodeSolm :
        0 <
          (UInt256.ofNat
            (((initState σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
              (dripVatAddress σ I)).option 0
                (fun acc => acc.code.size))).toNat :=
      dripVatCode_pos_of_codeSize_ne_zero
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcodeSizeSolm
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
            callGas (UInt256.ofNat evm.executionEnv.gasPrice) ⟨0⟩ ⟨0⟩
            ((dripVatIlksCalldataMem I (dripIlkHashMem I)).readWithPadding
              dripVatIlksOutPtr.toNat dripVatIlksInSize.toNat)
            (evm.executionEnv.depth + 1) (evm.executionEnv.header) (evm.executionEnv.blobVersionedHashes) (evm.executionEnv.blocks) true := by
      simpa [evm, initState, hperm] using hΘ'
    let σ'_solm := σ'
    let A'_solm := A'
    have hcallSolm :
        typedCallViaEVM config evm (EVM.address (dripVatAddress σ I)) "ilks" 0
          [.fixedBytes bytes32Width (fileDutyIlkBytes I)]
          (true, { evm with accountMap := σ', substate := A' }, out) true := by
      simpa [evm] using
        callCoincides hdepthNe htgt (dripVatIlksEncode_eq I hsz36) hΘE
    have hbaseWord : jugSlotWord ⟨4⟩ σ' I = jugSlotWord ⟨4⟩ σ'_solm I := by rfl
    have hdutyWord : jugSlotWord (fileDutyDutySlotFor I) σ' I = jugSlotWord (fileDutyDutySlotFor I) σ'_solm I := by rfl
    have haddNoSolm :
        ¬ UInt256.size ≤ (jugSlotWord ⟨4⟩ σ'_solm I).toNat +
          (jugSlotWord (fileDutyDutySlotFor I) σ'_solm I).toNat := by
      intro hbad
      exact haddOverflow (by
        simpa [hbaseWord, hdutyWord] using hbad)
    have hrhoPostWord : jugSlotWord (fileDutyRhoSlotFor I) σ' I = jugSlotWord (fileDutyRhoSlotFor I) σ'_solm I := by rfl
    have hage0Evm :
        UInt256.sub (UInt256.ofNat I.header.timestamp)
          (jugSlotWord (fileDutyRhoSlotFor I) σ' I) = ⟨0⟩ := by
      simpa [age] using hage0
    have hage0Solm :
        UInt256.sub (UInt256.ofNat I.header.timestamp)
          (jugSlotWord (fileDutyRhoSlotFor I) σ'_solm I) = ⟨0⟩ := by
      rw [← hrhoPostWord]
      exact hage0Evm
    have hfoldCodeSolm :
        Reasoning.Theory.extCodeSizeWord σ'_solm
            (dripVatTargetWord σ'_solm I) = ⟨0⟩ :=
      by simpa [σ'_solm] using hfoldCode
    have hfoldNoCodeSolmRaw :
        (UInt256.ofNat
          ((σ'_solm.find? (dripVatAddress σ'_solm I)).option 0
            (fun acc => acc.code.size))).toNat = 0 :=
      drip_extCodeSizeWord_zero_lookup_code_zero
        (σ := σ'_solm) (target := dripVatTargetWord σ'_solm I)
        (addr := dripVatAddress σ'_solm I)
        (dripVatAddress_eq_target σ'_solm I) hfoldCodeSolm
    have hbody :
        ExecTransitionBody config contract evm locals dripTransition.body
          .reverted := by
      simpa [evm, locals, initState, jugSlotWord] using
        (jugDripSourceBodyVatFoldNoCodeReverts
          (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
          (g := g)
          (evmVat :=
            { evm with
              accountMap := σ'_solm
              substate := A'_solm })
          (out := out) hwv hsz36 hleSolm hvatCodeSolm
          (by simpa [evm] using hcallSolm) _hdecOut
          (by simpa [evm, initState, jugSlotWord] using haddNoSolm)
          (by simpa [evm, initState, jugSlotWord] using hage0Solm)
          hfitRmul hprevMax
          (by
            simpa [evm, initState, State.lookupAccount] using
              hfoldNoCodeSolmRaw))
    have hrev := _foldNZeroNoCode hage0 hfitRmul hprevMax hfoldCode
    exact hrev.reEquivExecutionRevert hcode hdispatch
      (jugDecode_drip_ok hsz36) hbody
  · by_cases hDiffBoundNZero :
        age = ⟨0⟩ ∧
          jugRay.toNat * (dripVatIlksPrevWord out).toNat < UInt256.size ∧
          ¬ ((dripVatIlksPrevWord out).toNat : Int) ≤ maxInt256
    · rcases hDiffBoundNZero with ⟨hage0, hfitRmul, hprevMaxNot⟩
      let locals := dripLocals I
      let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
      have hrhoWord : jugSlotWord (fileDutyRhoSlotFor I) σ I =
          jugSlotWord (fileDutyRhoSlotFor I) σ I :=
        rfl
      have hleSolm :
          (jugSlotWord (fileDutyRhoSlotFor I) σ I).toNat ≤
            (UInt256.ofNat I.header.timestamp).toNat := by
        rw [← hrhoWord]
        exact hle
      have hcodeSizeSolm :
          Reasoning.Theory.extCodeSizeWord σ
              (dripVatTargetWord σ I) ≠ ⟨0⟩ :=
        hvatCode
      have hvatCodeSolm :
          0 <
            (UInt256.ofNat
              (((initState σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
                (dripVatAddress σ I)).option 0
                  (fun acc => acc.code.size))).toNat :=
        dripVatCode_pos_of_codeSize_ne_zero
          (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcodeSizeSolm
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
              callGas (UInt256.ofNat evm.executionEnv.gasPrice) ⟨0⟩ ⟨0⟩
              ((dripVatIlksCalldataMem I (dripIlkHashMem I)).readWithPadding
                dripVatIlksOutPtr.toNat dripVatIlksInSize.toNat)
              (evm.executionEnv.depth + 1) (evm.executionEnv.header) (evm.executionEnv.blobVersionedHashes) (evm.executionEnv.blocks) true := by
        simpa [evm, initState, hperm] using hΘ'
      let σ'_solm := σ'
      let A'_solm := A'
      have hcallSolm :
          typedCallViaEVM config evm (EVM.address (dripVatAddress σ I)) "ilks" 0
            [.fixedBytes bytes32Width (fileDutyIlkBytes I)]
            (true, { evm with accountMap := σ', substate := A' }, out) true := by
        simpa [evm] using
          callCoincides hdepthNe htgt (dripVatIlksEncode_eq I hsz36) hΘE
      have hbaseWord : jugSlotWord ⟨4⟩ σ' I = jugSlotWord ⟨4⟩ σ'_solm I := by rfl
      have hdutyWord : jugSlotWord (fileDutyDutySlotFor I) σ' I = jugSlotWord (fileDutyDutySlotFor I) σ'_solm I := by rfl
      have haddNoSolm :
          ¬ UInt256.size ≤ (jugSlotWord ⟨4⟩ σ'_solm I).toNat +
            (jugSlotWord (fileDutyDutySlotFor I) σ'_solm I).toNat := by
        intro hbad
        exact haddOverflow (by
          simpa [hbaseWord, hdutyWord] using hbad)
      have hrhoPostWord : jugSlotWord (fileDutyRhoSlotFor I) σ' I = jugSlotWord (fileDutyRhoSlotFor I) σ'_solm I := by rfl
      have hage0Evm :
          UInt256.sub (UInt256.ofNat I.header.timestamp)
            (jugSlotWord (fileDutyRhoSlotFor I) σ' I) = ⟨0⟩ := by
        simpa [age] using hage0
      have hage0Solm :
          UInt256.sub (UInt256.ofNat I.header.timestamp)
            (jugSlotWord (fileDutyRhoSlotFor I) σ'_solm I) = ⟨0⟩ := by
        rw [← hrhoPostWord]
        exact hage0Evm
      have hbody :
          ExecTransitionBody config contract evm locals dripTransition.body
            .reverted := by
        simpa [evm, locals, initState, jugSlotWord] using
          (jugDripSourceBodyVatIlksDiffBoundReverts
            (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
            (g := g)
            (evmVat :=
              { evm with
                accountMap := σ'_solm
                substate := A'_solm })
            (out := out) hwv hsz36 hleSolm hvatCodeSolm
            (by simpa [evm] using hcallSolm) _hdecOut
            (by simpa [evm, initState, jugSlotWord] using haddNoSolm)
            (by simpa [evm, initState, jugSlotWord] using hage0Solm)
            hfitRmul hprevMaxNot)
      have hrev := _diffNZeroBoundRevert hage0 hfitRmul hprevMaxNot
      exact hrev.reEquivExecutionRevert hcode hdispatch
        (jugDecode_drip_ok hsz36) hbody
    · by_cases hFoldCallReadyNZero :
          age = ⟨0⟩ ∧
            jugRay.toNat * (dripVatIlksPrevWord out).toNat < UInt256.size ∧
            ((dripVatIlksPrevWord out).toNat : Int) ≤ maxInt256 ∧
            Reasoning.Theory.extCodeSizeWord σ'
              (dripVatTargetWord σ' I) ≠ ⟨0⟩
      · rcases hFoldCallReadyNZero with
          ⟨hage0, hfitRmul, hprevMax, hfoldCode⟩
        let locals := dripLocals I
        let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
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
        obtain ⟨gasWord, _, _, rd1650⟩ :=
          _foldNZeroCallReady hage0 hfitRmul hprevMax hfoldCode
        obtain
          ⟨σ'', z, foldOut, AinFold, callGasFold, _, _, hΘFold,
            rd1651, hfoldOutSize⟩ :=
          RD.jugDripVatFoldPostCall rd1650 hdepth
        cases z
        · rcases hΘFold with ⟨gFold'', AFold', hΘFold'⟩
          have hrhoWord : jugSlotWord (fileDutyRhoSlotFor I) σ I =
              jugSlotWord (fileDutyRhoSlotFor I) σ I :=
            rfl
          have hleSolm :
              (jugSlotWord (fileDutyRhoSlotFor I) σ I).toNat ≤
                (UInt256.ofNat I.header.timestamp).toNat := by
            rw [← hrhoWord]
            exact hle
          have hcodeSizeSolm :
              Reasoning.Theory.extCodeSizeWord σ
                  (dripVatTargetWord σ I) ≠ ⟨0⟩ :=
            hvatCode
          have hvatCodeSolm :
              0 <
                (UInt256.ofNat
                  (((initState σ σ₀
                    (Sat256.ofUInt256 g) A I).lookupAccount
                      (dripVatAddress σ I)).option 0
                        (fun acc => acc.code.size))).toNat :=
            dripVatCode_pos_of_codeSize_ne_zero
              (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
              (g := g) hcodeSizeSolm
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
                  callGas (UInt256.ofNat evm.executionEnv.gasPrice) ⟨0⟩ ⟨0⟩
                  ((dripVatIlksCalldataMem I
                    (dripIlkHashMem I)).readWithPadding
                      dripVatIlksOutPtr.toNat dripVatIlksInSize.toNat)
                  (evm.executionEnv.depth + 1) evm.executionEnv.header evm.executionEnv.blobVersionedHashes evm.executionEnv.blocks true := by
            simpa [evm, initState, hperm] using hΘ'
          let σ'_solm := σ'
          let A'_solm := A'
          have hcallSolm :
              typedCallViaEVM config evm (EVM.address (dripVatAddress σ I)) "ilks" 0
                [.fixedBytes bytes32Width (fileDutyIlkBytes I)]
                (true, { evm with accountMap := σ', substate := A' }, out) true := by
            simpa [evm] using
              callCoincides hdepthNe htgt (dripVatIlksEncode_eq I hsz36) hΘE
          let evmVatE :=
            { evm with
              accountMap := σ',
              substate := A'_solm }
          let evmVatS :=
            { evm with
              accountMap := σ'_solm,
              substate := A'_solm }
          have hfoldDepthNe : evmVatE.executionEnv.depth ≠ 1024 := by
            simpa [evmVatE] using hdepthNe
          have hfoldTargetAddr :
              dripVatAddress σ'_solm I =
                AccountAddress.ofUInt256 (dripVatTargetWord σ' I) := by
            simpa [σ'_solm] using dripVatAddress_eq_target σ' I
          have hfoldTarget :
              EVM.address (dripVatAddress σ'_solm I) =
                AccountAddress.ofUInt256 (dripVatTargetWord σ' I) := by
            rw [hfoldTargetAddr]
            exact evmAddress_accountAddress _
          have hvowWord :
              dripVowTargetWord σ'_solm I = dripVowTargetWord σ' I :=
            by rfl
          have hzeroMax : ((⟨0⟩ : UInt256).toNat : Int) ≤ maxInt256 := by
            norm_num [maxInt256]
          have hfoldEncode :
              config.externalABI.encode? "fold"
                  [.fixedBytes bytes32Width (fileDutyIlkBytes I),
                    .address (AccountAddress.ofUInt256
                      (dripVowTargetWord σ'_solm I)),
                    .int (Int.ofNat (⟨0⟩ : UInt256).toNat)] =
                some ((dripVatFoldCalldataMem σ' I ⟨0⟩ foldBaseMem).readWithPadding
                  dripVatFoldOutPtr.toNat dripVatFoldInSize.toNat) := by
            rw [hvowWord]
            exact dripVatFoldEncode_eq σ' I ⟨0⟩ hfoldBaseSize hsz36
              hzeroMax
          have hΘFoldE :
              (σ'', gFold'', AFold', false, foldOut) =
                Ethereum.EVM.Θ evmVatE.accountMap evmVatE.σ₀ AinFold
                  (AccountAddress.ofUInt256
                    (UInt256.ofNat evmVatE.executionEnv.codeOwner))
                  evmVatE.executionEnv.sender
                  (AccountAddress.ofUInt256 (dripVatTargetWord σ' I))
                  (toExecute evmVatE.accountMap
                    (AccountAddress.ofUInt256 (dripVatTargetWord σ' I)))
                  callGasFold (UInt256.ofNat evmVatE.executionEnv.gasPrice)
                  ⟨0⟩ ⟨0⟩
                  ((dripVatFoldCalldataMem σ' I ⟨0⟩ foldBaseMem).readWithPadding
                    dripVatFoldOutPtr.toNat dripVatFoldInSize.toNat)
                  (evmVatE.executionEnv.depth + 1)
                  (evmVatE.executionEnv.header) (evmVatE.executionEnv.blobVersionedHashes) (evmVatE.executionEnv.blocks) true := by
            simpa [evmVatE, evm, initState, hperm, foldBaseMem] using
              hΘFold'
          let σ''_solm := σ''
          let A''_solm := AFold'
          have hfoldCallSolm :
              typedCallViaEVM config evmVatS
                (EVM.address (dripVatAddress σ'_solm I)) "fold" 0
                [.fixedBytes bytes32Width (fileDutyIlkBytes I),
                  .address (AccountAddress.ofUInt256 (dripVowTargetWord σ'_solm I)),
                  .int (Int.ofNat (⟨0⟩ : UInt256).toNat)]
                (false, { evmVatS with accountMap := σ'', substate := AFold' }, foldOut) true := by
            simpa [evmVatE, evmVatS, σ'_solm, evm] using
              callCoincides hfoldDepthNe hfoldTarget hfoldEncode hΘFoldE
          have hbaseWord : jugSlotWord ⟨4⟩ σ' I = jugSlotWord ⟨4⟩ σ'_solm I := by rfl
          have hdutyWord : jugSlotWord (fileDutyDutySlotFor I) σ' I = jugSlotWord (fileDutyDutySlotFor I) σ'_solm I := by rfl
          have haddNoSolm :
              ¬ UInt256.size ≤ (jugSlotWord ⟨4⟩ σ'_solm I).toNat +
                (jugSlotWord (fileDutyDutySlotFor I) σ'_solm I).toNat := by
            intro hbad
            exact haddOverflow (by
              simpa [hbaseWord, hdutyWord] using hbad)
          have hrhoPostWord : jugSlotWord (fileDutyRhoSlotFor I) σ' I = jugSlotWord (fileDutyRhoSlotFor I) σ'_solm I := by rfl
          have hage0Evm :
              UInt256.sub (UInt256.ofNat I.header.timestamp)
                (jugSlotWord (fileDutyRhoSlotFor I) σ' I) = ⟨0⟩ := by
            simpa [age] using hage0
          have hage0Solm :
              UInt256.sub (UInt256.ofNat I.header.timestamp)
                (jugSlotWord (fileDutyRhoSlotFor I) σ'_solm I) = ⟨0⟩ := by
            rw [← hrhoPostWord]
            exact hage0Evm
          have hfoldCodeSolmNe :
              Reasoning.Theory.extCodeSizeWord σ'_solm
                  (dripVatTargetWord σ'_solm I) ≠ ⟨0⟩ :=
            by simpa [σ'_solm] using hfoldCode
          have hfoldCodeSolm :
              0 <
                (UInt256.ofNat
                  ((evmVatS.lookupAccount
                    (dripVatAddress evmVatS.accountMap
                      evmVatS.executionEnv)).option 0
                        (fun acc => acc.code.size))).toNat := by
            simpa [evmVatS, evm, initState] using
              (dripVatCode_pos_of_codeSize_ne_zero                 (σ := σ'_solm) (σ₀ := σ₀) (A := A'_solm)
                (I := I) (g := g) hfoldCodeSolmNe)
          have hbody :
              ExecTransitionBody config contract evm locals dripTransition.body
                .reverted := by
            simpa [evm, evmVatS, locals, initState, jugSlotWord] using
              (jugDripSourceBodyVatFoldCallFailedReverts
                (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
                (g := g) (evmVat := evmVatS)
                (evmFold :=
                  { evmVatS with
                    accountMap := σ''_solm,
                    substate := A''_solm })
                (out := out) (foldOut := foldOut)
                hwv hsz36 hleSolm hvatCodeSolm
                (by simpa [evm, evmVatS] using hcallSolm) _hdecOut
                (by simpa [evmVatS, evm, initState, jugSlotWord] using
                  haddNoSolm)
                (by simpa [evmVatS, evm, initState, jugSlotWord] using
                  hage0Solm)
                hfitRmul hprevMax hfoldCodeSolm
                (by simpa [evmVatS] using hfoldCallSolm))
          have hrev := RD.jugDripVatFoldCallFailed
            (targetWord := dripVatTargetWord σ' I) rd1651 hfoldOutSize
          exact hrev.reEquivExecutionRevert hcode hdispatch
            (jugDecode_drip_ok hsz36) hbody
        · rcases hΘFold with ⟨gFold'', AFold', hΘFold'⟩
          have hfoldBaseRead64 :
              foldBaseMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
            dsimp [foldBaseMem]
            exact drip_twoWordHashMem_read64_of_ge96 (fileDutyIlkWord I)
              (⟨1⟩ : UInt256) (by rw [hinnerSize]; omega) hinnerRead64
          have hfoldCallMemSize :
              (dripVatFoldCalldataMem σ' I ⟨0⟩ foldBaseMem).size = 228 :=
            dripVatFoldCalldataMem_size σ' I ⟨0⟩ hfoldBaseSize
          have hfoldCallMemRead64 :
              (dripVatFoldCalldataMem σ' I ⟨0⟩ foldBaseMem).readWithPadding
                  64 32 = UInt256.toByteArray ⟨128⟩ :=
            dripVatFoldCalldataMem_read64 σ' I ⟨0⟩ hfoldBaseSize
              hfoldBaseRead64
          have hrhoWord : jugSlotWord (fileDutyRhoSlotFor I) σ I =
              jugSlotWord (fileDutyRhoSlotFor I) σ I :=
            rfl
          have hleSolm :
              (jugSlotWord (fileDutyRhoSlotFor I) σ I).toNat ≤
                (UInt256.ofNat I.header.timestamp).toNat := by
            rw [← hrhoWord]
            exact hle
          have hcodeSizeSolm :
              Reasoning.Theory.extCodeSizeWord σ
                  (dripVatTargetWord σ I) ≠ ⟨0⟩ :=
            hvatCode
          have hvatCodeSolm :
              0 <
                (UInt256.ofNat
                  (((initState σ σ₀
                    (Sat256.ofUInt256 g) A I).lookupAccount
                      (dripVatAddress σ I)).option 0
                        (fun acc => acc.code.size))).toNat :=
            dripVatCode_pos_of_codeSize_ne_zero
              (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
              (g := g) hcodeSizeSolm
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
                  callGas (UInt256.ofNat evm.executionEnv.gasPrice) ⟨0⟩ ⟨0⟩
                  ((dripVatIlksCalldataMem I
                    (dripIlkHashMem I)).readWithPadding
                      dripVatIlksOutPtr.toNat dripVatIlksInSize.toNat)
                  (evm.executionEnv.depth + 1) evm.executionEnv.header evm.executionEnv.blobVersionedHashes evm.executionEnv.blocks true := by
            simpa [evm, initState, hperm] using hΘ'
          let σ'_solm := σ'
          let A'_solm := A'
          have hcallSolm :
              typedCallViaEVM config evm (EVM.address (dripVatAddress σ I)) "ilks" 0
                [.fixedBytes bytes32Width (fileDutyIlkBytes I)]
                (true, { evm with accountMap := σ', substate := A' }, out) true := by
            simpa [evm] using
              callCoincides hdepthNe htgt (dripVatIlksEncode_eq I hsz36) hΘE
          let evmVatE :=
            { evm with
              accountMap := σ',
              substate := A'_solm }
          let evmVatS :=
            { evm with
              accountMap := σ'_solm,
              substate := A'_solm }
          have hfoldDepthNe : evmVatE.executionEnv.depth ≠ 1024 := by
            simpa [evmVatE] using hdepthNe
          have hfoldTargetAddr :
              dripVatAddress σ'_solm I =
                AccountAddress.ofUInt256 (dripVatTargetWord σ' I) := by
            simpa [σ'_solm] using dripVatAddress_eq_target σ' I
          have hfoldTarget :
              EVM.address (dripVatAddress σ'_solm I) =
                AccountAddress.ofUInt256 (dripVatTargetWord σ' I) := by
            rw [hfoldTargetAddr]
            exact evmAddress_accountAddress _
          have hvowWord :
              dripVowTargetWord σ'_solm I = dripVowTargetWord σ' I :=
            by rfl
          have hzeroMax : ((⟨0⟩ : UInt256).toNat : Int) ≤ maxInt256 := by
            norm_num [maxInt256]
          have hfoldEncode :
              config.externalABI.encode? "fold"
                  [.fixedBytes bytes32Width (fileDutyIlkBytes I),
                    .address (AccountAddress.ofUInt256
                      (dripVowTargetWord σ'_solm I)),
                    .int (Int.ofNat (⟨0⟩ : UInt256).toNat)] =
                some ((dripVatFoldCalldataMem σ' I ⟨0⟩ foldBaseMem).readWithPadding
                  dripVatFoldOutPtr.toNat dripVatFoldInSize.toNat) := by
            rw [hvowWord]
            exact dripVatFoldEncode_eq σ' I ⟨0⟩ hfoldBaseSize hsz36
              hzeroMax
          have hΘFoldE :
              (σ'', gFold'', AFold', true, foldOut) =
                Ethereum.EVM.Θ evmVatE.accountMap evmVatE.σ₀ AinFold
                  (AccountAddress.ofUInt256
                    (UInt256.ofNat evmVatE.executionEnv.codeOwner))
                  evmVatE.executionEnv.sender
                  (AccountAddress.ofUInt256 (dripVatTargetWord σ' I))
                  (toExecute evmVatE.accountMap
                    (AccountAddress.ofUInt256 (dripVatTargetWord σ' I)))
                  callGasFold (UInt256.ofNat evmVatE.executionEnv.gasPrice)
                  ⟨0⟩ ⟨0⟩
                  ((dripVatFoldCalldataMem σ' I ⟨0⟩ foldBaseMem).readWithPadding
                    dripVatFoldOutPtr.toNat dripVatFoldInSize.toNat)
                  (evmVatE.executionEnv.depth + 1)
                  (evmVatE.executionEnv.header) (evmVatE.executionEnv.blobVersionedHashes) (evmVatE.executionEnv.blocks) true := by
            simpa [evmVatE, evm, initState, hperm, foldBaseMem] using
              hΘFold'
          let σ''_solm := σ''
          let A''_solm := AFold'
          have hfoldCallSolm :
              typedCallViaEVM config evmVatS
                (EVM.address (dripVatAddress σ'_solm I)) "fold" 0
                [.fixedBytes bytes32Width (fileDutyIlkBytes I),
                  .address (AccountAddress.ofUInt256 (dripVowTargetWord σ'_solm I)),
                  .int (Int.ofNat (⟨0⟩ : UInt256).toNat)]
                (true, { evmVatS with accountMap := σ'', substate := AFold' }, foldOut) true := by
            simpa [evmVatE, evmVatS, σ'_solm, evm] using
              callCoincides hfoldDepthNe hfoldTarget hfoldEncode hΘFoldE
          have hbaseWord : jugSlotWord ⟨4⟩ σ' I = jugSlotWord ⟨4⟩ σ'_solm I := by rfl
          have hdutyWord : jugSlotWord (fileDutyDutySlotFor I) σ' I = jugSlotWord (fileDutyDutySlotFor I) σ'_solm I := by rfl
          have haddNoSolm :
              ¬ UInt256.size ≤ (jugSlotWord ⟨4⟩ σ'_solm I).toNat +
                (jugSlotWord (fileDutyDutySlotFor I) σ'_solm I).toNat := by
            intro hbad
            exact haddOverflow (by
              simpa [hbaseWord, hdutyWord] using hbad)
          have hrhoPostWord : jugSlotWord (fileDutyRhoSlotFor I) σ' I = jugSlotWord (fileDutyRhoSlotFor I) σ'_solm I := by rfl
          have hage0Evm :
              UInt256.sub (UInt256.ofNat I.header.timestamp)
                (jugSlotWord (fileDutyRhoSlotFor I) σ' I) = ⟨0⟩ := by
            simpa [age] using hage0
          have hage0Solm :
              UInt256.sub (UInt256.ofNat I.header.timestamp)
                (jugSlotWord (fileDutyRhoSlotFor I) σ'_solm I) = ⟨0⟩ := by
            rw [← hrhoPostWord]
            exact hage0Evm
          have hfoldCodeSolmNe :
              Reasoning.Theory.extCodeSizeWord σ'_solm
                  (dripVatTargetWord σ'_solm I) ≠ ⟨0⟩ :=
            by simpa [σ'_solm] using hfoldCode
          have hfoldCodeSolm :
              0 <
                (UInt256.ofNat
                  ((evmVatS.lookupAccount
                    (dripVatAddress evmVatS.accountMap
                      evmVatS.executionEnv)).option 0
                        (fun acc => acc.code.size))).toNat := by
            simpa [evmVatS, evm, initState] using
              (dripVatCode_pos_of_codeSize_ne_zero                 (σ := σ'_solm) (σ₀ := σ₀) (A := A'_solm)
                (I := I) (g := g) hfoldCodeSolmNe)
          let evmFoldS :=
            { evmVatS with
              accountMap := σ''_solm,
              substate := A''_solm }
          let finalLocals :=
            (dripDeltaLocals I out
              (jugSlotWord ⟨4⟩ evmVatS.accountMap evmVatS.executionEnv +
                jugSlotWord (fileDutyDutySlotFor I) evmVatS.accountMap
                  evmVatS.executionEnv)
              jugRay (dripVatIlksPrevWord out) ⟨0⟩).insert "_foldRet" .unit
          let evmRhoS :=
            Solm.EVM.storageStore evmFoldS evmFoldS.executionEnv.codeOwner
              (fileDutyRhoSlotFor I)
              (UInt256.ofNat evmFoldS.executionEnv.header.timestamp)
          have hbody :
              ExecTransitionBody config contract evm locals dripTransition.body
                (.returned { contract := contract, locals := finalLocals } evmRhoS
                  (some [.int (Int.ofNat (dripVatIlksPrevWord out).toNat)])) := by
            simpa [evm, evmVatS, evmFoldS, finalLocals, evmRhoS, locals,
              initState, jugSlotWord] using
              (jugDripSourceBodyVatFoldCallSucceededReturns
                (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
                (g := g) (evmVat := evmVatS) (evmFold := evmFoldS)
                (out := out) (foldOut := foldOut)
                hwv hsz36 hleSolm hvatCodeSolm
                (by simpa [evm, evmVatS] using hcallSolm) _hdecOut
                (by simpa [evmVatS, evm, initState, jugSlotWord] using
                  haddNoSolm)
                (by simpa [evmVatS, evm, initState, jugSlotWord] using
                  hage0Solm)
                hfitRmul hprevMax hfoldCodeSolm
                (by simpa [evmVatS] using hfoldCallSolm))
          obtain ⟨_, _, rd1669⟩ :=
            RD.jugDripVatFoldCallSucceeded
              (targetWord := dripVatTargetWord σ' I) rd1651
          have hret := RD.jugDripVatFoldStoreRhoReturns
            (targetWord := dripVatTargetWord σ' I)
            hsz36 hperm hfoldCallMemSize hfoldCallMemRead64 rd1669
          exact hret.reEquivExecutionGen hcode hdispatch
            (jugDecode_drip_ok hsz36) hbody
            (by
              simp [evmRhoS, evmFoldS, evmVatS, evmVatE, σ''_solm,
                A''_solm, σ'_solm, evm, initState, storageStore_accountMap])
            (by
              rw [show dripTransition.returnType = [uint256] by rfl]
              exact returnEquiv_of_encode
                (by simpa [uint256] using
                  uint256ReturnEncoding (dripVatIlksPrevWord out)))
      · have hageNZ : age ≠ ⟨0⟩ := by
          intro hage0
          by_cases hfit :
              jugRay.toNat * (dripVatIlksPrevWord out).toNat < UInt256.size
          · by_cases hprevMax :
                ((dripVatIlksPrevWord out).toNat : Int) ≤ maxInt256
            · by_cases hfoldCode :
                  Reasoning.Theory.extCodeSizeWord σ'
                    (dripVatTargetWord σ' I) = ⟨0⟩
              · exact hFoldNoCodeNZero
                  ⟨hage0, hfit, hprevMax, hfoldCode⟩
              · exact hFoldCallReadyNZero
                  ⟨hage0, hfit, hprevMax, hfoldCode⟩
            · exact hDiffBoundNZero ⟨hage0, hfit, hprevMax⟩
          · exact hRmulOverflowNZero ⟨hage0, hfit⟩
        by_cases hfeeZero : fee = ⟨0⟩
        · jug_drip_fee_zero_tac
        · jug_drip_age_one_tac
"#

elab "jug_drip_nzero_and_later_tac" : tactic => do
  let tacSeq ← match Mathlib.GuardExceptions.parseAsTacticSeq (← getEnv) jugDripNZeroScript with
    | .ok tacSeq => pure tacSeq
    | .error err => throwError "failed to parse jug_drip_nzero_and_later_tac:
{err}"
  evalTactic (← `(tactic| ($tacSeq:tacticSeq)))

end Benchmarks.Dss.Jug
