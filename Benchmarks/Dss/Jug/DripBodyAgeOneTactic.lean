import Benchmarks.Dss.Jug.DripBodyGenericTactic
import Mathlib.Util.ParseCommand
import Lean.Elab.Tactic

open Lean Elab Tactic
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Jug

set_option maxHeartbeats 1000000

private def jugDripAgeOneScript : String := r#"
by_cases hageOne : age = ⟨1⟩
· by_cases hRmulOverflowOne :
      UInt256.size ≤
        fee.toNat * (dripVatIlksPrevWord out).toNat
  · let locals := dripLocals I
    let evm :=
      initState σ σ₀ (Sat256.ofUInt256 g) A I
    have hrhoWord :
        jugSlotWord (fileDutyRhoSlotFor I) σ I =
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
        (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) hcodeSizeSolm
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
            evm.executionEnv.header evm.executionEnv.blobVersionedHashes evm.executionEnv.blocks true := by
      simpa [evm, initState, hperm] using hΘ'
    let σ'_solm := σ'
    let A'_solm := A'
    have hcallSolm :
        typedCallViaEVM config evm (EVM.address (dripVatAddress σ I)) "ilks" 0
          [.fixedBytes bytes32Width (fileDutyIlkBytes I)]
          (true, { evm with accountMap := σ', substate := A' }, out) true := by
      simpa [evm, evm] using
        callCoincides hdepthNe htgt (dripVatIlksEncode_eq I hsz36) hΘE
    have hbaseWord : jugSlotWord ⟨4⟩ σ' I =
        jugSlotWord ⟨4⟩ σ'_solm I :=
      rfl
    have hdutyWord :
        jugSlotWord (fileDutyDutySlotFor I) σ' I =
          jugSlotWord (fileDutyDutySlotFor I) σ'_solm I :=
      rfl
    have haddNoSolm :
        ¬ UInt256.size ≤ (jugSlotWord ⟨4⟩ σ'_solm I).toNat +
          (jugSlotWord (fileDutyDutySlotFor I) σ'_solm I).toNat := by
      intro hbad
      exact haddOverflow (by
        simpa [hbaseWord, hdutyWord] using hbad)
    have hfeeNZSolm :
        jugSlotWord ⟨4⟩ σ'_solm I +
            jugSlotWord (fileDutyDutySlotFor I) σ'_solm I ≠
          ⟨0⟩ := by
      intro hbad
      exact hfeeZero (by
        simpa [fee, hbaseWord, hdutyWord] using hbad)
    have hrhoPostWord :
        jugSlotWord (fileDutyRhoSlotFor I) σ' I =
          jugSlotWord (fileDutyRhoSlotFor I) σ'_solm I :=
      rfl
    have hageOneEvm :
        UInt256.sub (UInt256.ofNat I.header.timestamp)
          (jugSlotWord (fileDutyRhoSlotFor I) σ' I) = ⟨1⟩ := by
      simpa [age] using hageOne
    have hageOneSolm :
        UInt256.sub (UInt256.ofNat I.header.timestamp)
          (jugSlotWord (fileDutyRhoSlotFor I) σ'_solm I) = ⟨1⟩ := by
      simpa [hrhoPostWord] using hageOneEvm
    have hrmulOverflowSolm :
        UInt256.size ≤
          (jugSlotWord ⟨4⟩ σ'_solm I +
            jugSlotWord (fileDutyDutySlotFor I) σ'_solm I).toNat *
            (dripVatIlksPrevWord out).toNat := by
      simpa [fee, hbaseWord, hdutyWord] using hRmulOverflowOne
    have hbody :
        ExecTransitionBody config contract evm locals
          dripTransition.body .reverted := by
      simpa [evm, locals, initState, jugSlotWord] using
        (jugDripSourceBodyVatIlksRmulOverflowRevertsNOne
          (σ := σ)
          (σ₀ := σ₀) (A := A) (I := I) (g := g)
          (evmVat :=
            { evm with
              accountMap := σ'_solm
              substate := A'_solm })
          (out := out) hwv hsz36 hleSolm hvatCodeSolm
          (by simpa [evm] using hcallSolm) _hdecOut
          (by
            simpa [evm, initState, jugSlotWord] using
              haddNoSolm)
          (by
            simpa [evm, initState, jugSlotWord] using
              hfeeNZSolm)
          (by
            simpa [evm, initState, jugSlotWord] using
              hageOneSolm)
          (by
            simpa [evm, initState, jugSlotWord] using
              hrmulOverflowSolm))
    have rd2153One := by
      simpa [fee, age, hageOne] using _rd2153
    obtain ⟨_, _, rd1524One⟩ :=
      RD.jugDripRpowNOneReturns
        (R := [⟨1530⟩, dripVatIlksPrevWord out, ⟨0⟩,
          fileDutyIlkWord I, ⟨357⟩, jugSelWord I])
        (by simp) rd2153One
    have hrev := RD.jugDripRmulOverflowReverts
      (R := [⟨0⟩, fileDutyIlkWord I, ⟨357⟩, jugSelWord I])
      (by simp) hRmulOverflowOne rd1524One
    exact hrev.reEquivExecutionRevert hcode hdispatch
      (jugDecode_drip_ok hsz36) hbody
  · have hfitRmulOne :
        fee.toNat * (dripVatIlksPrevWord out).toNat <
          UInt256.size :=
      Nat.lt_of_not_ge hRmulOverflowOne
    let rate := UInt256.div (dripVatIlksPrevWord out * fee) jugRay
    by_cases hrateMax : (rate.toNat : Int) ≤ maxInt256
    · by_cases hprevMaxNot :
          ¬ ((dripVatIlksPrevWord out).toNat : Int) ≤ maxInt256
      · let locals := dripLocals I
        let evm :=
          initState σ σ₀ (Sat256.ofUInt256 g) A I
        have hrhoWord :
            jugSlotWord (fileDutyRhoSlotFor I) σ I =
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
            (σ := σ) (σ₀ := σ₀) (A := A)
            (I := I) (g := g) hcodeSizeSolm
        rcases hΘ with ⟨g'', A', hΘ'⟩
        have hdepthNe : evm.executionEnv.depth ≠ 1024 := by
          intro hbad
          simp [evm, initState] at hbad
          rw [hbad] at hdepth
          omega
        have htgtAddr :
            dripVatAddress σ I =
              AccountAddress.ofUInt256
                (dripVatTargetWord σ I) := by
          exact dripVatAddress_eq_target σ I
        have htgt :
            EVM.address (dripVatAddress σ I) =
              AccountAddress.ofUInt256
                (dripVatTargetWord σ I) := by
          rw [htgtAddr]
          exact evmAddress_accountAddress _
        have hΘE :
            (σ', g'', A', true, out) =
              Ethereum.EVM.Θ evm.accountMap evm.σ₀ Ain
                (AccountAddress.ofUInt256
                  (UInt256.ofNat evm.executionEnv.codeOwner))
                evm.executionEnv.sender
                (AccountAddress.ofUInt256
                  (dripVatTargetWord σ I))
                (toExecute evm.accountMap
                  (AccountAddress.ofUInt256
                    (dripVatTargetWord σ I)))
                callGas (UInt256.ofNat evm.executionEnv.gasPrice)
                ⟨0⟩ ⟨0⟩
                ((dripVatIlksCalldataMem I
                  (dripIlkHashMem I)).readWithPadding
                    dripVatIlksOutPtr.toNat dripVatIlksInSize.toNat)
                (evm.executionEnv.depth + 1)
                evm.executionEnv.header evm.executionEnv.blobVersionedHashes evm.executionEnv.blocks true := by
          simpa [evm, initState, hperm] using hΘ'
        let σ'_solm := σ'
        let A'_solm := A'
        have hcallSolm :
            typedCallViaEVM config evm (EVM.address (dripVatAddress σ I)) "ilks" 0
              [.fixedBytes bytes32Width (fileDutyIlkBytes I)]
              (true, { evm with accountMap := σ', substate := A' }, out) true := by
          simpa [evm, evm] using
            callCoincides hdepthNe htgt (dripVatIlksEncode_eq I hsz36) hΘE
        have hbaseWord : jugSlotWord ⟨4⟩ σ' I =
            jugSlotWord ⟨4⟩ σ'_solm I :=
          rfl
        have hdutyWord :
            jugSlotWord (fileDutyDutySlotFor I) σ' I =
              jugSlotWord (fileDutyDutySlotFor I) σ'_solm I :=
          rfl
        have haddNoSolm :
            ¬ UInt256.size ≤ (jugSlotWord ⟨4⟩ σ'_solm I).toNat +
              (jugSlotWord (fileDutyDutySlotFor I)
                σ'_solm I).toNat := by
          intro hbad
          exact haddOverflow (by
            simpa [hbaseWord, hdutyWord] using hbad)
        have hfeeNZSolm :
            jugSlotWord ⟨4⟩ σ'_solm I +
                jugSlotWord (fileDutyDutySlotFor I) σ'_solm I ≠
              ⟨0⟩ := by
          intro hbad
          exact hfeeZero (by
            simpa [fee, hbaseWord, hdutyWord] using hbad)
        have hrhoPostWord :
            jugSlotWord (fileDutyRhoSlotFor I) σ' I =
              jugSlotWord (fileDutyRhoSlotFor I) σ'_solm I :=
          rfl
        have hageOneEvm :
            UInt256.sub (UInt256.ofNat I.header.timestamp)
              (jugSlotWord (fileDutyRhoSlotFor I) σ' I) = ⟨1⟩ := by
          simpa [age] using hageOne
        have hageOneSolm :
            UInt256.sub (UInt256.ofNat I.header.timestamp)
              (jugSlotWord (fileDutyRhoSlotFor I) σ'_solm I) =
                ⟨1⟩ := by
          simpa [hrhoPostWord] using hageOneEvm
        have hfitRmulSolm :
            (jugSlotWord ⟨4⟩ σ'_solm I +
                jugSlotWord (fileDutyDutySlotFor I)
                  σ'_solm I).toNat *
              (dripVatIlksPrevWord out).toNat < UInt256.size := by
          simpa [fee, hbaseWord, hdutyWord] using hfitRmulOne
        have hrateMaxSolm :
            ((UInt256.div
                (dripVatIlksPrevWord out *
                  (jugSlotWord ⟨4⟩ σ'_solm I +
                    jugSlotWord (fileDutyDutySlotFor I)
                      σ'_solm I))
                jugRay).toNat : Int) ≤ maxInt256 := by
          simpa [rate, fee, hbaseWord, hdutyWord] using hrateMax
        have hbody :
            ExecTransitionBody config contract evm locals
              dripTransition.body .reverted := by
          simpa [evm, locals, initState, jugSlotWord] using
            (jugDripSourceBodyVatIlksDiffYBoundRevertsNOne
              (σ := σ)
              (σ₀ := σ₀) (A := A) (I := I) (g := g)
              (evmVat :=
                { evm with
                  accountMap := σ'_solm
                  substate := A'_solm })
              (out := out) hwv hsz36 hleSolm hvatCodeSolm
              (by simpa [evm] using hcallSolm) _hdecOut
              (by
                simpa [evm, initState, jugSlotWord] using
                  haddNoSolm)
              (by
                simpa [evm, initState, jugSlotWord] using
                  hfeeNZSolm)
              (by
                simpa [evm, initState, jugSlotWord] using
                  hageOneSolm)
              (by
                simpa [evm, initState, jugSlotWord] using
                  hfitRmulSolm)
              (by
                simpa [evm, initState, jugSlotWord] using
                  hrateMaxSolm)
              hprevMaxNot)
        have rd2153One := by
          simpa [fee, age, hageOne] using _rd2153
        obtain ⟨_, _, rd1524One⟩ :=
          RD.jugDripRpowNOneReturns
            (R := [⟨1530⟩, dripVatIlksPrevWord out, ⟨0⟩,
              fileDutyIlkWord I, ⟨357⟩, jugSelWord I])
            (by simp) rd2153One
        obtain ⟨_, _, rd1530OneRaw⟩ :=
          RD.jugDripRmulReturns
            (R := [⟨0⟩, fileDutyIlkWord I, ⟨357⟩,
              jugSelWord I])
            (by simp) hfitRmulOne rd1524One
        have rd1530One := by
          simpa [rate] using rd1530OneRaw
        obtain ⟨_, _, rd2397⟩ := RD.jugDripToDiffRoutine rd1530One
        have hrev := RD.jugDiffRevertYBound
          (R := [dripVowTargetWord σ' I, fileDutyIlkWord I,
            dripVatFoldSelectorWord, dripVatTargetWord σ' I,
            dripVatIlksPrevWord out, rate, fileDutyIlkWord I,
            ⟨357⟩, jugSelWord I])
          (g := g) (rate := rate) (prev := dripVatIlksPrevWord out)
          (by simp) hrateMax hprevMaxNot (by simpa using rd2397)
        exact hrev.reEquivExecutionRevert hcode hdispatch
          (jugDecode_drip_ok hsz36) hbody
      · have hprevMax :
            ((dripVatIlksPrevWord out).toNat : Int) ≤
              maxInt256 := by
          by_contra hbad
          exact hprevMaxNot hbad
        by_cases hfoldNoCode :
            Reasoning.Theory.extCodeSizeWord σ'
              (dripVatTargetWord σ' I) = ⟨0⟩
        · let locals := dripLocals I
          let evm :=
            initState σ σ₀ (Sat256.ofUInt256 g) A I
          have hrhoWord :
              jugSlotWord (fileDutyRhoSlotFor I) σ I =
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
              (σ := σ) (σ₀ := σ₀)
              (A := A) (I := I) (g := g) hcodeSizeSolm
          rcases hΘ with ⟨g'', A', hΘ'⟩
          have hdepthNe : evm.executionEnv.depth ≠ 1024 := by
            intro hbad
            simp [evm, initState] at hbad
            rw [hbad] at hdepth
            omega
          have htgtAddr :
              dripVatAddress σ I =
                AccountAddress.ofUInt256
                  (dripVatTargetWord σ I) := by
            exact dripVatAddress_eq_target σ I
          have htgt :
              EVM.address (dripVatAddress σ I) =
                AccountAddress.ofUInt256
                  (dripVatTargetWord σ I) := by
            rw [htgtAddr]
            exact evmAddress_accountAddress _
          have hΘE :
              (σ', g'', A', true, out) =
                Ethereum.EVM.Θ evm.accountMap evm.σ₀ Ain
                  (AccountAddress.ofUInt256
                    (UInt256.ofNat evm.executionEnv.codeOwner))
                  evm.executionEnv.sender
                  (AccountAddress.ofUInt256
                    (dripVatTargetWord σ I))
                  (toExecute evm.accountMap
                    (AccountAddress.ofUInt256
                      (dripVatTargetWord σ I)))
                  callGas (UInt256.ofNat evm.executionEnv.gasPrice)
                  ⟨0⟩ ⟨0⟩
                  ((dripVatIlksCalldataMem I
                    (dripIlkHashMem I)).readWithPadding
                      dripVatIlksOutPtr.toNat dripVatIlksInSize.toNat)
                  (evm.executionEnv.depth + 1)
                  evm.executionEnv.header evm.executionEnv.blobVersionedHashes evm.executionEnv.blocks true := by
            simpa [evm, initState, hperm] using hΘ'
          let σ'_solm := σ'
          let A'_solm := A'
          have hcallSolm :
              typedCallViaEVM config evm (EVM.address (dripVatAddress σ I)) "ilks" 0
                [.fixedBytes bytes32Width (fileDutyIlkBytes I)]
                (true, { evm with accountMap := σ', substate := A' }, out) true := by
            simpa [evm, evm] using
              callCoincides hdepthNe htgt (dripVatIlksEncode_eq I hsz36) hΘE
          have hbaseWord : jugSlotWord ⟨4⟩ σ' I =
              jugSlotWord ⟨4⟩ σ'_solm I :=
            rfl
          have hdutyWord :
              jugSlotWord (fileDutyDutySlotFor I) σ' I =
                jugSlotWord (fileDutyDutySlotFor I) σ'_solm I :=
            rfl
          have haddNoSolm :
              ¬ UInt256.size ≤
                (jugSlotWord ⟨4⟩ σ'_solm I).toNat +
                  (jugSlotWord (fileDutyDutySlotFor I)
                    σ'_solm I).toNat := by
            intro hbad
            exact haddOverflow (by
              simpa [hbaseWord, hdutyWord] using hbad)
          have hfeeNZSolm :
              jugSlotWord ⟨4⟩ σ'_solm I +
                  jugSlotWord (fileDutyDutySlotFor I) σ'_solm I ≠
                ⟨0⟩ := by
            intro hbad
            exact hfeeZero (by
              simpa [fee, hbaseWord, hdutyWord] using hbad)
          have hrhoPostWord :
              jugSlotWord (fileDutyRhoSlotFor I) σ' I =
                jugSlotWord (fileDutyRhoSlotFor I) σ'_solm I :=
            rfl
          have hageOneEvm :
              UInt256.sub (UInt256.ofNat I.header.timestamp)
                (jugSlotWord (fileDutyRhoSlotFor I) σ' I) =
                  ⟨1⟩ := by
            simpa [age] using hageOne
          have hageOneSolm :
              UInt256.sub (UInt256.ofNat I.header.timestamp)
                (jugSlotWord (fileDutyRhoSlotFor I) σ'_solm I) =
                  ⟨1⟩ := by
            simpa [hrhoPostWord] using hageOneEvm
          have hfitRmulSolm :
              (jugSlotWord ⟨4⟩ σ'_solm I +
                  jugSlotWord (fileDutyDutySlotFor I)
                    σ'_solm I).toNat *
                (dripVatIlksPrevWord out).toNat < UInt256.size := by
            simpa [fee, hbaseWord, hdutyWord] using hfitRmulOne
          have hrateMaxSolm :
              ((UInt256.div
                  (dripVatIlksPrevWord out *
                    (jugSlotWord ⟨4⟩ σ'_solm I +
                      jugSlotWord (fileDutyDutySlotFor I)
                        σ'_solm I))
                  jugRay).toNat : Int) ≤ maxInt256 := by
            simpa [rate, fee, hbaseWord, hdutyWord] using hrateMax
          have hfoldCodeSolm :
              Reasoning.Theory.extCodeSizeWord σ'_solm
                  (dripVatTargetWord σ'_solm I) = ⟨0⟩ :=
            hfoldNoCode
          have hfoldNoCodeSolmRaw :
              (UInt256.ofNat
                ((σ'_solm.find? (dripVatAddress σ'_solm I)).option
                  0 (fun acc => acc.code.size))).toNat = 0 :=
            drip_extCodeSizeWord_zero_lookup_code_zero
              (σ := σ'_solm)
              (target := dripVatTargetWord σ'_solm I)
              (addr := dripVatAddress σ'_solm I)
              (dripVatAddress_eq_target σ'_solm I) hfoldCodeSolm
          have hbody :
              ExecTransitionBody config contract evm locals
                dripTransition.body .reverted := by
            simpa [evm, locals, initState, jugSlotWord] using
              (jugDripSourceBodyVatFoldNoCodeRevertsNOne
                (σ := σ)
                (σ₀ := σ₀) (A := A) (I := I) (g := g)
                (evmVat :=
                  { evm with
                    accountMap := σ'_solm
                    substate := A'_solm })
                (out := out) hwv hsz36 hleSolm hvatCodeSolm
                (by simpa [evm] using hcallSolm) _hdecOut
                (by
                  simpa [evm, initState, jugSlotWord] using
                    haddNoSolm)
                (by
                  simpa [evm, initState, jugSlotWord] using
                    hfeeNZSolm)
                (by
                  simpa [evm, initState, jugSlotWord] using
                    hageOneSolm)
                (by
                  simpa [evm, initState, jugSlotWord] using
                    hfitRmulSolm)
                (by
                  simpa [evm, initState, jugSlotWord] using
                    hrateMaxSolm)
                hprevMax
                (by
                  simpa [evm, initState, State.lookupAccount] using
                    hfoldNoCodeSolmRaw))
          have rd2153One := by
            simpa [fee, age, hageOne] using _rd2153
          obtain ⟨_, _, rd1524One⟩ :=
            RD.jugDripRpowNOneReturns
              (R := [⟨1530⟩, dripVatIlksPrevWord out, ⟨0⟩,
                fileDutyIlkWord I, ⟨357⟩, jugSelWord I])
              (by simp) rd2153One
          obtain ⟨_, _, rd1530OneRaw⟩ :=
            RD.jugDripRmulReturns
              (R := [⟨0⟩, fileDutyIlkWord I, ⟨357⟩,
                jugSelWord I])
              (by simp) hfitRmulOne rd1524One
          have rd1530One := by
            simpa [rate] using rd1530OneRaw
          obtain ⟨_, _, rd2397⟩ :=
            RD.jugDripToDiffRoutine rd1530One
          obtain ⟨_, _, rd1570⟩ := RD.jugDiffReturns
            (R := [dripVowTargetWord σ' I, fileDutyIlkWord I,
              dripVatFoldSelectorWord, dripVatTargetWord σ' I,
              dripVatIlksPrevWord out, rate, fileDutyIlkWord I,
              ⟨357⟩, jugSelWord I])
            (g := g) (rate := rate)
            (prev := dripVatIlksPrevWord out)
            (by simp) hrateMax hprevMax (by simpa using rd2397)
          let foldBaseMem :=
            twoWordHashMem (fileDutyIlkWord I) ⟨1⟩
              (twoWordHashMem (fileDutyIlkWord I) ⟨1⟩
                (dripVatIlksPostCallMem I out))
          have hpostSize :
              (dripVatIlksPostCallMem I out).size = 192 :=
            dripVatIlksPostCallMem_size_long I out hlo hout
          have hpostRead64 :
              (dripVatIlksPostCallMem I out).readWithPadding 64 32 =
                UInt256.toByteArray ⟨128⟩ :=
            dripVatIlksPostCallMem_read64_long I out hlo hout
          have hinnerSize :
              (twoWordHashMem (fileDutyIlkWord I) ⟨1⟩
                (dripVatIlksPostCallMem I out)).size = 192 := by
            rw [drip_twoWordHashMem_size_of_ge64
              (fileDutyIlkWord I) (⟨1⟩ : UInt256)
              (by rw [hpostSize]; omega), hpostSize]
          have hinnerRead64 :
              (twoWordHashMem (fileDutyIlkWord I) ⟨1⟩
                (dripVatIlksPostCallMem I out)).readWithPadding
                  64 32 = UInt256.toByteArray ⟨128⟩ :=
            drip_twoWordHashMem_read64_of_ge96
              (fileDutyIlkWord I) (⟨1⟩ : UInt256)
              (by rw [hpostSize]; omega) hpostRead64
          have hfoldBaseSize : foldBaseMem.size = 192 := by
            dsimp [foldBaseMem]
            rw [drip_twoWordHashMem_size_of_ge64
              (fileDutyIlkWord I) (⟨1⟩ : UInt256)
              (by rw [hinnerSize]; omega), hinnerSize]
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
          have hpostSize :
              (dripVatIlksPostCallMem I out).size = 192 :=
            dripVatIlksPostCallMem_size_long I out hlo hout
          have hpostRead64 :
              (dripVatIlksPostCallMem I out).readWithPadding 64 32 =
                UInt256.toByteArray ⟨128⟩ :=
            dripVatIlksPostCallMem_read64_long I out hlo hout
          have hinnerSize :
              (twoWordHashMem (fileDutyIlkWord I) ⟨1⟩
                (dripVatIlksPostCallMem I out)).size = 192 := by
            rw [drip_twoWordHashMem_size_of_ge64
              (fileDutyIlkWord I) (⟨1⟩ : UInt256)
              (by rw [hpostSize]; omega), hpostSize]
          have hinnerRead64 :
              (twoWordHashMem (fileDutyIlkWord I) ⟨1⟩
                (dripVatIlksPostCallMem I out)).readWithPadding
                  64 32 = UInt256.toByteArray ⟨128⟩ :=
            drip_twoWordHashMem_read64_of_ge96
              (fileDutyIlkWord I) (⟨1⟩ : UInt256)
              (by rw [hpostSize]; omega) hpostRead64
          have hfoldBaseSize : foldBaseMem.size = 192 := by
            dsimp [foldBaseMem]
            rw [drip_twoWordHashMem_size_of_ge64
              (fileDutyIlkWord I) (⟨1⟩ : UInt256)
              (by rw [hinnerSize]; omega), hinnerSize]
          have hfoldBaseRead64 :
              foldBaseMem.readWithPadding 64 32 =
                UInt256.toByteArray ⟨128⟩ := by
            dsimp [foldBaseMem]
            exact drip_twoWordHashMem_read64_of_ge96
              (fileDutyIlkWord I) (⟨1⟩ : UInt256)
              (by rw [hinnerSize]; omega) hinnerRead64
          have rd2153One := by
            simpa [fee, age, hageOne] using _rd2153
          obtain ⟨_, _, rd1524One⟩ :=
            RD.jugDripRpowNOneReturns
              (R := [⟨1530⟩, dripVatIlksPrevWord out, ⟨0⟩,
                fileDutyIlkWord I, ⟨357⟩, jugSelWord I])
              (by simp) rd2153One
          obtain ⟨_, _, rd1530OneRaw⟩ :=
            RD.jugDripRmulReturns
              (R := [⟨0⟩, fileDutyIlkWord I, ⟨357⟩,
                jugSelWord I])
              (by simp) hfitRmulOne rd1524One
          have rd1530One := by
            simpa [rate] using rd1530OneRaw
          obtain ⟨_, _, rd2397⟩ :=
            RD.jugDripToDiffRoutine rd1530One
          obtain ⟨_, _, rd1570⟩ := RD.jugDiffReturns
            (R := [dripVowTargetWord σ' I, fileDutyIlkWord I,
              dripVatFoldSelectorWord, dripVatTargetWord σ' I,
              dripVatIlksPrevWord out, rate, fileDutyIlkWord I,
              ⟨357⟩, jugSelWord I])
            (g := g) (rate := rate)
            (prev := dripVatIlksPrevWord out)
            (by simp) hrateMax hprevMax (by simpa using rd2397)
          obtain ⟨gasWord, _, _, rd1650⟩ :=
            RD.jugDripVatFoldCallReady hfoldBaseSize hfoldBaseRead64
              hfoldNoCode rd1570
          obtain
            ⟨σ'', z, foldOut, AinFold, callGasFold, _, _,
              hΘFold, rd1651, hfoldOutSize⟩ :=
            RD.jugDripVatFoldPostCall rd1650 hdepth
          have hfoldCallMemSize :
              (dripVatFoldCalldataMem σ' I
                (UInt256.sub rate (dripVatIlksPrevWord out))
                foldBaseMem).size = 228 :=
            dripVatFoldCalldataMem_size σ' I
              (UInt256.sub rate (dripVatIlksPrevWord out))
              hfoldBaseSize
          have hfoldCallMemRead64 :
              (dripVatFoldCalldataMem σ' I
                (UInt256.sub rate (dripVatIlksPrevWord out))
                foldBaseMem).readWithPadding 64 32 =
                  UInt256.toByteArray ⟨128⟩ :=
            dripVatFoldCalldataMem_read64 σ' I
              (UInt256.sub rate (dripVatIlksPrevWord out))
              hfoldBaseSize hfoldBaseRead64
          have hrhoWord :
              jugSlotWord (fileDutyRhoSlotFor I) σ I =
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
              (σ := σ) (σ₀ := σ₀)
              (A := A) (I := I) (g := g) hcodeSizeSolm
          rcases hΘ with ⟨g'', A', hΘ'⟩
          have hdepthNe : evm.executionEnv.depth ≠ 1024 := by
            intro hbad
            simp [evm, initState] at hbad
            rw [hbad] at hdepth
            omega
          have htgtAddr :
              dripVatAddress σ I =
                AccountAddress.ofUInt256
                  (dripVatTargetWord σ I) := by
            exact dripVatAddress_eq_target σ I
          have htgt :
              EVM.address (dripVatAddress σ I) =
                AccountAddress.ofUInt256
                  (dripVatTargetWord σ I) := by
            rw [htgtAddr]
            exact evmAddress_accountAddress _
          have hΘE :
              (σ', g'', A', true, out) =
                Ethereum.EVM.Θ evm.accountMap evm.σ₀ Ain
                  (AccountAddress.ofUInt256
                    (UInt256.ofNat evm.executionEnv.codeOwner))
                  evm.executionEnv.sender
                  (AccountAddress.ofUInt256
                    (dripVatTargetWord σ I))
                  (toExecute evm.accountMap
                    (AccountAddress.ofUInt256
                      (dripVatTargetWord σ I)))
                  callGas (UInt256.ofNat evm.executionEnv.gasPrice)
                  ⟨0⟩ ⟨0⟩
                  ((dripVatIlksCalldataMem I
                    (dripIlkHashMem I)).readWithPadding
                      dripVatIlksOutPtr.toNat dripVatIlksInSize.toNat)
                  (evm.executionEnv.depth + 1)
                  evm.executionEnv.header evm.executionEnv.blobVersionedHashes evm.executionEnv.blocks true := by
            simpa [evm, initState, hperm] using hΘ'
          let σ'_solm := σ'
          let A'_solm := A'
          have hcallSolm :
              typedCallViaEVM config evm (EVM.address (dripVatAddress σ I)) "ilks" 0
                [.fixedBytes bytes32Width (fileDutyIlkBytes I)]
                (true, { evm with accountMap := σ', substate := A' }, out) true := by
            simpa [evm, evm] using
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
            rfl
          have hfoldEncode :
              config.externalABI.encode? "fold"
                  [.fixedBytes bytes32Width (fileDutyIlkBytes I),
                    .address (AccountAddress.ofUInt256
                      (dripVowTargetWord σ'_solm I)),
                    .int ((rate.toNat : Int) -
                      ((dripVatIlksPrevWord out).toNat : Int))] =
                some ((dripVatFoldCalldataMem σ' I
                  (UInt256.sub rate (dripVatIlksPrevWord out))
                  foldBaseMem).readWithPadding
                    dripVatFoldOutPtr.toNat
                    dripVatFoldInSize.toNat) := by
            rw [hvowWord]
            exact dripVatFoldEncode_signed_eq σ' I rate
              (dripVatIlksPrevWord out)
              (UInt256.sub rate (dripVatIlksPrevWord out))
              hfoldBaseSize hsz36 hrateMax hprevMax rfl
          have hbaseWord : jugSlotWord ⟨4⟩ σ' I =
              jugSlotWord ⟨4⟩ σ'_solm I :=
            rfl
          have hdutyWord :
              jugSlotWord (fileDutyDutySlotFor I) σ' I =
                jugSlotWord (fileDutyDutySlotFor I) σ'_solm I :=
            rfl
          have haddNoSolm :
              ¬ UInt256.size ≤
                (jugSlotWord ⟨4⟩ σ'_solm I).toNat +
                  (jugSlotWord (fileDutyDutySlotFor I)
                    σ'_solm I).toNat := by
            intro hbad
            exact haddOverflow (by
              simpa [hbaseWord, hdutyWord] using hbad)
          have hfeeNZSolm :
              jugSlotWord ⟨4⟩ σ'_solm I +
                  jugSlotWord (fileDutyDutySlotFor I) σ'_solm I ≠
                ⟨0⟩ := by
            intro hbad
            exact hfeeZero (by
              simpa [fee, hbaseWord, hdutyWord] using hbad)
          have hrhoPostWord :
              jugSlotWord (fileDutyRhoSlotFor I) σ' I =
                jugSlotWord (fileDutyRhoSlotFor I) σ'_solm I :=
            rfl
          have hageOneEvm :
              UInt256.sub (UInt256.ofNat I.header.timestamp)
                (jugSlotWord (fileDutyRhoSlotFor I) σ' I) =
                  ⟨1⟩ := by
            simpa [age] using hageOne
          have hageOneSolm :
              UInt256.sub (UInt256.ofNat I.header.timestamp)
                (jugSlotWord (fileDutyRhoSlotFor I) σ'_solm I) =
                  ⟨1⟩ := by
            simpa [hrhoPostWord] using hageOneEvm
          have hfitRmulSolm :
              (jugSlotWord ⟨4⟩ σ'_solm I +
                  jugSlotWord (fileDutyDutySlotFor I)
                    σ'_solm I).toNat *
                (dripVatIlksPrevWord out).toNat < UInt256.size := by
            simpa [fee, hbaseWord, hdutyWord] using hfitRmulOne
          have hrateMaxSolm :
              ((UInt256.div
                  (dripVatIlksPrevWord out *
                    (jugSlotWord ⟨4⟩ σ'_solm I +
                      jugSlotWord (fileDutyDutySlotFor I)
                        σ'_solm I))
                  jugRay).toNat : Int) ≤ maxInt256 := by
            simpa [rate, fee, hbaseWord, hdutyWord] using hrateMax
          have hrateSolmEq :
              UInt256.div
                  (dripVatIlksPrevWord out *
                    (solcSlotWord σ'_solm I ⟨4⟩ +
                      solcSlotWord σ'_solm I
                        (fileDutyDutySlotFor I)))
                  jugRay =
                rate := by
            change UInt256.div
                (dripVatIlksPrevWord out *
                  (jugSlotWord ⟨4⟩ σ'_solm I +
                    jugSlotWord (fileDutyDutySlotFor I) σ'_solm I))
                jugRay = rate
            simpa [rate, fee, hbaseWord, hdutyWord]
          have hfoldCodeSolmNe :
              Reasoning.Theory.extCodeSizeWord σ'_solm
                  (dripVatTargetWord σ'_solm I) ≠ ⟨0⟩ :=
            hfoldNoCode
          have hfoldCodeSolm :
              0 <
                (UInt256.ofNat
                  ((evmVatS.lookupAccount
                    (dripVatAddress evmVatS.accountMap
                      evmVatS.executionEnv)).option 0
                        (fun acc => acc.code.size))).toNat := by
            simpa [evmVatS, evm, initState] using
              (dripVatCode_pos_of_codeSize_ne_zero
                (σ := σ'_solm) (σ₀ := σ₀)
                (A := A'_solm) (I := I) (g := g) hfoldCodeSolmNe)
          cases z
          · rcases hΘFold with ⟨gFold'', AFold', hΘFold'⟩
            have hΘFoldE :
                (σ'', gFold'', AFold', false, foldOut) =
                  Ethereum.EVM.Θ evmVatE.accountMap
                    evmVatE.σ₀ AinFold
                    (AccountAddress.ofUInt256
                      (UInt256.ofNat
                        evmVatE.executionEnv.codeOwner))
                    evmVatE.executionEnv.sender
                    (AccountAddress.ofUInt256
                      (dripVatTargetWord σ' I))
                    (toExecute evmVatE.accountMap
                      (AccountAddress.ofUInt256
                        (dripVatTargetWord σ' I)))
                    callGasFold
                    (UInt256.ofNat evmVatE.executionEnv.gasPrice)
                    ⟨0⟩ ⟨0⟩
                    ((dripVatFoldCalldataMem σ' I
                      (UInt256.sub rate (dripVatIlksPrevWord out))
                      foldBaseMem).readWithPadding
                        dripVatFoldOutPtr.toNat
                        dripVatFoldInSize.toNat)
                    (evmVatE.executionEnv.depth + 1)
                    evmVatE.executionEnv.header evmVatE.executionEnv.blobVersionedHashes evmVatE.executionEnv.blocks true := by
              simpa [evmVatE, evm, initState, hperm, foldBaseMem] using
                hΘFold'
            let σ''_solm := σ''
            let A''_solm := AFold'
            have hfoldCallSolm :
                typedCallViaEVM config evmVatS
                  (EVM.address (dripVatAddress σ'_solm I)) "fold" 0
                  [.fixedBytes bytes32Width (fileDutyIlkBytes I),
                    .address (AccountAddress.ofUInt256 (dripVowTargetWord σ'_solm I)),
                    .int ((rate.toNat : Int) -
                      ((dripVatIlksPrevWord out).toNat : Int))]
                  (false, { evmVatS with accountMap := σ'', substate := AFold' }, foldOut) true := by
              simpa [evmVatE, evmVatS, evm] using
                callCoincides hfoldDepthNe hfoldTarget hfoldEncode hΘFoldE
            have hbody :
                ExecTransitionBody config contract evm locals
                  dripTransition.body .reverted := by
              simpa [evm, evmVatS, locals, initState, jugSlotWord,
                hrateSolmEq] using
                (jugDripSourceBodyVatFoldCallFailedRevertsNOne
                  (σ := σ)
                  (σ₀ := σ₀) (A := A) (I := I) (g := g)
                  (evmVat := evmVatS)
                  (evmFold :=
                    { evmVatS with
                      accountMap := σ''_solm,
                      substate := A''_solm })
                  (out := out) (foldOut := foldOut)
                  hwv hsz36 hleSolm hvatCodeSolm
                  (by simpa [evm, evmVatS] using hcallSolm)
                  _hdecOut
                  (by
                    simpa [evmVatS, evm, initState, jugSlotWord]
                      using haddNoSolm)
                  (by
                    simpa [evmVatS, evm, initState, jugSlotWord]
                      using hfeeNZSolm)
                  (by
                    simpa [evmVatS, evm, initState, jugSlotWord]
                      using hageOneSolm)
                  (by
                    simpa [evmVatS, evm, initState, jugSlotWord]
                      using hfitRmulSolm)
                  (by
                    simpa [evmVatS, evm, initState, jugSlotWord]
                      using hrateMaxSolm)
                  hprevMax hfoldCodeSolm
                  (by
                    simpa [evmVatS, evm, initState, jugSlotWord,
                      hrateSolmEq] using hfoldCallSolm))
            have hrev := RD.jugDripVatFoldCallFailed
              (targetWord := dripVatTargetWord σ' I) rd1651
              hfoldOutSize
            exact hrev.reEquivExecutionRevert hcode hdispatch
              (jugDecode_drip_ok hsz36) hbody
          · rcases hΘFold with ⟨gFold'', AFold', hΘFold'⟩
            have hΘFoldE :
                (σ'', gFold'', AFold', true, foldOut) =
                  Ethereum.EVM.Θ evmVatE.accountMap
                    evmVatE.σ₀ AinFold
                    (AccountAddress.ofUInt256
                      (UInt256.ofNat
                        evmVatE.executionEnv.codeOwner))
                    evmVatE.executionEnv.sender
                    (AccountAddress.ofUInt256
                      (dripVatTargetWord σ' I))
                    (toExecute evmVatE.accountMap
                      (AccountAddress.ofUInt256
                        (dripVatTargetWord σ' I)))
                    callGasFold
                    (UInt256.ofNat evmVatE.executionEnv.gasPrice)
                    ⟨0⟩ ⟨0⟩
                    ((dripVatFoldCalldataMem σ' I
                      (UInt256.sub rate (dripVatIlksPrevWord out))
                      foldBaseMem).readWithPadding
                        dripVatFoldOutPtr.toNat
                        dripVatFoldInSize.toNat)
                    (evmVatE.executionEnv.depth + 1)
                    evmVatE.executionEnv.header evmVatE.executionEnv.blobVersionedHashes evmVatE.executionEnv.blocks true := by
              simpa [evmVatE, evm, initState, hperm, foldBaseMem] using
                hΘFold'
            let σ''_solm := σ''
            let A''_solm := AFold'
            have hfoldCallSolm :
                typedCallViaEVM config evmVatS
                  (EVM.address (dripVatAddress σ'_solm I)) "fold" 0
                  [.fixedBytes bytes32Width (fileDutyIlkBytes I),
                    .address (AccountAddress.ofUInt256 (dripVowTargetWord σ'_solm I)),
                    .int ((rate.toNat : Int) -
                      ((dripVatIlksPrevWord out).toNat : Int))]
                  (true, { evmVatS with accountMap := σ'', substate := AFold' }, foldOut) true := by
              simpa [evmVatE, evmVatS, evm] using
                callCoincides hfoldDepthNe hfoldTarget hfoldEncode hΘFoldE
            let evmFoldS :=
              { evmVatS with
                accountMap := σ''_solm,
                substate := A''_solm }
            let finalLocals :=
              (dripDeltaLocalsInt I out
                (jugSlotWord ⟨4⟩
                  evmVatS.accountMap evmVatS.executionEnv +
                  jugSlotWord (fileDutyDutySlotFor I)
                    evmVatS.accountMap evmVatS.executionEnv)
                (jugSlotWord ⟨4⟩
                  evmVatS.accountMap evmVatS.executionEnv +
                  jugSlotWord (fileDutyDutySlotFor I)
                    evmVatS.accountMap evmVatS.executionEnv)
                rate
                ((rate.toNat : Int) -
                  ((dripVatIlksPrevWord out).toNat : Int))).insert
                    "_foldRet" .unit
            let evmRhoS :=
              Solm.EVM.storageStore evmFoldS
                evmFoldS.executionEnv.codeOwner
                (fileDutyRhoSlotFor I)
                (UInt256.ofNat evmFoldS.executionEnv.header.timestamp)
            have hbody :
                ExecTransitionBody config contract evm locals
                  dripTransition.body
                  (.returned
                    { contract := contract, locals := finalLocals }
                    evmRhoS
                    (some [.int (Int.ofNat rate.toNat)])) := by
              simpa [evm, evmVatS, evmFoldS, finalLocals, evmRhoS,
                locals, initState, jugSlotWord, hrateSolmEq] using
                (jugDripSourceBodyVatFoldCallSucceededReturnsNOne
                  (σ := σ)
                  (σ₀ := σ₀) (A := A) (I := I) (g := g)
                  (evmVat := evmVatS) (evmFold := evmFoldS)
                  (out := out) (foldOut := foldOut)
                  hwv hsz36 hleSolm hvatCodeSolm
                  (by simpa [evm, evmVatS] using hcallSolm)
                  _hdecOut
                  (by
                    simpa [evmVatS, evm, initState, jugSlotWord]
                      using haddNoSolm)
                  (by
                    simpa [evmVatS, evm, initState, jugSlotWord]
                      using hfeeNZSolm)
                  (by
                    simpa [evmVatS, evm, initState, jugSlotWord]
                      using hageOneSolm)
                  (by
                    simpa [evmVatS, evm, initState, jugSlotWord]
                      using hfitRmulSolm)
                  (by
                    simpa [evmVatS, evm, initState, jugSlotWord]
                      using hrateMaxSolm)
                  hprevMax hfoldCodeSolm
                  (by
                    simpa [evmVatS, evm, initState, jugSlotWord,
                      hrateSolmEq] using hfoldCallSolm))
            obtain ⟨_, _, rd1669⟩ :=
              RD.jugDripVatFoldCallSucceeded
                (targetWord := dripVatTargetWord σ' I) rd1651
            have hret := RD.jugDripVatFoldStoreRhoReturns
              (targetWord := dripVatTargetWord σ' I)
              hsz36 hperm hfoldCallMemSize hfoldCallMemRead64 rd1669
            exact hret.reEquivExecutionGen hcode hdispatch
              (jugDecode_drip_ok hsz36) hbody
              (by
                simp [evmRhoS, evmFoldS, evmVatS, evm, σ''_solm,
                  A''_solm, σ'_solm, initState, storageStore_accountMap])
              (by
                rw [show dripTransition.returnType = [uint256] by rfl]
                exact returnEquiv_of_encode
                  (by simpa [uint256] using
                    uint256ReturnEncoding rate))
    · let locals := dripLocals I
      let evm :=
        initState σ σ₀ (Sat256.ofUInt256 g) A I
      have hrhoWord :
          jugSlotWord (fileDutyRhoSlotFor I) σ I =
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
          (σ := σ) (σ₀ := σ₀) (A := A)
          (I := I) (g := g) hcodeSizeSolm
      rcases hΘ with ⟨g'', A', hΘ'⟩
      have hdepthNe : evm.executionEnv.depth ≠ 1024 := by
        intro hbad
        simp [evm, initState] at hbad
        rw [hbad] at hdepth
        omega
      have htgtAddr :
          dripVatAddress σ I =
            AccountAddress.ofUInt256
              (dripVatTargetWord σ I) := by
        exact dripVatAddress_eq_target σ I
      have htgt :
          EVM.address (dripVatAddress σ I) =
            AccountAddress.ofUInt256
              (dripVatTargetWord σ I) := by
        rw [htgtAddr]
        exact evmAddress_accountAddress _
      have hΘE :
          (σ', g'', A', true, out) =
            Ethereum.EVM.Θ evm.accountMap evm.σ₀ Ain
              (AccountAddress.ofUInt256
                (UInt256.ofNat evm.executionEnv.codeOwner))
              evm.executionEnv.sender
              (AccountAddress.ofUInt256
                (dripVatTargetWord σ I))
              (toExecute evm.accountMap
                (AccountAddress.ofUInt256
                  (dripVatTargetWord σ I)))
              callGas (UInt256.ofNat evm.executionEnv.gasPrice)
              ⟨0⟩ ⟨0⟩
              ((dripVatIlksCalldataMem I
                (dripIlkHashMem I)).readWithPadding
                  dripVatIlksOutPtr.toNat dripVatIlksInSize.toNat)
              (evm.executionEnv.depth + 1)
              evm.executionEnv.header evm.executionEnv.blobVersionedHashes evm.executionEnv.blocks true := by
        simpa [evm, initState, hperm] using hΘ'
      let σ'_solm := σ'
      let A'_solm := A'
      have hcallSolm :
          typedCallViaEVM config evm (EVM.address (dripVatAddress σ I)) "ilks" 0
            [.fixedBytes bytes32Width (fileDutyIlkBytes I)]
            (true, { evm with accountMap := σ', substate := A' }, out) true := by
        simpa [evm, evm] using
          callCoincides hdepthNe htgt (dripVatIlksEncode_eq I hsz36) hΘE
      have hbaseWord : jugSlotWord ⟨4⟩ σ' I =
          jugSlotWord ⟨4⟩ σ'_solm I :=
        rfl
      have hdutyWord :
          jugSlotWord (fileDutyDutySlotFor I) σ' I =
            jugSlotWord (fileDutyDutySlotFor I) σ'_solm I :=
        rfl
      have haddNoSolm :
          ¬ UInt256.size ≤ (jugSlotWord ⟨4⟩ σ'_solm I).toNat +
            (jugSlotWord (fileDutyDutySlotFor I)
              σ'_solm I).toNat := by
        intro hbad
        exact haddOverflow (by
          simpa [hbaseWord, hdutyWord] using hbad)
      have hfeeNZSolm :
          jugSlotWord ⟨4⟩ σ'_solm I +
              jugSlotWord (fileDutyDutySlotFor I) σ'_solm I ≠
            ⟨0⟩ := by
        intro hbad
        exact hfeeZero (by
          simpa [fee, hbaseWord, hdutyWord] using hbad)
      have hrhoPostWord :
          jugSlotWord (fileDutyRhoSlotFor I) σ' I =
            jugSlotWord (fileDutyRhoSlotFor I) σ'_solm I :=
        rfl
      have hageOneEvm :
          UInt256.sub (UInt256.ofNat I.header.timestamp)
            (jugSlotWord (fileDutyRhoSlotFor I) σ' I) = ⟨1⟩ := by
        simpa [age] using hageOne
      have hageOneSolm :
          UInt256.sub (UInt256.ofNat I.header.timestamp)
            (jugSlotWord (fileDutyRhoSlotFor I) σ'_solm I) =
              ⟨1⟩ := by
        simpa [hrhoPostWord] using hageOneEvm
      have hfitRmulSolm :
          (jugSlotWord ⟨4⟩ σ'_solm I +
              jugSlotWord (fileDutyDutySlotFor I)
                σ'_solm I).toNat *
            (dripVatIlksPrevWord out).toNat < UInt256.size := by
        simpa [fee, hbaseWord, hdutyWord] using hfitRmulOne
      have hrateMaxNotSolm :
          ¬ ((UInt256.div
              (dripVatIlksPrevWord out *
                (jugSlotWord ⟨4⟩ σ'_solm I +
                  jugSlotWord (fileDutyDutySlotFor I) σ'_solm I))
              jugRay).toNat : Int) ≤ maxInt256 := by
        intro hbad
        exact hrateMax (by
          simpa [rate, fee, hbaseWord, hdutyWord] using hbad)
      have hbody :
          ExecTransitionBody config contract evm locals
            dripTransition.body .reverted := by
        simpa [evm, locals, initState, jugSlotWord] using
          (jugDripSourceBodyVatIlksDiffXBoundRevertsNOne
            (σ := σ)
            (σ₀ := σ₀) (A := A) (I := I) (g := g)
            (evmVat :=
              { evm with
                accountMap := σ'_solm
                substate := A'_solm })
            (out := out) hwv hsz36 hleSolm hvatCodeSolm
            (by simpa [evm] using hcallSolm) _hdecOut
            (by
              simpa [evm, initState, jugSlotWord] using
                haddNoSolm)
            (by
              simpa [evm, initState, jugSlotWord] using
                hfeeNZSolm)
            (by
              simpa [evm, initState, jugSlotWord] using
                hageOneSolm)
            (by
              simpa [evm, initState, jugSlotWord] using
                hfitRmulSolm)
            (by
              simpa [evm, initState, jugSlotWord] using
                hrateMaxNotSolm))
      have rd2153One := by
        simpa [fee, age, hageOne] using _rd2153
      obtain ⟨_, _, rd1524One⟩ :=
        RD.jugDripRpowNOneReturns
          (R := [⟨1530⟩, dripVatIlksPrevWord out, ⟨0⟩,
            fileDutyIlkWord I, ⟨357⟩, jugSelWord I])
          (by simp) rd2153One
      obtain ⟨_, _, rd1530OneRaw⟩ :=
        RD.jugDripRmulReturns
          (R := [⟨0⟩, fileDutyIlkWord I, ⟨357⟩,
            jugSelWord I])
          (by simp) hfitRmulOne rd1524One
      have rd1530One := by
        simpa [rate] using rd1530OneRaw
      obtain ⟨_, _, rd2397⟩ := RD.jugDripToDiffRoutine rd1530One
      have hrev := RD.jugDiffRevertXBound
        (R := [dripVowTargetWord σ' I, fileDutyIlkWord I,
          dripVatFoldSelectorWord, dripVatTargetWord σ' I,
          dripVatIlksPrevWord out, rate, fileDutyIlkWord I,
          ⟨357⟩, jugSelWord I])
        (g := g) (rate := rate) (prev := dripVatIlksPrevWord out)
        (by simp) hrateMax (by simpa using rd2397)
      exact hrev.reEquivExecutionRevert hcode hdispatch
        (jugDecode_drip_ok hsz36) hbody
· jug_drip_generic_age_tac
"#

elab "jug_drip_age_one_tac" : tactic => do
  let tacSeq ← match Mathlib.GuardExceptions.parseAsTacticSeq (← getEnv) jugDripAgeOneScript with
    | .ok tacSeq => pure tacSeq
    | .error err => throwError "failed to parse jug_drip_age_one_tac:
{err}"
  evalTactic (← `(tactic| ($tacSeq:tacticSeq)))

end Benchmarks.Dss.Jug
