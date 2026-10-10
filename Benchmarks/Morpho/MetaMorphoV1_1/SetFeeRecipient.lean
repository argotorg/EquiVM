import Benchmarks.Morpho.MetaMorphoV1_1.Dispatch
import Benchmarks.Morpho.MetaMorphoV1_1.SetFeeRecipientSource
import Benchmarks.Morpho.MetaMorphoV1_1.SetFeeRecipientRoutines

/-!
# MetaMorphoV1_1 `setFeeRecipient(address)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 1158; reach lemma `metaMorphoV1_1ReachSetFeeRecipientBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

open SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

/-- `setFeeRecipient(address)`: the theorem `Correct.lean` routes selector 71 to. -/
theorem metaMorphoV1_1SetFeeRecipientBody {σ σ₀ A I} {g : UInt256} (v : MetaMorphoV1_1Immutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (metaMorphoV1_1SelBytes 71)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (metaMorphoV1_1SelBytes 71) rfl hsel
  have hd : dispatchMsg contract I.calldata = some setFeeRecipientTransition := by
    apply metaMorphoV1_1Dispatch_setFeeRecipient <;>
      first | exact hsel | exact selectorMismatch hsel (by decide +kernel)
  obtain ⟨k, C, rd⟩ := metaMorphoV1_1ReachSetFeeRecipientBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hlen : 36 ≤ I.calldata.size
    · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
      · obtain ⟨_, _, rd11163⟩ := setFeeRecipientReachDecoder v (by simp) hwv hlen hhi hsize rd
        by_cases hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · have hdec := decodeCalldata_address_ok (x := "newFeeRecipient") hlen hhi hcanon
          obtain ⟨_, _, rd12917⟩ := setFeeRecipientReachOwner v (by simp) hcanon rd11163
          by_cases howner : AccountAddress.ofNat
              (UInt256.land (codeOwnerStorageWord I σ ⟨8⟩) solcAddrMask).toNat = I.source
          · obtain ⟨_, _, rd1191⟩ := checkOwnerReturn v (by simp) howner
              (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) rd12917
            have haddr : AccountAddress.ofNat (calldataWord I.calldata 4).toNat =
                AccountAddress.ofNat
                  (UInt256.shiftRight (codeOwnerStorageWord I σ ⟨18⟩) ⟨96⟩).toNat ↔
                calldataWord I.calldata 4 =
                  UInt256.shiftRight (codeOwnerStorageWord I σ ⟨18⟩) ⟨96⟩ := by
              rw [addressOfNat_eq_iff_solcAddrMask_eq, solcAddrMask_clean_left hcanon,
                solcAddrMask_clean_left (shiftRight96_canonical _)]
            by_cases heq : calldataWord I.calldata 4 =
                UInt256.shiftRight (codeOwnerStorageWord I σ ⟨18⟩) ⟨96⟩
            · exact (setFeeRecipientSameRevert v (by simp) hcanon heq rd1191).reEquivExecutionRevert
                hcode hd hdec (setFeeRecipientRevertsSame _ _ _ hwv hhi howner (haddr.mpr heq))
            · obtain ⟨aw1, k1, C1, h1⟩ :=
                setFeeRecipientDifferentGuard v (by simp) hcanon heq rd1191
              have hzero : AccountAddress.ofNat (calldataWord I.calldata 4).toNat =
                  AccountAddress.ofNat 0 ↔ calldataWord I.calldata 4 = ⟨0⟩ := by
                change AccountAddress.ofNat (calldataWord I.calldata 4).toNat =
                  AccountAddress.ofNat (⟨0⟩ : UInt256).toNat ↔ _
                rw [addressOfNat_eq_iff_solcAddrMask_eq, solcAddrMask_clean_left hcanon]
                rfl
              by_cases hbad : calldataWord I.calldata 4 = ⟨0⟩ ∧
                  UInt256.land (codeOwnerStorageWord I σ ⟨18⟩)
                    (UInt256.ofNat (2 ^ 96 - 1)) ≠ ⟨0⟩
              · exact (setFeeRecipientInvalidRevert v (by simp) hbad h1).reEquivExecutionRevert
                  hcode hd hdec (setFeeRecipientRevertsZero _ _ _ hwv hhi howner
                    (haddr.not.mpr heq) ⟨hzero.mpr hbad.1, hbad.2⟩)
              · have hpre := setFeeRecipientPrefix
                  (initState σ σ₀ (Sat256.ofUInt256 g) A I) (immStore v)
                  (AccountAddress.ofNat (calldataWord I.calldata 4).toNat) hwv hhi howner
                  (haddr.not.mpr heq) (fun hb ↦ hbad ⟨hzero.mp hb.1, hb.2⟩)
                obtain ⟨aw2, k2, C2, h2⟩ := setFeeRecipientReachAccrual v (by simp) hbad h1
                rcases accrueInterestSimulation v (by simp) hsize solcFreePtrMem_mload64
                    (by decide) (by rw [solcFreePtrMem_size]) SourceState.init
                    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h2 with
                  ⟨hbad, hrev⟩ | ⟨hstatic, hhalt⟩ |
                    ⟨evm', frame', ptr, mem', out, hperm, hs', hbody, aw3, k3, C3, h3⟩
                · exact hrev.reEquivExecutionRevert hcode hd hdec
                    (setFeeRecipientAccrualReverts _ _ _ hpre hbad)
                · exact hhalt.reEquivStaticHalt hcode hd hdec
                    (setFeeRecipientAccrualStatic _ _ _ hpre hstatic)
                · nth_rw 1 [← hs'.env] at h3
                  have hp : evm'.executionEnv.perm = true := by rw [hs'.env]; exact hperm
                  exact (setFeeRecipientStoreReturn v (by simp) hcanon hp h3).reEquivExecutionGen
                    hcode hd hdec (setFeeRecipientBodyReturns _ _ _ _ _ _ hpre hbody)
                    rfl voidReturnEquiv
          · exact (checkOwnerRevert v (by simp) howner rd12917).reEquivExecutionRevert
              hcode hd hdec (adminBodyRevertsOwner _ _ (immStore v) _ hwv hhi howner)
        · exact (decodeAddressAt4Revert v (by simp) hcanon rd11163).reEquivDecodingFailed
            hcode hd (decodeCalldata_address_none_noncanon hlen hhi hcanon)
      · have hrev := setFeeRecipientRevertLength v (by simp) hwv (by
          rw [calldataNot3_eq_sub hsz hsize,
            solcDecodeLenCheckHuge_4_32 (Nat.le_of_not_gt hhi) hsize]
          decide) rd
        exact hrev.reEquivDecodingFailed hcode hd
          (decodeCalldata_address_none_huge (Nat.le_of_not_gt hhi))
    · have hrev := setFeeRecipientRevertLength v (by simp) hwv (by
        rw [calldataNot3_eq_sub hsz hsize,
          solcDecodeLenCheckShort_4_32 hsz (by omega) hsize]
        decide) rd
      exact hrev.reEquivDecodingFailed hcode hd (decodeCalldata_address_none_short hsz (by omega))
  · exact dispatchedRevert hcode hd (setFeeRecipientRevertNonPayable v (by simp) hwv rd)
      (fun _ ↦ bodyReverts_nonPayable hwv)

end Benchmarks.Morpho.MetaMorphoV1_1
