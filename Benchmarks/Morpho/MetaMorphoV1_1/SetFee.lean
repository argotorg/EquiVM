import Benchmarks.Morpho.MetaMorphoV1_1.Dispatch
import Benchmarks.Morpho.MetaMorphoV1_1.SetFeeSource
import Benchmarks.Morpho.MetaMorphoV1_1.SetFeeRoutines

/-!
# MetaMorphoV1_1 `setFee(uint256)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 7417; reach lemma `metaMorphoV1_1ReachSetFeeBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

open SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

/-- `setFee(uint256)`: the theorem `Correct.lean` routes selector 28 to. -/
theorem metaMorphoV1_1SetFeeBody {σ σ₀ A I} {g : UInt256} (v : MetaMorphoV1_1Immutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (metaMorphoV1_1SelBytes 28)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (metaMorphoV1_1SelBytes 28) rfl hsel
  have hd : dispatchMsg contract I.calldata = some setFeeTransition := by
    apply metaMorphoV1_1Dispatch_setFee <;>
      first | exact hsel | exact selectorMismatch hsel (by decide +kernel)
  obtain ⟨k, C, rd⟩ := metaMorphoV1_1ReachSetFeeBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  let value := calldataWord I.calldata 4
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hlen : 36 ≤ I.calldata.size
    · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
      · have hdec := decodeCalldata_uint256_ok (x := "newFee") hlen hhi
        obtain ⟨_, _, rd12917⟩ := setFeeReachOwner v (by simp) hwv hlen hhi hsize rd
        by_cases howner : ownerAddress evm = I.source
        · obtain ⟨_, _, rd7445⟩ := checkOwnerReturn v (by simp) howner
            (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) rd12917
          by_cases heq : value = setFeeOld evm
          · exact (setFeeSameRevert v (by simp) heq rd7445).reEquivExecutionRevert
              hcode hd hdec (setFeeRevertsGuard evm (immStore v) value hwv hhi howner
                (fun hg ↦ hg.1 heq))
          · obtain ⟨aw1, k1, C1, h1⟩ := setFeeDifferentGuard v (by simp) heq rd7445
            by_cases hbound : value.toNat ≤ 500000000000000000
            · obtain ⟨aw2, k2, C2, h2⟩ := setFeeBoundGuard v (by simp) hbound h1
              have hzero : accrueFeeRecipient evm = AccountAddress.ofNat 0 ↔
                  UInt256.shiftRight (codeOwnerStorageWord I σ ⟨18⟩) ⟨96⟩ = ⟨0⟩ := by
                change AccountAddress.ofNat
                  (UInt256.shiftRight (codeOwnerStorageWord I σ ⟨18⟩) ⟨96⟩).toNat =
                    AccountAddress.ofNat (⟨0⟩ : UInt256).toNat ↔ _
                rw [addressOfNat_eq_iff_solcAddrMask_eq,
                  solcAddrMask_clean_left (shiftRight96_canonical _)]
                rfl
              by_cases hbad : value ≠ ⟨0⟩ ∧
                  UInt256.shiftRight (codeOwnerStorageWord I σ ⟨18⟩) ⟨96⟩ = ⟨0⟩
              · exact (setFeeInvalidRevert v (by simp) hbad h2).reEquivExecutionRevert
                  hcode hd hdec (setFeeRevertsGuard evm (immStore v) value hwv hhi howner
                    (fun hg ↦ hg.2.2 ⟨hbad.1, hzero.mpr hbad.2⟩))
              · have hgood : setFeeAllowed evm value :=
                  ⟨heq, hbound, fun hb ↦ hbad ⟨hb.1, hzero.mp hb.2⟩⟩
                have hpre := setFeePrefix evm (immStore v) value hwv hhi howner hgood
                obtain ⟨aw3, k3, C3, h3⟩ := setFeeReachAccrual v (by simp) hbad h2
                rcases accrueInterestSimulation v (by simp) hsize solcFreePtrMem_mload64
                    (by decide) (by rw [solcFreePtrMem_size]) SourceState.init
                    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h3 with
                  ⟨hbad, hrev⟩ | ⟨hstatic, hhalt⟩ |
                    ⟨evm', frame', ptr, mem', out, hperm, hs', hbody, aw4, k4, C4, h4⟩
                · exact hrev.reEquivExecutionRevert hcode hd hdec
                    (setFeeAccrualReverts evm (immStore v) value hpre hbad)
                · exact hhalt.reEquivStaticHalt hcode hd hdec
                    (setFeeAccrualStatic evm (immStore v) value hpre hstatic)
                · nth_rw 1 [← hs'.env] at h4
                  have hp : evm'.executionEnv.perm = true := by rw [hs'.env]; exact hperm
                  exact (setFeeStoreReturn v (by simp) hp h4).reEquivExecutionGen
                    hcode hd hdec (setFeeBodyReturns evm evm' (immStore v) value frame' ptr
                      (by omega) hpre hbody) rfl voidReturnEquiv
            · exact (setFeeBoundRevert v (by simp) hbound h1).reEquivExecutionRevert
                hcode hd hdec (setFeeRevertsGuard evm (immStore v) value hwv hhi howner
                  (fun hg ↦ hbound hg.2.1))
        · exact (checkOwnerRevert v (by simp) howner rd12917).reEquivExecutionRevert
            hcode hd hdec (adminBodyRevertsOwner evm _ (immStore v) setFeeAdminTail hwv hhi howner)
      · have hrev := setFeeRevertLength v (by simp) hwv (by
          rw [calldataNot3_eq_sub hsz hsize,
            solcDecodeLenCheckHuge_4_32 (Nat.le_of_not_gt hhi) hsize]
          decide) rd
        exact hrev.reEquivDecodingFailed hcode hd
          (decodeCalldata_uint256_none_huge (Nat.le_of_not_gt hhi))
    · have hrev := setFeeRevertLength v (by simp) hwv (by
        rw [calldataNot3_eq_sub hsz hsize,
          solcDecodeLenCheckShort_4_32 hsz (by omega) hsize]
        decide) rd
      exact hrev.reEquivDecodingFailed hcode hd (decodeCalldata_uint256_none_short (by omega))
  · exact dispatchedRevert hcode hd (setFeeRevertNonPayable v (by simp) hwv rd)
      (fun _ ↦ bodyReverts_nonPayable hwv)

end Benchmarks.Morpho.MetaMorphoV1_1
