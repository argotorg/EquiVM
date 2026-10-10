import Benchmarks.Morpho.MetaMorphoV1_1.Dispatch
import Benchmarks.Morpho.MetaMorphoV1_1.SetAllocatorRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.SetAllocatorStatic

/-!
# MetaMorphoV1_1 `setIsAllocator(address,bool)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 3552; reach lemma `metaMorphoV1_1ReachSetIsAllocatorBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option maxRecDepth 2000000

/-- `setIsAllocator(address,bool)`: the theorem `Correct.lean` routes selector 52 to. -/
theorem metaMorphoV1_1SetIsAllocatorBody {σ σ₀ A I} {g : UInt256} (v : MetaMorphoV1_1Immutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (metaMorphoV1_1SelBytes 52)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (metaMorphoV1_1SelBytes 52) rfl hsel
  have hd : dispatchMsg contract I.calldata = some setIsAllocatorTransition := by
    apply metaMorphoV1_1Dispatch_setIsAllocator <;>
      first | exact hsel | exact selectorMismatch hsel (by decide +kernel)
  obtain ⟨k, C, rd⟩ := metaMorphoV1_1ReachSetIsAllocatorBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  let addr := AccountAddress.ofNat (calldataWord I.calldata 4).toNat
  let flag := calldataWord I.calldata 36
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hlen : 68 ≤ I.calldata.size
    · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
      · obtain ⟨_, _, rd11163⟩ := setAllocatorReachDecoder v (by simp) hwv hlen hhi hsize rd
        by_cases hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · by_cases hflag : flag = ⟨0⟩ ∨ flag = ⟨1⟩
          · have hdec := decodeCalldata_addr_bool_ok
              (x := "newAllocator") (y := "newIsAllocator") hlen hhi hcanon hflag
            have hw : UInt256.ofNat addr.val = calldataWord I.calldata 4 := by
              change EVM.word (AccountAddress.ofNat (calldataWord I.calldata 4).toNat).val = _
              rw [word_of_addressOfNat_eq_mask, solcAddrMask_clean hcanon]
            obtain ⟨_, _, rd12917⟩ := setAllocatorReachOwner v (by simp) hcanon hflag rd11163
            by_cases howner : ownerAddress evm = I.source
            · obtain ⟨_, _, rd3599⟩ := checkOwnerReturn v (by simp) howner
                (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) rd12917
              rw [← hw] at rd3599
              by_cases hne : allocatorBoolWord evm addr ≠ flag
              · obtain ⟨_, _, _, rd3637⟩ := setAllocatorReachStore (evm := evm) v
                  (by simp) hne rd3599
                by_cases hperm : I.perm = true
                · have hret := setAllocatorStoreReturn (evm := evm) v (by simp)
                    hflag hperm rd3637
                  exact hret.reEquivExecutionGen hcode hd hdec
                    (setAllocatorBodyReturns evm (immStore v) addr flag hflag hwv hhi howner hne)
                    rfl voidReturnEquiv
                · have hp : I.perm = false := Bool.eq_false_of_not_eq_true hperm
                  have hstatic := setAllocatorStoreStatic v (by simp) hp rd3637
                  exact hstatic.reEquivStaticHalt hcode hd hdec
                    (setAllocatorBodyStatic evm (immStore v) addr flag hflag
                      hwv hhi howner hne hp)
              · have heq : allocatorBoolWord evm addr = flag := not_not.mp hne
                have hrev := setAllocatorRevertUnchanged (evm := evm) v (by simp) heq rd3599
                exact hrev.reEquivExecutionRevert hcode hd hdec
                  (setAllocatorBodyReverts evm (immStore v) addr flag hflag hwv hhi howner heq)
            · exact (checkOwnerRevert v (by simp) howner rd12917).reEquivExecutionRevert
                hcode hd hdec (adminBodyRevertsOwner evm _ (immStore v) setAllocatorTail
                  hwv hhi howner)
          · exact (setAllocatorRevertFlag v (by simp) hcanon hflag rd11163).reEquivDecodingFailed
              hcode hd (decodeCalldata_addr_bool_none_noncanon_bool hlen hhi hcanon
                (fun hz ↦ hflag (.inl hz)) (fun ho ↦ hflag (.inr ho)))
        · exact (decodeAddressAt4Revert v (by simp) hcanon rd11163).reEquivDecodingFailed
            hcode hd (decodeCalldata_addr_bool_none_noncanon_addr hlen hhi hcanon)
      · have hrev := setAllocatorRevertLength v (by simp) hwv (by
          rw [calldataNot3_eq_sub hsz hsize,
            solcDecodeLenCheckHuge_4_64 (Nat.le_of_not_gt hhi) hsize]
          decide) rd
        exact hrev.reEquivDecodingFailed hcode hd
          (decodeCalldata_addr_bool_none_huge (Nat.le_of_not_gt hhi))
    · have hrev := setAllocatorRevertLength v (by simp) hwv (by
        rw [calldataNot3_eq_sub hsz hsize,
          solcDecodeLenCheckShort_4_64 hsz (by omega) hsize]
        decide) rd
      exact hrev.reEquivDecodingFailed hcode hd (decodeCalldata_addr_bool_none_short hsz (by omega))
  · exact dispatchedRevert hcode hd (setAllocatorRevertNonPayable v (by simp) hwv rd)
      (fun _ ↦ bodyReverts_nonPayable hwv)

end Benchmarks.Morpho.MetaMorphoV1_1
