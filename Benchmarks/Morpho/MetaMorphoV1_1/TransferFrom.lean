import Benchmarks.Morpho.MetaMorphoV1_1.Dispatch
import Benchmarks.Morpho.MetaMorphoV1_1.TransferFromEntry
import Benchmarks.Morpho.MetaMorphoV1_1.TransferFromBodySource
import Benchmarks.Morpho.MetaMorphoV1_1.SpendAllowanceFunction
import Benchmarks.Morpho.MetaMorphoV1_1.TransferFunction
import Benchmarks.Morpho.MetaMorphoV1_1.ApproveEntry

/-!
# MetaMorphoV1_1 `transferFrom(address,address,uint256)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 10441; reach lemma `metaMorphoV1_1ReachTransferFromBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

/-- `transferFrom(address,address,uint256)`: the theorem `Correct.lean` routes selector 9 to. -/
theorem metaMorphoV1_1TransferFromBody {σ σ₀ A I} {g : UInt256} (v : MetaMorphoV1_1Immutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (metaMorphoV1_1SelBytes 9)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (metaMorphoV1_1SelBytes 9) rfl hsel
  have hd : dispatchMsg contract I.calldata = some transferFromTransition := by
    apply metaMorphoV1_1Dispatch_transferFrom <;>
      first | exact hsel | exact selectorMismatch hsel (by decide +kernel)
  obtain ⟨k, C, rd⟩ := metaMorphoV1_1ReachTransferFromBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hlen : 100 ≤ I.calldata.size
    · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
      · obtain ⟨aw0, k0, C0, h0⟩ := transferFromReachDecoder v (by simp) hwv hlen hhi hsize rd
        by_cases hc0 : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · obtain ⟨aw1, k1, C1, h1⟩ := transferFromDecodeFirst v (by simp) hc0 h0
          by_cases hc1 : (calldataWord I.calldata 36).toNat < EVM.addressModulus
          · have hdec := decodeCalldata_address_address_uint256_ok
              (x := "from") (y := "to") (z := "value") hlen hhi hc0 hc1
            let sender := AccountAddress.ofNat (calldataWord I.calldata 4).toNat
            let recipient := AccountAddress.ofNat (calldataWord I.calldata 36).toNat
            let value := calldataWord I.calldata 68
            let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
            let locals := (((∅ : Store).insert "from" (.address sender)).insert "to"
              (.address recipient)).insert "value" (uint256Value value)
            have hf : locals.get? "from" = some (.address sender) := by
              simp only [locals, store_get_ne _ _ (by decide : ("value" == "from") = false),
                store_get_ne _ _ (by decide : ("to" == "from") = false), store_get_self]
            have ht : locals.get? "to" = some (.address recipient) := by
              simp only [locals, store_get_ne _ _ (by decide : ("value" == "to") = false),
                store_get_self]
            have hv : locals.get? "value" = some (uint256Value value) := store_get_self _ _ _
            obtain ⟨aw2, k2, C2, h2⟩ := transferFromReachFunction v (by simp) hc0 hc1 h1
            by_cases hs : spendAllowanceAllowed evm sender I.source value
            · by_cases hwrite : allowanceWord evm sender I.source = unlimitedAllowance ∨
                  I.perm = true
              · obtain ⟨mem3, aw3, k3, C3, h3⟩ := spendAllowanceFunctionReturn
                  (evm := evm) v (by simp) hs hwrite
                  (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h2
                obtain ⟨aw4, k4, C4, h4⟩ :=
                  metaMorphoV1_1Blocks.metaMorphoV1_1_block_10492_packed
                    (immWords := wordsOf (immStore v)) (by simp)
                    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h3
                let spent := spendAllowanceState evm sender I.source value
                have he : spent.executionEnv = I := spendAllowanceState_executionEnv _ _ _ _
                have h4' : RD (deployedRuntime v) spent.executionEnv (Sat256.ofUInt256 g) evm
                    ⟨12728⟩ [UInt256.ofNat sender.toNat, UInt256.ofNat recipient.toNat, value,
                      ⟨4161⟩, UInt256.shiftRight (calldataWord I.calldata 0) ⟨224⟩]
                    mem3 aw4 ByteArray.empty spent.accountMap k4 C4 := by
                  rw [he]
                  exact h4
                by_cases hg : transferAllowed spent sender recipient value
                · by_cases hp : I.perm = true
                  · obtain ⟨mem5, aw5, k5, C5, h5⟩ := transferFunctionReturn v (by simp) hg
                      (by rw [he]; exact hp)
                      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h4'
                    exact (approveEncodeReturn v (by simp) h5).reEquivExecutionGen hcode hd hdec
                      (transferFromBodyReturns v evm locals sender recipient value
                        hwv hhi hf ht hv hs hg) rfl (returnEquiv_of_encode boolTrueReturnEncoding)
                  · have hp' : I.perm = false := Bool.eq_false_of_not_eq_true hp
                    exact (transferFunctionStatic v (by simp) hg (by rw [he]; exact hp') h4')
                      |>.reEquivStaticHalt hcode hd hdec
                        (transferFromTransferStatic v evm locals sender recipient value
                          hwv hhi hf ht hv hs hg hp')
                · exact (transferFunctionRevert v (by simp) hg h4').reEquivExecutionRevert
                    hcode hd hdec (transferFromTransferReverts v evm locals sender recipient value
                      hwv hhi hf ht hv hs hg)
              · have hfinite : allowanceWord evm sender I.source ≠ unlimitedAllowance :=
                  fun h ↦ hwrite (.inl h)
                have hp : I.perm = false := Bool.eq_false_of_not_eq_true (fun h ↦ hwrite (.inr h))
                exact (spendAllowanceFunctionStatic (evm := evm) v (by simp) hs hfinite hp h2)
                  |>.reEquivStaticHalt hcode hd hdec
                    (transferFromSpendStatic v evm locals sender value hwv hhi hf hv hs hfinite hp)
            · exact (spendAllowanceFunctionRevert (evm := evm) v (by simp) hs h2)
                |>.reEquivExecutionRevert hcode hd hdec
                  (transferFromSpendReverts v evm locals sender value hwv hhi hf hv hs)
          · exact (decodeAddressAt36Revert v (by simp) hc1 h1).reEquivDecodingFailed hcode hd
              (decodeCalldata_address_address_uint256_none_noncanon1 hlen hhi hc0 hc1)
        · exact (decodeAddressAt4Revert v (by simp) hc0 h0).reEquivDecodingFailed hcode hd
            (decodeCalldata_address_address_uint256_none_noncanon0 hlen hhi hc0)
      · have hrev := transferFromRevertLength v (by simp) hwv (by
          rw [calldataNot3_eq_sub hsz hsize,
            solcDecodeLenCheckHuge (head := ⟨4⟩) (need := ⟨96⟩)
              (Nat.le_of_not_gt hhi) hsize (by decide)]
          decide) rd
        exact hrev.reEquivDecodingFailed hcode hd
          (decodeCalldata_address_address_uint256_none_huge (Nat.le_of_not_gt hhi))
    · have hrev := transferFromRevertLength v (by simp) hwv (by
        rw [calldataNot3_eq_sub hsz hsize,
          solcDecodeLenCheckShort (head := ⟨4⟩) (need := ⟨96⟩) hsz (by exact Nat.lt_of_not_ge hlen)
            hsize (by decide)]
        decide) rd
      exact hrev.reEquivDecodingFailed hcode hd
        (decodeCalldata_address_address_uint256_none_short hsz (by omega))
  · exact dispatchedRevert hcode hd (transferFromRevertNonPayable v (by simp) hwv rd)
      (fun _ ↦ bodyReverts_nonPayable hwv)

end Benchmarks.Morpho.MetaMorphoV1_1
