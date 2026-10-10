import Benchmarks.Morpho.MetaMorphoV1_1.Dispatch
import Benchmarks.Morpho.MetaMorphoV1_1.PermitEntry
import Benchmarks.Morpho.MetaMorphoV1_1.PermitNonceStatic
import Benchmarks.Morpho.MetaMorphoV1_1.PermitBodySimulation

/-!
# MetaMorphoV1_1 `permit(address,address,uint256,uint256,uint8,bytes32,bytes32)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 1586; reach lemma `metaMorphoV1_1ReachPermitBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

/-- `permit(address,address,uint256,uint256,uint8,bytes32,bytes32)`: the theorem `Correct.lean` routes selector 65 to. -/
theorem metaMorphoV1_1PermitBody {σ σ₀ A I} {g : UInt256} (v : MetaMorphoV1_1Immutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (metaMorphoV1_1SelBytes 65)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (metaMorphoV1_1SelBytes 65) rfl hsel
  have hd : dispatchMsg contract I.calldata = some permitTransition := by
    apply metaMorphoV1_1Dispatch_permit <;>
      first | exact hsel | exact selectorMismatch hsel (by decide +kernel)
  obtain ⟨k, C, rd⟩ := metaMorphoV1_1ReachPermitBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  case neg =>
    exact dispatchedRevert hcode hd (permitRevertNonPayable v (by simp) hwv rd)
      (fun _ ↦ bodyReverts_nonPayable hwv)
  by_cases hlen : 228 ≤ I.calldata.size
  case neg =>
    have hrev := permitRevertLength v (by simp) hwv (by
      change UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size)
        (UInt256.ofNat (32 * 7)) ≠ ⟨0⟩
      rw [calldataNot3_eq_sub hsz hsize,
        solcCalldataStaticLenCheckShort (words := 7) hsz (by omega) hsize (by decide)]
      decide) rd
    exact hrev.reEquivDecodingFailed hcode hd (permitDecodeShort (by omega))
  by_cases hhi : I.calldata.size < 2 ^ 255 + 4
  case neg =>
    have hrev := permitRevertLength v (by simp) hwv (by
      change UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size)
        (UInt256.ofNat (32 * 7)) ≠ ⟨0⟩
      rw [calldataNot3_eq_sub hsz hsize,
        solcCalldataStaticLenCheckHuge (words := 7) (Nat.le_of_not_gt hhi) hsize (by decide)]
      decide) rd
    exact hrev.reEquivDecodingFailed hcode hd (permitDecodeHuge (Nat.le_of_not_gt hhi))
  obtain ⟨k1, C1, r1⟩ := permitReachDecoder v (by simp) hwv hlen hhi hsize rd
  rcases permitDecodeRuntime v (by simp) r1 with ⟨hbad, hrev⟩ | ⟨hc, k2, C2, r2⟩
  · exact hrev.reEquivDecodingFailed hcode hd (by
      change decodeCalldata permitNames permitTypes I.calldata = none
      rw [permitDecodeLong hlen hhi, if_neg hbad])
  · let p := permitCalldataData I.calldata
    let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
    have hdec : decodeCalldata permitNames permitTypes I.calldata = some p.locals := by
      rw [permitDecodeLong hlen hhi, if_pos hc]
    by_cases htime : (UInt256.ofNat I.header.timestamp).toNat ≤ p.deadline.toNat
    · obtain ⟨k3, C3, r3⟩ := permitDeadlinePass v (by simp) htime r2
      by_cases hperm : I.perm = true
      · rcases permitBodySimulation (evm := evm) p v 128 (by simp) hperm (by decide)
          (by decide) (by rw [solcFreePtrMem_size]) solcFreePtrMem_mload64
          hc.2.2 rfl rfl SourceState.init r3 with
          ⟨hbody, hrev⟩ | ⟨state, frame, hbody, hret⟩
        · exact hrev.reEquivExecutionRevert hcode hd hdec
            (ExecFuncBody.execBlockRevert ((permitPublicPrefix p evm v hwv hhi htime).run hbody))
        · exact hret.reEquivExecutionGen hcode hd hdec
            (ExecFuncBody.execBlockOK ((permitPublicPrefix p evm v hwv hhi htime).run hbody))
            rfl voidReturnEquiv
      · have hp : I.perm = false := Bool.eq_false_of_not_eq_true hperm
        exact (permitNonceStatic v (by simp) hp r3).reEquivStaticHalt hcode hd hdec
          (permitPublicStatic p evm v hwv hhi htime hp)
    · exact (permitDeadlineFail v (by simp) htime r2).reEquivExecutionRevert hcode hd hdec
        (permitDeadlineReverts p evm v hwv hhi htime)

end Benchmarks.Morpho.MetaMorphoV1_1
