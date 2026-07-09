import Benchmarks.OpenZeppelinBench.TimelockController.AbiDecode

/-!
# OpenZeppelin TimelockController `hashOperation` Solm body evaluation

The Solm body of `hashOperation` is `nonpayable ++ [.return [keccak256(abi.encode(...))]]`.  Under the
decoded store `tlcHashOpStore I`, the return expression `hashOperationExpr` evaluates to the
`bytes32` keccak of the canonical ABI encoding — the exact `ffi.KEC` of `tlcAbiEncHashOperationBytes`,
i.e. the same preimage the runtime encoder writes to `mem[0xa0..]` and hashes.

Template: `Benchmarks/Dss/Dai/Permit.lean` `evalExpr_permitDigest` (770-834) — but that uses
`abiEncodePacked`; here the outer node is `.abiEncodeCall "__abi_encode_hashOperation"` which routes
through `config.externalABI.encode? = timelockExternalABI.encode?
  = ABI.encodeReturnValues? [addr, uint256, bytesTy, bytes32, bytes32]` (see `Spec.lean:206`),
and that encode is exactly `tlcAbiEncHashOperation` (green, in `AbiEncode.lean`).
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1600000

namespace OpenZeppelinBench.TimelockController

/-- The canonical `hashOperation` preimage as a `ByteArray` (what the runtime hashes at `mem[0xa0]`
    and what the Solm `abi.encode` produces). -/
abbrev tlcHashOpCanonBytes (I : ExecutionEnv) : ByteArray :=
  ⟨(tlcAbiEncHashOperationBytes (tlcHashOpTarget I) (tlcHashOpValue I).toNat
    (tlcHashOpData I) (tlcHashOpPred I) (tlcHashOpSalt I)).toArray⟩

/-- The `bytes32` result of `hashOperation`: `keccak256` of the canonical ABI encoding. -/
abbrev tlcHashOpKecList (I : ExecutionEnv) : List UInt8 := (ffi.KEC (tlcHashOpCanonBytes I)).toList

/-- The Solm `hashOperation` body returns `keccak256(abi.encode(target,value,data,predecessor,salt))`.
    Requires a well-formed calldata so the decoded `predecessor`/`salt` are full 32-byte words and the
    `value` is in `uint256` range (all from `tlcHashOpWF`). -/
theorem tlcHashOperationBodyReturns {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hwf : tlcHashOpWF I) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ g A I) (tlcHashOpStore I)
      hashOperationTransition.body
      (.returned { contract := contract, locals := tlcHashOpStore I }
        (initState cA gh bl σ σ₀ g A I)
        (some [.fixedBytes bytes32Width (tlcHashOpKecList I)])) := by
  have hhead := hwf.head
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  -- Side conditions for `tlcAbiEncHashOperation`.
  have hi0 : 0 ≤ tlcHashOpValue I := by unfold tlcHashOpValue; exact Int.natCast_nonneg _
  have hi1 : tlcHashOpValue I < 2 ^ 256 := by
    have h : (calldataWord I.calldata 36).toNat < UInt256.size :=
      (calldataWord I.calldata 36).val.isLt
    have hsz : UInt256.size = 2 ^ 256 := by norm_num [UInt256.size]
    rw [hsz] at h; unfold tlcHashOpValue
    show ((calldataWord I.calldata 36).toNat : ℤ) < 2 ^ 256
    exact_mod_cast h
  have hp : (tlcHashOpPred I).length = 32 := by
    unfold tlcHashOpPred; rw [List.length_take, List.length_drop, htlen]; omega
  have hs : (tlcHashOpSalt I).length = 32 := by
    unfold tlcHashOpSalt; rw [List.length_take, List.length_drop, htlen]; omega
  -- Store lookups for the five decoded parameters.
  have gT : (tlcHashOpStore I).get? "target" = some (.address (tlcHashOpTarget I)) := by
    unfold tlcHashOpStore
    rw [store_get_ne4 ((∅ : Store).insert "target" (.address (tlcHashOpTarget I)))
      (.int (tlcHashOpValue I)) (.bytes (tlcHashOpData I))
      (.fixedBytes bytes32Width (tlcHashOpPred I)) (.fixedBytes bytes32Width (tlcHashOpSalt I))
      (by decide) (by decide) (by decide) (by decide)]
    simp
  have gV : (tlcHashOpStore I).get? "value" = some (.int (tlcHashOpValue I)) := by
    unfold tlcHashOpStore
    rw [store_get_ne3 (((∅ : Store).insert "target" (.address (tlcHashOpTarget I))).insert
        "value" (.int (tlcHashOpValue I)))
      (.bytes (tlcHashOpData I)) (.fixedBytes bytes32Width (tlcHashOpPred I))
      (.fixedBytes bytes32Width (tlcHashOpSalt I))
      (by decide) (by decide) (by decide)]
    simp
  have gD : (tlcHashOpStore I).get? "data" = some (.bytes (tlcHashOpData I)) := by
    unfold tlcHashOpStore
    rw [store_get_ne2 ((((∅ : Store).insert "target" (.address (tlcHashOpTarget I))).insert
        "value" (.int (tlcHashOpValue I))).insert "data" (.bytes (tlcHashOpData I)))
      (.fixedBytes bytes32Width (tlcHashOpPred I)) (.fixedBytes bytes32Width (tlcHashOpSalt I))
      (by decide) (by decide)]
    simp
  have gP : (tlcHashOpStore I).get? "predecessor"
      = some (.fixedBytes bytes32Width (tlcHashOpPred I)) := by
    unfold tlcHashOpStore
    rw [store_get_ne (((((∅ : Store).insert "target" (.address (tlcHashOpTarget I))).insert
        "value" (.int (tlcHashOpValue I))).insert "data" (.bytes (tlcHashOpData I))).insert
        "predecessor" (.fixedBytes bytes32Width (tlcHashOpPred I)))
      (.fixedBytes bytes32Width (tlcHashOpSalt I)) (by decide)]
    simp
  have gS : (tlcHashOpStore I).get? "salt"
      = some (.fixedBytes bytes32Width (tlcHashOpSalt I)) := by
    unfold tlcHashOpStore; simp
  -- The five `.var` expressions evaluate to the decoded values.
  have eT : evalExpr? config { contract := contract, locals := tlcHashOpStore I }
      (initState cA gh bl σ σ₀ g A I) (.var "target") = .ok (.address (tlcHashOpTarget I)) := by
    simp only [evalExpr?, gT, EvalResult.ofOption]
  have eV : evalExpr? config { contract := contract, locals := tlcHashOpStore I }
      (initState cA gh bl σ σ₀ g A I) (.var "value") = .ok (.int (tlcHashOpValue I)) := by
    simp only [evalExpr?, gV, EvalResult.ofOption]
  have eD : evalExpr? config { contract := contract, locals := tlcHashOpStore I }
      (initState cA gh bl σ σ₀ g A I) (.var "data") = .ok (.bytes (tlcHashOpData I)) := by
    simp only [evalExpr?, gD, EvalResult.ofOption]
  have eP : evalExpr? config { contract := contract, locals := tlcHashOpStore I }
      (initState cA gh bl σ σ₀ g A I) (.var "predecessor")
      = .ok (.fixedBytes bytes32Width (tlcHashOpPred I)) := by
    simp only [evalExpr?, gP, EvalResult.ofOption]
  have eS : evalExpr? config { contract := contract, locals := tlcHashOpStore I }
      (initState cA gh bl σ σ₀ g A I) (.var "salt")
      = .ok (.fixedBytes bytes32Width (tlcHashOpSalt I)) := by
    simp only [evalExpr?, gS, EvalResult.ofOption]
  -- The argument list evaluates to the five decoded values.
  have hlist : evalExprList? config { contract := contract, locals := tlcHashOpStore I }
      (initState cA gh bl σ σ₀ g A I)
      [.var "target", .var "value", .var "data", .var "predecessor", .var "salt"]
      = .ok [.address (tlcHashOpTarget I), .int (tlcHashOpValue I), .bytes (tlcHashOpData I),
          .fixedBytes bytes32Width (tlcHashOpPred I), .fixedBytes bytes32Width (tlcHashOpSalt I)] := by
    simp only [evalExprList?, eT, eV, eD, eP, eS, EvalResult.bind, bind, pure]
  -- The `abi.encode` call produces the canonical preimage bytes.
  have henc : config.externalABI.encode? "__abi_encode_hashOperation"
      [Value.address (tlcHashOpTarget I), .int (tlcHashOpValue I), .bytes (tlcHashOpData I),
        .fixedBytes bytes32Width (tlcHashOpPred I), .fixedBytes bytes32Width (tlcHashOpSalt I)]
      = some (tlcHashOpCanonBytes I) :=
    tlcAbiEncHashOperation (tlcHashOpTarget I) (tlcHashOpValue I) ⟨hi0, hi1⟩
      (tlcHashOpData I) (tlcHashOpPred I) (tlcHashOpSalt I) hp hs
  -- The `abi.encode` call evaluates to the canonical preimage bytes.
  have hcall : evalExpr? config { contract := contract, locals := tlcHashOpStore I }
      (initState cA gh bl σ σ₀ g A I)
      (.abiEncodeCall "__abi_encode_hashOperation"
        [.var "target", .var "value", .var "data", .var "predecessor", .var "salt"])
      = .ok (.bytes (tlcHashOpCanonBytes I)) := by
    rw [evalExpr?, hlist]
    simp only [EvalResult.bind, bind, pure]
    rw [henc]; rfl
  -- Assemble: keccak256 of the encoded preimage.
  refine nonpayableReturnExprBodyReturns (by simp only [initState]; exact hwv) ?_
  unfold hashOperationExpr
  rw [evalExpr?, hcall]; rfl

end OpenZeppelinBench.TimelockController
