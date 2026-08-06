import Examples.Precompiles.Blake2f.Fallback.Setup

/-!
# BLAKE2F fallback invalid-input traces

Invalid calldata length and invalid final-flag traces are kept separate from the successful return
path so they do not rebuild when return-loop proofs change.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-! ## Explicit EIP-152 validation failure sink -/

/-- Exact terminal rule for the local source's explicit EIP-152 validation failure target.

The patched source uses `invalid()` for invalid length and invalid final-flag checks.  The compiler
shares those checks at PC `310` (`JUMPDEST`) followed by PC `311` (`INVALID`).  This lemma packages
that sink independently of the stack and memory shape used to reach it. -/
theorem invalidValidationSink {cA gh bl σ σ₀ A I} {g : Sat256}
    {stk : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {k C : Nat}
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨310⟩ stk mem aw rdata (cA, σ) k C)
    (hov : stk.length ≤ 1024) :
    ∃ errorThreshold,
      RDxErr runtimeBytecode g (initState cA gh bl σ σ₀ g A I)
        .InvalidInstruction errorThreshold := by
  have rd311 := evm_run h with [
    raw jumpdest (by decide) hov ]
  exact ⟨C + 1, RDx.invalid rd311 (by decide)⟩

/-- Invalid calldata length reaches the explicit validation `INVALID` before allocating
`msg.data`.

This is the first closed branch of the BLAKE2F precompile-style bytecode proof.  It relies on the
fallback guard added in the local source; the older wrapper allocated `msg.data` first, which made
large invalid lengths route through compiler `REVERT` paths instead. -/
theorem invalidLengthTrace {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size)
    (hlen : I.calldata.size ≠ 213) :
    ∃ errorThreshold,
      RDxErr runtimeBytecode g (initState cA gh bl σ σ₀ g A I)
        .InvalidInstruction errorThreshold := by
  obtain ⟨k0, rd10⟩ := zeroValuePrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv
  have hcond : UInt256.sub (calldataSizeWord I) ⟨213⟩ ≠ ⟨0⟩ :=
    lengthGuardSub_ne_zero hsize hlen
  have rd310 := evm_run rd10 with [
    push1 ⟨213⟩,
    calldatasize,
    sub,
    push2 ⟨310⟩,
    jumpiT hcond (by jump_dest) ]
  obtain ⟨threshold, herr⟩ := invalidValidationSink rd310 (by simp)
  exact ⟨threshold, herr⟩

/-- Final-flag guard trace, stated against the exact bytecode-decoded flag word.

The remaining model-facing bridge is to show that this `finalFlagWord` is the same byte as
`Model.validFinalFlag`'s `input[212]!` under the length-213 assumption. -/
theorem invalidFinalFlagTraceRaw {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hflag : UInt256.gt (finalFlagWord I) ⟨1⟩ ≠ ⟨0⟩) :
    ∃ errorThreshold,
      RDxErr runtimeBytecode g (initState cA gh bl σ σ₀ g A I)
        .InvalidInstruction errorThreshold := by
  obtain ⟨k0, rd10⟩ := zeroValuePrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv
  have hlenOk : UInt256.sub (calldataSizeWord I) ⟨213⟩ = ⟨0⟩ :=
    lengthGuardSub_zero hlen
  have rd310 := evm_run rd10 with [
    push1 ⟨213⟩,
    calldatasize,
    sub,
    push2 ⟨310⟩,
    jumpiNT hlenOk,
    push1 ⟨1⟩,
    push1 ⟨212⟩,
    calldataload,
    push0,
    byte,
    gt,
    push2 ⟨310⟩,
    jumpiT hflag (by jump_dest) ]
  obtain ⟨threshold, herr⟩ := invalidValidationSink rd310 (by simp)
  exact ⟨threshold, herr⟩

end Blake2f
