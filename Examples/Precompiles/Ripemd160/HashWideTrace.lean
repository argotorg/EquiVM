import Examples.Precompiles.Ripemd160.HashWideRun
import Examples.Precompiles.Ripemd160.HashRun
import Reasoning.Bytecode

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Ripemd160

/-- Execution environments supported by the successful RIPEMD-160 bytecode theorem. -/
def ripemd160Accepts (I : ExecutionEnv) : Prop :=
  I.weiValue = ⟨0⟩ ∧ I.calldata.size < UInt256.size ∧
    I.calldata.size ≤ maxFallbackCalldataSize

def ripemd160GasCost (I : ExecutionEnv) : Nat :=
  let blocks := Model.paddedLength I.calldata.size / 64
  let initial := runtimeInitialHashState I
  let final := runtimeHashRun I blocks initial
  ripemd160SetupGas I + ripemd160BlocksGas I blocks initial
    + ripemd160FinishGas final.cursor.aw

/-- The deployed bytecode trace returns the mathematical RIPEMD-160 raw word and retains the exact
    cumulative gas consumed by the successful execution. -/
theorem ripemd160X_successExactGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = ripemd160RuntimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    RDxRet ripemd160RuntimeBytecode g
      (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (Model.rawOutput I.calldata) (ripemd160GasCost I) := by
  obtain ⟨k0, rd0⟩ := ripemd160X_reachBlockLoopGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hcode hwv hsize hsmall
  let blocks := Model.paddedLength I.calldata.size / 64
  have rdInitial : RDx ripemd160RuntimeBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1028⟩
      (hashBlockLoopStack I ⟨0⟩ (runtimeInitialHashState I).chain)
      (runtimeInitialHashState I).cursor.mem
      (runtimeInitialHashState I).cursor.aw ByteArray.empty (cA, σ) k0
        (ripemd160SetupGas I) := by
    simpa [runtimeInitialHashState, runtimeInitialChain, hashBlockLoopStack] using rd0
  obtain ⟨k1, rd1, _⟩ := ripemd160X_blocks_wideGas (blocks := blocks)
    (le_refl blocks) (RuntimePaddedCursor.initial I hsmall) hsmall rdInitial
  have hcount := hashBlockCountWord_toNat I hsmall
  have hblocksUint : blocks < UInt256.size := by
    have hp := (hashPaddedLength_bounds I.calldata.size).2
    rw [show UInt256.size = 2 ^ 256 from by decide]
    unfold blocks maxFallbackCalldataSize at *
    omega
  have hword : UInt256.ofNat blocks = hashBlockCountWord I := by
    apply u256_inj
    rw [ulit_toNat' blocks hblocksUint, hcount]
  have hdone : UInt256.lt (UInt256.ofNat blocks) (hashBlockCountWord I) = ⟨0⟩ := by
    rw [hword]
    exact ult_zero (le_refl _)
  have rdret := ripemd160X_finishGas hdone rd1
  rw [runtimeHashRun_final_digest I hsmall] at rdret
  simpa [ripemd160GasCost, blocks, Nat.add_assoc] using rdret

/-- Strong bytecode-only theorem: `ripemd160GasCost` is both the exact successful charge and the
precise OOG threshold. -/
theorem ripemd160BytecodeExactGas :
    ExactGasSpec ripemd160RuntimeBytecode
      (fun ctx => ripemd160Accepts ctx.executionEnv)
      (fun ctx => Model.rawOutput ctx.executionEnv.calldata)
      (fun ctx => ripemd160GasCost ctx.executionEnv) := by
  apply ExactGasSpec.ofRDxRet
  intro ctx hcode haccepts
  exact ripemd160X_successExactGas
    (cA := ctx.createdAccounts) (gh := ctx.genesisBlockHeader) (bl := ctx.blocks)
    (σ := ctx.accountMap) (σ₀ := ctx.originalAccountMap) (A := ctx.substate)
    (I := ctx.executionEnv) (g := ctx.gas)
    hcode haccepts.1 haccepts.2.1 haccepts.2.2

/-- Exact public `Ξ` result, with the two gas regions stated separately. -/
theorem ripemd160Xi_exactGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = ripemd160RuntimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    (g.toNat < ripemd160GasCost I →
      Ξ cA gh bl σ σ₀ g.toUInt256 A I = .error .OutOfGass) ∧
    (ripemd160GasCost I ≤ g.toNat → ∃ A' : Substate,
      Ξ cA gh bl σ σ₀ g.toUInt256 A I =
        .ok (.success
          (cA, σ, (g.subNat (ripemd160GasCost I)).toUInt256, A')
          (Model.rawOutput I.calldata))) :=
  (ripemd160X_successExactGas hcode hwv hsize hsmall).xiResult hcode

/-- OOG occurs exactly when the supplied gas is below the bytecode-specific exact cost. -/
theorem ripemd160Xi_oog_iff {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = ripemd160RuntimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    Ξ cA gh bl σ σ₀ g.toUInt256 A I = .error .OutOfGass ↔
      g.toNat < ripemd160GasCost I :=
  (ripemd160X_successExactGas hcode hwv hsize hsmall).xiOOG_iff hcode

/-- Functional projection of `ripemd160X_successExactGas`. -/
theorem ripemd160X_success {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = ripemd160RuntimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    RDret ripemd160RuntimeBytecode g
      (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (Model.rawOutput I.calldata) := by
  exact (ripemd160X_successExactGas hcode hwv hsize hsmall).toRDret

end Ripemd160
