import Benchmarks.Midnight.TickLibWrapper.Common
import Benchmarks.Midnight.TickLibWrapper.CreationBlocks_001

/-!
# TickLibWrapper constructor correctness

Creation-code equivalence: the constructor's EVM trace (callvalue guard, runtime-code copy,
`RETURN`) against the Stele constructor body, composed from the creation summaries.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight.TickLibWrapper

set_option maxRecDepth 2000000

/-- The success trace: `PUSH1 0x80; …; MSTORE; CALLVALUE=0; PUSH2 728; …; CODECOPY; RETURN`. -/
theorem tickLibWrapperCtorRetRun {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = tickLibWrapperCreationBytecode) (hwv : I.weiValue = ⟨0⟩) :
    RDret tickLibWrapperCreationBytecode g (initState σ σ₀ g A I) σ
      tickLibWrapperBytecode := by
  have rd0 : RD (tickLibWrapperCreationBytecode ++ ByteArray.empty) I g
      (initState σ σ₀ g A I) (UInt256.ofNat 0) [] ByteArray.empty (UInt256.ofNat 0)
      ByteArray.empty σ 0 0 := by
    rw [ByteArray.append_empty]
    exact RD.initState (g := g) (σ := σ) (σ₀ := σ₀) (A := A) hcode
  have rd1 := tickLibWrapperCreationBlocks.tickLibWrapperCreation_block_0_fallthrough
    (by simp) hwv rd0
  have rd2 := tickLibWrapperCreationBlocks.tickLibWrapperCreation_block_10 (by simp) rd1
  simp only [tickLibWrapperCreationBlocks.tickLibWrapperCreation_block_0_fallthrough_memory,
    ByteArray.append_empty] at rd2
  rw [show (UInt256.ofNat 128 : UInt256).toNat = 128 from by decide,
    show (UInt256.ofNat 728 : UInt256).toNat = 728 from by decide,
    show (UInt256.ofNat 26 : UInt256).toNat = 26 from by decide] at rd2
  rw [show ((tickLibWrapperCreationBytecode).write 26
      ((UInt256.ofNat 128).toByteArray.write 0 ByteArray.empty (UInt256.ofNat 64).toNat 32)
        128 728).readWithPadding 128 728 = tickLibWrapperBytecode from by native_decide] at rd2
  exact rd2

/-- The revert trace: nonzero callvalue jumps into the `PUSH0; DUP1; REVERT` tail at 21. -/
theorem tickLibWrapperCtorRevRun {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = tickLibWrapperCreationBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev tickLibWrapperCreationBytecode g (initState σ σ₀ g A I) := by
  have rd0 : RD (tickLibWrapperCreationBytecode ++ ByteArray.empty) I g
      (initState σ σ₀ g A I) (UInt256.ofNat 0) [] ByteArray.empty (UInt256.ofNat 0)
      ByteArray.empty σ 0 0 := by
    rw [ByteArray.append_empty]
    exact RD.initState (g := g) (σ := σ) (σ₀ := σ₀) (A := A) hcode
  have rd1 := tickLibWrapperCreationBlocks.tickLibWrapperCreation_block_0_taken
    (by simp) hwv (by jump_dest) rd0
  have rd2 := tickLibWrapperCreationBlocks.tickLibWrapperCreation_block_21
    (by simp [tickLibWrapperCreationBlocks.tickLibWrapperCreation_block_0_taken_stack]) rd1
  rwa [ByteArray.append_empty] at rd2

/-- The Stele ctor body `[require (callvalue == 0)]` returns `none` at zero callvalue. -/
theorem tickLibWrapperCtorBodyOk {σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅
      contract.ctor.body
      (.returned { contract := contract, locals := (∅ : Store) }
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) .none) := by
  show ExecTransitionBody config contract _ ∅
    [.require (.binary .eq (.env .callvalue) (.intLit 0))] _
  exact ExecFuncBody.execBlockOK
    ((ABlock.start.requireStep
      (evalCallvalueEq_true (by simp only [initState]; exact hwv))).run ExecBlock.nil)

theorem tickLibWrapperConstructorCorrect :
    typedConstructorRefinement config tickLibWrapperCreationBytecode contract
      (fun _ => tickLibWrapperBytecode) := by
  intro σ σ₀ g A I args deployedInitcode hdeploy hcode _hcd _hperm
  have hdeployed := emptyCtorDeployment_eq_initcode rfl rfl hdeploy
  have hargs : args = [] :=
    List.eq_nil_iff_length_eq_zero.mpr
      (emptyCtorDeployment_args_length (cfg := config) (contract := contract) rfl rfl hdeploy)
  subst hargs
  rw [hdeployed] at hcode
  by_cases hwv : I.weiValue = ⟨0⟩
  · exact (tickLibWrapperCtorRetRun (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) hcode hwv)
      |>.constructorRefinementEmptyParams hcode rfl (tickLibWrapperCtorBodyOk hwv) rfl
  · exact (tickLibWrapperCtorRevRun (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) hcode hwv)
      |>.constructorRefinementEmptyParams hcode rfl
      (by show ExecTransitionBody config contract _ ∅
            [.require (.binary .eq (.env .callvalue) (.intLit 0))] .reverted
          exact bodyReverts_nonPayable (by simp only [initState]; exact hwv))

end Benchmarks.Midnight.TickLibWrapper
