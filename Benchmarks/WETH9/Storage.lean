import Benchmarks.WETH9.Routines

/-!
# WETH9 shared storage helpers for mutating functions

Reusable source-level facts for the caller-keyed `balanceOf` mapping and the wrapping (`unchecked`)
uint256 store that WETH9's `deposit`/`withdraw`/`transferFrom` perform.  The two `wordOfInt` lemmas
are general library candidates (`Reasoning.Storage`).
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.WETH9

/-- `wordOfInt (Int.ofNat m) = ofNat m` — a nonneg int cast is the natural-value word.
    LIBRARY CANDIDATE: `Reasoning.Memory` (generalizes `wordOfInt_ofNat_toNat`). -/
theorem wordOfInt_ofNat_toNat_gen (m : ℕ) : EVM.wordOfInt (Int.ofNat m) = UInt256.ofNat m := by
  unfold EVM.wordOfInt; rw [if_neg (by simp)]; rfl

/-- `wordOfInt (a + b) = a ⊕ b` (the wrapping `+=` truncation on store). -/
theorem wordOfInt_add_words (a b : UInt256) :
    EVM.wordOfInt (Int.ofNat a.toNat + Int.ofNat b.toNat) = UInt256.add a b := by
  have hcast : (Int.ofNat a.toNat + Int.ofNat b.toNat) = Int.ofNat (a.toNat + b.toNat) := rfl
  rw [hcast, wordOfInt_ofNat_toNat_gen]
  apply u256_inj
  change (UInt256.ofNat (a.toNat + b.toNat)).toNat = (a + b).toNat
  rw [uadd_toNat]; rfl

/-- General uint256 scalar store: truncates the stored `Int` to a word via `wordOfInt`.
    LIBRARY CANDIDATE: `Reasoning.Storage` (generalizes `storageLocStore_uint256`). -/
theorem storageLocStore_uint256_int (evm : EVM.State) (slot : UInt256) (n : Int) :
    storageLocStore evm (uint256Loc slot) (.int n) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot (EVM.wordOfInt n)) := by
  unfold storageLocStore storageLocWriteWord uint256Loc
  simp only [valueToWord, bind, Option.bind, pure]
  have hslen := (EVM.Word.toBytesLEWithSizeProof
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2
  have hvlen := (EVM.Word.toBytesLEWithSizeProof (EVM.wordOfInt n)).2
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (0 : Fin 32).val _ ++ List.take (32 : Fin 33).val _
        ++ List.drop ((0 : Fin 32).val + (32 : Fin 33).val) _) = (EVM.wordOfInt n).toNat
  rw [show (0 : Fin 32).val = 0 from rfl, show (32 : Fin 33).val = 32 from rfl,
    List.take_zero, List.nil_append, List.drop_eq_nil_of_le (by rw [hslen]),
    List.append_nil, List.take_of_length_le (by rw [hvlen]), fromBytes'_toBytesLEWithSizeProof]

/-! ## Caller-keyed `balanceOf[msg.sender]` -/

/-- The evaluated storage ref for `balanceOf[msg.sender]`. -/
abbrev callerBalRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "balanceOf", steps := [.mindex (.address I.source)] }

/-- The `balanceOf[msg.sender]` slot. -/
def callerBalSlot (I : ExecutionEnv) : UInt256 := balanceOfSlot (.address I.source)

/-- Reading `balanceOf[msg.sender]` in the source semantics. -/
theorem evalCallerBal (evm : EVM.State) (I : ExecutionEnv) (locals : Store)
    (hsrc : evm.executionEnv = I) (hbase : locals.get? "balanceOf" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage (balanceOfRef sender)) =
      .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (callerBalSlot I)).toNat)) := by
  refine evalExpr_storage_scalar_value
    (cfg := config) (solm := { contract := contract, locals := locals })
    (slot := balanceOfRef sender) (er := callerBalRef I) (t := .int uint256Int)
    (loc := wordLoc (callerBalSlot I))
    (value := .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
      (callerBalSlot I)).toNat))
    (hbase := by simpa [balanceOfRef] using hbase) ?_ ?_ (by rfl) ?_
  · simp only [balanceOfRef, sender, evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
      evalExpr?, envValue, hsrc, valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure]
  · simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St]
  · simpa [wordLoc, uint256Loc, uint256Int, callerBalSlot] using
      storageLocLoad_uint256 evm (callerBalSlot I)

end Benchmarks.WETH9
