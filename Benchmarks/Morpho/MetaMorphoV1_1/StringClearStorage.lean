import Benchmarks.Morpho.MetaMorphoV1_1.StringClearStart

/-! Old metadata data words are cleared exactly when the source storage backend clears them. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

def stringOldLengthPC (symbol : Bool) : UInt256 := if symbol then ⟨3051⟩ else ⟨2289⟩

def stringShrinkCheckPC (symbol : Bool) : UInt256 := if symbol then ⟨3336⟩ else ⟨2580⟩

def stringClearedAccounts (owner : AccountAddress) (σ : AccountMap) (symbol : Bool)
    (old len : Nat) : AccountMap :=
  if old < 32 then σ else
    clearDataWordsForwardFrom owner σ (solidityBytesDataBaseSlot (stringViewSlot symbol))
      (UInt256.ofNat (stringFirstClearedWord len))
      (solidityBytesDataWordCount old - stringFirstClearedWord len)

theorem stringClearDispatch {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {old len : UInt256} {R : List UInt256} (v : MetaMorphoV1_1Immutables)
    (symbol : Bool) (hstack : R.length + 4 ≤ 1024)
    (rd : RD (deployedRuntime v) I g s0 (stringOldLengthPC symbol)
      (old :: len :: R) mem aw out σ k C) :
    ((old.toNat < 32 ∨ old.toNat ≤ len.toNat) ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 (stringSetStoreSelectPC symbol)
        (old :: len :: R) mem aw' out σ k' C') ∨
    (32 ≤ old.toNat ∧ len.toNat < old.toNat ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 (stringClearStartPC symbol)
        (old :: len :: R) mem aw' out σ k' C') := by
  by_cases hs : old.toNat < 32
  · refine .inl ⟨.inl hs, ?_⟩
    have hc : UInt256.gt old (UInt256.ofNat 31) = UInt256.ofNat 0 :=
      ult_zero (by change old.toNat ≤ 31; omega)
    cases symbol with
    | false =>
        exact metaMorphoV1_1_block_2289_fallthrough_packed
          (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) hc rd
    | true =>
        exact metaMorphoV1_1_block_3051_fallthrough_packed
          (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) hc rd
  · have hc : UInt256.gt old (UInt256.ofNat 31) ≠ UInt256.ofNat 0 := by
      rw [show UInt256.gt old (UInt256.ofNat 31) = ⟨1⟩ from
        ult_one (by change 31 < old.toNat; omega)]
      decide
    have hnext : ∃ aw' k' C', RD (deployedRuntime v) I g s0 (stringShrinkCheckPC symbol)
        (old :: len :: R) mem aw' out σ k' C' := by
      cases symbol with
      | false =>
          exact metaMorphoV1_1_block_2289_taken_packed (immWords := wordsOf (immStore v))
            (by simp only [List.length_cons]; omega) hc
            (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
      | true =>
          exact metaMorphoV1_1_block_3051_taken_packed (immWords := wordsOf (immStore v))
            (by simp only [List.length_cons]; omega) hc
            (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    obtain ⟨aw1, k1, C1, h1⟩ := hnext
    by_cases hg : old.toNat ≤ len.toNat
    · refine .inl ⟨.inr hg, ?_⟩
      have hcond : UInt256.isZero (UInt256.gt old len) ≠ UInt256.ofNat 0 := by
        change UInt256.isZero (UInt256.lt len old) ≠ ⟨0⟩
        rw [ult_zero hg]; decide
      cases symbol with
      | false =>
          exact metaMorphoV1_1_block_2580_taken_packed (immWords := wordsOf (immStore v))
            hstack hcond (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
      | true =>
          exact metaMorphoV1_1_block_3336_taken_packed (immWords := wordsOf (immStore v))
            hstack hcond (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
    · refine .inr ⟨by omega, by omega, ?_⟩
      have hcond : UInt256.isZero (UInt256.gt old len) = UInt256.ofNat 0 := by
        change UInt256.isZero (UInt256.lt len old) = ⟨0⟩
        rw [ult_one (by omega)]; decide
      cases symbol with
      | false =>
          exact metaMorphoV1_1_block_2580_fallthrough_packed
            (immWords := wordsOf (immStore v)) hstack hcond h1
      | true =>
          exact metaMorphoV1_1_block_3336_fallthrough_packed
            (immWords := wordsOf (immStore v)) hstack hcond h1

theorem stringClearLoopStatic {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {i start count : UInt256} {R : List UInt256} (v : MetaMorphoV1_1Immutables)
    (symbol : Bool) (hstack : R.length + 6 ≤ 1024) (hperm : I.perm = false)
    (hcond : UInt256.lt i count ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 (stringClearLoopPC symbol)
      (i :: start :: count :: R) mem aw out σ k C) :
    RDstatic (deployedRuntime v) g s0 := by
  cases symbol with
  | false =>
      obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_2621_taken_packed
        (immWords := wordsOf (immStore v)) (by omega) hcond
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
      exact stringClearBodyStatic v false hstack hperm h1
  | true =>
      obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_3377_taken_packed
        (immWords := wordsOf (immStore v)) (by omega) hcond
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
      exact stringClearBodyStatic v true hstack hperm h1

theorem stringClearRun {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (v : MetaMorphoV1_1Immutables) (symbol : Bool) (start count : Nat)
    (hstack : R.length + 6 ≤ 1024) (hcount : count < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 (stringClearLoopPC symbol)
      (⟨0⟩ :: UInt256.ofNat start :: UInt256.ofNat count :: R) mem aw out σ k C) :
    (I.perm = false ∧ RDstatic (deployedRuntime v) g s0) ∨
    (∃ aw' k' C', RD (deployedRuntime v) I g s0 (stringSetStoreSelectPC symbol)
      (UInt256.ofNat count :: R) mem aw' out
      (clearDataWordsForwardFrom I.codeOwner σ (solidityBytesDataBaseSlot (stringViewSlot symbol))
        (UInt256.ofNat start) count) k' C') := by
  by_cases hz : count = 0
  · subst count
    exact .inr (stringClearLoopExit v symbol (by omega) (by decide) rd)
  · cases hp : I.perm with
    | false =>
        refine .inl ⟨rfl, stringClearLoopStatic v symbol hstack hp ?_ rd⟩
        rw [ult_one (by rw [UInt256.toNat_ofNat_of_lt hcount]; change 0 < count; omega)]
        decide
    | true => exact .inr (stringClearWords v symbol start count hstack hp hcount rd)

theorem stringClearStorage {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {old len : UInt256} {R : List UInt256} (v : MetaMorphoV1_1Immutables)
    (symbol : Bool) (hstack : R.length + 7 ≤ 1024)
    (hold : old.toNat < 2 ^ 255) (hsmall : len.toNat < 2 ^ 255)
    (rd : RD (deployedRuntime v) I g s0 (stringOldLengthPC symbol)
      (old :: len :: R) mem aw out σ k C) :
    (I.perm = false ∧ RDstatic (deployedRuntime v) g s0) ∨
    (∃ mem' junk aw' k' C', (mem' = mem ∨ mem' = stringStorageScratch mem symbol) ∧
      RD (deployedRuntime v) I g s0 (stringSetStoreSelectPC symbol)
        (junk :: len :: R) mem' aw' out
        (stringClearedAccounts I.codeOwner σ symbol old.toNat len.toNat) k' C') := by
  rcases stringClearDispatch v symbol (by omega) rd with
    ⟨hskip, aw1, k1, C1, h1⟩ | ⟨hlong, hshrink, aw1, k1, C1, h1⟩
  · have ha : stringClearedAccounts I.codeOwner σ symbol old.toNat len.toNat = σ := by
      unfold stringClearedAccounts
      split
      · rfl
      · have hle : old.toNat ≤ len.toNat := hskip.resolve_left ‹_›
        have hn : ¬ len.toNat < 32 := by omega
        simp only [stringFirstClearedWord, if_neg hn]
        have hc : solidityBytesDataWordCount old.toNat - solidityBytesDataWordCount len.toNat =
            0 := by unfold solidityBytesDataWordCount; omega
        rw [hc]; rfl
    exact .inr ⟨mem, old, aw1, k1, C1, .inl rfl, by rw [ha]; exact h1⟩
  · obtain ⟨aw2, k2, C2, h2⟩ := stringClearInit v symbol (by omega) hold hsmall
      (by omega) h1
    rcases stringClearRun v symbol (stringFirstClearedWord len.toNat)
      (solidityBytesDataWordCount old.toNat - stringFirstClearedWord len.toNat)
      (by simp only [List.length_cons]; omega) (by
        unfold solidityBytesDataWordCount
        change _ < 2 ^ 256
        omega) h2 with hstatic | ⟨aw3, k3, C3, h3⟩
    · exact .inl hstatic
    · refine .inr ⟨_, UInt256.ofNat
        (solidityBytesDataWordCount old.toNat - stringFirstClearedWord len.toNat),
        aw3, k3, C3, .inr rfl, ?_⟩
      simpa only [stringClearedAccounts, if_neg (show ¬ old.toNat < 32 by omega)] using h3

end Benchmarks.Morpho.MetaMorphoV1_1
