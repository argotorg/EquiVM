import Benchmarks.Midnight.TakeGateABI
import Benchmarks.Midnight.BoolReplyAllocation
import Benchmarks.Midnight.RuntimeBlocks_051
import Benchmarks.Midnight.RuntimeBlocks_052
import Benchmarks.Midnight.RuntimeBlocks_053

variable {fork : Ethereum.Fork}

/-! Both entry gates reject failed calls and malformed Boolean replies. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight
open midnightBlocks

def TakeGateKind.resumePC : TakeGateKind → UInt256
  | .credit => ⟨14327⟩
  | .debt => ⟨14206⟩

def TakeGateKind.lengthPC : TakeGateKind → UInt256
  | .credit => ⟨14347⟩
  | .debt => ⟨14226⟩

def TakeGateKind.decodedPC : TakeGateKind → UInt256
  | .credit => ⟨14372⟩
  | .debt => ⟨14251⟩

set_option maxRecDepth 10000

theorem midnightTakeGateReturn {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw root : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (kind : TakeGateKind) (success : Bool)
    (hstack : R.length + 10 ≤ 1024) (hout : out.size < UInt256.size)
    (hroot : root.toNat + 32 < 2^64)
    (hword : 32 ≤ out.size →
      memLoad root (writeWord mem 64 (root + UInt256.ofNat 32)) = calldataWord out 0)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 kind.resumePC
      ((if success then ⟨1⟩ else ⟨0⟩) :: root :: R) mem aw out σ k C) :
    ((success = false ∨ ¬ (32 ≤ out.size ∧
        (calldataWord out 0 = ⟨0⟩ ∨ calldataWord out 0 = ⟨1⟩))) ∧
      RDrev fork midnightBytecode g s0) ∨
    (success = true ∧ 32 ≤ out.size ∧
      (calldataWord out 0 = ⟨0⟩ ∨ calldataWord out 0 = ⟨1⟩) ∧ ∃ aw' k' C',
      MemoryFunding credit (writeWord mem 64 (root + UInt256.ofNat 32)) aw' C' ∧
      RD fork midnightBytecode I g s0 kind.decodedPC (calldataWord out 0 :: R)
        (writeWord mem 64 (root + UInt256.ofNat 32)) aw' out σ k' C') := by
  have hn : (UInt256.ofNat out.size).toNat = out.size := UInt256.toNat_ofNat_of_lt hout
  cases success with
  | false =>
    have rd1 : RD fork midnightBytecode I g s0 ⟨13748⟩ (root :: ⟨0⟩ :: R)
        mem aw out σ (k + 5) (C + 22) := by
      cases kind with
      | credit =>
        exact midnight_block_14327_taken
          (by omega) (by decide) (by jump_dest) rd
      | debt =>
        exact midnight_block_14206_taken
          (by omega) (by decide) (by jump_dest) rd
    exact Or.inl ⟨Or.inl rfl, midnight_block_13748
      (by simp only [List.length_cons]; omega) (by rw [hn]; change 0 + _ ≤ _; omega) rd1⟩
  | true =>
    have rd2 : RD fork midnightBytecode I g s0 kind.lengthPC (root :: ⟨0⟩ :: R)
        mem aw out σ (k + 5 + 4) (C + 22 + 18) := by
      cases kind with
      | credit =>
        have rd1 := midnight_block_14327_fallthrough
          (by omega) (by decide) rd
        exact midnight_block_14334_taken
          (by omega) (by decide) (by jump_dest) rd1
      | debt =>
        have rd1 := midnight_block_14206_fallthrough
          (by omega) (by decide) rd
        exact midnight_block_14213_taken
          (by omega) (by decide) (by jump_dest) rd1
    by_cases hshort : out.size < 32
    · have hcond : UInt256.gt (UInt256.ofNat 32) (UInt256.ofNat out.size) ≠ ⟨0⟩ := by
        rw [ugt_one (by rw [hn]; exact hshort)]
        decide
      have rd3 : RD fork midnightBytecode I g s0 ⟨8404⟩
          (UInt256.ofNat 32 :: root :: kind.decodedPC :: R)
          mem aw out σ (k + 5 + 4 + 10) (C + 22 + 18 + 33) := by
        cases kind with
        | credit =>
          exact midnight_block_14347_taken
            (by omega) hcond (by jump_dest) rd2
        | debt =>
          exact midnight_block_14226_taken
            (by omega) hcond (by jump_dest) rd2
      exact Or.inl ⟨Or.inr (by omega), midnightBoolReplyShort hstack hshort hroot rd3⟩
    · have h32 : 32 ≤ out.size := by omega
      have hcond := ugt_zero (a := UInt256.ofNat 32) (b := UInt256.ofNat out.size)
        (by rw [hn]; exact h32)
      have rd4 : RD fork midnightBytecode I g s0 ⟨18444⟩
          (root :: UInt256.ofNat 32 :: UInt256.ofNat 8390 :: UInt256.ofNat 32 ::
            root :: kind.decodedPC :: R)
          mem aw out σ (k + 5 + 4 + 10 + 5) (C + 22 + 18 + 33 + 20) := by
        cases kind with
        | credit =>
          have rd3 := midnight_block_14347_fallthrough
            (by omega) hcond rd2
          exact midnight_block_14363
            (by simp only [List.length_cons]; omega) (by jump_dest) rd3
        | debt =>
          have rd3 := midnight_block_14226_fallthrough
            (by omega) hcond rd2
          exact midnight_block_14242
            (by simp only [List.length_cons]; omega) (by jump_dest) rd3
      rcases midnightBoolReplyFull hstack hroot (by cases kind <;> native_decide)
          (hword h32) (ha.mono (by omega)) rd4 with
        ⟨hbad, hrev⟩ | ⟨hc, aw5, k5, C5, ha5, rd5⟩
      · exact Or.inl ⟨Or.inr (fun h ↦ hbad h.2), hrev⟩
      · exact Or.inr ⟨rfl, h32, hc, aw5, k5, C5, ha5, rd5⟩

end Benchmarks.Midnight
