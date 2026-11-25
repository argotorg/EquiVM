import Benchmarks.Midnight.TakeGateMemory
import Benchmarks.Midnight.TakeGateReturn
import Benchmarks.Midnight.AddressDecode

variable {fork : Ethereum.Fork}

/-! Preparing the fixed calldata buffer for either entry gate. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight
open midnightBlocks

def TakeGateKind.preparePC : TakeGateKind → UInt256
  | .credit => ⟨14281⟩
  | .debt => ⟨14160⟩

def TakeGateKind.callPC : TakeGateKind → UInt256
  | .credit => ⟨14326⟩
  | .debt => ⟨14205⟩

def TakeGateKind.userOffset : TakeGateKind → UInt256
  | .credit => ⟨576⟩
  | .debt => ⟨448⟩

set_option maxRecDepth 10000

theorem midnightTakeGatePrepare {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw root gate flag : UInt256} {user : AccountAddress}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (kind : TakeGateKind)
    (hstack : R.length + 10 ≤ 1024) (hroot : root.toNat + 36 < 2^64)
    (hlower : 608 ≤ root.toNat) (hm : 608 ≤ mem.size)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (huser : memLoad kind.userOffset mem = UInt256.ofNat user.val)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 kind.preparePC (gate :: flag :: R)
      mem aw rdata σ k C) :
    ∃ gas aw' k' C', MemoryFunding credit (takeGateCallMemory kind mem root user) aw' C' ∧
      RD fork midnightBytecode I g s0 kind.callPC
        (gas :: gate :: root :: UInt256.ofNat 36 :: root :: UInt256.ofNat 32 :: root :: R)
        (takeGateCallMemory kind mem root user) aw' rdata σ k' C' := by
  have hoff : kind.userOffset.toNat ≤ 576 := by cases kind <;> decide
  have hu : memLoad kind.userOffset (writeWord mem root.toNat kind.selectorWord) =
      UInt256.ofNat user.val := by
    rw [memLoad_writeWord_preserved _ _ _ _ (by omega) (Or.inl (by omega)), huser]
  have hclean : UInt256.land solcAddrMask (UInt256.ofNat user.val) =
      UInt256.ofNat user.val := by
    rw [u256_land_comm]
    exact addressWord_val_clean user
  have hadd := uadd_word_ofNat_toNat root 4 (by change _ < 2^256; omega)
  cases kind with
  | credit =>
    have rd1 := midnight_block_14281 (by omega) rd
    have ha1 := memoryFundingAt (credit := credit) rd1 (by
      unfold midnight_block_14281_memory
      memory_fund ha)
    have hsel : UInt256.shiftLeft (UInt256.ofNat 743854031) (UInt256.ofNat 225) =
        TakeGateKind.credit.selectorWord := by decide +kernel
    have hmem : midnight_block_14281_memory (mem := mem) =
        takeGateCallMemory .credit mem root user := by
      simp only [midnight_block_14281_memory, hfree, hsel, hadd, addressMask_computed]
      change writeWord (writeWord mem root.toNat TakeGateKind.credit.selectorWord)
        (root.toNat + 4) (UInt256.land solcAddrMask
          (memLoad TakeGateKind.credit.userOffset
            (writeWord mem root.toNat TakeGateKind.credit.selectorWord))) = _
      rw [hu, hclean]
      rfl
    rw [hmem] at rd1 ha1
    simp only [midnight_block_14281_stack, hfree] at rd1
    simp only [hfree] at ha1
    exact ⟨_, _, _, _, ha1, rd1⟩
  | debt =>
    have rd1 := midnight_block_14160 (by omega) rd
    have ha1 := memoryFundingAt (credit := credit) rd1 (by
      unfold midnight_block_14160_memory
      memory_fund ha)
    have hsel : UInt256.shiftLeft (UInt256.ofNat 2135817387) (UInt256.ofNat 225) =
        TakeGateKind.debt.selectorWord := by decide +kernel
    have hmem : midnight_block_14160_memory (mem := mem) =
        takeGateCallMemory .debt mem root user := by
      simp only [midnight_block_14160_memory, hfree, hsel, hadd, addressMask_computed]
      change writeWord (writeWord mem root.toNat TakeGateKind.debt.selectorWord)
        (root.toNat + 4) (UInt256.land solcAddrMask
          (memLoad TakeGateKind.debt.userOffset
            (writeWord mem root.toNat TakeGateKind.debt.selectorWord))) = _
      rw [hu, hclean]
      rfl
    rw [hmem] at rd1 ha1
    simp only [midnight_block_14160_stack, hfree] at rd1
    simp only [hfree] at ha1
    exact ⟨_, _, _, _, ha1, rd1⟩

end Benchmarks.Midnight
