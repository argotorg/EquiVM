import Benchmarks.Safe.SignatureSwitchSource
import Benchmarks.Safe.MemoryPreserves

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

def SignatureBranchResult (p : SignatureInput) (I : ExecutionEnv) (g : Sat256) (s0 : EVM.State)
    (f : Frame) (evm : EVM.State) (i : Nat) (last executor : UInt256) (src ptr : Nat)
    (mem : ByteArray) (R : List UInt256) (body : List Stmt) : Prop :=
  (RDrev safeBytecode g s0 ∧ ExecBlock config f evm body .reverted) ∨
  ∃ f' evm' σ' mem' ptr' aw' out s' r' v' owner k' C',
    ExecBlock config f evm body (.ok f' evm') ∧ SignatureContext p f' i last ∧
    f'.locals["currentOwner"]? = some (.address (AccountAddress.ofUInt256 owner)) ∧
    evm'.executionEnv = I ∧ evm'.accountMap = σ' ∧ evm'.σ₀ = s0.σ₀ ∧
    RD safeBytecode I g s0 ⟨2679⟩
      (UInt256.ofNat i :: s' :: r' :: v' :: owner :: last :: p.required :: UInt256.ofNat src ::
        p.hash :: executor :: R) mem' aw' out σ' k' C' ∧
    BytesMemory mem' src p.signatures ∧ memLoad ⟨64⟩ mem' = UInt256.ofNat ptr' ∧
    memLoad ⟨96⟩ mem' = ⟨0⟩ ∧ ptr ≤ ptr' ∧ ptr' ≤ ptr + 2 ^ 140 ∧
    mem'.size ≤ max mem.size (ptr + 2 ^ 140) ∧ MemoryPreserves mem mem' 96 ptr

theorem SignatureBranchResult.map {p I g s0 f evm i last executor src ptr mem R a b}
    (h : SignatureBranchResult p I g s0 f evm i last executor src ptr mem R a)
    (hs : ∀ result, ExecBlock config f evm a result → ExecBlock config f evm b result) :
    SignatureBranchResult p I g s0 f evm i last executor src ptr mem R b := by
  rcases h with ⟨hrev, hsource⟩ | ⟨f', evm', σ', mem', ptr', aw', out, s', r', v', owner,
    k', C', hsource, hrest⟩
  · exact .inl ⟨hrev, hs _ hsource⟩
  · exact .inr ⟨f', evm', σ', mem', ptr', aw', out, s', r', v', owner, k', C',
      hs _ hsource, hrest⟩

end Benchmarks.Safe
