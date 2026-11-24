import Benchmarks.Safe.ViaIR.TokenTransferPrepare
import Benchmarks.Safe.ViaIR.TokenTransferReturn
import Benchmarks.Safe.ViaIR.RawValueCall

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.ViaIR

def tokenTransferOutputMemory (mem : ByteArray) (ptr : Nat)
    (p : TokenTransferInput) (out : ByteArray) : ByteArray :=
  callOutputMem (tokenTransferMemory mem ptr (UInt256.ofNat p.receiver.val) p.amount)
    out ⟨0⟩ ⟨32⟩

theorem tokenTransferOutputMemory_size (mem : ByteArray) (ptr : Nat)
    (p : TokenTransferInput) (out : ByteArray) (hb : out.size < UInt256.size) :
    (tokenTransferOutputMemory mem ptr p out).size = max mem.size (ptr + 100) := by
  rw [tokenTransferOutputMemory, callOutput32_size _ _ _ hb (by
    rw [tokenTransferMemory_size]; change 0 + 32 ≤ _; omega), tokenTransferMemory_size]

theorem tokenTransferOutputMemory_preserved (mem : ByteArray) (ptr : Nat)
    (p : TokenTransferInput) (out : ByteArray) (hb : out.size < UInt256.size) :
    MemoryPreserves mem (tokenTransferOutputMemory mem ptr p out) 96 ptr := by
  have ht := tokenTransferMemory_preserved mem ptr (UInt256.ofNat p.receiver.val) p.amount
  refine ⟨by rw [tokenTransferOutputMemory_size _ _ _ _ hb]; omega, ?_⟩
  intro off count hl hh hin
  rw [tokenTransferOutputMemory, callOutput32_read_above _ _ _ _ _ hb
    (hin.trans ht.size) (by exact Nat.zero_le _) (by change 0 + 32 ≤ off; omega),
    ht.read off count hl hh hin]

theorem tokenTransferOutputMemory_free (mem : ByteArray) (ptr : Nat)
    (p : TokenTransferInput) (out : ByteArray) (hb : out.size < UInt256.size) (hp : 96 ≤ ptr) :
    memLoad ⟨64⟩ (tokenTransferOutputMemory mem ptr p out) = UInt256.ofNat (ptr + 128) := by
  rw [memLoadReadWord]
  change uInt256OfByteArray ((tokenTransferOutputMemory mem ptr p out).readWithPadding 64 32) = _
  rw [tokenTransferOutputMemory, callOutput32_read_above _ _ _ _ _ hb
    (by rw [tokenTransferMemory_size]; omega) (by exact Nat.zero_le _) (by decide),
    ← show (⟨64⟩ : UInt256).toNat = 64 from rfl, ← memLoadReadWord,
    tokenTransferMemory_free _ _ _ _ hp]

set_option maxRecDepth 5000 in
theorem safeTokenTransferTrace (p : TokenTransferInput) (evm : EVM.State)
    {I g s0 σ k C aw mem rdata ptr} {guard success hash flag : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨5152⟩
      (p.amount :: UInt256.ofNat p.token.val :: ⟨0⟩ :: ⟨32⟩ :: UInt256.ofNat p.receiver.val ::
        guard :: success :: hash :: flag :: ⟨0⟩ :: R) mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr) (hm : 128 ≤ mem.size) (hp : 128 ≤ ptr)
    (hz : memLoad ⟨96⟩ mem = ⟨0⟩) (hb : ptr + 128 < UInt256.size)
    (hov : R.length + 24 ≤ 1024) :
    RDrev fork safeBytecode g s0 ∨
    ∃ (evm' : EVM.State) (σ' : AccountMap) (z : Bool) (out : ByteArray)
      (aw' : UInt256) (k' C' : Nat),
      ExecFuncBody fork config p.frame evm transferTokenFunction.body
        (.returned (p.finalFrame z out) evm' (some [.bool (tokenTransferResult z out)])) ∧
      evm'.executionEnv = I ∧ evm'.accountMap = σ' ∧ evm'.σ₀ = s0.σ₀ ∧
      RD fork safeBytecode I g s0 ⟨5231⟩
        ((tokenTransferResult z out).toUInt256 :: p.amount :: guard :: success :: hash ::
          flag :: ⟨0⟩ :: R) (tokenTransferOutputMemory mem ptr p out) aw' out σ' k' C' ∧
      memLoad ⟨64⟩ (tokenTransferOutputMemory mem ptr p out) = UInt256.ofNat (ptr + 128) ∧
      memLoad ⟨96⟩ (tokenTransferOutputMemory mem ptr p out) = ⟨0⟩ ∧
      MemoryPreserves mem (tokenTransferOutputMemory mem ptr p out) 96 ptr ∧
      (tokenTransferOutputMemory mem ptr p out).size = max mem.size (ptr + 100) ∧
      out.size < UInt256.size ∧ ptr + 128 < 2 ^ 64 := by
  have hr : (UInt256.ofNat p.receiver.val).toNat < EVM.addressModulus := by
    rw [ulit_toNat' _ (lt_trans p.receiver.isLt (by decide))]
    exact p.receiver.isLt
  obtain hrev | ⟨gasArg, aw₁, k₁, C₁, hcap, h₁⟩ := safeTokenTransferPrepare h hf (by omega)
    hb hr (by simp; omega)
  · exact .inl hrev
  obtain ⟨evm', σ', z, out, aw₂, k₂, C₂, hc, hee', hacc', hw', h₂, hout, _⟩ :=
    rawValueCallTraceFrom evm h₁ hee hacc hworld (by native_decide)
      (by simp; omega) (.inr rfl)
  have hread := tokenTransferMemory_read mem ptr (UInt256.ofNat p.receiver.val) p.amount
    (by omega)
  have hc' : callViaEVM fork evm (EVM.address p.token) 0 p.callBytes (z, evm', out) := by
    simpa only [accountAddress_roundtrip, addressOfAddress, ulit_toNat' (ptr + 32) (by omega),
      show (⟨68⟩ : UInt256).toNat = 68 from rfl, hread, TokenTransferInput.callBytes] using hc
  have hbz : (if z then (⟨1⟩ : UInt256) else ⟨0⟩) = z.toUInt256 := by cases z <;> rfl
  rw [hbz] at h₂
  obtain ⟨aw₃, k₃, C₃, h₃⟩ := safeTokenTransferReturn z h₂ hout (by omega)
  have hpres := tokenTransferOutputMemory_preserved mem ptr p out hout
  have hzero : memLoad ⟨96⟩ (tokenTransferOutputMemory mem ptr p out) = ⟨0⟩ := by
    rw [memLoadReadWord, show (⟨96⟩ : UInt256).toNat = 96 from rfl,
      hpres.read 96 32 (by decide) (by omega) hm,
      ← show (⟨96⟩ : UInt256).toNat = 96 from rfl, ← memLoadReadWord, hz]
  exact .inr ⟨evm', σ', z, out, aw₃, k₃, C₃, safeTokenTransferSource hc', hee', hacc', hw', h₃,
    tokenTransferOutputMemory_free _ _ _ _ hout (by omega), hzero, hpres,
    tokenTransferOutputMemory_size _ _ _ _ hout, hout, hcap⟩

end Benchmarks.Safe.ViaIR
