import Benchmarks.Midnight.MarketData
import Benchmarks.Midnight.CollateralEncodeStep

variable {fork : Ethereum.Fork}

/-! The final four static fields of the market ABI encoding. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def MarketData.tailWords (m : MarketData) : List UInt256 :=
  [m.maturity, m.rcfThreshold, UInt256.ofNat m.enterGate.val, UInt256.ofNat m.liquidatorGate.val]

def marketEncodeTailRaw (mem : ByteArray) (ptr output : UInt256) : ByteArray :=
  let mask := UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)
  let m1 := writeWord mem (output + UInt256.ofNat 128).toNat (memLoad (ptr + UInt256.ofNat 128) mem)
  let m2 := writeWord m1 (output + UInt256.ofNat 160).toNat (memLoad (ptr + UInt256.ofNat 160) m1)
  let m3 := writeWord m2 (output + UInt256.ofNat 192).toNat
    (UInt256.land (memLoad (ptr + UInt256.ofNat 192) m2) mask)
  writeWord m3 (output + UInt256.ofNat 224).toNat
    (UInt256.land (memLoad (ptr + UInt256.ofNat 224) m3) mask)

theorem marketEncodeTailBlock_shape (mem : ByteArray) (ptr output : UInt256) :
    midnightBlocks.midnight_block_19269_memory (mem := mem) (x3 := ptr) (x4 := output) =
      marketEncodeTailRaw mem ptr output := rfl

theorem marketEncodeTailRaw_eq {mem : ByteArray} {ptr output arrayPtr : UInt256} (m : MarketData)
    (hm : MemoryWords mem ptr.toNat (m.words arrayPtr))
    (hbelow : ptr.toNat + 256 ≤ output.toNat) (hout : output.toNat + 256 < UInt256.size) :
    marketEncodeTailRaw mem ptr output = writeWordArray mem (output.toNat + 128) m.tailWords := by
  have hlen : (m.words arrayPtr).length = 8 := rfl
  have add (off : Nat) (ho : off ≤ 224) : (output + UInt256.ofNat off).toNat = output.toNat + off :=
    uadd_word_ofNat_toNat _ _ (by omega)
  have he : (UInt256.ofNat m.enterGate.val).toNat < EVM.addressModulus :=
    addressWord_val_canonical m.enterGate
  have hl : (UInt256.ofNat m.liquidatorGate.val).toNat < EVM.addressModulus :=
    addressWord_val_canonical m.liquidatorGate
  have h128 : memLoad (ptr + UInt256.ofNat 128) mem = m.maturity :=
    hm.load_offset ⟨4, by simp [MarketData.words]⟩ rfl
  let m1 := writeWord mem (output + UInt256.ofNat 128).toNat m.maturity
  have hm1 : MemoryWords m1 ptr.toNat (m.words arrayPtr) :=
    hm.writeWord _ (Or.inl (by rw [add 128 (by decide)]; omega))
  have h160 : memLoad (ptr + UInt256.ofNat 160) m1 = m.rcfThreshold :=
    hm1.load_offset ⟨5, by simp [MarketData.words]⟩ rfl
  let m2 := writeWord m1 (output + UInt256.ofNat 160).toNat m.rcfThreshold
  have hm2 : MemoryWords m2 ptr.toNat (m.words arrayPtr) :=
    hm1.writeWord _ (Or.inl (by rw [add 160 (by decide)]; omega))
  have h192 : memLoad (ptr + UInt256.ofNat 192) m2 = UInt256.ofNat m.enterGate.val :=
    hm2.load_offset ⟨6, by simp [MarketData.words]⟩ rfl
  let m3 := writeWord m2 (output + UInt256.ofNat 192).toNat (UInt256.ofNat m.enterGate.val)
  have hm3 : MemoryWords m3 ptr.toNat (m.words arrayPtr) :=
    hm2.writeWord _ (Or.inl (by rw [add 192 (by decide)]; omega))
  have h224 : memLoad (ptr + UInt256.ofNat 224) m3 = UInt256.ofNat m.liquidatorGate.val :=
    hm3.load_offset ⟨7, by simp [MarketData.words]⟩ rfl
  unfold marketEncodeTailRaw
  dsimp only
  rw [addressMask_computed, h128]
  change writeWord (writeWord (writeWord m1 (output + UInt256.ofNat 160).toNat
    (memLoad (ptr + UInt256.ofNat 160) m1)) (output + UInt256.ofNat 192).toNat _)
    (output + UInt256.ofNat 224).toNat _ = _
  rw [h160]
  change writeWord (writeWord m2 (output + UInt256.ofNat 192).toNat
    (UInt256.land (memLoad (ptr + UInt256.ofNat 192) m2) solcAddrMask))
    (output + UInt256.ofNat 224).toNat _ = _
  rw [h192, solcAddrMask_clean he]
  change writeWord m3 (output + UInt256.ofNat 224).toNat
    (UInt256.land (memLoad (ptr + UInt256.ofNat 224) m3) solcAddrMask) = _
  rw [h224, solcAddrMask_clean hl]
  simp only [m3, m2, m1, add 128 (by decide), add 160 (by decide), add 192 (by decide),
    add 224 (by decide), MarketData.tailWords, writeWordArray, Nat.add_assoc, Nat.reduceAdd]

theorem midnightMarketEncodeEnd {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr arrayPtr output finish index count readPtr ret : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (m : MarketData)
    (hstack : R.length + 10 ≤ 1024)
    (hm : MemoryWords mem ptr.toNat (m.words arrayPtr))
    (hbelow : ptr.toNat + 256 ≤ output.toNat) (hout : output.toNat + 256 < UInt256.size)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD fork midnightBytecode I g s0 ⟨19269⟩
      (index :: count :: readPtr :: ptr :: output :: finish :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork midnightBytecode I g s0 ret (finish :: R)
      (writeWordArray mem (output.toNat + 128) m.tailWords) aw' rdata σ k' C' := by
  have rd1 := midnightBlocks.midnight_block_19269 hstack hret rd
  simp only [midnightBlocks.midnight_block_19269_stack, marketEncodeTailBlock_shape,
    marketEncodeTailRaw_eq m hm hbelow hout] at rd1
  exact ⟨_, _, _, rd1⟩

end Benchmarks.Midnight
