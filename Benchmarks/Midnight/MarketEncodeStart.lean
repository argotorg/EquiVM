import Benchmarks.Midnight.MarketData
import Benchmarks.Midnight.CollateralEncodeStep

/-! Initial static fields and the collateral-array header of the market ABI encoder. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def MarketData.firstWords (m : MarketData) : List UInt256 :=
  [m.chainId, UInt256.ofNat m.midnight.val, UInt256.ofNat m.loanToken.val]

def MarketData.headWords (m : MarketData) : List UInt256 :=
  m.firstWords ++ [UInt256.ofNat 256]

def marketEncodeFirstRaw (mem : ByteArray) (ptr output : UInt256) : ByteArray :=
  let mask := UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)
  let m1 := writeWord mem output.toNat (memLoad ptr mem)
  let m2 := writeWord m1 (output + UInt256.ofNat 32).toNat
    (UInt256.land (memLoad (ptr + UInt256.ofNat 32) m1) mask)
  writeWord m2 (output + UInt256.ofNat 64).toNat
    (UInt256.land (memLoad (ptr + UInt256.ofNat 64) m2) mask)

def marketEncodeHeadRaw (mem : ByteArray) (ptr output : UInt256) : ByteArray × UInt256 × UInt256 :=
  let m3 := marketEncodeFirstRaw mem ptr output
  let arrayPtr := memLoad (ptr + UInt256.ofNat 96) m3
  let m4 := writeWord m3 (output + UInt256.ofNat 96).toNat (UInt256.ofNat 256)
  let n := memLoad arrayPtr m4
  (writeWord m4 (output + UInt256.ofNat 256).toNat n, arrayPtr, n)

def marketEncodeHeadMemory (mem : ByteArray) (output : Nat) (m : MarketData) : ByteArray :=
  writeWord (writeWordArray mem output m.headWords) (output + 256)
    (UInt256.ofNat m.collaterals.length)

theorem marketEncodeHeadBlock_memory (mem : ByteArray) (ptr output : UInt256) :
    midnightBlocks.midnight_block_19181_memory (mem := mem) (x0 := ptr) (x1 := output) =
      (marketEncodeHeadRaw mem ptr output).1 := rfl

theorem marketEncodeHeadBlock_stack (mem : ByteArray) (ptr output : UInt256) (R : List UInt256) :
    midnightBlocks.midnight_block_19181_stack (mem := mem) (x0 := ptr) (x1 := output) (R := R) =
      UInt256.ofNat 0 :: (marketEncodeHeadRaw mem ptr output).2.2 ::
        ((marketEncodeHeadRaw mem ptr output).2.1 + UInt256.ofNat 32) :: ptr :: output ::
        (output + UInt256.ofNat 288) :: R := rfl

theorem marketEncodeFirstRaw_eq {mem : ByteArray} {ptr output arrayPtr : UInt256} (m : MarketData)
    (hm : MemoryWords mem ptr.toNat (m.words arrayPtr))
    (hbelow : ptr.toNat + 256 ≤ output.toNat) (hout : output.toNat + 288 < UInt256.size) :
    marketEncodeFirstRaw mem ptr output = writeWordArray mem output.toNat m.firstWords := by
  have hlen : (m.words arrayPtr).length = 8 := rfl
  have add (off : Nat) (ho : off ≤ 64) : (output + UInt256.ofNat off).toNat = output.toNat + off :=
    uadd_word_ofNat_toNat _ _ (by omega)
  have ha : (UInt256.ofNat m.midnight.val).toNat < EVM.addressModulus :=
    addressWord_val_canonical m.midnight
  have hb : (UInt256.ofNat m.loanToken.val).toNat < EVM.addressModulus :=
    addressWord_val_canonical m.loanToken
  have h0 : memLoad ptr mem = m.chainId := hm.load_word ⟨0, by simp [MarketData.words]⟩ (by simp)
  let m1 := writeWord mem output.toNat m.chainId
  have hm1 : MemoryWords m1 ptr.toNat (m.words arrayPtr) := hm.writeWord _ (Or.inl hbelow)
  have h32 : memLoad (ptr + UInt256.ofNat 32) m1 = UInt256.ofNat m.midnight.val :=
    hm1.load_offset ⟨1, by simp [MarketData.words]⟩ rfl
  let m2 := writeWord m1 (output + UInt256.ofNat 32).toNat (UInt256.ofNat m.midnight.val)
  have hm2 : MemoryWords m2 ptr.toNat (m.words arrayPtr) :=
    hm1.writeWord _ (Or.inl (by rw [add 32 (by decide)]; omega))
  have h64 : memLoad (ptr + UInt256.ofNat 64) m2 = UInt256.ofNat m.loanToken.val :=
    hm2.load_offset ⟨2, by simp [MarketData.words]⟩ rfl
  unfold marketEncodeFirstRaw
  dsimp only
  rw [addressMask_computed, h0]
  change writeWord (writeWord m1 (output + UInt256.ofNat 32).toNat
    (UInt256.land (memLoad (ptr + UInt256.ofNat 32) m1) solcAddrMask))
    (output + UInt256.ofNat 64).toNat _ = _
  rw [h32, solcAddrMask_clean ha]
  change writeWord m2 (output + UInt256.ofNat 64).toNat
    (UInt256.land (memLoad (ptr + UInt256.ofNat 64) m2) solcAddrMask) = _
  rw [h64, solcAddrMask_clean hb]
  simp only [m2, m1, add 32 (by decide), add 64 (by decide),
    MarketData.firstWords, writeWordArray, Nat.add_assoc, Nat.reduceAdd]

theorem marketEncodeHeadRaw_eq {mem : ByteArray} {ptr output arrayPtr : UInt256} (m : MarketData)
    (hm : MemoryWords mem ptr.toNat (m.words arrayPtr))
    (hn : memLoad arrayPtr mem = UInt256.ofNat m.collaterals.length)
    (hnin : arrayPtr.toNat + 32 ≤ mem.size)
    (hbelow : ptr.toNat + 256 ≤ output.toNat) (harray : arrayPtr.toNat + 32 ≤ output.toNat)
    (hout : output.toNat + 288 < UInt256.size) :
    marketEncodeHeadRaw mem ptr output =
      (marketEncodeHeadMemory mem output.toNat m, arrayPtr, UInt256.ofNat m.collaterals.length) := by
  let m3 := writeWordArray mem output.toNat m.firstWords
  have hm3 : MemoryWords m3 ptr.toNat (m.words arrayPtr) := hm.writeWords _ (Or.inl hbelow)
  have h96 : memLoad (ptr + UInt256.ofNat 96) m3 = arrayPtr :=
    hm3.load_offset ⟨3, by simp [MarketData.words]⟩ rfl
  have ho96 : (output + UInt256.ofNat 96).toNat = output.toNat + 96 :=
    uadd_word_ofNat_toNat _ _ (by omega)
  have ho256 : (output + UInt256.ofNat 256).toNat = output.toNat + 256 :=
    uadd_word_ofNat_toNat _ _ (by omega)
  have hN : memLoad arrayPtr (writeWord m3 (output.toNat + 96) (UInt256.ofNat 256)) =
      UInt256.ofNat m.collaterals.length := by
    rw [memLoad_writeWord_preserved _ _ _ _
      (hnin.trans (writeWordArray_size_ge _ _ _)) (Or.inl (by omega)),
      memLoad_writeWordArray_preserved _ _ _ _ hnin (Or.inl harray), hn]
  unfold marketEncodeHeadRaw
  rw [marketEncodeFirstRaw_eq m hm hbelow hout]
  change (writeWord (writeWord m3 (output + UInt256.ofNat 96).toNat (UInt256.ofNat 256))
    (output + UInt256.ofNat 256).toNat
    (memLoad (memLoad (ptr + UInt256.ofNat 96) m3)
      (writeWord m3 (output + UInt256.ofNat 96).toNat (UInt256.ofNat 256))),
    memLoad (ptr + UInt256.ofNat 96) m3, _) = _
  rw [h96, ho96, ho256, hN]
  rfl

theorem midnightMarketEncodeStart {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr arrayPtr output : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (m : MarketData)
    (hstack : R.length + 7 ≤ 1024)
    (hm : MemoryWords mem ptr.toNat (m.words arrayPtr))
    (hn : memLoad arrayPtr mem = UInt256.ofNat m.collaterals.length)
    (hnin : arrayPtr.toNat + 32 ≤ mem.size)
    (hbelow : ptr.toNat + 256 ≤ output.toNat) (harray : arrayPtr.toNat + 32 ≤ output.toNat)
    (hout : output.toNat + 288 < UInt256.size)
    (rd : RD midnightBytecode I g s0 ⟨19181⟩ (ptr :: output :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD midnightBytecode I g s0 ⟨19261⟩
      (UInt256.ofNat 0 :: UInt256.ofNat m.collaterals.length :: (arrayPtr + UInt256.ofNat 32) ::
        ptr :: output :: (output + UInt256.ofNat 288) :: R)
      (marketEncodeHeadMemory mem output.toNat m) aw' rdata σ k' C' := by
  have rd1 := midnightBlocks.midnight_block_19181 hstack rd
  simp only [marketEncodeHeadBlock_memory, marketEncodeHeadBlock_stack,
    marketEncodeHeadRaw_eq m hm hn hnin hbelow harray hout] at rd1
  exact ⟨_, _, _, rd1⟩

end Benchmarks.Midnight
