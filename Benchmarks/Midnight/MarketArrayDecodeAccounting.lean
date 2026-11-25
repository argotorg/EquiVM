import Benchmarks.Midnight.MarketHeapMemory
import Benchmarks.Midnight.MarketArrayAllocationAccounting
import Benchmarks.Midnight.MarketLastFieldsAccounting
import Benchmarks.Midnight.MemoryBufferBounds
import Benchmarks.Midnight.CollateralLoopAccounting

variable {fork : Ethereum.Fork}

/-! Composing the collateral array decoder with the final market fields. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightMarketCalldataArrayDecode_accounted {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr n header head ret : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 25 ≤ 1024)
    (hsize : I.calldata.size < 2^255) (hsmall : head.toNat < 2^127)
    (hhead : head.toNat + 256 ≤ I.calldata.size)
    (hlo : 96 ≤ ptr.toNat) (hptr : ptr.toNat + 256 < 2^64)
    (hfirst : MemoryWords mem ptr.toNat (marketFirstWords I.calldata head.toNat))
    (hfree : memLoad (UInt256.ofNat 64) mem = ptr + UInt256.ofNat 256)
    (hm : (calldataWord I.calldata (head.toNat + 32)).toNat < EVM.addressModulus)
    (hl : (calldataWord I.calldata (head.toNat + 64)).toNat < EVM.addressModulus)
    (hoff : (calldataWord I.calldata (head.toNat + 96)).toNat < 2^64)
    (harrayhead : head.toNat + (calldataWord I.calldata (head.toNat + 96)).toNat + 32 ≤ I.calldata.size)
    (hnword : n = calldataWord I.calldata
      (head.toNat + (calldataWord I.calldata (head.toNat + 96)).toNat))
    (hn : n.toNat < 2^64)
    (hheader : header.toNat = head.toNat + (calldataWord I.calldata (head.toNat + 96)).toNat)
    (hvalid : (D_J midnightBytecode 0).contains ret = true)
    (ha0 : MemoryAccounting mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨18684⟩
      (UInt256.ofNat (pointerArrayAllocation n.toNat) :: n :: header :: UInt256.ofNat I.calldata.size ::
        head :: ptr :: ret :: ptr :: R) mem aw rdata σ k C) :
    ((∀ m, decodeMarketData I.calldata head.toNat = some m →
        ¬ ptr.toNat + 288 + 160 * m.collaterals.length < 2^64) ∧ RDrev fork midnightBytecode g s0) ∨
    (∃ m, decodeMarketData I.calldata head.toNat = some m ∧
      ptr.toNat + 288 + 160 * m.collaterals.length < 2^64 ∧
      ∃ mem' root aw' k' C',
        root.toNat = ptr.toNat + 288 + 160 * m.collaterals.length ∧
        MarketStored mem' ptr (ptr + UInt256.ofNat 256) root m ∧
        memLoad (UInt256.ofNat 64) mem' = root ∧
        root.toNat ≤ mem'.size ∧ MemoryAccounting mem' aw' C' ∧
        RD fork midnightBytecode I g s0 ret (ptr :: R) mem' aw' rdata σ k' C') := by
  have count {m : MarketData} (hd : decodeMarketData I.calldata head.toNat = some m) :
      m.collaterals.length = n.toNat := by
    rw [decodeMarketData_collateralCount hd, hnword]
  let arrayPtr := ptr + UInt256.ofNat 256
  let dataPtr := arrayPtr + UInt256.ofNat (pointerArrayAllocation n.toNat)
  have ha : arrayPtr.toNat = ptr.toNat + 256 :=
    uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
  have hd : dataPtr.toNat = ptr.toNat + 288 + 32 * n.toNat := by
    rw [show dataPtr = arrayPtr + UInt256.ofNat (pointerArrayAllocation n.toNat) from rfl,
      uadd_word_ofNat_toNat _ _ (by rw [ha]; change _ + (32 + 32 * n.toNat) < 2^256; omega),
      ha, pointerArrayAllocation]
    omega
  have hcd : (UInt256.ofNat I.calldata.size).toNat = I.calldata.size :=
    UInt256.toNat_ofNat_of_lt (by change _ < 2^256; omega)
  rcases midnightMarketCalldataArrayAllocation_accounted (by simp only [List.length_cons]; omega)
      hfree (by rw [ha]; exact hptr) hn (by rw [hheader]; omega) ha0 rd with
    ⟨hcap, hr⟩ | ⟨hshort, hr⟩ | ⟨hfit, hbound, aw1, k1, C1, ha1, rd1⟩
  · left
    refine ⟨fun m hm ↦ ?_, hr⟩
    rw [count hm]
    change ¬ arrayPtr.toNat + (32 + 32 * n.toNat) < 2^64 at hcap
    rw [ha] at hcap
    omega
  · left
    refine ⟨fun m hm ↦ ?_, hr⟩
    rcases decodeMarketData_success hm with ⟨_, _, _, _, _, cs, hc, _⟩
    rw [← hnword] at hc
    have hb := decodeCollateralElements_bound hc
    rw [hheader, hcd] at hshort
    omega
  · let arrayMem := marketArrayMemory mem arrayPtr n
    have haw : (arrayPtr + UInt256.ofNat 32).toNat = arrayPtr.toNat + 32 :=
      uadd_word_ofNat_toNat _ _ (by rw [ha]; change _ < 2^256; omega)
    have hread : (UInt256.ofNat 32 + header).toNat = header.toNat + 32 := by
      rw [uadd_toNat]
      change (32 + header.toNat) % UInt256.size = header.toNat + 32
      rw [Nat.mod_eq_of_lt (by rw [hheader]; change _ < 2^256; omega)]
      omega
    have hstop : (UInt256.ofNat (header.toNat + 32 + 128 * n.toNat)).toNat =
        header.toNat + 32 + 128 * n.toNat :=
      UInt256.toNat_ofNat_of_lt (by rw [hheader]; change _ < 2^256; omega)
    have hf1 : memLoad (UInt256.ofNat 64) arrayMem = dataPtr :=
      marketArrayMemory_free (by rw [ha]; omega)
    have hdata : dataPtr.toNat < 2^64 := by
      change arrayPtr.toNat + pointerArrayAllocation n.toNat < 2^64 at hfit
      rw [ha, pointerArrayAllocation] at hfit
      rw [hd]
      omega
    have hptrarray : (arrayPtr + UInt256.ofNat 32).toNat + 32 * n.toNat ≤ dataPtr.toNat := by
      rw [haw, ha, hd]
    rcases midnightCollateralCalldataLoop_accounted (ptr := dataPtr)
        (by simp only [List.length_cons]; omega)
        (by rw [hread]; rw [hcd] at hbound; exact hbound) hsize
        (by rw [hstop, hread]) hdata hf1 (by rw [haw, ha]; omega) hptrarray ha1 rd1 with
      ⟨hnone, hr⟩ | ⟨hcap, hr⟩ | ⟨cs, hc, hfit', hf2, aw2, k2, C2, ha2, rd2⟩
    · left
      refine ⟨fun m hm ↦ ?_, hr⟩
      rcases decodeMarketData_success hm with ⟨_, _, _, _, _, cs, hc, _⟩
      rw [← hnword] at hc
      rw [hread, hheader] at hnone
      rw [hnone] at hc
      cases hc
    · left
      refine ⟨fun m hm ↦ ?_, hr⟩
      rw [count hm]
      rw [hd] at hcap
      omega
    · rw [hread, hheader] at hc
      have hclen : cs.length = n.toNat := decodeCollateralElements_length hc
      let root := dataPtr + UInt256.ofNat (128 * n.toNat)
      have hroot : root.toNat = dataPtr.toNat + 128 * n.toNat :=
        uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
      have hrootsmall : root.toNat < 2^64 := by rw [hroot]; exact hfit'
      have hm1 : MemoryWords arrayMem ptr.toNat (marketFirstWords I.calldata head.toNat) :=
        marketArrayMemory_preserve hfirst hlo (by
          change ptr.toNat + 32 * 3 ≤ arrayPtr.toNat
          rw [ha]; omega)
      have hm2 := hm1.collateralLoop (ptr := dataPtr) (writePtr := arrayPtr + UInt256.ofNat 32) cs hlo (by
        change ptr.toNat + 32 * 3 ≤ (arrayPtr + UInt256.ofNat 32).toNat
        rw [haw, ha]; omega) (by rw [hclen]; exact hfit') (by rw [hclen]; exact hptrarray)
      have hh := (marketArrayMemory_header (mem := mem) (ptr := arrayPtr) (n := n)
        (by rw [ha]; change _ < 2^256; omega)).collateralLoop
          (ptr := dataPtr) (writePtr := arrayPtr + UInt256.ofNat 32) cs (by rw [ha]; omega)
        (by simp only [haw, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul]; omega)
        (by rw [hclen]; exact hfit') (by rw [hclen]; exact hptrarray)
      have hc2 := collateralLoopMemory_stored (mem := arrayMem) (ptr := dataPtr)
        (writePtr := arrayPtr + UInt256.ofNat 32) cs (by rw [hclen]; exact hfit')
        (by rw [hclen]; exact hptrarray) (by rw [haw, ha]; omega)
      rw [hclen, ← hroot] at hc2
      rcases midnightMarketCalldataLastFields_accounted (by simp only [List.length_cons]; omega)
          (by change _ < 2^256; omega) (by change _ < 2^256; omega) hvalid ha2 rd2 with
        ⟨hnone, hr⟩ | ⟨he, hliq, aw3, k3, C3, ha3, rd3⟩
      · left
        exact ⟨(fun m hm ↦ by rw [hnone] at hm; cases hm), hr⟩
      · right
        refine ⟨MarketData.at I.calldata head.toNat cs,
          decodeMarketData_of_elements hhead ⟨hm, hl, he, hliq⟩ hoff harrayhead
            (by rw [← hnword]; exact hn) (by simpa only [hnword] using hc), ?_,
          _, root, aw3, k3, C3, ?_, ?_, ?_, ?_, ha3, rd3⟩
        · change ptr.toNat + 288 + 160 * cs.length < 2^64
          rw [hclen]
          rw [hd] at hfit'
          omega
        · change root.toNat = ptr.toNat + 288 + 160 * cs.length
          rw [hroot, hd, hclen]; omega
        · apply marketLastMemory_stored hm2 _ hc2 hlo (by rw [ha])
            (by rw [hroot, ha, hd]; omega) hrootsmall ⟨hm, hl, he, hliq⟩
          simpa only [hclen, u256_ofNat_toNat] using hh
        · exact marketLastMemory_free hf2 (by
            have hs := hm2.size
            change ptr.toNat + 32 * 3 ≤ _ at hs
            omega) hlo

        · have hs := collateralLoopMemory_end (mem := arrayMem) (ptr := dataPtr)
            (writePtr := arrayPtr + UInt256.ofNat 32) cs
            (by rw [hclen]; change _ < 2^256; omega) (by
              intro hz
              have hzero : n.toNat = 0 := by rw [hz] at hclen; simpa using hclen.symm
              have hsz := (marketArrayMemory_header (mem := mem) (ptr := arrayPtr) (n := n)
                (by rw [ha]; change _ < 2^256; omega)).size
              simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul] at hsz
              change arrayPtr.toNat + 32 ≤ arrayMem.size at hsz
              rw [ha] at hsz
              rw [hd]
              omega)
          have hlast := writeWordArray_size_ge
            (collateralLoopMemory arrayMem dataPtr (arrayPtr + UInt256.ofNat 32) cs)
            (ptr.toNat + 96) (marketLastWords I.calldata head.toNat arrayPtr)
          change root.toNat ≤ _
          rw [hroot, ← hclen]
          exact hs.trans hlast

end Benchmarks.Midnight
