import Benchmarks.Midnight.SellCallbackFields
import Benchmarks.Midnight.SellCallbackMemory
import Benchmarks.Midnight.MarketEncoderFunding

variable {fork : Ethereum.Fork}

/-! Complete construction of the seller callback input and CALL stack. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightSellCallbackPrepare {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata data : ByteArray} {aw root market arrayPtr limit ptr id assets units fee user receiver : UInt256}
    {callback : AccountAddress} {σ : AccountMap} {k C : Nat} {R : List UInt256} (m : MarketData)
    (hstack : R.length + 26 ≤ 1024)
    (hm : MarketStored mem market arrayPtr limit m) (hlimit : limit.toNat ≤ root.toNat)
    (hroot : root.toNat < 2^128) (hlo : 608 ≤ root.toNat) (hmem : 608 ≤ mem.size)
    (hd : MemoryByteString mem ptr data)
    (hbelow : ptr.toNat + 32 + paddedSize data.size ≤ root.toNat)
    (hmarket : memLoad (memLoad (UInt256.ofNat 384) mem) mem = market)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hid : memLoad (UInt256.ofNat 512) mem = id)
    (haRead : memLoad (UInt256.ofNat 416) mem = assets)
    (huRead : calldataWord I.calldata 68 = units)
    (hfRead : memLoad (UInt256.ofNat 160) mem = fee)
    (hbRead : memLoad (UInt256.ofNat 448) mem = user)
    (hrRead : memLoad (UInt256.ofNat 128) mem = receiver)
    (hrcanon : receiver.toNat < EVM.addressModulus)
    (hf128 : fee.toNat < 2^128) (huser : user.toNat < EVM.addressModulus)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨13482⟩
      ([UInt256.ofNat callback.val, ptr, ⟨32⟩, ⟨13626⟩] ++ R) mem aw rdata σ k C) :
    ∃ gasArg aw' k' C',
      MemoryFunding (credit + 128 * m.collaterals.length + 3 * ((data.size + 31) / 32))
        (sellCallbackMemory mem root.toNat m id assets units fee user receiver ptr.toNat data.size) aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨13630⟩
        ([gasArg, UInt256.ofNat callback.val, ⟨0⟩, root, UInt256.ofNat (sellCallbackSize m data.size),
          root, ⟨32⟩, root] ++ R)
        (sellCallbackMemory mem root.toNat m id assets units fee user receiver ptr.toNat data.size)
        aw' rdata σ k' C' := by
  have hn := hm.collateralCount
  have hlen := hd.length
  have ho (n : Nat) (hn' : n ≤ sellCallbackSize m data.size + 32) :
      (root + UInt256.ofNat n).toNat = root.toNat + n :=
    uadd_word_ofNat_toNat _ _ (by
      unfold sellCallbackSize returnDataAllocation at hn'
      change _ < 2^256
      omega)
  obtain ⟨aw1, k1, C1, ha1, rd1⟩ := midnightSellCallbackHead (by omega)
    (by change _ < 2^256; omega) (by omega) (by omega) hmarket hfree hid ha rd
  have hp1 := sellCallbackHeaderMemory_prefix mem root.toNat limit.toNat id hlimit
  have hm1 := hm.preserve hp1
  simp only [List.cons_append, List.nil_append] at rd1
  obtain ⟨aw2, k2, C2, ha2, rd2⟩ := midnightMarketEncoder_funded m
    (R := [ptr, ⟨13626⟩, root, ⟨0⟩, root, UInt256.ofNat callback.val,
      root, ⟨32⟩, root] ++ R)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    hm1.words hm1.length
    (by simpa only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul]
      using hm1.header.size) hm1.collaterals
    (by have hh := hm.array; have he := hm.extent; omega) hm.extent
    (by rw [ho 260 (by unfold sellCallbackSize; omega)]; omega)
    (by rw [ho 260 (by unfold sellCallbackSize; omega)]; change _ < 2^256; omega)
    (by jump_dest) ha1 rd1
  have he : 260 + (288 + 128 * m.collaterals.length) = 548 + 128 * m.collaterals.length := by
    omega
  simp only [wordAddNat_add, he, List.cons_append, List.nil_append,
    ho 260 (by unfold sellCallbackSize; omega)] at rd2 ha2
  let encoded := marketEncodeMemory (sellCallbackHeaderMemory mem root.toNat id)
    (root.toNat + 260) m
  have hp2 : MemoryPrefix mem encoded root.toNat :=
    (sellCallbackHeaderMemory_prefix _ _ _ _ le_rfl).trans
      (marketEncodeMemory_prefix _ _ _ _ (by omega))
  have hread (read : UInt256) (hread : read.toNat + 32 ≤ 608) (hl : 96 ≤ read.toNat) :
      memLoad read encoded = memLoad read mem := hp2.load read hl (by omega) (by omega)
  obtain ⟨aw3, k3, C3, ha3, rd3⟩ := midnightSellCallbackFields
    (R := [⟨0⟩, root, UInt256.ofNat callback.val, root, ⟨32⟩, root] ++ R)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    (by change _ < 2^256; omega) hlo (by have hh := hp2.size; change 608 ≤ encoded.size; omega)
    ((hread _ (by decide) (by decide)).trans haRead) huRead
    ((hread _ (by decide) (by decide)).trans hfRead)
    ((hread _ (by decide) (by decide)).trans hbRead)
    ((hread _ (by decide) (by decide)).trans hrRead) hrcanon hf128 huser ha2 rd2
  let fields := sellCallbackFieldsMemory mem root.toNat m id assets units fee user receiver
  have hp3 : MemoryPrefix mem fields root.toNat :=
    sellCallbackFieldsMemory_prefix _ _ _ _ _ _ _ _ _ _ le_rfl
  have hd3 := hd.preserve hp3 hbelow
  change MemoryFunding (credit + 128 * m.collaterals.length) fields aw3 C3 at ha3
  obtain ⟨aw4, k4, C4, ha4, rd4⟩ := midnightMemoryBytesEncoder_funded
    (R := [root, ⟨0⟩, root, UInt256.ofNat callback.val, root, ⟨32⟩, root] ++ R)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    hlen (by have hh := hd.bound; omega)
    (by rw [ho (548 + 128 * m.collaterals.length) (by unfold sellCallbackSize; omega)]
        change _ < 2^256; omega) hd3.header (by jump_dest) ha3 rd3
  have he' : 548 + 128 * m.collaterals.length + returnDataAllocation data.size =
      sellCallbackSize m data.size := rfl
  simp only [wordAddNat_add, he', List.cons_append, List.nil_append,
    ho (548 + 128 * m.collaterals.length) (by unfold sellCallbackSize; omega)] at rd4 ha4
  have rd5 := midnightBlocks.midnight_block_13626
    (by simp only [List.length_cons]; omega) rd4
  have ha5 := memoryFundingAt
    (credit := credit + 128 * m.collaterals.length + 3 * ((data.size + 31) / 32)) rd5
    (ha4.mono (by omega))
  simp only [midnightBlocks.midnight_block_13626_stack, word_add_sub_left] at rd5
  have houtput : memoryBytesEncodeMemory fields ptr.toNat
      (root.toNat + (548 + 128 * m.collaterals.length)) data.size =
      sellCallbackMemory mem root.toNat m id assets units fee user receiver ptr.toNat data.size := by
    simp only [sellCallbackMemory, Nat.add_assoc]
    rfl
  rw [houtput] at rd5 ha5
  exact ⟨_, _, _, _, ha5, rd5⟩

end Benchmarks.Midnight
