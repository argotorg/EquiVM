import Benchmarks.Midnight.TakeUnlock
import Benchmarks.Midnight.TakeHealth
import Benchmarks.Midnight.TakeTransfers

variable {fork : Ethereum.Fork}

/-! The complete take suffix from lock restoration through the health check and return. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem takeCleanup_shape : takeTransition.body.drop 71 =
    takeTransition.body[71]! :: takeTransition.body[72]! :: takeTransition.body.drop 73 := rfl

theorem midnightTakeCleanup {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {mem rdata : ByteArray} {aw root market arrayPtr callbackPtr offerRoot
      id seller wasLocked ignored bought sold : UInt256} {offer : OfferData}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 24 ≤ 1024) (hfork : fork ≥ .osaka)
    (hc : frame.contract = contract) (hcanon : seller.toNat < EVM.addressModulus)
    (hfOffer : frame.locals.get? "offer" = some (Model.offerValue offer.value))
    (hfId : frame.locals.get? "id" = some (wordBytes32Value id))
    (hfSeller : frame.locals.get? "seller" = some (.address (AccountAddress.ofNat seller.toNat)))
    (hfWasLocked : frame.locals.get? "wasLocked" = some (wordToElem .bool wasLocked))
    (hfBought : frame.locals.get? "buyerAssets" = some (.int bought.toNat))
    (hfSold : frame.locals.get? "sellerAssets" = some (.int sold.toNat))
    (ho : OfferStored mem ⟨832⟩ market arrayPtr callbackPtr offerRoot offer)
    (hheap : offerRoot.toNat ≤ root.toNat)
    (hroot : root.toNat + 4352 < 2^64) (hlo : 832 ≤ root.toNat) (hsize : 832 ≤ mem.size)
    (hperm : I.perm = true) (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hoffer : memLoad (UInt256.ofNat 384) mem = ⟨832⟩)
    (hid : memLoad (UInt256.ofNat 512) mem = id)
    (hseller : memLoad (UInt256.ofNat 448) mem = seller)
    (hbought : memLoad (UInt256.ofNat 256) mem = bought)
    (hsold : memLoad (UInt256.ofNat 416) mem = sold)
    (ha : MemoryFunding credit mem aw C) (hs : SourceState s0 I σ evm)
    (rd : RD fork midnightBytecode I g s0 ⟨13336⟩
      (ignored :: wasLocked :: R) mem aw rdata σ k C) :
    (ExecBlock fork config frame evm (takeTransition.body.drop 71) .reverted ∧
      RDrev fork midnightBytecode g s0) ∨
    ∃ frame' evm',
      ExecBlock fork config frame evm (takeTransition.body.drop 71)
        (.returned frame' evm' (some [.int bought.toNat, .int sold.toNat])) ∧
      RDret fork midnightBytecode g s0 evm'.accountMap (wordArrayBytes [bought, sold]) := by
  obtain ⟨frame1, evm1, σ1, mem1, root1, aw1, k1, C1,
      hx1, hc1, hf1, hs1, hp1, hroot1, hfree1, ha1, rd1⟩ :=
    midnightTakeUnlock (by omega) hc hcanon hfId hfSeller hfWasLocked (by omega)
      hlo hperm hfree hid hseller ha hs rd
  have hn128 : (root + UInt256.ofNat 128).toNat = root.toNat + 128 :=
    uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
  have hlo1 : root.toNat ≤ root1.toNat := by rcases hroot1 with rfl | rfl <;> omega
  have hhi1 : root1.toNat ≤ root.toNat + 128 := by rcases hroot1 with rfl | rfl <;> omega
  have hi1 := (hf1 "id" (by decide)).trans hfId
  have hsel1 := (hf1 "seller" (by decide)).trans hfSeller
  have hread1 (off : UInt256) (hl : 96 ≤ off.toNat) (hh : off.toNat + 32 ≤ 832) :
      memLoad off mem1 = memLoad off mem := hp1.load off hl (by omega) (by omega)
  obtain ⟨aw2, k2, C2, hx2, ha2, rd2⟩ := midnightTakeReadLock (by omega) (hc1.trans hc)
    hcanon hi1 hsel1 (by omega) (by omega) hfree1
    ((hread1 _ (by decide) (by decide)).trans hid)
    ((hread1 _ (by decide) (by decide)).trans hseller) ha1 hs1 rd1
  let mem2 := dynamicLockMemory mem1 root1 id seller
  let frame2 := takeLockedFrame frame1 evm1 id seller
  let root2 := root1 + UInt256.ofNat 128
  have hn2 : root2.toNat = root1.toNat + 128 :=
    uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
  have hp2 : MemoryPrefix mem mem2 root.toNat :=
    hp1.trans ((dynamicLockMemory_prefix mem1 root1 id seller).mono hlo1)
  have ho2 := ho.preserve (hp2.mono hheap)
  have hread2 (off : UInt256) (hl : 96 ≤ off.toNat) (hh : off.toNat + 32 ≤ 832) :
      memLoad off mem2 = memLoad off mem := hp2.load off hl (by omega) (by omega)
  have hget2 (name : Ident) (hn : name ≠ "locked") (hn' : name ≠ "__c31") :
      frame2.locals.get? name = frame.locals.get? name :=
    (store_get_ne _ _ (by simpa using hn.symm)).trans (hf1 name hn')
  have hmarket : memLoad (memLoad (UInt256.ofNat 384) mem2) mem2 = market := by
    rw [(hread2 _ (by decide) (by decide)).trans hoffer]
    exact ho2.words.load_offset ⟨0, by change 0 < 15; decide⟩ rfl
  have sourcePrefix {result} (hx : ExecBlock fork config frame2 evm1 (takeTransition.body.drop 73) result) :
      ExecBlock fork config frame evm (takeTransition.body.drop 71) result := by
    rw [takeCleanup_shape]
    exact ExecBlock.consNormal hx1 (ExecBlock.consNormal hx2 hx)
  rcases midnightTakeHealth (frame := frame2) (root := root2) hstack hfork (hc1.trans hc) hcanon
      ((hget2 _ (by decide) (by decide)).trans hfOffer)
      ((hget2 _ (by decide) (by decide)).trans hfId)
      ((hget2 _ (by decide) (by decide)).trans hfSeller)
      (by exact store_get_self _ _ _)
      ((hget2 _ (by decide) (by decide)).trans hfBought)
      ((hget2 _ (by decide) (by decide)).trans hfSold)
      ho2.market (by have hh := ho.extent; omega) (by omega) (by omega)
      (hsize.trans hp2.size) (dynamicLockMemory_free ..) hmarket
      ((hread2 _ (by decide) (by decide)).trans hid)
      ((hread2 _ (by decide) (by decide)).trans hseller)
      ((hread2 _ (by decide) (by decide)).trans hbought)
      ((hread2 _ (by decide) (by decide)).trans hsold) ha2 hs1 rd2 with
    ⟨hx, hr⟩ | ⟨frame3, evm3, hx, hr⟩
  · exact Or.inl ⟨sourcePrefix hx, hr⟩
  · exact Or.inr ⟨frame3, evm3, sourcePrefix hx, hr⟩

end Benchmarks.Midnight
