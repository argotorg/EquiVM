import Benchmarks.Midnight.TakePayerSelect
import Benchmarks.Midnight.TakeReceiverSelect

variable {fork : Ethereum.Fork}

/-! Source and runtime agreement through all trade-recipient choices. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem takeReceiverMemory_size (mem : ByteArray) (offer : OfferData) (receiver : AccountAddress)
    (hm : 160 ≤ mem.size) : (takeReceiverMemory mem offer receiver).size = mem.size := by
  simp only [takeReceiverMemory, writeWord_sparse_size]
  omega

theorem takeReceiverMemory_load {mem : ByteArray} (offer : OfferData) (receiver : AccountAddress)
    (read : UInt256) (hin : read.toNat + 32 ≤ mem.size)
    (hd : read.toNat + 32 ≤ 128 ∨ 160 ≤ read.toNat) :
    memLoad read (takeReceiverMemory mem offer receiver) = memLoad read mem := by
  rw [takeReceiverMemory, memLoad_writeWord_preserved _ _ _ _
      (by rw [writeWord_sparse_size]; omega) hd,
    memLoad_writeWord_preserved _ _ _ _ hin hd]

theorem takeReceiverMemory_receiver (mem : ByteArray) (offer : OfferData) (receiver : AccountAddress) :
    memLoad (UInt256.ofNat 128) (takeReceiverMemory mem offer receiver) =
      UInt256.ofNat (takeReceiver offer receiver).val := memLoad_writeWord _ _ _

theorem takeReceiverMemory_offer {mem : ByteArray}
    {marketPtr arrayPtr callbackPtr root : UInt256} {offer : OfferData} (receiver : AccountAddress)
    (ho : OfferStored mem ⟨832⟩ marketPtr arrayPtr callbackPtr root offer) :
    OfferStored (takeReceiverMemory mem offer receiver)
      ⟨832⟩ marketPtr arrayPtr callbackPtr root offer :=
  (ho.writeWord_below (off := 128) ⟨0⟩ (by decide)).writeWord_below _ (by decide)

theorem TakeSourceFrame.recipients {frame : Frame} {offer : OfferData} {id units taker : UInt256}
    {receiver callback buyer sender : AccountAddress} {ratifierData data : ByteArray}
    (hf : TakeSourceFrame frame offer id units taker receiver callback ratifierData data) :
    TakeSourceFrame (takeRecipientsFrame frame offer callback buyer sender receiver)
      offer id units taker receiver callback ratifierData data :=
  (((hf.insert "buyerCallback" (.address (takeBuyerCallback offer callback)) (by decide)).insert
    "sellerCallback" (.address (takeSellerCallback offer callback)) (by decide)).insert
    "payer" (.address (takePayer offer callback buyer sender)) (by decide)).insert
    "receiver" (.address (takeReceiver offer receiver)) (by decide)

theorem takeRecipientsFrame_get {frame : Frame} {offer : OfferData}
    {receiver callback buyer sender : AccountAddress} (name : Ident)
    (hn : name ∉ ["buyerCallback", "sellerCallback", "payer", "receiver"]) :
    (takeRecipientsFrame frame offer callback buyer sender receiver).locals.get? name =
      frame.locals.get? name := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  have hn1 : ("buyerCallback" == name) = false := by
    simp only [beq_eq_false_iff_ne]
    exact fun he ↦ hn.1 he.symm
  have hn2 : ("sellerCallback" == name) = false := by
    simp only [beq_eq_false_iff_ne]
    exact fun he ↦ hn.2.1 he.symm
  have hn3 : ("payer" == name) = false := by
    simp only [beq_eq_false_iff_ne]
    exact fun he ↦ hn.2.2.1 he.symm
  have hn4 : ("receiver" == name) = false := by
    simp only [beq_eq_false_iff_ne]
    exact fun he ↦ hn.2.2.2 he.symm
  exact (store_get_ne _ _ hn4).trans ((store_get_ne _ _ hn3).trans
    ((store_get_ne _ _ hn2).trans (store_get_ne _ _ hn1)))

theorem midnightTakeRecipients {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {mem rdata : ByteArray}
    {aw id units taker decrease ratifierPtr increase marketPtr arrayPtr callbackPtr root : UInt256}
    {offer : OfferData} {callback buyer receiver : AccountAddress} {ratifierData data : ByteArray}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024) (hc : OfferCanonical offer)
    (hf : TakeSourceFrame frame offer id units taker receiver callback ratifierData data)
    (hb : frame.locals.get? "buyer" = some (.address buyer))
    (ho : OfferStored mem ⟨832⟩ marketPtr arrayPtr callbackPtr root offer)
    (hoffer : memLoad (UInt256.ofNat 384) mem = ⟨832⟩)
    (hcallback : memLoad (UInt256.ofNat 192) mem = UInt256.ofNat callback.val)
    (hbuyer : memLoad (UInt256.ofNat 576) mem = UInt256.ofNat buyer.val)
    (hreceiver : memLoad (UInt256.ofNat 288) mem = UInt256.ofNat receiver.val)
    (hs : SourceState s0 I σ evm) (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨12719⟩
      ([offer.buy, decrease, ratifierPtr, increase] ++ R) mem aw rdata σ k C) :
    ∃ aw' k' C',
      ABlock fork config evm frame (takeTransition.body.drop 60)
        (takeRecipientsFrame frame offer callback buyer I.source receiver)
        (takeTransition.body.drop 64) ∧
      MemoryFunding credit (takeReceiverMemory mem offer receiver) aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨12792⟩
        ([decrease, increase, ratifierPtr, UInt256.ofNat (takeSellerCallback offer callback).val,
          UInt256.ofNat (takePayer offer callback buyer I.source).val,
          UInt256.ofNat (takeBuyerCallback offer callback).val] ++ R)
        (takeReceiverMemory mem offer receiver) aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, ha1, rd1⟩ := midnightTakeCallbackSelect (by omega) hc ho hoffer hcallback ha rd
  obtain ⟨aw2, k2, C2, ha2, rd2⟩ := midnightTakePayerSelect (by omega) hc hbuyer ha1 rd1
  obtain ⟨aw3, k3, C3, ha3, rd3⟩ := midnightTakeReceiverSelect
    (R := [decrease, increase, ratifierPtr, UInt256.ofNat (takeSellerCallback offer callback).val,
      UInt256.ofNat (takePayer offer callback buyer I.source).val,
      UInt256.ofNat (takeBuyerCallback offer callback).val] ++ R)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    hc ho hoffer hreceiver ha2 rd2
  refine ⟨aw3, k3, C3, ?_, ha3, rd3⟩
  simpa only [hs.env] using
    takeRecipientsSource (evm := evm) hf.offerValue hf.callback hb hf.receiver

end Benchmarks.Midnight
