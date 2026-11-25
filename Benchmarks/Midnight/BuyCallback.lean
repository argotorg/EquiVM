import Benchmarks.Midnight.BuyCallbackPrepare
import Benchmarks.Midnight.BuyCallbackReturn
import Benchmarks.Midnight.BuyCallbackSource
import Benchmarks.Midnight.TypedCallFunding

variable {fork : Ethereum.Fork}

/-! The buyer's typed external call and acknowledgement, preserving the allocated heap. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightBuyCallback {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {mem rdata data : ByteArray}
    {aw root market arrayPtr limit ptr id assets units fee user : UInt256}
    {callback : AccountAddress} {σ : AccountMap} {k C : Nat} {R : List UInt256} (m : MarketData)
    (hstack : R.length + 26 ≤ 1024)
    (hm : MarketStored mem market arrayPtr limit m) (hlimit : limit.toNat ≤ root.toNat)
    (hroot : root.toNat + 32 < 2^64) (hlo : 832 ≤ root.toNat) (hmem : 608 ≤ mem.size)
    (hd : MemoryByteString mem ptr data)
    (hbelow : ptr.toNat + 32 + paddedSize data.size ≤ root.toNat)
    (hmarket : memLoad (memLoad (UInt256.ofNat 384) mem) mem = market)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hid : memLoad (UInt256.ofNat 512) mem = id)
    (haRead : memLoad (UInt256.ofNat 256) mem = assets)
    (huRead : calldataWord I.calldata 68 = units)
    (hfRead : memLoad (UInt256.ofNat 224) mem = fee)
    (hbRead : memLoad (UInt256.ofNat 576) mem = user)
    (hf128 : fee.toNat < 2^128) (huser : user.toNat < EVM.addressModulus)
    (ht : frame.locals.get? "buyerCallback" = some (.address callback))
    (hargs : evalExprs? config frame evm buyCallbackExprs =
      .ok (buyCallbackArguments m id assets units fee (AccountAddress.ofNat user.toNat) data))
    (ha : MemoryFunding credit mem aw C) (hs : SourceState s0 I σ evm)
    (rd : RD fork midnightBytecode I g s0 ⟨13805⟩
      ([UInt256.ofNat callback.val, ptr, ⟨32⟩, ⟨13931⟩] ++ R) mem aw rdata σ k C) :
    X fork (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (ExecBlock fork config frame evm [buyCallbackStmt, .require buyMagicGuard] .reverted ∧
      RDrev fork midnightBytecode g s0) ∨
    ∃ (evm' : State) (σ' : AccountMap) (out mem' : ByteArray) (aw' : UInt256) (k' C' : Nat),
      ExecBlock fork config frame evm [buyCallbackStmt, .require buyMagicGuard]
        (.ok (buyCallbackFrame frame (calldataWord out 0)) evm') ∧
      SourceState s0 I σ' evm' ∧ MemoryPrefix mem mem' root.toNat ∧
      memLoad (UInt256.ofNat 64) mem' = root + UInt256.ofNat 32 ∧
      root.toNat + 32 ≤ mem'.size ∧
      MemoryFunding (credit + 128 * m.collaterals.length + 3 * ((data.size + 31) / 32))
        mem' aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨13971⟩ R mem' aw' out σ' k' C' := by
  obtain ⟨gasArg, aw1, k1, C1, ha1, rd1⟩ := midnightBuyCallbackPrepare m hstack hm hlimit
    (by omega) (by omega) hmem hd hbelow hmarket hfree hid haRead huRead hfRead hbRead
    hf128 huser ha rd
  let input := buyCallbackMemory mem root.toNat m id assets units fee user ptr.toNat data.size
  change MemoryFunding
    (credit + 128 * m.collaterals.length + 3 * ((data.size + 31) / 32)) input aw1 C1 at ha1
  have hsrc : ptr.toNat + 32 + data.size ≤ mem.size := by
    have hh := hd.size
    have hp := nat_le_paddedSize data.size
    omega
  have hm1 := buyCallbackMemory_size_lower mem root.toNat m id assets units fee user
    ptr.toNat data.size hsrc
  change root.toNat + 580 + 128 * m.collaterals.length + data.size ≤ input.size at hm1
  have hn := hm.collateralCount
  have hdata := hd.length
  have hlen : buyCallbackSize m data.size < 2^72 := by
    unfold buyCallbackSize returnDataAllocation
    omega
  have hsiz : (UInt256.ofNat (buyCallbackSize m data.size)).toNat =
      buyCallbackSize m data.size := UInt256.toNat_ofNat_of_lt (by change _ < 2^256; omega)
  have hinmem : root.toNat + buyCallbackSize m data.size ≤ input.size := by
    unfold buyCallbackSize returnDataAllocation
    omega
  have houtmem : root.toNat + 32 ≤ input.size := by omega
  have hp : MemoryPrefix mem input root.toNat :=
    buyCallbackMemory_prefix _ _ _ _ _ _ _ _ _ _ _ le_rfl hsrc
  have hcd : config.externalABI.encode? "onBuy"
      (buyCallbackArguments m id assets units fee (AccountAddress.ofNat user.toNat) data) =
      some (input.readWithPadding root.toNat
        (UInt256.ofNat (buyCallbackSize m data.size)).toNat) := by
    have hr := buyCallbackMemory_read root.toNat m id assets units fee
      (AccountAddress.ofNat user.toNat) hd (by omega) hbelow
      (by have hh := paddedSize_le_add31 data.size; change _ < 2^256; omega)
    have huser' : UInt256.ofNat (AccountAddress.ofNat user.toNat).val = user :=
      addressWord_eq_ofNat_address huser
    rw [huser'] at hr
    rw [hsiz, hr]
    exact encodeBuyCallback _ _ _ _ _ _ _
  rcases typedZeroValueCallFunded rd1 hs (by native_decide) hcd
      (by
        rw [hsiz]
        have hmax : 2^72 ≤ maxReturnDataSizeByGas := by decide +kernel
        omega)
      (by change R.length + 2 ≤ 1024; omega) ha1
      (by rw [hsiz]; exact hinmem.trans ha1.covered)
      (by exact houtmem.trans ha1.covered) with
    hoog | ⟨evm', σ', success, out, k2, C2, hcall, hs', rd2, hout, ha2⟩
  · exact Or.inl hoog
  have hout' : out.size < UInt256.size := by change _ < 2^256; omega
  have hreply := wordReplyMemory_eq input out root hout'
  change out.write 0 input root.toNat (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat =
    wordReplyMemory input out root at hreply
  rw [hreply] at rd2 ha2
  simp only [accountAddress_roundtrip] at hcall
  rcases midnightBuyCallbackReturn success (by change R.length + 11 ≤ 1024; omega) hout' hroot hlo houtmem
      (fun ht ↦ (ha2 ht).budget) rd2 with
    ⟨hbad, hrev⟩ | ⟨htrue, h32, he, aw3, k3, C3, ha3, rd3⟩
  · refine Or.inr (Or.inl ⟨?_, hrev⟩)
    cases success with
    | false => exact .consRevert (buyCallbackFailure ht hargs hcall)
    | true =>
      by_cases hshort : out.size < 32
      · exact .consRevert (buyCallbackShort ht hargs hcall hshort)
      · have hne : calldataWord out 0 ≠ flashLoanMagic := by simpa [hshort] using hbad
        refine .consNormal (buyCallbackSuccess ht hargs hcall (by omega))
          (.consRevert (.requireFalse ?_))
        rw [buyMagicGuard_eval, decide_eq_false hne]
  · subst success
    have hm2 : root.toNat + 32 ≤ (wordReplyMemory input out root).size := by
      rw [wordReplyMemory_size _ _ _ houtmem]; exact houtmem
    refine Or.inr (Or.inr ⟨evm', σ', out, _, aw3, k3, C3, ?_, hs',
      (hp.trans (wordReplyMemory_prefix _ _ _ _ houtmem le_rfl)).trans
        (callbackResultMemory_prefix _ _ _), callbackResultMemory_free _ _ (by omega),
      ?_, ha3.funding, rd3⟩)
    · refine .consNormal (buyCallbackSuccess ht hargs hcall h32)
        (.consNormal (.requireTrue ?_) .nil)
      rw [buyMagicGuard_eval, decide_eq_true he]
    · rw [callbackResultMemory_size _ _ (by omega)]; exact hm2

end Benchmarks.Midnight
