import Solm.Benchmarks.Auction.ErrorPayloadMemory
import Solm.Benchmarks.Auction.ReturnDataCopy

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

theorem errorDecodeShort {I g s0 ret R mem aw out acc k C}
    (h : RD auctionBytecode I g s0 ⟨5925⟩ (ret :: R) mem aw out acc k C)
    (hl : out.size < 68) (hret : (D_J auctionBytecode 0).contains ret = true)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ret (⟨0⟩ :: R) mem aw out acc k' C' := by
  have hn : (UInt256.ofNat out.size).toNat = out.size :=
    ulit_toNat' _ (by change out.size < 2 ^ 256; omega)
  have hlt : UInt256.lt (UInt256.ofNat out.size) ⟨68⟩ = ⟨1⟩ :=
    ult_one (by change _ < 68; omega)
  exact ⟨_, _, evm_run h with [jumpdest, push0, push1 ⟨68⟩,
    raw returndatasize (by native_decide) (by evm_ov), lt, iszero, push2 ⟨5938⟩,
    jumpiNT (by rw [hlt]; decide), swap1, jump hret]⟩

theorem lnot3_add_returnSize {size : Nat} (hl : 4 ≤ size) (hb : size < UInt256.size) :
    UInt256.lnot ⟨3⟩ + UInt256.ofNat size = UInt256.ofNat (size - 4) := by
  apply u256_inj
  rw [uadd_toNat, ulit_toNat' size hb, ulit_toNat' (size - 4) (by omega)]
  have hn : (UInt256.lnot (⟨3⟩ : UInt256)).toNat = 2 ^ 256 - 4 := by native_decide
  rw [hn]
  change (2 ^ 256 - 4 + size) % (2 ^ 256) = size - 4
  change size < 2 ^ 256 at hb
  omega

theorem errorDecodeLongPrefix {I g s0 ret R mem aw ptr out acc k C}
    (h : RD auctionBytecode I g s0 ⟨5925⟩ (ret :: R) mem aw out acc k C)
    (hm : HeapMemory mem aw ptr) (hin : ptr.toNat ≤ mem.size) (hl : 68 ≤ out.size)
    (hb : ptr.toNat + out.size ≤ 2 ^ 200) (hov : R.length + 13 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ⟨5978⟩
      (⟨5986⟩ :: UInt256.isZero
        (UInt256.lor (UInt256.gt (errorOffset out) ⟨2 ^ 64 - 1⟩)
          (UInt256.gt (errorOffset out + ⟨36⟩) (UInt256.ofNat out.size))) ::
        ⟨2 ^ 64 - 1⟩ :: UInt256.ofNat out.size :: errorOffset out :: UInt256.lnot ⟨3⟩ ::
        ptr :: ⟨0⟩ :: ret :: R)
      (errorPayloadMem mem out ptr) (errorPayloadWords aw ptr out) out acc k' C' := by
  have ho : out.size < UInt256.size := by change out.size < 2 ^ 256; omega
  have hn : (UInt256.ofNat out.size).toNat = out.size := ulit_toNat' _ ho
  have hn4 : (UInt256.ofNat (out.size - 4)).toNat = out.size - 4 :=
    ulit_toNat' _ (by omega)
  have hlt : UInt256.lt (UInt256.ofNat out.size) ⟨68⟩ = ⟨0⟩ :=
    ult_zero (by change 68 ≤ _; omega)
  have rd5942 := evm_run h with [jumpdest, push0, push1 ⟨68⟩,
    raw returndatasize (by native_decide) (by evm_ov), lt, iszero, push2 ⟨5938⟩,
    jumpiT (by rw [hlt]; decide) (by jump_dest), jumpdest, push1 ⟨64⟩,
    raw mloadSymbolic (by native_decide) (by evm_ov)]
  rw [hm.load64, expandedWords64_eq hm.active] at rd5942
  have rd5951 := evm_run rd5942 with [push1 ⟨3⟩, not,
    raw returndatasize (by native_decide) (by evm_ov), dup2, add, push1 ⟨4⟩, dup4]
  rw [lnot3_add_returnSize (by omega) ho] at rd5951
  obtain ⟨_, _, rd5952⟩ := rd5951.returndatacopySymbolic (by native_decide)
    (by rw [hn4]; change 4 + (out.size - 4) ≤ out.size; omega) (by evm_ov)
  simp only [show (⟨4⟩ : UInt256).toNat = 4 from rfl, hn4] at rd5952
  have rd5954 := evm_run rd5952 with [dup2,
    raw mloadSymbolic (by native_decide) (by evm_ov)]
  have hr := errorPayload_load hm hin hl hb ⟨0⟩ (by change 0 + 36 ≤ out.size; omega)
  have he := errorPayload_expand hm hin hl hb ⟨0⟩ (by change 0 + 36 ≤ out.size; omega)
  rw [u256_add_comm ptr ⟨0⟩, u256_zero_add] at hr he
  change loadedWord (errorPayloadMem mem out ptr) (errorPayloadWords aw ptr out) ptr =
    errorOffset out at hr
  change RD _ _ _ _ ⟨5954⟩
    (loadedWord (errorPayloadMem mem out ptr) (errorPayloadWords aw ptr out) ptr ::
      UInt256.lnot ⟨3⟩ :: ptr :: ⟨0⟩ :: ret :: R)
    (errorPayloadMem mem out ptr) (expandedWords (errorPayloadWords aw ptr out) ptr ⟨32⟩)
    out acc _ _ at rd5954
  rw [hr, he] at rd5954
  have rd5955 := evm_run rd5954 with [raw returndatasize (by native_decide) (by evm_ov)]
  have rd5964 := rd5955.pushConst ⟨0xffffffffffffffff⟩ (width := 8) (op := .PUSH8)
    (by decide) (by native_decide) (by evm_ov)
  exact ⟨_, _, evm_run rd5964 with [dup2, push1 ⟨36⟩, dup5, add, gt, dup2, dup5, gt,
    or, iszero, push2 ⟨5986⟩]⟩

end Auction
