import Benchmarks.Dss.Clipper.TakeChost
import Benchmarks.Dss.Clipper.TakeChostSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

def clipperTakeNoPartialPurchaseRawWord : UInt256 :=
  UInt256.ofNat
    0x436c69707065722f6e6f2d7061727469616c2d70757263686173650000000000

theorem clipperTakeNoPartialPurchaseRawWord_eq :
    clipperTakeNoPartialPurchaseRawWord =
      UInt256.ofNat
        0x436c69707065722f6e6f2d7061727469616c2d70757263686173650000000000 := rfl

set_option maxHeartbeats 1000000 in
theorem RD.clipperTakeNoPartialPurchaseRevertTail {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {stk : List UInt256} {mem rdata : ByteArray} {k C : ℕ}
    (h : RD code ee g s0 ⟨4127⟩ stk mem (UInt256.ofNat 7) rdata acc k C)
    (hmem : mem.size = 196)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : stk.length + 5 ≤ 1024) :
    RDrev code g s0 := by
  have rdMload := evm_run h with [
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 7) (by clipper_runtime_decode)
      mem_cost
      (mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64)
      (by decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by clipper_runtime_decode)
    (by evm_ov)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw mstore 0 (solcErrorStringMem0 mem)
      (UInt256.ofNat 7) (by clipper_runtime_decode) mem_cost (by rfl)
      (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨4⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw mstore 0 (solcErrorStringMem1 mem)
      (UInt256.ofNat 7) (by clipper_runtime_decode) mem_cost (by rfl)
      (by decide) (by evm_ov),
    raw push1 ⟨27⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨36⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw mstore 0 (solcErrorStringMem2 ⟨27⟩ mem)
      (UInt256.ofNat 7) (by clipper_runtime_decode) mem_cost (by rfl)
      (by decide) (by evm_ov)]
  have rdRaw := rdPrefix.pushConst clipperTakeNoPartialPurchaseRawWord
    (width := 32) (op := .PUSH32) (by decide)
    (by clipper_runtime_decode)
    (by evm_ov)
  exact evm_run rdRaw with [
    raw push1 ⟨68⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw mstore 3
      (solcErrorStringMem3 ⟨27⟩ clipperTakeNoPartialPurchaseRawWord mem)
      (UInt256.ofNat 8) (by clipper_runtime_decode) mem_cost (by rfl)
      (by decide) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by clipper_runtime_decode)
      mem_cost
      (solcErrorStringMem3_mload64_of_size196 ⟨27⟩
        clipperTakeNoPartialPurchaseRawWord hmem hread64)
      (by decide) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨100⟩ (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw rev 0 (by clipper_runtime_decode) mem_cost (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem RD.clipperTakeOweLtTabSliceLtLotNoPartialPurchaseReverts {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {price slice tab lot tic packed stopped dataLen dataStart who max amt id : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {k C : ℕ}
    (h : RD code ee g s0 ⟨4057⟩
      (UInt256.mul price slice :: slice :: ⟨0⟩ :: tab :: lot ::
        price :: tic :: packed :: stopped :: dataLen :: dataStart :: who ::
        max :: amt :: id :: R)
      mem (UInt256.ofNat 7) rdata (cA, σ) k C)
    (hle : (UInt256.mul price slice).toNat ≤ tab.toNat)
    (hlt : (UInt256.mul price slice).toNat < tab.toNat)
    (hsliceLt : slice.toNat < lot.toNat)
    (hremainingLt : (UInt256.sub tab (UInt256.mul price slice)).toNat <
      (solcSlotWord σ ee ⟨9⟩).toNat)
    (htabLeChost : tab.toNat ≤ (solcSlotWord σ ee ⟨9⟩).toNat)
    (hmem : mem.size = 196)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 30 ≤ 1024) :
    RDrev code g s0 := by
  have hgtWord : UInt256.gt (UInt256.mul price slice) tab = ⟨0⟩ := ugt_zero hle
  have hltWord : UInt256.lt (UInt256.mul price slice) tab = ⟨1⟩ := ult_one hlt
  have hsliceLtWord : UInt256.lt slice lot = ⟨1⟩ := ult_one hsliceLt
  have hchostGtWord :
      UInt256.gt (solcSlotWord σ ee ⟨9⟩)
        (UInt256.sub tab (UInt256.mul price slice)) = ⟨1⟩ :=
    ugt_one hremainingLt
  have htabChostWord : UInt256.gt tab (solcSlotWord σ ee ⟨9⟩) = ⟨0⟩ :=
    ugt_zero htabLeChost
  have rd4067pre := evm_run h with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw gt (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨4087⟩ (by clipper_runtime_decode) (by evm_ov)]
  rw [hgtWord] at rd4067pre
  have rd4087 := rd4067pre.jumpiT (by clipper_runtime_decode) (by decide)
    (clipperTakeJumpDest4087 v hpatch) (by evm_ov)
  have rd4096pre := evm_run rd4087 with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw lt (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨4101⟩ (by clipper_runtime_decode) (by evm_ov)]
  rw [hltWord] at rd4096pre
  have rd4097 := rd4096pre.jumpiNT (by clipper_runtime_decode) (by decide) (by evm_ov)
  have rd4101 := evm_run rd4097 with [
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw dup4 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw lt (by clipper_runtime_decode) (by evm_ov)]
  rw [hsliceLtWord] at rd4101
  have rd4106pre := evm_run rd4101 with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨4223⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd4107 := rd4106pre.jumpiNT (by clipper_runtime_decode) (by decide) (by evm_ov)
  have rd4109pre := evm_run rd4107 with [raw push1 ⟨9⟩ (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨_, _, rd4110raw⟩ := rd4109pre.sload (by clipper_runtime_decode) (by evm_ov)
  have rd4119pre := evm_run rd4110raw with [
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw dup5 (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw gt (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨4221⟩ (by clipper_runtime_decode) (by evm_ov)]
  rw [hchostGtWord] at rd4119pre
  have rd4120 := rd4119pre.jumpiNT (by clipper_runtime_decode) (by decide) (by evm_ov)
  have rd4126pre := evm_run rd4120 with [
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw dup5 (by clipper_runtime_decode) (by evm_ov),
    raw gt (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨4203⟩ (by clipper_runtime_decode) (by evm_ov)]
  rw [htabChostWord] at rd4126pre
  have rd4127 := rd4126pre.jumpiNT (by clipper_runtime_decode) (by decide) (by evm_ov)
  apply RD.clipperTakeNoPartialPurchaseRevertTail v hpatch rd4127 hmem hread64
  simp only [List.length_cons, List.length_nil]
  omega

end Benchmarks.Dss.Clipper
