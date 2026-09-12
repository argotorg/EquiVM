import Benchmarks.Dss.Clipper.KickIncentiveEVM
import Benchmarks.Dss.Clipper.RedoTailEVM

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

theorem clipperKickEventMem0_size_192 {mem : ByteArray} (top : UInt256)
    (hmem : mem.size = 192) : (clipperRedoEventMem0 mem top).size = 192 := by
  unfold clipperRedoEventMem0
  exact toByteArray_write32_size_of_le mem top 128 192 192 hmem
    (by rw [hmem]; omega) (by native_decide)

theorem clipperKickEventMem1_size_192 {mem : ByteArray} (top tab : UInt256)
    (hmem : mem.size = 192) : (clipperRedoEventMem1 mem top tab).size = 192 := by
  unfold clipperRedoEventMem1
  exact toByteArray_write32_size_of_le (clipperRedoEventMem0 mem top) tab
    160 192 192 (clipperKickEventMem0_size_192 top hmem)
    (by rw [clipperKickEventMem0_size_192 top hmem]; omega) (by native_decide)

theorem clipperKickEventMem2_size_192 {mem : ByteArray} (top tab lot : UInt256)
    (hmem : mem.size = 192) : (clipperRedoEventMem2 mem top tab lot).size = 224 := by
  unfold clipperRedoEventMem2
  exact toByteArray_write32_size_of_le (clipperRedoEventMem1 mem top tab) lot
    192 192 224 (clipperKickEventMem1_size_192 top tab hmem)
    (by rw [clipperKickEventMem1_size_192 top tab hmem]) (by native_decide)

theorem clipperKickEventMem_size_192 {mem : ByteArray}
    (top tab lot coin : UInt256) (hmem : mem.size = 192) :
    (clipperRedoEventMem mem top tab lot coin).size = 256 := by
  unfold clipperRedoEventMem
  exact toByteArray_write32_size_of_le (clipperRedoEventMem2 mem top tab lot) coin
    224 224 256 (clipperKickEventMem2_size_192 top tab lot hmem)
    (by rw [clipperKickEventMem2_size_192 top tab lot hmem]) (by native_decide)

theorem clipperKickEventMem_read64_192 {mem : ByteArray}
    (top tab lot coin : UInt256) (hmem : mem.size = 192)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (clipperRedoEventMem mem top tab lot coin).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold clipperRedoEventMem clipperRedoEventMem2 clipperRedoEventMem1
    clipperRedoEventMem0
  rw [toByteArray_write_read_below_of_gap coin _ 224 64
    (by rw [clipperKickEventMem2_size_192 top tab lot hmem]; omega)
    (by omega)
    (by rw [clipperKickEventMem2_size_192 top tab lot hmem]; native_decide)]
  rw [toByteArray_write_read_below_of_gap lot _ 192 64
    (by rw [clipperKickEventMem1_size_192 top tab hmem]; omega)
    (by omega)
    (by rw [clipperKickEventMem1_size_192 top tab hmem]; native_decide)]
  rw [toByteArray_write_read_below_of_gap tab _ 160 64
    (by rw [clipperKickEventMem0_size_192 top hmem]; omega)
    (by omega)
    (by rw [clipperKickEventMem0_size_192 top hmem]; native_decide)]
  rw [toByteArray_write_read_below_of_gap top _ 128 64
    (by rw [hmem]; omega) (by omega) (by rw [hmem]; native_decide)]
  exact hread64

set_option maxHeartbeats 1000000 in
theorem RD.clipperKickReturnWordFromMem8 {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {val ret : UInt256} {R : List UInt256} {mem rdata : ByteArray} {k C : ℕ}
    (rd : RD code ee g s0 ⟨476⟩ (val :: ret :: R) mem (UInt256.ofNat 8)
      rdata acc k C)
    (hmem : mem.size = 256)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 5 ≤ 1024) :
    RDret code g s0 acc (UInt256.toByteArray val) := by
  let memout : ByteArray := val.toByteArray.write 0 mem 128 32
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨
          (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (mem := mem) (aw := UInt256.ofNat 8)
      (by rw [hmem]; norm_num) (by native_decide) hread64
  have hmemoutSize : memout.size = 256 := by
    unfold memout
    exact toByteArray_write32_size_of_le mem val 128 256 256 hmem
      (by rw [hmem]; omega) (by native_decide)
  have hmemoutRead64 : memout.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    unfold memout
    rw [toByteArray_write_read_below_of_gap val mem 128 64
      (by rw [hmem]; omega) (by omega) (by rw [hmem]; native_decide)]
    exact hread64
  have hmloadOut64 :
      (if (⟨64⟩ : UInt256).toNat ≥ memout.size ∨
          (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (memout.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (mem := memout) (aw := UInt256.ofNat 8)
      (by rw [hmemoutSize]; norm_num) (by native_decide) hmemoutRead64
  have hread128 : memout.readWithPadding 128 32 = UInt256.toByteArray val := by
    unfold memout
    rw [toByteArray_write_read_back_of_gap val mem 128 (by rw [hmem]; native_decide)]
  rcases clipperReturnWord476Wf v hpatch with
    ⟨hd0, hd1, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10, hd11, hd12, hd13, hd15,
      hd16, hd17⟩
  exact evm_run rd with [
    raw jumpdest hd0 (by evm_ov),
    raw push1 ⟨64⟩ hd1 (by evm_ov),
    raw dup1 hd3 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) hd4 mem_cost hmload64 (by decide) (by evm_ov),
    raw swap2 hd5 (by evm_ov),
    raw dup3 hd6 (by evm_ov),
    raw mstore 0 memout (UInt256.ofNat 8) hd7 mem_cost (by rfl)
      (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) hd8 mem_cost hmloadOut64 (by decide)
      (by evm_ov),
    raw swap1 hd9 (by evm_ov),
    raw dup2 hd10 (by evm_ov),
    raw swap1 hd11 (by evm_ov),
    raw sub hd12 (by evm_ov),
    raw push1 ⟨32⟩ hd13 (by evm_ov),
    raw add hd15 (by evm_ov),
    raw swap1 hd16 (by evm_ov),
    raw ret 0 (UInt256.toByteArray val) hd17 mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show ((⟨32⟩ : UInt256) + UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩).toNat = 32
            from by decide]
        exact hread128)
      (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem RD.clipperKickEventUnlockReturnFrom228 {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {coin chip tip top id kpr usr lot tab sel : UInt256}
    {R : List UInt256} {mem out : ByteArray} {k C : ℕ}
    (rd : RD code ee g s0 ⟨6394⟩
      (coin :: chip :: tip :: top :: ⟨1⟩ :: id :: kpr :: usr :: lot :: tab :: ⟨476⟩ ::
        sel :: R)
      mem (UInt256.ofNat 8) out (cA, σ) k C)
    (hmem : mem.size = 228)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hperm : ee.perm = true) (hov : R.length + 50 ≤ 1024) :
    RDret code g s0 (cA, sstoreAccountMap ee.codeOwner σ ⟨13⟩ ⟨0⟩)
      (UInt256.toByteArray id) := by
  let eventTopic : UInt256 :=
    ⟨0x7c5bfdc0a5e8192f6cd4972f382cec69116862fb62e6abff8003874c58e064b8⟩
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨
          (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (mem := mem) (aw := UInt256.ofNat 8)
      (by rw [hmem]; norm_num) (by native_decide) hread64
  have rdMemPre := evm_run rd with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov)]
  have rdMem := rdMemPre.mload 0 ⟨128⟩ (UInt256.ofNat 8)
    (by clipper_runtime_decode) mem_cost hmload64 (by native_decide) (by evm_ov)
  have rdTopPre := evm_run rdMem with [
    raw dup6 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov)]
  have rdTop := rdTopPre.mstore 0 (clipperRedoEventMem0 mem top)
    (UInt256.ofNat 8) (by clipper_runtime_decode) mem_cost
    (by rfl) (by native_decide) (by evm_ov)
  have rdTabPre := evm_run rdTop with [
    raw push1 ⟨32⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw dup13 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov)]
  have rdTab := rdTabPre.mstore 0 (clipperRedoEventMem1 mem top tab)
    (UInt256.ofNat 8) (by clipper_runtime_decode) mem_cost
    (by
      rw [show ((⟨128⟩ : UInt256) + ⟨32⟩).toNat = 160 from by native_decide])
    (by native_decide) (by evm_ov)
  have rdLotPre0 := evm_run rdTab with [
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov)]
  have rdLotPre1 := RD.clipperRedoDup12 rdLotPre0 (by clipper_runtime_decode)
    (by simp only [List.length_cons]; omega)
  have rdLotPre := evm_run rdLotPre1 with [
    raw swap1 (by clipper_runtime_decode) (by evm_ov)]
  have rdLot := rdLotPre.mstore 0 (clipperRedoEventMem2 mem top tab lot)
    (UInt256.ofNat 8) (by clipper_runtime_decode) mem_cost
    (by
      rw [show ((⟨64⟩ : UInt256) + ⟨128⟩).toNat = 192 from by native_decide])
    (by native_decide) (by evm_ov)
  have rdCoinPre := evm_run rdLot with [
    raw push1 ⟨96⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw dup4 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov)]
  have rdCoin := rdCoinPre.mstore 0 (clipperRedoEventMem mem top tab lot coin)
    (UInt256.ofNat 8) (by clipper_runtime_decode) mem_cost
    (by
      rw [show ((⟨128⟩ : UInt256) + ⟨96⟩).toNat = 224 from by native_decide])
    (by native_decide) (by evm_ov)
  have hmemEvent : (clipperRedoEventMem mem top tab lot coin).size = 256 :=
    clipperRedoEventMem_size top tab lot coin hmem
  have hreadEvent :
      (clipperRedoEventMem mem top tab lot coin).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    clipperRedoEventMem_read64 top tab lot coin hmem hread64
  have hmloadEvent64 :
      (if (⟨64⟩ : UInt256).toNat ≥ (clipperRedoEventMem mem top tab lot coin).size ∨
          (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
          ((clipperRedoEventMem mem top tab lot coin).readWithPadding 64 32))) = ⟨128⟩ :=
    mloadFreePtrValue (mem := clipperRedoEventMem mem top tab lot coin)
      (aw := UInt256.ofNat 8) (by rw [hmemEvent]; norm_num) (by native_decide) hreadEvent
  have rdMloadPre := rdCoin.swap1 (by clipper_runtime_decode) (by evm_ov)
  have rdMload := rdMloadPre.mload 0 ⟨128⟩ (UInt256.ofNat 8)
    (by clipper_runtime_decode) mem_cost hmloadEvent64 (by native_decide) (by evm_ov)
  have rdTopicPre0 := evm_run rdMload with [
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw dup11 (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw swap3 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov)]
  have rdTopicPre1 := RD.clipperRedoDup12 rdTopicPre0 (by clipper_runtime_decode)
    (by simp only [List.length_cons]; omega)
  have rdTopicPre := evm_run rdTopicPre1 with [
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw dup10 (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov)]
  have rdTopic := rdTopicPre.pushConst eventTopic
    (width := 32) (op := .PUSH32) (by decide)
    (by simpa [eventTopic] using
      (show decode code ⟨6442⟩ = some (.PUSH32, some (eventTopic, 32)) by
        clipper_runtime_decode))
    (by evm_ov)
  have rdLogPre := evm_run rdTopic with [
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨128⟩ (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov)]
  have rdLog := RD.log4 0 (UInt256.ofNat 8) rdLogPre
    (by clipper_runtime_decode) hperm
    (by
      intro s hawEq hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hawEq, hstk]
      native_decide)
    (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdUnlockPre := evm_run rdLog with [
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨13⟩ (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨_, _, rdUnlock⟩ := rdUnlockPre.sstore hperm (by clipper_runtime_decode)
    (by simp only [List.length_cons]; omega)
  have rdReturn := evm_run rdUnlock with [
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw swap7 (by clipper_runtime_decode) (by evm_ov),
    raw swap6 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov)]
  have rd476 := rdReturn.jump (by clipper_runtime_decode)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨476⟩ : UInt256) (by native_decide))
    (by evm_ov)
  exact RD.clipperKickReturnWordFromMem8 v hpatch rd476 hmemEvent hreadEvent
    (by omega)

set_option maxHeartbeats 1000000 in
theorem RD.clipperKickEventUnlockReturnFrom192 {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {coin chip tip top id kpr usr lot tab sel : UInt256}
    {R : List UInt256} {mem out : ByteArray} {k C : ℕ}
    (rd : RD code ee g s0 ⟨6394⟩
      (coin :: chip :: tip :: top :: ⟨1⟩ :: id :: kpr :: usr :: lot :: tab :: ⟨476⟩ ::
        sel :: R)
      mem (UInt256.ofNat 6) out (cA, σ) k C)
    (hmem : mem.size = 192)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hperm : ee.perm = true) (hov : R.length + 50 ≤ 1024) :
    RDret code g s0 (cA, sstoreAccountMap ee.codeOwner σ ⟨13⟩ ⟨0⟩)
      (UInt256.toByteArray id) := by
  let eventTopic : UInt256 :=
    ⟨0x7c5bfdc0a5e8192f6cd4972f382cec69116862fb62e6abff8003874c58e064b8⟩
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨
          (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (mem := mem) (aw := UInt256.ofNat 6)
      (by rw [hmem]; norm_num) (by native_decide) hread64
  have rdMemPre := evm_run rd with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov)]
  have rdMem := rdMemPre.mload 0 ⟨128⟩ (UInt256.ofNat 6)
    (by clipper_runtime_decode) mem_cost hmload64 (by native_decide) (by evm_ov)
  have rdTopPre := evm_run rdMem with [
    raw dup6 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov)]
  have rdTop := rdTopPre.mstore 0 (clipperRedoEventMem0 mem top)
    (UInt256.ofNat 6) (by clipper_runtime_decode) mem_cost
    (by rfl) (by native_decide) (by evm_ov)
  have rdTabPre := evm_run rdTop with [
    raw push1 ⟨32⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw dup13 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov)]
  have rdTab := rdTabPre.mstore 0 (clipperRedoEventMem1 mem top tab)
    (UInt256.ofNat 6) (by clipper_runtime_decode) mem_cost
    (by rw [show ((⟨128⟩ : UInt256) + ⟨32⟩).toNat = 160 from by native_decide])
    (by native_decide) (by evm_ov)
  have rdLotPre0 := evm_run rdTab with [
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov)]
  have rdLotPre1 := RD.clipperRedoDup12 rdLotPre0 (by clipper_runtime_decode)
    (by simp only [List.length_cons]; omega)
  have rdLotPre := rdLotPre1.swap1 (by clipper_runtime_decode) (by evm_ov)
  have rdLot := rdLotPre.mstore 3 (clipperRedoEventMem2 mem top tab lot)
    (UInt256.ofNat 7) (by clipper_runtime_decode) mem_cost
    (by rw [show ((⟨64⟩ : UInt256) + ⟨128⟩).toNat = 192 from by native_decide])
    (by native_decide) (by evm_ov)
  have rdCoinPre := evm_run rdLot with [
    raw push1 ⟨96⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw dup4 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov)]
  have rdCoin := rdCoinPre.mstore 3 (clipperRedoEventMem mem top tab lot coin)
    (UInt256.ofNat 8) (by clipper_runtime_decode) mem_cost
    (by rw [show ((⟨128⟩ : UInt256) + ⟨96⟩).toNat = 224 from by native_decide])
    (by native_decide) (by evm_ov)
  have hmemEvent : (clipperRedoEventMem mem top tab lot coin).size = 256 :=
    clipperKickEventMem_size_192 top tab lot coin hmem
  have hreadEvent :
      (clipperRedoEventMem mem top tab lot coin).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    clipperKickEventMem_read64_192 top tab lot coin hmem hread64
  have hmloadEvent64 :
      (if (⟨64⟩ : UInt256).toNat ≥ (clipperRedoEventMem mem top tab lot coin).size ∨
          (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
          ((clipperRedoEventMem mem top tab lot coin).readWithPadding 64 32))) = ⟨128⟩ :=
    mloadFreePtrValue (mem := clipperRedoEventMem mem top tab lot coin)
      (aw := UInt256.ofNat 8) (by rw [hmemEvent]; norm_num) (by native_decide) hreadEvent
  have rdMloadPre := rdCoin.swap1 (by clipper_runtime_decode) (by evm_ov)
  have rdMload := rdMloadPre.mload 0 ⟨128⟩ (UInt256.ofNat 8)
    (by clipper_runtime_decode) mem_cost hmloadEvent64 (by native_decide) (by evm_ov)
  have rdTopicPre0 := evm_run rdMload with [
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw dup11 (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw swap3 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov)]
  have rdTopicPre1 := RD.clipperRedoDup12 rdTopicPre0 (by clipper_runtime_decode)
    (by simp only [List.length_cons]; omega)
  have rdTopicPre := evm_run rdTopicPre1 with [
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw dup10 (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov)]
  have rdTopic := rdTopicPre.pushConst eventTopic
    (width := 32) (op := .PUSH32) (by decide)
    (by simpa [eventTopic] using
      (show decode code ⟨6442⟩ = some (.PUSH32, some (eventTopic, 32)) by
        clipper_runtime_decode))
    (by evm_ov)
  have rdLogPre := evm_run rdTopic with [
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨128⟩ (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov)]
  have rdLog := RD.log4 0 (UInt256.ofNat 8) rdLogPre
    (by clipper_runtime_decode) hperm
    (by
      intro s hawEq hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hawEq, hstk]
      native_decide)
    (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdUnlockPre := evm_run rdLog with [
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨13⟩ (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨_, _, rdUnlock⟩ := rdUnlockPre.sstore hperm (by clipper_runtime_decode)
    (by simp only [List.length_cons]; omega)
  have rdReturn := evm_run rdUnlock with [
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw swap7 (by clipper_runtime_decode) (by evm_ov),
    raw swap6 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov)]
  have rd476 := rdReturn.jump (by clipper_runtime_decode)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨476⟩ : UInt256) (by native_decide))
    (by evm_ov)
  exact RD.clipperKickReturnWordFromMem8 v hpatch rd476 hmemEvent hreadEvent (by omega)

end Benchmarks.Dss.Clipper
