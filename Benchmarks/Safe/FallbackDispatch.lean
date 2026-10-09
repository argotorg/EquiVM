import Benchmarks.Safe.SelectorMiss
import Benchmarks.Safe.Blocks.Runtime_005

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

def safeSelectorWords : List UInt256 :=
  [
    ⟨0xffa1ad74⟩, ⟨0x0d582f13⟩, ⟨0xd4d9bdcd⟩, ⟨0x7d832974⟩, ⟨0x694e80c3⟩, ⟨0x12fb68e0⟩,
    ⟨0x1fcac7f3⟩, ⟨0x934f3a11⟩, ⟨0xf855438b⟩, ⟨0xe009cfde⟩, ⟨0xf698da25⟩, ⟨0x610b5925⟩,
    ⟨0x6a761202⟩, ⟨0x468721a7⟩, ⟨0x5229073f⟩, ⟨0xcc2f8452⟩, ⟨0xa0e67e2b⟩, ⟨0x5624b25b⟩,
    ⟨0xe75235b8⟩, ⟨0xd8d11f78⟩, ⟨0x2d9ad53d⟩, ⟨0x2f54bf6e⟩, ⟨0xaffed0e0⟩, ⟨0xf8dc5dd9⟩,
    ⟨0xf08a0323⟩, ⟨0xe19a9dd9⟩, ⟨0xe068df37⟩, ⟨0xb63e800d⟩, ⟨0x5ae6bd37⟩, ⟨0xb4faba09⟩,
    ⟨0xe318b52b⟩]

theorem safeSelectorMisses {I : ExecutionEnv}
    (hd : selectorDispatchMsg contract I.calldata = none) (hlong : 4 ≤ I.calldata.size) :
    ∀ w ∈ safeSelectorWords, UInt256.eq w (selWord I) = ⟨0⟩ := by
  intro w hw
  simp only [safeSelectorWords, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact selectorMissWord 0xff 0xa1 0xad 0x74 ⟨0xffa1ad74⟩ hd
      (List.getElem_mem (l := contract.transitions) (n := 0) (by decide))
      hlong versionSelectorBytes (by decide)
  · exact selectorMissWord 0x0d 0x58 0x2f 0x13 ⟨0x0d582f13⟩ hd
      (List.getElem_mem (l := contract.transitions) (n := 1) (by decide))
      hlong addownerwiththresholdSelectorBytes (by decide)
  · exact selectorMissWord 0xd4 0xd9 0xbd 0xcd ⟨0xd4d9bdcd⟩ hd
      (List.getElem_mem (l := contract.transitions) (n := 2) (by decide))
      hlong approvehashSelectorBytes (by decide)
  · exact selectorMissWord 0x7d 0x83 0x29 0x74 ⟨0x7d832974⟩ hd
      (List.getElem_mem (l := contract.transitions) (n := 3) (by decide))
      hlong approvedhashesSelectorBytes (by decide)
  · exact selectorMissWord 0x69 0x4e 0x80 0xc3 ⟨0x694e80c3⟩ hd
      (List.getElem_mem (l := contract.transitions) (n := 4) (by decide))
      hlong changethresholdSelectorBytes (by decide)
  · exact selectorMissWord 0x12 0xfb 0x68 0xe0 ⟨0x12fb68e0⟩ hd
      (List.getElem_mem (l := contract.transitions) (n := 5) (by decide))
      hlong checknsignaturesSelectorBytes (by decide)
  · exact selectorMissWord 0x1f 0xca 0xc7 0xf3 ⟨0x1fcac7f3⟩ hd
      (List.getElem_mem (l := contract.transitions) (n := 6) (by decide))
      hlong checknsignaturesAddressBytes32BytesUint256SelectorBytes (by decide)
  · exact selectorMissWord 0x93 0x4f 0x3a 0x11 ⟨0x934f3a11⟩ hd
      (List.getElem_mem (l := contract.transitions) (n := 7) (by decide))
      hlong checksignaturesSelectorBytes (by decide)
  · exact selectorMissWord 0xf8 0x55 0x43 0x8b ⟨0xf855438b⟩ hd
      (List.getElem_mem (l := contract.transitions) (n := 8) (by decide))
      hlong checksignaturesAddressBytes32BytesSelectorBytes (by decide)
  · exact selectorMissWord 0xe0 0x09 0xcf 0xde ⟨0xe009cfde⟩ hd
      (List.getElem_mem (l := contract.transitions) (n := 9) (by decide))
      hlong disablemoduleSelectorBytes (by decide)
  · exact selectorMissWord 0xf6 0x98 0xda 0x25 ⟨0xf698da25⟩ hd
      (List.getElem_mem (l := contract.transitions) (n := 10) (by decide))
      hlong domainseparatorSelectorBytes (by decide)
  · exact selectorMissWord 0x61 0x0b 0x59 0x25 ⟨0x610b5925⟩ hd
      (List.getElem_mem (l := contract.transitions) (n := 11) (by decide))
      hlong enablemoduleSelectorBytes (by decide)
  · exact selectorMissWord 0x6a 0x76 0x12 0x02 ⟨0x6a761202⟩ hd
      (List.getElem_mem (l := contract.transitions) (n := 12) (by decide))
      hlong exectransactionSelectorBytes (by decide)
  · exact selectorMissWord 0x46 0x87 0x21 0xa7 ⟨0x468721a7⟩ hd
      (List.getElem_mem (l := contract.transitions) (n := 13) (by decide))
      hlong exectransactionfrommoduleSelectorBytes (by decide)
  · exact selectorMissWord 0x52 0x29 0x07 0x3f ⟨0x5229073f⟩ hd
      (List.getElem_mem (l := contract.transitions) (n := 14) (by decide))
      hlong exectransactionfrommodulereturndataSelectorBytes (by decide)
  · exact selectorMissWord 0xcc 0x2f 0x84 0x52 ⟨0xcc2f8452⟩ hd
      (List.getElem_mem (l := contract.transitions) (n := 15) (by decide))
      hlong getmodulespaginatedSelectorBytes (by decide)
  · exact selectorMissWord 0xa0 0xe6 0x7e 0x2b ⟨0xa0e67e2b⟩ hd
      (List.getElem_mem (l := contract.transitions) (n := 16) (by decide))
      hlong getownersSelectorBytes (by decide)
  · exact selectorMissWord 0x56 0x24 0xb2 0x5b ⟨0x5624b25b⟩ hd
      (List.getElem_mem (l := contract.transitions) (n := 17) (by decide))
      hlong getstorageatSelectorBytes (by decide)
  · exact selectorMissWord 0xe7 0x52 0x35 0xb8 ⟨0xe75235b8⟩ hd
      (List.getElem_mem (l := contract.transitions) (n := 18) (by decide))
      hlong getthresholdSelectorBytes (by decide)
  · exact selectorMissWord 0xd8 0xd1 0x1f 0x78 ⟨0xd8d11f78⟩ hd
      (List.getElem_mem (l := contract.transitions) (n := 19) (by decide))
      hlong gettransactionhashSelectorBytes (by decide)
  · exact selectorMissWord 0x2d 0x9a 0xd5 0x3d ⟨0x2d9ad53d⟩ hd
      (List.getElem_mem (l := contract.transitions) (n := 20) (by decide))
      hlong ismoduleenabledSelectorBytes (by decide)
  · exact selectorMissWord 0x2f 0x54 0xbf 0x6e ⟨0x2f54bf6e⟩ hd
      (List.getElem_mem (l := contract.transitions) (n := 21) (by decide))
      hlong isownerSelectorBytes (by decide)
  · exact selectorMissWord 0xaf 0xfe 0xd0 0xe0 ⟨0xaffed0e0⟩ hd
      (List.getElem_mem (l := contract.transitions) (n := 22) (by decide))
      hlong nonceSelectorBytes (by decide)
  · exact selectorMissWord 0xf8 0xdc 0x5d 0xd9 ⟨0xf8dc5dd9⟩ hd
      (List.getElem_mem (l := contract.transitions) (n := 23) (by decide))
      hlong removeownerSelectorBytes (by decide)
  · exact selectorMissWord 0xf0 0x8a 0x03 0x23 ⟨0xf08a0323⟩ hd
      (List.getElem_mem (l := contract.transitions) (n := 24) (by decide))
      hlong setfallbackhandlerSelectorBytes (by decide)
  · exact selectorMissWord 0xe1 0x9a 0x9d 0xd9 ⟨0xe19a9dd9⟩ hd
      (List.getElem_mem (l := contract.transitions) (n := 25) (by decide))
      hlong setguardSelectorBytes (by decide)
  · exact selectorMissWord 0xe0 0x68 0xdf 0x37 ⟨0xe068df37⟩ hd
      (List.getElem_mem (l := contract.transitions) (n := 26) (by decide))
      hlong setmoduleguardSelectorBytes (by decide)
  · exact selectorMissWord 0xb6 0x3e 0x80 0x0d ⟨0xb63e800d⟩ hd
      (List.getElem_mem (l := contract.transitions) (n := 27) (by decide))
      hlong setupSelectorBytes (by decide)
  · exact selectorMissWord 0x5a 0xe6 0xbd 0x37 ⟨0x5ae6bd37⟩ hd
      (List.getElem_mem (l := contract.transitions) (n := 28) (by decide))
      hlong signedmessagesSelectorBytes (by decide)
  · exact selectorMissWord 0xb4 0xfa 0xba 0x09 ⟨0xb4faba09⟩ hd
      (List.getElem_mem (l := contract.transitions) (n := 29) (by decide))
      hlong simulateandrevertSelectorBytes (by decide)
  · exact selectorMissWord 0xe3 0x18 0xb5 0x2b ⟨0xe318b52b⟩ hd
      (List.getElem_mem (l := contract.transitions) (n := 30) (by decide))
      hlong swapownerSelectorBytes (by decide)

def safeMissCertificate (start : UInt256) (n : Nat) (stop : UInt256) : Prop :=
  (∀ j : Fin n, armWellFormed safeBytecode (nthArmPc safeBytecode start j)) ∧
  (∀ j : Fin n, armSelNat safeBytecode (nthArmPc safeBytecode start j) ∈
    safeSelectorWords) ∧
  nthArmPc safeBytecode start n = stop

set_option synthInstance.maxSize 10000 in
instance (start : UInt256) (n : Nat) (stop : UInt256) :
    Decidable (safeMissCertificate start n stop) := by
  unfold safeMissCertificate
  infer_instance

theorem safeSkipSelectorGroup {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {R : List UInt256} {start : UInt256} {k C : Nat} (n : Nat) (stop : UInt256)
    (h : RD safeBytecode I g s0 start (selWord I :: R) mem aw rdata σ k C)
    (hm : ∀ w ∈ safeSelectorWords, UInt256.eq w (selWord I) = ⟨0⟩)
    (hc : safeMissCertificate start n stop) (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', RD safeBytecode I g s0 stop (selWord I :: R) mem aw rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := skipSelectorArms n h (fun j hj ↦ hc.1 ⟨j, hj⟩)
    (fun j hj ↦ hm _ (hc.2.1 ⟨j, hj⟩)) hov
  exact ⟨k', C', hc.2.2 ▸ h'⟩

theorem safeSelectorStart_mem (w : UInt256) :
    safeSelectorStart w ∈ [⟨51⟩, ⟨100⟩, ⟨160⟩, ⟨209⟩, ⟨280⟩, ⟨329⟩, ⟨389⟩, ⟨438⟩] := by
  unfold safeSelectorStart
  split <;> split <;> split <;> simp

set_option maxRecDepth 100000 in
theorem safeReachFallbackLong {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = safeBytecode) (hsize : I.calldata.size < UInt256.size)
    (hlong : 4 ≤ I.calldata.size) (hd : selectorDispatchMsg contract I.calldata = none) :
    ∃ k C, RD safeBytecode I g (initState σ σ₀ g A I) ⟨535⟩ [selWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  obtain ⟨k, C, h⟩ := safeReachSelectorGroup (σ := σ) (σ₀ := σ₀) (A := A)
    (g := g) hcode hsize hlong
  have hm := safeSelectorMisses hd hlong
  have hs := safeSelectorStart_mem (selWord I)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with hs | hs | hs | hs | hs | hs | hs | hs
  · rw [hs] at h
    obtain ⟨k', C', h'⟩ := safeSkipSelectorGroup 4 ⟨95⟩ h hm
      (by native_decide) (by decide)
    exact ⟨_, _, safeRuntime_block_95 (by evm_ov) (by jump_dest) h'⟩
  · rw [hs] at h
    obtain ⟨k', C', h'⟩ := safeSkipSelectorGroup 4 ⟨144⟩ h hm
      (by native_decide) (by decide)
    exact ⟨_, _, safeRuntime_block_144 (by evm_ov) (by jump_dest) h'⟩
  · rw [hs] at h
    obtain ⟨k', C', h'⟩ := safeSkipSelectorGroup 4 ⟨204⟩ h hm
      (by native_decide) (by decide)
    exact ⟨_, _, safeRuntime_block_204 (by evm_ov) (by jump_dest) h'⟩
  · rw [hs] at h
    obtain ⟨k', C', h'⟩ := safeSkipSelectorGroup 4 ⟨253⟩ h hm
      (by native_decide) (by decide)
    exact ⟨_, _, safeRuntime_block_253 (by evm_ov) (by jump_dest) h'⟩
  · rw [hs] at h
    obtain ⟨k', C', h'⟩ := safeSkipSelectorGroup 4 ⟨324⟩ h hm
      (by native_decide) (by decide)
    exact ⟨_, _, safeRuntime_block_324 (by evm_ov) (by jump_dest) h'⟩
  · rw [hs] at h
    obtain ⟨k', C', h'⟩ := safeSkipSelectorGroup 4 ⟨373⟩ h hm
      (by native_decide) (by decide)
    exact ⟨_, _, safeRuntime_block_373 (by evm_ov) (by jump_dest) h'⟩
  · rw [hs] at h
    obtain ⟨k', C', h'⟩ := safeSkipSelectorGroup 4 ⟨433⟩ h hm
      (by native_decide) (by decide)
    exact ⟨_, _, safeRuntime_block_433 (by evm_ov) (by jump_dest) h'⟩
  · rw [hs] at h
    obtain ⟨k', C', h'⟩ := safeSkipSelectorGroup 3 ⟨471⟩ h hm
      (by native_decide) (by decide)
    exact ⟨_, _, safeRuntime_block_471 (by evm_ov) (by jump_dest) h'⟩

set_option maxRecDepth 100000 in
theorem safeReachFallback {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = safeBytecode) (hsize : I.calldata.size < UInt256.size)
    (hnonempty : I.calldata.size ≠ 0) (hd : selectorDispatchMsg contract I.calldata = none) :
    ∃ R k C, R.length ≤ 1 ∧
      RD safeBytecode I g (initState σ σ₀ g A I) ⟨535⟩ R
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  by_cases hlong : 4 ≤ I.calldata.size
  · obtain ⟨k, C, h⟩ := safeReachFallbackLong (σ := σ) (σ₀ := σ₀) (A := A)
      (g := g) hcode hsize hlong hd
    exact ⟨_, k, C, by simp, h⟩
  · obtain ⟨k, C, h⟩ := safeReachShort (σ := σ) (σ₀ := σ₀) (A := A)
      (g := g) hcode (by omega)
    have hn : UInt256.ofNat I.calldata.size ≠ UInt256.ofNat 0 := by
      intro he
      have he' := congrArg UInt256.toNat he
      rw [ulit_toNat' _ hsize] at he'
      exact hnonempty he'
    exact ⟨[], _, _, by decide,
      safeRuntime_block_475_taken (by decide) hn (by jump_dest) h⟩

end Benchmarks.Safe
