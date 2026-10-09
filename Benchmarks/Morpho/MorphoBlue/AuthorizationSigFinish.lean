import Benchmarks.Morpho.MorphoBlue.AuthorizationSigVerification
import Benchmarks.Morpho.MorphoBlue.WordCallOutputMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000



def authorizationFinalAccounts (a : AuthorizationWords) (σ : AccountMap) (ee : ExecutionEnv) : AccountMap :=
  sstoreAccountMap ee.codeOwner σ (authorizationSlot a.authorizer a.authorized)
    (setBoolOffset0Word (solcSlotWordAt (authorizationSlot a.authorizer a.authorized) σ ee) a.enabled)

theorem morphoAuthorizationFinish {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (a : AuthorizationWords) (hc : a.Canonical) (ho : EcrecoverOutput out)
    (hstack : R.length + 24 ≤ 1024) (hperm : ee.perm = true)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 6527) (authorizationVerifiedTail R)
      (authorizationVerifiedMem v a ee.calldata out) aw out σ k C) :
    RDret (deployedRuntime v) g s0 (authorizationFinalAccounts a σ ee) ByteArray.empty := by
  let mem := authorizationVerifiedMem v a ee.calldata out
  have hp := authorizationVerifiedMem_properties v a ee.calldata out ho
  have hn : memLoad (UInt256.ofNat 224) mem = a.nonce := hp.2.1 ⟨3, by decide⟩
  let m := writeWord mem 832 a.nonce
  have hm : a.InMemory m := hp.2.1.prefix
    (memoryPrefix_sparse_writeWord mem 832 288 a.nonce (Or.inl (by decide))) le_rfl (by omega)
  have hs : m.size = 896 := by
    dsimp only [m]
    rw [writeWord_size _ _ _ (by rw [hp.1]; exact USize.size_pos), hp.1]; rfl
  have ha : memLoad (UInt256.ofNat 128) m = a.authorizer := hm ⟨0, by decide⟩
  have hb : memLoad (UInt256.ofNat 160) (twoWordHashMem a.authorizer (UInt256.ofNat 6) m) =
      a.authorized := (hm.hash (by omega) _ _) ⟨1, by decide⟩
  have he : memLoad (UInt256.ofNat 192) m = a.enabled := hm ⟨2, by decide⟩
  have hma := solcAddrMask_clean hc.1
  have hmb := solcAddrMask_clean hc.2.1
  have hbool : UInt256.isZero (UInt256.isZero a.enabled) = a.enabled := (boolWordClean_iff _).mpr hc.2.2
  have hbyte : UInt256.land a.enabled (UInt256.ofNat 255) = a.enabled := by
    apply u256LandMaskCleanOfToNat (bits := 8) _ _ (by decide)
    rcases hc.2.2 with hz | ho
    · rw [hz]; decide
    · rw [ho]; decide
  obtain ⟨k1, C1, r1⟩ := morphoBlocks.morpho_block_6527 (immWords := wordsOf (immStore v))
    (by change R.length + 14 ≤ 1024; omega) hperm
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  have ret := morphoBlocks.morpho_block_6659 (immWords := wordsOf (immStore v))
    (by change R.length + 8 ≤ 1024; omega) hperm r1
  simp only [show (UInt256.ofNat 0).toNat = 0 from rfl, byteArray_readWithPadding_zero] at ret
  rw [hn, hp.2.2.1] at ret
  let key0 := UInt256.land (memLoad (UInt256.ofNat 128) m) solcAddrMask
  let m0 := twoWordHashMem key0 (UInt256.ofNat 6) m
  let key1 := UInt256.land (memLoad (UInt256.ofNat 160) m0) solcAddrMask
  let slot0 := keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) m0
  let slot := keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (twoWordHashMem key1 slot0 m0)
  change RDret _ _ _ (sstoreAccountMap ee.codeOwner σ slot
    (UInt256.lor (UInt256.land (UInt256.isZero (UInt256.isZero
      (UInt256.isZero (UInt256.isZero (memLoad (UInt256.ofNat 192) m))))) (UInt256.ofNat 255))
      (UInt256.land (solcSlotWordAt slot σ ee)
        (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639680))))
    ByteArray.empty at ret
  have hash (key base : UInt256) (memory : ByteArray) :
      keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (twoWordHashMem key base memory) =
        solcMappingSlot base key := twoWordHashMem_solcMappingSlot_any _ _ _
  have hslot : slot = authorizationSlot a.authorizer a.authorized := by
    dsimp only [slot, key1, slot0, m0, key0]
    rw [ha, hma, hb, hmb, hash, hash]
    rfl
  rw [hslot, he, hbool, hbool, hbyte] at ret
  have hmask : UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639680 =
      UInt256.lnot (⟨255⟩ : UInt256) := by decide
  simpa only [authorizationFinalAccounts, authorizationSlot, setBoolOffset0Word, hbool,
    hmask, u256_lor_comm] using ret

end Benchmarks.Morpho.MorphoBlue
