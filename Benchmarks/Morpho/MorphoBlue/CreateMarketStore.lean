import Benchmarks.Morpho.MorphoBlue.CreateMarketGuards
import Benchmarks.Morpho.MorphoBlue.MarketStorageBridge
import Benchmarks.Morpho.MorphoBlue.BorrowRateEncode

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def createMarketTimestampAccounts (σ : AccountMap) (I : ExecutionEnv)
    (p : MarketParamsWords) : AccountMap :=
  sstoreAccountMap I.codeOwner σ (marketFieldSlot p.id 4)
    (setUint128LowWord (solcSlotWordAt (marketFieldSlot p.id 4) σ I)
      (halfWord false (UInt256.ofNat I.header.timestamp)))

def createMarketAccounts (σ : AccountMap) (I : ExecutionEnv) (p : MarketParamsWords) : AccountMap :=
  storeMarketParamsAccounts (createMarketTimestampAccounts σ I p) I p.id p

theorem createMarketStored_bridge {s0 : State} {I : ExecutionEnv} {σ : AccountMap} {evm : State}
    (hs : SourceState s0 I σ evm) (p : MarketParamsWords) :
    SourceState s0 I (createMarketAccounts σ I p) (createMarketStored evm p) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [createMarketStored, storeMarketParams_world, storeMarketLastUpdate, storageStore_σ₀]
    exact hs.world
  · rw [createMarketStored, storeMarketParams_executionEnv, storeMarketLastUpdate_executionEnv]
    exact hs.env
  · rw [createMarketStored, storeMarketParams_accounts, storeMarketLastUpdate_accounts,
      storeMarketLastUpdate_executionEnv, hs.env, ← hs.accounts]
    rfl

def createMarketStoreMem (p : MarketParamsWords) : ByteArray :=
  writeWord (twoWordHashMem p.id (UInt256.ofNat 3) (createMarketUnusedMem p)) 32 (UInt256.ofNat 8)

theorem createMarketStoreHeap (p : MarketParamsWords) : CreateMarketHeap p 480 (createMarketStoreMem p) := by
  have hp := (createMarketUnusedHeap p).1.hash (by decide) p.id (UInt256.ofNat 3)
  constructor
  · rw [createMarketStoreMem, writeWord_size _ _ _ (by rw [hp.size]; exact lt_usize _ (by decide)), hp.size]
    rfl
  · rw [createMarketStoreMem, memLoad_writeWord_disjoint _ _ _ _
      (by rw [hp.size]; exact lt_usize _ (by decide)) (by rw [hp.size]; decide) (by right; decide)]
    exact hp.freePtr
  · exact hp.params.writeWord 32 (UInt256.ofNat 8) (by decide) (by rw [hp.size]; decide)
      (by rw [hp.size]; exact lt_usize _ (by decide)) (by right; decide)

def createMarketAddressPrefix (σ : AccountMap) (I : ExecutionEnv) (p : MarketParamsWords) : AccountMap :=
  storeAddressAccounts (storeAddressAccounts (createMarketTimestampAccounts σ I p) I
    (marketParamsFieldSlot p.id 0) p.loanToken) I (marketParamsFieldSlot p.id 1) p.collateralToken

theorem morphoCreateMarketStoreFirst {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    (p : MarketParamsWords) (hperm : ee.perm = true)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 4950)
      [uint128Mask, UInt256.ofNat 256, UInt256.ofNat 224, solcAddrMask, p.id,
       UInt256.ofNat 128, UInt256.ofNat 32, UInt256.ofNat 0]
      (createMarketUnusedMem p) aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 5087)
      [UInt256.ofNat 64, solcAddrMask, marketParamsFieldSlot p.id 2, UInt256.lnot solcAddrMask,
       UInt256.ofNat 256, UInt256.ofNat 4, solcMappingSlot ⟨8⟩ p.id,
       UInt256.ofNat 224, solcAddrMask, p.id, UInt256.ofNat 128, UInt256.ofNat 32, UInt256.ofNat 0]
      (createMarketStoreMem p) aw' rdata (createMarketAddressPrefix σ ee p) k' C' := by
  have hp := createMarketStoreHeap p
  have h0 : memLoad (UInt256.ofNat 128) (createMarketStoreMem p) = p.loanToken := by
    simpa only [MarketParamsWords.word, Nat.reduceMul,
      show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl, u256_add_zero] using hp.params ⟨0, by decide⟩
  have h1 : memLoad (UInt256.ofNat 128 + UInt256.ofNat 32) (createMarketStoreMem p) = p.collateralToken := by
    simpa only [MarketParamsWords.word] using hp.params ⟨1, by decide⟩
  have h3 : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      (twoWordHashMem p.id (UInt256.ofNat 3) (createMarketUnusedMem p)) = solcMappingSlot ⟨3⟩ p.id :=
    twoWordHashMem_solcMappingSlot_any _ _ _
  have h8 : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (createMarketStoreMem p) =
      solcMappingSlot ⟨8⟩ p.id :=
    twoWordHashMem_replaceSlot_hash _ _ _ _ (by rw [(createMarketUnusedHeap p).1.size]; decide)
  obtain ⟨aw1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_4950_packed
    (immWords := wordsOf (immStore v)) (by simp) hperm h
  simp only [morphoBlocks.morpho_block_4950_stack, morphoBlocks.morpho_block_4950_memory] at rd1
  change RD _ _ _ _ _
    [UInt256.ofNat 64, solcAddrMask,
     keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (createMarketStoreMem p) + UInt256.ofNat 2,
     UInt256.lnot solcAddrMask, UInt256.ofNat 256, UInt256.ofNat 4,
     keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (createMarketStoreMem p),
     UInt256.ofNat 224, solcAddrMask, p.id, UInt256.ofNat 128, UInt256.ofNat 32, UInt256.ofNat 0]
    (createMarketStoreMem p) _ _ _ _ _ at rd1
  have hm8 : (UInt256.ofNat 8).toByteArray.write 0
      ((UInt256.ofNat 3).toByteArray.write 0
        (p.id.toByteArray.write 0 (createMarketUnusedMem p) (UInt256.ofNat 0).toNat 32)
        (UInt256.ofNat 32).toNat 32) (UInt256.ofNat 32).toNat 32 = createMarketStoreMem p := rfl
  have hm3 : (UInt256.ofNat 3).toByteArray.write 0
      (p.id.toByteArray.write 0 (createMarketUnusedMem p) (UInt256.ofNat 0).toNat 32)
      (UInt256.ofNat 32).toNat 32 =
        twoWordHashMem p.id (UInt256.ofNat 3) (createMarketUnusedMem p) := rfl
  rw [hm8, hm3, h8, h3, h0, h1] at rd1
  refine ⟨aw1, k1, C1, ?_⟩
  simpa only [createMarketAddressPrefix, createMarketTimestampAccounts, storeAddressAccounts,
    setAddressOffset0Word, setUint128LowWord, halfWord, marketParamsFieldSlot, marketFieldSlot,
    solcSlotWordAt, solcSlotWord, h3, h8, h0, h1, ↓reduceIte, Nat.reduceDiv,
    show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl, u256_add_zero] using rd1

def createMarketEventMem (p : MarketParamsWords) : ByteArray :=
  marketParamsMem p (UInt256.ofNat 480) (createMarketStoreMem p)

def createMarketLogStack (p : MarketParamsWords) : List UInt256 :=
  [UInt256.ofNat 480, UInt256.ofNat 160,
   UInt256.ofNat 77930571974472193577215730001454066985566282397930517691434906231634542363564,
   p.id, UInt256.ofNat 224, solcAddrMask, p.id,
   UInt256.ofNat 128, UInt256.ofNat 32, UInt256.ofNat 0]

theorem createMarketEventMemory (p : MarketParamsWords) :
    (createMarketEventMem p).size = 640 ∧
    memLoad (UInt256.ofNat 64) (createMarketEventMem p) = UInt256.ofNat 480 ∧
    p.InMemory (UInt256.ofNat 128) (createMarketEventMem p) := by
  have hp := createMarketStoreHeap p
  have hg : (UInt256.ofNat 480).toNat + 160 - (createMarketStoreMem p).size < USize.size := by
    rw [hp.size]; exact lt_usize _ (by decide)
  refine ⟨?_, ?_, hp.params.copyAfter p (by decide) (by decide)
    (by rw [hp.size]; decide) (by decide) (by rw [hp.size]; exact lt_usize _ (by decide))⟩
  · rw [createMarketEventMem, marketParamsMem_size p _ _ (by decide) hg, hp.size]
    rfl
  · rw [createMarketEventMem, marketParamsMem_asWordWrites p _ _ (by decide),
      memLoad_writeReturnWords_below _ _ _ _ (by rw [hp.size]; exact lt_usize _ (by decide))
        (by rw [hp.size]; decide) (by decide), hp.freePtr]

theorem morphoCreateMarketStoreRest {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    (p : MarketParamsWords) (hc : p.Canonical) (hperm : ee.perm = true)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 5087)
      [UInt256.ofNat 64, solcAddrMask, marketParamsFieldSlot p.id 2, UInt256.lnot solcAddrMask,
       UInt256.ofNat 256, UInt256.ofNat 4, solcMappingSlot ⟨8⟩ p.id,
       UInt256.ofNat 224, solcAddrMask, p.id, UInt256.ofNat 128, UInt256.ofNat 32, UInt256.ofNat 0]
      (createMarketStoreMem p) aw rdata (createMarketAddressPrefix σ ee p) k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 5234)
      (createMarketLogStack p) (createMarketEventMem p) aw' rdata (createMarketAccounts σ ee p) k' C' := by
  have hp := createMarketStoreHeap p
  let m1 := writeWord (createMarketStoreMem p) (UInt256.ofNat 480).toNat p.loanToken
  let m2 := writeWord m1 (UInt256.ofNat 480 + UInt256.ofNat 32).toNat p.collateralToken
  have hs1 : m1.size = 512 := by
    rw [writeWord_size _ _ _ (by rw [hp.size]; exact lt_usize _ (by decide)), hp.size]; rfl
  have hs2 : m2.size = 544 := by
    rw [writeWord_size _ _ _ (by rw [hs1]; exact lt_usize _ (by decide)), hs1]; rfl
  have hr1 : p.InMemory (UInt256.ofNat 128) m1 := hp.params.writeWord _ _ (by decide)
    (by rw [hp.size]; decide) (by rw [hp.size]; exact lt_usize _ (by decide)) (by left; decide)
  have hr2 : p.InMemory (UInt256.ofNat 128) m2 := hr1.writeWord _ _ (by decide)
    (by rw [hs1]; decide) (by rw [hs1]; exact lt_usize _ (by decide)) (by left; decide)
  have h0 := hp.params ⟨0, by decide⟩
  have h1 := hr1 ⟨1, by decide⟩
  have h2 := hr2 ⟨2, by decide⟩
  have ho := hp.params ⟨2, by decide⟩
  have hi := hp.params ⟨3, by decide⟩
  have hl := hp.params ⟨4, by decide⟩
  simp only [MarketParamsWords.word, Nat.reduceMul,
    show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl, u256_add_zero] at h0 h1 h2 ho hi hl
  change memLoad (UInt256.ofNat 224) (createMarketStoreMem p) = p.irm at hi
  change memLoad (UInt256.ofNat 256) (createMarketStoreMem p) = p.lltv at hl
  dsimp only [m2, m1, Reasoning.Theory.writeWord] at h1 h2
  obtain ⟨aw1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_5087_packed
    (immWords := wordsOf (immStore v)) (by simp) hperm h
  simp only [morphoBlocks.morpho_block_5087_stack, morphoBlocks.morpho_block_5087_memory,
    hp.freePtr, show UInt256.ofNat 1461501637330902918203684832716283019655932542975 = solcAddrMask from rfl,
    h0, solcAddrMask_clean hc.1, h1, solcAddrMask_clean hc.2.1,
    h2, solcAddrMask_clean hc.2.2.1, ho, hi, hl] at rd1
  have rd1' : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 5212)
      ([p.oracle, solcAddrMask, UInt256.ofNat 128, UInt256.ofNat 128, UInt256.ofNat 128,
        UInt256.ofNat 480, UInt256.ofNat 5234] ++ createMarketLogStack p)
      m2 aw1 rdata (createMarketAccounts σ ee p) k1 C1 := by
    simpa only [createMarketAccounts, storeMarketParamsAccounts, createMarketAddressPrefix,
      storeAddressAccounts, setAddressOffset0Word, marketParamsFieldSlot, solcSlotWordAt, solcSlotWord,
      solcAddrMask_clean hc.1, solcAddrMask_clean hc.2.1,
      solcAddrMask_clean hc.2.2.1, solcAddrMask_clean hc.2.2.2] using rd1
  obtain ⟨aw2, k2, C2, rd2⟩ := morphoBlocks.morpho_block_5212_packed
    (immWords := wordsOf (immStore v)) (by simp [createMarketLogStack])
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd1'
  have hcopy := morphoMarketParamsCopyMemory p (UInt256.ofNat 128) (UInt256.ofNat 480)
    (createMarketStoreMem p) hc hp.params (by decide) (by decide) (by rw [hp.size]; decide)
    (by decide) (by rw [hp.size]; exact lt_usize _ (by decide))
  simp only [morphoBlocks.morpho_block_12367_memory,
    show UInt256.ofNat 1461501637330902918203684832716283019655932542975 = solcAddrMask from rfl,
    h0, solcAddrMask_clean hc.1, h1, solcAddrMask_clean hc.2.1,
    h2, solcAddrMask_clean hc.2.2.1] at hcopy
  have hmem : morphoBlocks.morpho_block_5212_memory (mem := m2) (x0 := p.oracle)
      (x1 := solcAddrMask) (x2 := UInt256.ofNat 128) (x3 := UInt256.ofNat 128)
      (x4 := UInt256.ofNat 128) (x5 := UInt256.ofNat 480) = createMarketEventMem p := hcopy
  rw [hmem] at rd2
  exact ⟨aw2, k2, C2, rd2⟩

end Benchmarks.Morpho.MorphoBlue
