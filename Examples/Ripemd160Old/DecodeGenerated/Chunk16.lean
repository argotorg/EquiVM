import Examples.Ripemd160Old.DecodeGenerated.Chunk15

open Ethereum Ethereum.EVM

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

private def generatedDecodes16 :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨2315⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨2316⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨2317⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2318⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2319⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2011⟩, 2))),
  (⟨2322⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨2323⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨2324⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2325⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨16⟩, 1))),
  (⟨2327⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨2328⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨2329⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP4), none)),
  (⟨2330⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2331⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.MOD), none)),
  (⟨2332⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨2333⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none)),
  (⟨2334⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨2335⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2750⟩, 2))),
  (⟨2338⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨2339⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨2340⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1))),
  (⟨2342⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨2343⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2731⟩, 2))),
  (⟨2346⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨2347⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨2348⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1))),
  (⟨2350⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨2351⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2712⟩, 2))),
  (⟨2354⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨2355⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨2356⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1))),
  (⟨2358⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨2359⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2693⟩, 2))),
  (⟨2362⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨2363⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨2364⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1))),
  (⟨2366⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨2367⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2674⟩, 2))),
  (⟨2370⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨2371⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨2372⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1))),
  (⟨2374⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨2375⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2655⟩, 2))),
  (⟨2378⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨2379⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨2380⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1))),
  (⟨2382⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨2383⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2636⟩, 2))),
  (⟨2386⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨2387⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨2388⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1))),
  (⟨2390⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨2391⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2617⟩, 2))),
  (⟨2394⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨2395⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨2396⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1))),
  (⟨2398⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨2399⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2598⟩, 2))),
  (⟨2402⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨2403⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨2404⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1))),
  (⟨2406⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨2407⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2579⟩, 2))),
  (⟨2410⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨2411⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨2412⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP15), none)),
  (⟨2413⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨2414⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2560⟩, 2))),
  (⟨2417⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨2418⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨2419⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1))),
  (⟨2421⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨2422⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2541⟩, 2))),
  (⟨2425⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨2426⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨2427⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1))),
  (⟨2429⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨2430⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2522⟩, 2))),
  (⟨2433⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨2434⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨2435⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1))),
  (⟨2437⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨2438⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2503⟩, 2))),
  (⟨2441⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨2442⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨2443⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1))),
  (⟨2445⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨2446⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2484⟩, 2))),
  (⟨2449⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨2450⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1))),
  (⟨2452⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨2453⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2466⟩, 2))),
  (⟨2456⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨2457⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨2458⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨2459⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨2460⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨2461⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none)),
  (⟨2462⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨494⟩, 2))),
  (⟨2465⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none))
]

private theorem generatedDecodes16_correct : ∀ i : Fin generatedDecodes16.size,
    decode runtimeBytecode generatedDecodes16[i].1 = generatedDecodes16[i].2 := by
  native_decide

theorem decode_2315 : decode runtimeBytecode ⟨2315⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨0, by decide⟩
theorem decode_2316 : decode runtimeBytecode ⟨2316⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨1, by decide⟩
theorem decode_2317 : decode runtimeBytecode ⟨2317⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨2, by decide⟩
theorem decode_2318 : decode runtimeBytecode ⟨2318⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨3, by decide⟩
theorem decode_2319 : decode runtimeBytecode ⟨2319⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2011⟩, 2)) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨4, by decide⟩
theorem decode_2322 : decode runtimeBytecode ⟨2322⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨5, by decide⟩
theorem decode_2323 : decode runtimeBytecode ⟨2323⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨6, by decide⟩
theorem decode_2324 : decode runtimeBytecode ⟨2324⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨7, by decide⟩
theorem decode_2325 : decode runtimeBytecode ⟨2325⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨16⟩, 1)) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨8, by decide⟩
theorem decode_2327 : decode runtimeBytecode ⟨2327⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨9, by decide⟩
theorem decode_2328 : decode runtimeBytecode ⟨2328⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨10, by decide⟩
theorem decode_2329 : decode runtimeBytecode ⟨2329⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP4), none) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨11, by decide⟩
theorem decode_2330 : decode runtimeBytecode ⟨2330⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨12, by decide⟩
theorem decode_2331 : decode runtimeBytecode ⟨2331⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.MOD), none) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨13, by decide⟩
theorem decode_2332 : decode runtimeBytecode ⟨2332⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨14, by decide⟩
theorem decode_2333 : decode runtimeBytecode ⟨2333⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨15, by decide⟩
theorem decode_2334 : decode runtimeBytecode ⟨2334⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨16, by decide⟩
theorem decode_2335 : decode runtimeBytecode ⟨2335⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2750⟩, 2)) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨17, by decide⟩
theorem decode_2338 : decode runtimeBytecode ⟨2338⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨18, by decide⟩
theorem decode_2339 : decode runtimeBytecode ⟨2339⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨19, by decide⟩
theorem decode_2340 : decode runtimeBytecode ⟨2340⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1)) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨20, by decide⟩
theorem decode_2342 : decode runtimeBytecode ⟨2342⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨21, by decide⟩
theorem decode_2343 : decode runtimeBytecode ⟨2343⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2731⟩, 2)) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨22, by decide⟩
theorem decode_2346 : decode runtimeBytecode ⟨2346⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨23, by decide⟩
theorem decode_2347 : decode runtimeBytecode ⟨2347⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨24, by decide⟩
theorem decode_2348 : decode runtimeBytecode ⟨2348⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1)) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨25, by decide⟩
theorem decode_2350 : decode runtimeBytecode ⟨2350⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨26, by decide⟩
theorem decode_2351 : decode runtimeBytecode ⟨2351⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2712⟩, 2)) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨27, by decide⟩
theorem decode_2354 : decode runtimeBytecode ⟨2354⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨28, by decide⟩
theorem decode_2355 : decode runtimeBytecode ⟨2355⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨29, by decide⟩
theorem decode_2356 : decode runtimeBytecode ⟨2356⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1)) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨30, by decide⟩
theorem decode_2358 : decode runtimeBytecode ⟨2358⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨31, by decide⟩
theorem decode_2359 : decode runtimeBytecode ⟨2359⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2693⟩, 2)) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨32, by decide⟩
theorem decode_2362 : decode runtimeBytecode ⟨2362⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨33, by decide⟩
theorem decode_2363 : decode runtimeBytecode ⟨2363⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨34, by decide⟩
theorem decode_2364 : decode runtimeBytecode ⟨2364⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1)) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨35, by decide⟩
theorem decode_2366 : decode runtimeBytecode ⟨2366⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨36, by decide⟩
theorem decode_2367 : decode runtimeBytecode ⟨2367⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2674⟩, 2)) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨37, by decide⟩
theorem decode_2370 : decode runtimeBytecode ⟨2370⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨38, by decide⟩
theorem decode_2371 : decode runtimeBytecode ⟨2371⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨39, by decide⟩
theorem decode_2372 : decode runtimeBytecode ⟨2372⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1)) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨40, by decide⟩
theorem decode_2374 : decode runtimeBytecode ⟨2374⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨41, by decide⟩
theorem decode_2375 : decode runtimeBytecode ⟨2375⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2655⟩, 2)) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨42, by decide⟩
theorem decode_2378 : decode runtimeBytecode ⟨2378⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨43, by decide⟩
theorem decode_2379 : decode runtimeBytecode ⟨2379⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨44, by decide⟩
theorem decode_2380 : decode runtimeBytecode ⟨2380⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1)) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨45, by decide⟩
theorem decode_2382 : decode runtimeBytecode ⟨2382⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨46, by decide⟩
theorem decode_2383 : decode runtimeBytecode ⟨2383⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2636⟩, 2)) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨47, by decide⟩
theorem decode_2386 : decode runtimeBytecode ⟨2386⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨48, by decide⟩
theorem decode_2387 : decode runtimeBytecode ⟨2387⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨49, by decide⟩
theorem decode_2388 : decode runtimeBytecode ⟨2388⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1)) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨50, by decide⟩
theorem decode_2390 : decode runtimeBytecode ⟨2390⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨51, by decide⟩
theorem decode_2391 : decode runtimeBytecode ⟨2391⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2617⟩, 2)) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨52, by decide⟩
theorem decode_2394 : decode runtimeBytecode ⟨2394⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨53, by decide⟩
theorem decode_2395 : decode runtimeBytecode ⟨2395⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨54, by decide⟩
theorem decode_2396 : decode runtimeBytecode ⟨2396⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1)) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨55, by decide⟩
theorem decode_2398 : decode runtimeBytecode ⟨2398⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨56, by decide⟩
theorem decode_2399 : decode runtimeBytecode ⟨2399⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2598⟩, 2)) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨57, by decide⟩
theorem decode_2402 : decode runtimeBytecode ⟨2402⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨58, by decide⟩
theorem decode_2403 : decode runtimeBytecode ⟨2403⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨59, by decide⟩
theorem decode_2404 : decode runtimeBytecode ⟨2404⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1)) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨60, by decide⟩
theorem decode_2406 : decode runtimeBytecode ⟨2406⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨61, by decide⟩
theorem decode_2407 : decode runtimeBytecode ⟨2407⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2579⟩, 2)) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨62, by decide⟩
theorem decode_2410 : decode runtimeBytecode ⟨2410⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨63, by decide⟩
theorem decode_2411 : decode runtimeBytecode ⟨2411⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨64, by decide⟩
theorem decode_2412 : decode runtimeBytecode ⟨2412⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP15), none) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨65, by decide⟩
theorem decode_2413 : decode runtimeBytecode ⟨2413⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨66, by decide⟩
theorem decode_2414 : decode runtimeBytecode ⟨2414⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2560⟩, 2)) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨67, by decide⟩
theorem decode_2417 : decode runtimeBytecode ⟨2417⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨68, by decide⟩
theorem decode_2418 : decode runtimeBytecode ⟨2418⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨69, by decide⟩
theorem decode_2419 : decode runtimeBytecode ⟨2419⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1)) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨70, by decide⟩
theorem decode_2421 : decode runtimeBytecode ⟨2421⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨71, by decide⟩
theorem decode_2422 : decode runtimeBytecode ⟨2422⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2541⟩, 2)) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨72, by decide⟩
theorem decode_2425 : decode runtimeBytecode ⟨2425⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨73, by decide⟩
theorem decode_2426 : decode runtimeBytecode ⟨2426⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨74, by decide⟩
theorem decode_2427 : decode runtimeBytecode ⟨2427⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1)) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨75, by decide⟩
theorem decode_2429 : decode runtimeBytecode ⟨2429⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨76, by decide⟩
theorem decode_2430 : decode runtimeBytecode ⟨2430⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2522⟩, 2)) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨77, by decide⟩
theorem decode_2433 : decode runtimeBytecode ⟨2433⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨78, by decide⟩
theorem decode_2434 : decode runtimeBytecode ⟨2434⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨79, by decide⟩
theorem decode_2435 : decode runtimeBytecode ⟨2435⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1)) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨80, by decide⟩
theorem decode_2437 : decode runtimeBytecode ⟨2437⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨81, by decide⟩
theorem decode_2438 : decode runtimeBytecode ⟨2438⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2503⟩, 2)) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨82, by decide⟩
theorem decode_2441 : decode runtimeBytecode ⟨2441⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨83, by decide⟩
theorem decode_2442 : decode runtimeBytecode ⟨2442⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨84, by decide⟩
theorem decode_2443 : decode runtimeBytecode ⟨2443⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1)) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨85, by decide⟩
theorem decode_2445 : decode runtimeBytecode ⟨2445⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨86, by decide⟩
theorem decode_2446 : decode runtimeBytecode ⟨2446⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2484⟩, 2)) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨87, by decide⟩
theorem decode_2449 : decode runtimeBytecode ⟨2449⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨88, by decide⟩
theorem decode_2450 : decode runtimeBytecode ⟨2450⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1)) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨89, by decide⟩
theorem decode_2452 : decode runtimeBytecode ⟨2452⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨90, by decide⟩
theorem decode_2453 : decode runtimeBytecode ⟨2453⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2466⟩, 2)) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨91, by decide⟩
theorem decode_2456 : decode runtimeBytecode ⟨2456⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨92, by decide⟩
theorem decode_2457 : decode runtimeBytecode ⟨2457⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨93, by decide⟩
theorem decode_2458 : decode runtimeBytecode ⟨2458⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨94, by decide⟩
theorem decode_2459 : decode runtimeBytecode ⟨2459⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨95, by decide⟩
theorem decode_2460 : decode runtimeBytecode ⟨2460⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨96, by decide⟩
theorem decode_2461 : decode runtimeBytecode ⟨2461⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨97, by decide⟩
theorem decode_2462 : decode runtimeBytecode ⟨2462⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨494⟩, 2)) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨98, by decide⟩
theorem decode_2465 : decode runtimeBytecode ⟨2465⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes16] using generatedDecodes16_correct ⟨99, by decide⟩

end Ripemd160Old
