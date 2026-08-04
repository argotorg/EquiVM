import Examples.Ripemd160Old.DecodeGenerated.Chunk16

open Ethereum Ethereum.EVM

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

private def generatedDecodes17 :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨2466⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨2467⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨2468⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2469⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨2470⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨2471⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨2472⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨2473⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1))),
  (⟨2475⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨2476⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨2477⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨2478⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2479⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2480⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2457⟩, 2))),
  (⟨2483⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨2484⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨2485⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2486⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨2487⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2488⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨2489⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨2490⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨2491⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨2492⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1))),
  (⟨2494⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨2495⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨2496⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨2497⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2498⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2499⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2457⟩, 2))),
  (⟨2502⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨2503⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨2504⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2505⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨2506⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2507⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨2508⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨2509⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨2510⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨2511⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1))),
  (⟨2513⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨2514⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨2515⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨2516⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2517⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2518⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2457⟩, 2))),
  (⟨2521⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨2522⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨2523⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2524⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨2525⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2526⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨2527⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨2528⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨2529⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨2530⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1))),
  (⟨2532⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨2533⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨2534⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨2535⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2536⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2537⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2457⟩, 2))),
  (⟨2540⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨2541⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨2542⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2543⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨2544⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2545⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨2546⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨2547⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨2548⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨2549⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1))),
  (⟨2551⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨2552⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨2553⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨2554⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2555⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2556⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2457⟩, 2))),
  (⟨2559⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨2560⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨2561⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2562⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨2563⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2564⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨2565⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨2566⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨2567⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨2568⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1))),
  (⟨2570⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨2571⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨2572⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨2573⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2574⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2575⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2457⟩, 2))),
  (⟨2578⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨2579⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨2580⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2581⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨2582⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2583⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none))
]

private theorem generatedDecodes17_correct : ∀ i : Fin generatedDecodes17.size,
    decode runtimeBytecode generatedDecodes17[i].1 = generatedDecodes17[i].2 := by
  native_decide

theorem decode_2466 : decode runtimeBytecode ⟨2466⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨0, by decide⟩
theorem decode_2467 : decode runtimeBytecode ⟨2467⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨1, by decide⟩
theorem decode_2468 : decode runtimeBytecode ⟨2468⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨2, by decide⟩
theorem decode_2469 : decode runtimeBytecode ⟨2469⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨3, by decide⟩
theorem decode_2470 : decode runtimeBytecode ⟨2470⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨4, by decide⟩
theorem decode_2471 : decode runtimeBytecode ⟨2471⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨5, by decide⟩
theorem decode_2472 : decode runtimeBytecode ⟨2472⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨6, by decide⟩
theorem decode_2473 : decode runtimeBytecode ⟨2473⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1)) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨7, by decide⟩
theorem decode_2475 : decode runtimeBytecode ⟨2475⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨8, by decide⟩
theorem decode_2476 : decode runtimeBytecode ⟨2476⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨9, by decide⟩
theorem decode_2477 : decode runtimeBytecode ⟨2477⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨10, by decide⟩
theorem decode_2478 : decode runtimeBytecode ⟨2478⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨11, by decide⟩
theorem decode_2479 : decode runtimeBytecode ⟨2479⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨12, by decide⟩
theorem decode_2480 : decode runtimeBytecode ⟨2480⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2457⟩, 2)) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨13, by decide⟩
theorem decode_2483 : decode runtimeBytecode ⟨2483⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨14, by decide⟩
theorem decode_2484 : decode runtimeBytecode ⟨2484⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨15, by decide⟩
theorem decode_2485 : decode runtimeBytecode ⟨2485⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨16, by decide⟩
theorem decode_2486 : decode runtimeBytecode ⟨2486⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨17, by decide⟩
theorem decode_2487 : decode runtimeBytecode ⟨2487⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨18, by decide⟩
theorem decode_2488 : decode runtimeBytecode ⟨2488⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨19, by decide⟩
theorem decode_2489 : decode runtimeBytecode ⟨2489⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨20, by decide⟩
theorem decode_2490 : decode runtimeBytecode ⟨2490⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨21, by decide⟩
theorem decode_2491 : decode runtimeBytecode ⟨2491⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨22, by decide⟩
theorem decode_2492 : decode runtimeBytecode ⟨2492⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1)) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨23, by decide⟩
theorem decode_2494 : decode runtimeBytecode ⟨2494⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨24, by decide⟩
theorem decode_2495 : decode runtimeBytecode ⟨2495⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨25, by decide⟩
theorem decode_2496 : decode runtimeBytecode ⟨2496⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨26, by decide⟩
theorem decode_2497 : decode runtimeBytecode ⟨2497⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨27, by decide⟩
theorem decode_2498 : decode runtimeBytecode ⟨2498⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨28, by decide⟩
theorem decode_2499 : decode runtimeBytecode ⟨2499⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2457⟩, 2)) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨29, by decide⟩
theorem decode_2502 : decode runtimeBytecode ⟨2502⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨30, by decide⟩
theorem decode_2503 : decode runtimeBytecode ⟨2503⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨31, by decide⟩
theorem decode_2504 : decode runtimeBytecode ⟨2504⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨32, by decide⟩
theorem decode_2505 : decode runtimeBytecode ⟨2505⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨33, by decide⟩
theorem decode_2506 : decode runtimeBytecode ⟨2506⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨34, by decide⟩
theorem decode_2507 : decode runtimeBytecode ⟨2507⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨35, by decide⟩
theorem decode_2508 : decode runtimeBytecode ⟨2508⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨36, by decide⟩
theorem decode_2509 : decode runtimeBytecode ⟨2509⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨37, by decide⟩
theorem decode_2510 : decode runtimeBytecode ⟨2510⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨38, by decide⟩
theorem decode_2511 : decode runtimeBytecode ⟨2511⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1)) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨39, by decide⟩
theorem decode_2513 : decode runtimeBytecode ⟨2513⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨40, by decide⟩
theorem decode_2514 : decode runtimeBytecode ⟨2514⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨41, by decide⟩
theorem decode_2515 : decode runtimeBytecode ⟨2515⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨42, by decide⟩
theorem decode_2516 : decode runtimeBytecode ⟨2516⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨43, by decide⟩
theorem decode_2517 : decode runtimeBytecode ⟨2517⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨44, by decide⟩
theorem decode_2518 : decode runtimeBytecode ⟨2518⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2457⟩, 2)) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨45, by decide⟩
theorem decode_2521 : decode runtimeBytecode ⟨2521⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨46, by decide⟩
theorem decode_2522 : decode runtimeBytecode ⟨2522⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨47, by decide⟩
theorem decode_2523 : decode runtimeBytecode ⟨2523⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨48, by decide⟩
theorem decode_2524 : decode runtimeBytecode ⟨2524⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨49, by decide⟩
theorem decode_2525 : decode runtimeBytecode ⟨2525⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨50, by decide⟩
theorem decode_2526 : decode runtimeBytecode ⟨2526⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨51, by decide⟩
theorem decode_2527 : decode runtimeBytecode ⟨2527⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨52, by decide⟩
theorem decode_2528 : decode runtimeBytecode ⟨2528⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨53, by decide⟩
theorem decode_2529 : decode runtimeBytecode ⟨2529⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨54, by decide⟩
theorem decode_2530 : decode runtimeBytecode ⟨2530⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1)) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨55, by decide⟩
theorem decode_2532 : decode runtimeBytecode ⟨2532⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨56, by decide⟩
theorem decode_2533 : decode runtimeBytecode ⟨2533⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨57, by decide⟩
theorem decode_2534 : decode runtimeBytecode ⟨2534⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨58, by decide⟩
theorem decode_2535 : decode runtimeBytecode ⟨2535⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨59, by decide⟩
theorem decode_2536 : decode runtimeBytecode ⟨2536⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨60, by decide⟩
theorem decode_2537 : decode runtimeBytecode ⟨2537⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2457⟩, 2)) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨61, by decide⟩
theorem decode_2540 : decode runtimeBytecode ⟨2540⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨62, by decide⟩
theorem decode_2541 : decode runtimeBytecode ⟨2541⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨63, by decide⟩
theorem decode_2542 : decode runtimeBytecode ⟨2542⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨64, by decide⟩
theorem decode_2543 : decode runtimeBytecode ⟨2543⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨65, by decide⟩
theorem decode_2544 : decode runtimeBytecode ⟨2544⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨66, by decide⟩
theorem decode_2545 : decode runtimeBytecode ⟨2545⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨67, by decide⟩
theorem decode_2546 : decode runtimeBytecode ⟨2546⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨68, by decide⟩
theorem decode_2547 : decode runtimeBytecode ⟨2547⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨69, by decide⟩
theorem decode_2548 : decode runtimeBytecode ⟨2548⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨70, by decide⟩
theorem decode_2549 : decode runtimeBytecode ⟨2549⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1)) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨71, by decide⟩
theorem decode_2551 : decode runtimeBytecode ⟨2551⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨72, by decide⟩
theorem decode_2552 : decode runtimeBytecode ⟨2552⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨73, by decide⟩
theorem decode_2553 : decode runtimeBytecode ⟨2553⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨74, by decide⟩
theorem decode_2554 : decode runtimeBytecode ⟨2554⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨75, by decide⟩
theorem decode_2555 : decode runtimeBytecode ⟨2555⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨76, by decide⟩
theorem decode_2556 : decode runtimeBytecode ⟨2556⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2457⟩, 2)) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨77, by decide⟩
theorem decode_2559 : decode runtimeBytecode ⟨2559⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨78, by decide⟩
theorem decode_2560 : decode runtimeBytecode ⟨2560⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨79, by decide⟩
theorem decode_2561 : decode runtimeBytecode ⟨2561⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨80, by decide⟩
theorem decode_2562 : decode runtimeBytecode ⟨2562⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨81, by decide⟩
theorem decode_2563 : decode runtimeBytecode ⟨2563⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨82, by decide⟩
theorem decode_2564 : decode runtimeBytecode ⟨2564⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨83, by decide⟩
theorem decode_2565 : decode runtimeBytecode ⟨2565⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨84, by decide⟩
theorem decode_2566 : decode runtimeBytecode ⟨2566⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨85, by decide⟩
theorem decode_2567 : decode runtimeBytecode ⟨2567⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨86, by decide⟩
theorem decode_2568 : decode runtimeBytecode ⟨2568⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1)) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨87, by decide⟩
theorem decode_2570 : decode runtimeBytecode ⟨2570⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨88, by decide⟩
theorem decode_2571 : decode runtimeBytecode ⟨2571⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨89, by decide⟩
theorem decode_2572 : decode runtimeBytecode ⟨2572⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨90, by decide⟩
theorem decode_2573 : decode runtimeBytecode ⟨2573⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨91, by decide⟩
theorem decode_2574 : decode runtimeBytecode ⟨2574⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨92, by decide⟩
theorem decode_2575 : decode runtimeBytecode ⟨2575⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2457⟩, 2)) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨93, by decide⟩
theorem decode_2578 : decode runtimeBytecode ⟨2578⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨94, by decide⟩
theorem decode_2579 : decode runtimeBytecode ⟨2579⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨95, by decide⟩
theorem decode_2580 : decode runtimeBytecode ⟨2580⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨96, by decide⟩
theorem decode_2581 : decode runtimeBytecode ⟨2581⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨97, by decide⟩
theorem decode_2582 : decode runtimeBytecode ⟨2582⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨98, by decide⟩
theorem decode_2583 : decode runtimeBytecode ⟨2583⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes17] using generatedDecodes17_correct ⟨99, by decide⟩

end Ripemd160Old
