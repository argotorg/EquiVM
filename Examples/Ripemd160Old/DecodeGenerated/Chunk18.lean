import Examples.Ripemd160Old.DecodeGenerated.Chunk17

open Ethereum Ethereum.EVM

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

private def generatedDecodes18 :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨2584⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨2585⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨2586⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨2587⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1))),
  (⟨2589⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨2590⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨2591⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨2592⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2593⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2594⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2457⟩, 2))),
  (⟨2597⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨2598⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨2599⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2600⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨2601⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2602⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨2603⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨2604⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨2605⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨2606⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1))),
  (⟨2608⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨2609⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨2610⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨2611⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2612⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2613⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2457⟩, 2))),
  (⟨2616⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨2617⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨2618⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2619⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨2620⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2621⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨2622⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨2623⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨2624⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨2625⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1))),
  (⟨2627⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨2628⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨2629⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨2630⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2631⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2632⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2457⟩, 2))),
  (⟨2635⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨2636⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨2637⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2638⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨2639⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2640⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨2641⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨2642⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨2643⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨2644⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1))),
  (⟨2646⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨2647⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨2648⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨2649⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2650⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2651⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2457⟩, 2))),
  (⟨2654⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨2655⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨2656⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2657⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨2658⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2659⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨2660⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨2661⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨2662⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨2663⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1))),
  (⟨2665⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨2666⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨2667⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨2668⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2669⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2670⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2457⟩, 2))),
  (⟨2673⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨2674⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨2675⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2676⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨2677⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2678⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨2679⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨2680⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨2681⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨2682⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1))),
  (⟨2684⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨2685⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨2686⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨2687⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2688⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2689⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2457⟩, 2))),
  (⟨2692⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨2693⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨2694⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2695⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨2696⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨2697⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨2698⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨2699⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨2700⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨2701⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1)))
]

private theorem generatedDecodes18_correct : ∀ i : Fin generatedDecodes18.size,
    decode runtimeBytecode generatedDecodes18[i].1 = generatedDecodes18[i].2 := by
  native_decide

theorem decode_2584 : decode runtimeBytecode ⟨2584⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨0, by decide⟩
theorem decode_2585 : decode runtimeBytecode ⟨2585⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨1, by decide⟩
theorem decode_2586 : decode runtimeBytecode ⟨2586⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨2, by decide⟩
theorem decode_2587 : decode runtimeBytecode ⟨2587⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1)) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨3, by decide⟩
theorem decode_2589 : decode runtimeBytecode ⟨2589⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨4, by decide⟩
theorem decode_2590 : decode runtimeBytecode ⟨2590⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨5, by decide⟩
theorem decode_2591 : decode runtimeBytecode ⟨2591⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨6, by decide⟩
theorem decode_2592 : decode runtimeBytecode ⟨2592⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨7, by decide⟩
theorem decode_2593 : decode runtimeBytecode ⟨2593⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨8, by decide⟩
theorem decode_2594 : decode runtimeBytecode ⟨2594⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2457⟩, 2)) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨9, by decide⟩
theorem decode_2597 : decode runtimeBytecode ⟨2597⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨10, by decide⟩
theorem decode_2598 : decode runtimeBytecode ⟨2598⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨11, by decide⟩
theorem decode_2599 : decode runtimeBytecode ⟨2599⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨12, by decide⟩
theorem decode_2600 : decode runtimeBytecode ⟨2600⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨13, by decide⟩
theorem decode_2601 : decode runtimeBytecode ⟨2601⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨14, by decide⟩
theorem decode_2602 : decode runtimeBytecode ⟨2602⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨15, by decide⟩
theorem decode_2603 : decode runtimeBytecode ⟨2603⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨16, by decide⟩
theorem decode_2604 : decode runtimeBytecode ⟨2604⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨17, by decide⟩
theorem decode_2605 : decode runtimeBytecode ⟨2605⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨18, by decide⟩
theorem decode_2606 : decode runtimeBytecode ⟨2606⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1)) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨19, by decide⟩
theorem decode_2608 : decode runtimeBytecode ⟨2608⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨20, by decide⟩
theorem decode_2609 : decode runtimeBytecode ⟨2609⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨21, by decide⟩
theorem decode_2610 : decode runtimeBytecode ⟨2610⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨22, by decide⟩
theorem decode_2611 : decode runtimeBytecode ⟨2611⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨23, by decide⟩
theorem decode_2612 : decode runtimeBytecode ⟨2612⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨24, by decide⟩
theorem decode_2613 : decode runtimeBytecode ⟨2613⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2457⟩, 2)) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨25, by decide⟩
theorem decode_2616 : decode runtimeBytecode ⟨2616⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨26, by decide⟩
theorem decode_2617 : decode runtimeBytecode ⟨2617⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨27, by decide⟩
theorem decode_2618 : decode runtimeBytecode ⟨2618⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨28, by decide⟩
theorem decode_2619 : decode runtimeBytecode ⟨2619⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨29, by decide⟩
theorem decode_2620 : decode runtimeBytecode ⟨2620⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨30, by decide⟩
theorem decode_2621 : decode runtimeBytecode ⟨2621⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨31, by decide⟩
theorem decode_2622 : decode runtimeBytecode ⟨2622⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨32, by decide⟩
theorem decode_2623 : decode runtimeBytecode ⟨2623⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨33, by decide⟩
theorem decode_2624 : decode runtimeBytecode ⟨2624⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨34, by decide⟩
theorem decode_2625 : decode runtimeBytecode ⟨2625⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1)) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨35, by decide⟩
theorem decode_2627 : decode runtimeBytecode ⟨2627⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨36, by decide⟩
theorem decode_2628 : decode runtimeBytecode ⟨2628⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨37, by decide⟩
theorem decode_2629 : decode runtimeBytecode ⟨2629⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨38, by decide⟩
theorem decode_2630 : decode runtimeBytecode ⟨2630⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨39, by decide⟩
theorem decode_2631 : decode runtimeBytecode ⟨2631⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨40, by decide⟩
theorem decode_2632 : decode runtimeBytecode ⟨2632⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2457⟩, 2)) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨41, by decide⟩
theorem decode_2635 : decode runtimeBytecode ⟨2635⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨42, by decide⟩
theorem decode_2636 : decode runtimeBytecode ⟨2636⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨43, by decide⟩
theorem decode_2637 : decode runtimeBytecode ⟨2637⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨44, by decide⟩
theorem decode_2638 : decode runtimeBytecode ⟨2638⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨45, by decide⟩
theorem decode_2639 : decode runtimeBytecode ⟨2639⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨46, by decide⟩
theorem decode_2640 : decode runtimeBytecode ⟨2640⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨47, by decide⟩
theorem decode_2641 : decode runtimeBytecode ⟨2641⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨48, by decide⟩
theorem decode_2642 : decode runtimeBytecode ⟨2642⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨49, by decide⟩
theorem decode_2643 : decode runtimeBytecode ⟨2643⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨50, by decide⟩
theorem decode_2644 : decode runtimeBytecode ⟨2644⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1)) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨51, by decide⟩
theorem decode_2646 : decode runtimeBytecode ⟨2646⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨52, by decide⟩
theorem decode_2647 : decode runtimeBytecode ⟨2647⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨53, by decide⟩
theorem decode_2648 : decode runtimeBytecode ⟨2648⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨54, by decide⟩
theorem decode_2649 : decode runtimeBytecode ⟨2649⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨55, by decide⟩
theorem decode_2650 : decode runtimeBytecode ⟨2650⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨56, by decide⟩
theorem decode_2651 : decode runtimeBytecode ⟨2651⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2457⟩, 2)) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨57, by decide⟩
theorem decode_2654 : decode runtimeBytecode ⟨2654⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨58, by decide⟩
theorem decode_2655 : decode runtimeBytecode ⟨2655⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨59, by decide⟩
theorem decode_2656 : decode runtimeBytecode ⟨2656⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨60, by decide⟩
theorem decode_2657 : decode runtimeBytecode ⟨2657⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨61, by decide⟩
theorem decode_2658 : decode runtimeBytecode ⟨2658⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨62, by decide⟩
theorem decode_2659 : decode runtimeBytecode ⟨2659⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨63, by decide⟩
theorem decode_2660 : decode runtimeBytecode ⟨2660⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨64, by decide⟩
theorem decode_2661 : decode runtimeBytecode ⟨2661⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨65, by decide⟩
theorem decode_2662 : decode runtimeBytecode ⟨2662⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨66, by decide⟩
theorem decode_2663 : decode runtimeBytecode ⟨2663⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1)) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨67, by decide⟩
theorem decode_2665 : decode runtimeBytecode ⟨2665⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨68, by decide⟩
theorem decode_2666 : decode runtimeBytecode ⟨2666⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨69, by decide⟩
theorem decode_2667 : decode runtimeBytecode ⟨2667⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨70, by decide⟩
theorem decode_2668 : decode runtimeBytecode ⟨2668⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨71, by decide⟩
theorem decode_2669 : decode runtimeBytecode ⟨2669⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨72, by decide⟩
theorem decode_2670 : decode runtimeBytecode ⟨2670⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2457⟩, 2)) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨73, by decide⟩
theorem decode_2673 : decode runtimeBytecode ⟨2673⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨74, by decide⟩
theorem decode_2674 : decode runtimeBytecode ⟨2674⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨75, by decide⟩
theorem decode_2675 : decode runtimeBytecode ⟨2675⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨76, by decide⟩
theorem decode_2676 : decode runtimeBytecode ⟨2676⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨77, by decide⟩
theorem decode_2677 : decode runtimeBytecode ⟨2677⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨78, by decide⟩
theorem decode_2678 : decode runtimeBytecode ⟨2678⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨79, by decide⟩
theorem decode_2679 : decode runtimeBytecode ⟨2679⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨80, by decide⟩
theorem decode_2680 : decode runtimeBytecode ⟨2680⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨81, by decide⟩
theorem decode_2681 : decode runtimeBytecode ⟨2681⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨82, by decide⟩
theorem decode_2682 : decode runtimeBytecode ⟨2682⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1)) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨83, by decide⟩
theorem decode_2684 : decode runtimeBytecode ⟨2684⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨84, by decide⟩
theorem decode_2685 : decode runtimeBytecode ⟨2685⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨85, by decide⟩
theorem decode_2686 : decode runtimeBytecode ⟨2686⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨86, by decide⟩
theorem decode_2687 : decode runtimeBytecode ⟨2687⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨87, by decide⟩
theorem decode_2688 : decode runtimeBytecode ⟨2688⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨88, by decide⟩
theorem decode_2689 : decode runtimeBytecode ⟨2689⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨2457⟩, 2)) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨89, by decide⟩
theorem decode_2692 : decode runtimeBytecode ⟨2692⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨90, by decide⟩
theorem decode_2693 : decode runtimeBytecode ⟨2693⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨91, by decide⟩
theorem decode_2694 : decode runtimeBytecode ⟨2694⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨92, by decide⟩
theorem decode_2695 : decode runtimeBytecode ⟨2695⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨93, by decide⟩
theorem decode_2696 : decode runtimeBytecode ⟨2696⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨94, by decide⟩
theorem decode_2697 : decode runtimeBytecode ⟨2697⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨95, by decide⟩
theorem decode_2698 : decode runtimeBytecode ⟨2698⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨96, by decide⟩
theorem decode_2699 : decode runtimeBytecode ⟨2699⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨97, by decide⟩
theorem decode_2700 : decode runtimeBytecode ⟨2700⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨98, by decide⟩
theorem decode_2701 : decode runtimeBytecode ⟨2701⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1)) := by
  simpa [generatedDecodes18] using generatedDecodes18_correct ⟨99, by decide⟩

end Ripemd160Old
