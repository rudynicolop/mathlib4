/-
Copyright (c) 2025 Rudy Peterson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rudy Peterson
-/
import Mathlib.Computability.Language
import Mathlib.Algebra.Ring.Defs
import Mathlib.Computability.WeightedPath

/-!
# Weighted Deterministic Finite Automata

TODO: explain stuff.
-/

universe k u v

open Computability

/-- A Weighted DFA (`𝓐`) over a semiring (`𝓦 = (κ, ⊕, ⊗, 0, 1)`)
is a 5-tuple (`(α, σ, step, start, final)`) where
* (`α`) is a (finite) alphabet.
* (`σ`) is a (finite) set of states.
* (`step : σ → α → σ × κ`) is a (finite) set of transitions.
* (`start : σ × κ`) the start state and its weight.
* (`final : σ → κ`) is a weighting function assigning states their final values.
-/
structure WDFA (α : Type u) (σ : Type v) (κ : Type k) where
  /-- A transition function from state to state labelled by the alphabet producing a weight.  -/
  step : σ → α → σ × κ
  /-- Starting state and weight. -/
  start : σ × κ
  /-- Final weights. -/
  final : σ → κ

namespace WDFA

variable {α : Type u} {σ : Type v} {κ : Type k} (M : WDFA α σ κ) [W : Semiring κ]

instance [Inhabited σ] [Inhabited κ] : Inhabited (WDFA α σ κ) :=
⟨WDFA.mk (fun _ _ => ⟨default, default⟩) ⟨default, default⟩ (fun _ ↦ 0)⟩

def PathInWDFA {s₁ s₃ : σ} : WeightedPath α κ s₁ s₃ → Prop :=
  WeightedPath.All (fun q₁ a w q₂ ↦ M.step q₁ a = (q₂, w))

end WDFA
