/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rudy Peterson
-/
import Mathlib.Computability.Language
import Mathlib.Algebra.Ring.Defs

/-!
# Weighted Deterministic Finite Automata

TODO: explain stuff.
-/

universe k u v

open Computability

/-- A Weighted DFA (`𝓐`) over a semiring (`𝓦 = (𝕂, ⊕, ⊗, 0, 1)`)
is a 5-tuple (`(α, σ, step, start, final)`) where
* (`α`) is a (finite) alphabet.
* (`σ`) is a (finite) set of states.
* (`step : σ → α → σ × 𝕂`) is a (finite) set of transitions.
* (`start : σ × 𝕂`) the start state and its weight.
* (`final : σ → 𝕂`) is a weighting function assigning states their final values.
-/
structure WDFA (α : Type u) (σ : Type v) (κ : Type k) where
  /-- A transition function from state to state labelled by the alphabet producing a weight.  -/
  step : σ → α → σ × κ
  /-- Starting state and weight. -/
  start : σ × κ
  /-- Final weights. -/
  final : σ → κ
