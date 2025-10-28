/-
Copyright (c) 2025 Rudy Peterson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson
-/
import Mathlib.Computability.WeightedLanguage

/-!
# Weighted Regular Expressions

This file contains the formal definition for *semiring-weighted* regular expressions and basic
lemmas.

TODO: more explanation
-/

open List

universe u k

/-- This is the definition of *semiring-weighted* regular expressions. We mirror uniweghted
`RegularExpression` data type.
* `0` (`zero`) matches nothing (weight `0`)
* `1` (`epsilon`) matches only the empty string with weight `1`
* `char a` matches only the string 'a' with weight `1`
* `P + Q` (`plus P Q`) matches anything which match `P` or `Q` and adds the weights
* `P * Q` (`comp P Q`) matches `x ++ y` if `x` matches `P` and `y` matches `Q` and multiples the
  weights
* `w` matchs the empty string with weight `w`

NOTE: We do not yet support kleene stars for weighted languages, which naively would involve an
infinite computation.
-/
inductive WRegExp (α : Type u) (κ : Type k) where
  | zero : WRegExp α κ
  | epsilon : WRegExp α κ
  | char : α → WRegExp α κ
  | plus : WRegExp α κ → WRegExp α κ → WRegExp α κ
  | comp : WRegExp α κ → WRegExp α κ → WRegExp α κ
  | weight : κ → WRegExp α κ

namespace WRegExp

variable {α : Type u} {κ : Type k}

instance : Inhabited (WRegExp α κ) :=
  ⟨zero⟩

instance : Add (WRegExp α κ) :=
  ⟨plus⟩

instance : Mul (WRegExp α κ) :=
  ⟨comp⟩

instance : One (WRegExp α κ) :=
  ⟨epsilon⟩

instance : Zero (WRegExp α κ) :=
  ⟨zero⟩

instance : Pow (WRegExp α κ) ℕ :=
  ⟨fun n r => npowRec r n⟩

@[simp]
theorem zero_def : (zero : WRegExp α κ) = 0 :=
  rfl

@[simp]
theorem one_def : (epsilon : WRegExp α κ) = 1 :=
  rfl

@[simp]
theorem plus_def (P Q : WRegExp α κ) : plus P Q = P + Q :=
  rfl

@[simp]
theorem comp_def (P Q : WRegExp α κ) : comp P Q = P * Q :=
  rfl

section matches'

variable [W : Semiring κ] [DecidableEq α]

/-- `macthes' P` provides a *weighted* language for all strings that `P` macthes.

Not named `matches` since that is a reserved word.
-/
@[simp]
def matches' : WRegExp α κ → WeightedLanguage α κ
  | 0 => 0
  | 1 => 1
  | char a => fun x ↦ if x = [a] then 1 else 0
  | weight w => WeightedLanguage.scalar_prodl w 1
  | P + Q => P.matches' + Q.matches'
  | P * Q => P.matches' * Q.matches'

end matches'

end WRegExp
