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

variable [DecidableEq α] [W : Semiring κ]

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

theorem matches'_zero : (0 : WRegExp α κ).matches' = 0 :=
  rfl

theorem matches'_epsilon : (1 : WRegExp α κ).matches' = 1 :=
  rfl

theorem matches'_char (a : α) : (char a).matches' = (fun x ↦ if x = [a] then W.one else 0) :=
  rfl

theorem matches'_add (P Q : WRegExp α κ) : (P + Q).matches' = P.matches' + Q.matches' :=
  rfl

theorem matches'_mul (P Q : WRegExp α κ) : (P * Q).matches' = P.matches' * Q.matches' :=
  rfl

@[simp]
theorem matches'_pow (P : WRegExp α κ) (n : ℕ) : (P ^ n).matches' = P.matches' ^ n := by
  induction n generalizing P
  case zero => rfl
  case succ n ih =>
    simp [pow_succ, ←ih]
    rfl

/-- `matchEpsilon P` is true if and only if `P` matches the empty string -/
def matchEpsilon : WRegExp α κ → κ
  | 0 => 1
  | 1 => 0
  | char _ => 0
  | weight w => w
  | P + Q => P.matchEpsilon + Q.matchEpsilon
  | P * Q => P.matchEpsilon * Q.matchEpsilon

/-- `P.deriv a` matches `x` if `P` matches `a :: x`, the Brzozowski derivative of `P` with respect
  to `a` -/
def deriv : WRegExp α κ → α → WRegExp α κ
  | 0, _ => 0
  | 1, _ => 0
  | weight _, _ => 0
  | char a₁, a₂ => if a₁ = a₂ then 1 else 0
  | P + Q, a => deriv P a + deriv Q a
  | P * Q, a => deriv P a * Q + weight P.matchEpsilon * deriv Q a

@[simp]
theorem deriv_zero (a : α) : deriv 0 a = (0 : WRegExp α κ) :=
  rfl

@[simp]
theorem deriv_one (a : α) : deriv 1 a = (0 : WRegExp α κ) :=
  rfl

@[simp]
theorem deriv_char_self (a : α) : deriv (char a) a = (1 : WRegExp α κ) :=
  if_pos rfl

@[simp]
theorem deriv_char_of_ne (a b : α) (h : a ≠ b) : deriv (char a) b = (0 : WRegExp α κ) :=
  if_neg h

@[simp]
theorem deriv_add (P Q : WRegExp α κ) (a : α) : deriv (P + Q) a = deriv P a + deriv Q a :=
  rfl

-- TODO: does this actually compute the weight?
def rmatch : WRegExp α κ → List α → κ
  | P, [] => matchEpsilon P
  | P, a :: as => rmatch (P.deriv a) as

end matches'

end WRegExp
