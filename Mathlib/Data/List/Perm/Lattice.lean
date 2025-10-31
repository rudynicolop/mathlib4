/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro, Rudy Peterson
-/
import Mathlib.Data.List.Forall2
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.List.Lattice
import Mathlib.Data.List.Nodup
import Batteries.Data.List.Perm

/-!
# List Permutations and list lattice operations.

This file develops theory about the `List.Perm` relation and the lattice structure on lists.
-/

-- Make sure we don't import algebra
assert_not_exists Monoid

open Nat

namespace List
variable {α : Type*}

open Perm (swap)

lemma Nodup.splits_nodup (l : List α) : l.splits.Nodup := by
  simp only [List.splits, splitAt_eq]
  apply List.Nodup.map_on
  · simp only [mem_range, Prod.mk.injEq, take_eq_take_iff, and_imp]
    omega
  · apply List.nodup_range

lemma Disjoint_self (l : List α) :
    (∃ a, a ∈ l) → ¬ l.Disjoint l := by simp [Disjoint]

lemma Nodup.splits₃_left_nodup (l : List α) : l.splits₃_left.Nodup := by
  simp [List.splits₃_left, List.nodup_flatMap]
  constructor
  · intros t d htd_splits
    apply List.Nodup.map_on
    · rintro ⟨ta1, ta2⟩ hta_splits ⟨tb1, tb2⟩ htb_splits; simp
    · apply Nodup.splits_nodup
  · induction l <;> simp
    case cons a l ihl =>
      constructor
      · rintro b c x1 x2 hx1x2_l_splits rfl rfl
        simp [Function.onFun]
      · refine (List.Pairwise.map ?_ ?_ ihl); clear ihl
        rintro ⟨x1, x2⟩ ⟨y1, y2⟩
        simp only [Function.onFun, splits_cons, map_cons, map_map, disjoint_cons_right, mem_cons,
          Prod.mk.injEq, cons.injEq, true_and, mem_map, Function.comp_apply, reduceCtorEq,
          false_and, and_false, exists_const, or_false, not_and, disjoint_cons_left,
          not_false_eq_true]
        intro hdisj_map
        constructor
        · rintro rfl rfl
          apply List.Disjoint.of_map at hdisj_map
          have hnil : ∃ l, l ∈ y1.splits := by
            exists ([], y1)
            apply List.nil_self_mem_splits
          apply List.Disjoint_self _ hnil at hdisj_map
          assumption
        · unfold Function.comp
          simp only [Disjoint, mem_map, Prod.exists, imp_false, not_exists, not_and,
            forall_exists_index, and_imp, Prod.forall, Prod.mk.injEq] at *
          rintro z1 z2 z3 z4 z5 hx1_splits rfl rfl rfl z6 z7 hy1_splits ⟨_,rfl⟩ rfl rfl
          specialize hdisj_map _ _ _ _ _ hx1_splits rfl rfl rfl _ _ hy1_splits rfl rfl rfl
          assumption

lemma Nodup.splits₃_right_nodup (l : List α) : l.splits₃_right.Nodup := by
  simp [List.splits₃_right, List.nodup_flatMap]
  constructor
  · intros t d htd_l_splits
    apply List.Nodup.map_on
    · rintro ⟨d1, d2⟩ hd_splits ⟨d1', d2'⟩ hd'_splits ⟨_, rfl, rfl⟩
      rfl
    · apply Nodup.splits_nodup
  · induction l
    case nil =>
      simp
    case cons a l ihl =>
      simp
      constructor
      · clear ihl
        rintro b c l1 l2 hl_splits rfl rfl
        simp only [Function.onFun, Disjoint, splits_cons, map_cons, map_map, mem_cons, mem_map,
          Function.comp, Prod.exists, imp_false, not_exists, not_and, forall_eq_or_imp,
          Prod.mk.injEq, reduceCtorEq, false_and, not_false_eq_true, implies_true,
          forall_exists_index, and_imp, Prod.forall, nil_eq, true_and]
        rintro y1 y2 b y1' y2' hy' rfl rfl rfl z1 z2 hz ⟨⟩
      · refine (List.Pairwise.map ?_ ?_ ihl); clear ihl
        rintro ⟨x1, x2⟩ ⟨y1, y2⟩
        simp only [Function.onFun]
        rintro hdisj_map ⟨t, d1, d2⟩ hx2_splits hy2_splits
        simp only [mem_map, Prod.mk.injEq, Prod.exists, ↓existsAndEq, and_true,
          exists_eq_right_right] at hx2_splits hy2_splits
        rcases hx2_splits with ⟨hx2_splits, rfl⟩
        rcases hy2_splits with ⟨hy2_splits, ⟨_, rfl⟩⟩
        apply List.Disjoint.of_map at hdisj_map
        specialize hdisj_map hx2_splits hy2_splits
        contradiction

lemma Perm.splits₃_left_right_perm (l : List α) : l.splits₃_left ~ l.splits₃_right := by
  rw [List.perm_ext_iff_of_nodup]
  · rintro ⟨x, y, z⟩; simp [List.mem_splits₃_left_iff, List.mem_splits₃_right_iff]
  · apply Nodup.splits₃_left_nodup
  · apply Nodup.splits₃_right_nodup

variable [DecidableEq α]

theorem Perm.bagInter_right {l₁ l₂ : List α} (t : List α) (h : l₁ ~ l₂) :
    l₁.bagInter t ~ l₂.bagInter t := by
  induction h generalizing t with grind

theorem Perm.bagInter_left (l : List α) {t₁ t₂ : List α} (p : t₁ ~ t₂) :
    l.bagInter t₁ = l.bagInter t₂ := by
  induction l generalizing t₁ t₂ p with | nil => simp | cons a l IH => ?_
  by_cases h : a ∈ t₁
  · simp [h, p.subset h, IH (p.erase _)]
  · simp [h, mt p.mem_iff.2 h, IH p]

theorem Perm.bagInter {l₁ l₂ t₁ t₂ : List α} (hl : l₁ ~ l₂) (ht : t₁ ~ t₂) :
    l₁.bagInter t₁ ~ l₂.bagInter t₂ :=
  ht.bagInter_left l₂ ▸ hl.bagInter_right _

theorem Perm.inter_append {l t₁ t₂ : List α} (h : Disjoint t₁ t₂) :
    l ∩ (t₁ ++ t₂) ~ l ∩ t₁ ++ l ∩ t₂ := by
  induction l with
  | nil => simp
  | cons x xs l_ih =>
    by_cases h₁ : x ∈ t₁
    · have h₂ : x ∉ t₂ := h h₁
      simp [*]
    by_cases h₂ : x ∈ t₂
    · simp only [*, inter_cons_of_notMem, false_or, mem_append, inter_cons_of_mem,
        not_false_iff]
      refine Perm.trans (Perm.cons _ l_ih) ?_
      change [x] ++ xs ∩ t₁ ++ xs ∩ t₂ ~ xs ∩ t₁ ++ ([x] ++ xs ∩ t₂)
      rw [← List.append_assoc]
      solve_by_elim [Perm.append_right, perm_append_comm]
    · simp [*]

theorem Perm.take_inter {xs ys : List α} (n : ℕ) (h : xs ~ ys)
    (h' : ys.Nodup) : xs.take n ~ ys.inter (xs.take n) := by
  simp only [List.inter]
  exact Perm.trans (show xs.take n ~ xs.filter (xs.take n).elem by
      conv_lhs => rw [Nodup.take_eq_filter_mem ((Perm.nodup_iff h).2 h')])
    (Perm.filter _ h)

theorem Perm.drop_inter {xs ys : List α} (n : ℕ) (h : xs ~ ys) (h' : ys.Nodup) :
    xs.drop n ~ ys.inter (xs.drop n) := by
  by_cases h'' : n ≤ xs.length
  · let n' := xs.length - n
    have h₀ : n = xs.length - n' := by rwa [Nat.sub_sub_self]
    have h₁ : xs.drop n = (xs.reverse.take n').reverse := by
      rw [take_reverse, h₀, reverse_reverse]
    rw [h₁]
    apply (reverse_perm _).trans
    rw [inter_reverse]
    apply Perm.take_inter _ _ h'
    apply (reverse_perm _).trans; assumption
  · have : xs.drop n = [] := by
      apply eq_nil_of_length_eq_zero
      rw [length_drop, Nat.sub_eq_zero_iff_le]
      apply le_of_not_ge h''
    simp [this, List.inter]

theorem Perm.dropSlice_inter {xs ys : List α} (n m : ℕ) (h : xs ~ ys)
    (h' : ys.Nodup) : List.dropSlice n m xs ~ ys ∩ List.dropSlice n m xs := by
  simp only [dropSlice_eq]
  have : n ≤ n + m := Nat.le_add_right _ _
  have h₂ := h.nodup_iff.2 h'
  apply Perm.trans _ (Perm.inter_append _).symm
  · exact Perm.append (Perm.take_inter _ h h') (Perm.drop_inter _ h h')
  · exact disjoint_take_drop h₂ this

end List
