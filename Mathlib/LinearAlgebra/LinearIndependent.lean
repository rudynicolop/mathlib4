/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Alexander Bentkamp, Anne Baanen
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Reflection
import Mathlib.Data.Set.Subsingleton
import Mathlib.Lean.Expr.ExtraRecognizers
import Mathlib.LinearAlgebra.Finsupp.SumProd
import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!

# Linear independence

This file defines linear independence in a module or vector space.

It is inspired by Isabelle/HOL's linear algebra, and hence indirectly by HOL Light.

We define `LinearIndependent R v` as `Function.Injective (Finsupp.linearCombination R v)`. Here
`Finsupp.linearCombination` is the linear map sending a function `f : ι →₀ R` with finite support to
the linear combination of vectors from `v` with these coefficients. Then we prove that several other
statements are equivalent to this one, including `ker (Finsupp.linearCombination R v) = ⊥` and
some versions with explicitly written linear combinations.

## Main definitions
All definitions are given for families of vectors, i.e. `v : ι → M` where `M` is the module or
vector space and `ι : Type*` is an arbitrary indexing type.

* `LinearIndependent R v` states that the elements of the family `v` are linearly independent.

* `LinearIndepOn R v s` states that the elements of the family `v` indexed by the members
of the set `s : Set ι` are linearly independent.

* `LinearIndependent.repr hv x` returns the linear combination representing `x : span R (range v)`
on the linearly independent vectors `v`, given `hv : LinearIndependent R v`
(using classical choice). `LinearIndependent.repr hv` is provided as a linear map.

## Main statements

We prove several specialized tests for linear independence of families of vectors and of sets of
vectors.

* `Fintype.linearIndependent_iff`: if `ι` is a finite type, then any function `f : ι → R` has
  finite support, so we can reformulate the statement using `∑ i : ι, f i • v i` instead of a sum
  over an auxiliary `s : Finset ι`;
* `linearIndependent_empty_type`: a family indexed by an empty type is linearly independent;
* `linearIndependent_unique_iff`: if `ι` is a singleton, then `LinearIndependent K v` is
  equivalent to `v default ≠ 0`;
* `linearIndependent_option`, `linearIndependent_sum`, `linearIndependent_fin_cons`,
  `linearIndependent_fin_succ`: type-specific tests for linear independence of families of vector
  fields;
* `linearIndependent_insert`, `linearIndependent_union`, `linearIndependent_pair`,
  `linearIndependent_singleton`: linear independence tests for set operations.

In many cases we additionally provide dot-style operations (e.g., `LinearIndependent.union`) to
make the linear independence tests usable as `hv.insert ha` etc.

We also prove that, when working over a division ring,
any family of vectors includes a linear independent subfamily spanning the same subspace.

## Implementation notes

We use families instead of sets because it allows us to say that two identical vectors are linearly
dependent.

If you want to reason about linear independence of the of a subfamily of
an indexed family `v : ι → M` of vectors corresponding to a set `s : Set ι`,
then use `LinearIndepOn R v s`.
If `s : Set M` is instead an explicit set of vectors, then use `LinearIndepOn R id s`.

The lemmas `LinearIndepOn.linearIndependent` and `linearIndepOn_id_range_iff`
connect those two worlds.

## TODO

Rework proofs to hold in semirings, by avoiding the path through
`ker (Finsupp.linearCombination R v) = ⊥`.

## Tags

linearly dependent, linear dependence, linearly independent, linear independence

-/

assert_not_exists Cardinal

noncomputable section

open Function Set Submodule

universe u' u

variable {ι : Type u'} {ι' : Type*} {R : Type*} {K : Type*} {s : Set ι}
variable {M : Type*} {M' : Type*} {V : Type u}

section Semiring


variable {v : ι → M}
variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M']
variable [Module R M] [Module R M']
variable (R) (v)
/-- `LinearIndependent R v` states the family of vectors `v` is linearly independent over `R`. -/
def LinearIndependent : Prop :=
  Injective (Finsupp.linearCombination R v)

open Lean PrettyPrinter.Delaborator SubExpr in
/-- Delaborator for `LinearIndependent` that suggests pretty printing with type hints
in case the family of vectors is over a `Set`.

Type hints look like `LinearIndependent fun (v : ↑s) => ↑v` or `LinearIndependent (ι := ↑s) f`,
depending on whether the family is a lambda expression or not. -/
@[app_delab LinearIndependent]
def delabLinearIndependent : Delab :=
  whenPPOption getPPNotation <|
  whenNotPPOption getPPAnalysisSkip <|
  withOptionAtCurrPos `pp.analysis.skip true do
    let e ← getExpr
    guard <| e.isAppOfArity ``LinearIndependent 7
    let some _ := (e.getArg! 0).coeTypeSet? | failure
    let optionsPerPos ← if (e.getArg! 3).isLambda then
      withNaryArg 3 do return (← read).optionsPerPos.setBool (← getPos) pp.funBinderTypes.name true
    else
      withNaryArg 0 do return (← read).optionsPerPos.setBool (← getPos) `pp.analysis.namedArg true
    withTheReader Context ({· with optionsPerPos}) delab

/-- `LinearIndepOn R v s` states that the vectors in the family `v` that are indexed
by the elements of `s` are linearly independent over `R`. -/
def LinearIndepOn (s : Set ι) : Prop := LinearIndependent R (fun x : s ↦ v x)

variable {R v}

theorem LinearIndepOn.linearIndependent {s : Set ι} (h : LinearIndepOn R v s) :
    LinearIndependent R (fun x : s ↦ v x) := h

theorem linearIndependent_iff_injective_linearCombination :
    LinearIndependent R v ↔ Injective (Finsupp.linearCombination R v) := Iff.rfl

alias ⟨LinearIndependent.injective_linearCombination, _⟩ :=
  linearIndependent_iff_injective_linearCombination

theorem Fintype.linearIndependent_iff_injective [Fintype ι] :
    LinearIndependent R v ↔ Injective (Fintype.linearCombination R ℕ v) := by
  simp [← Finsupp.linearCombination_eq_fintype_linearCombination, LinearIndependent]

theorem LinearIndependent.injective [Nontrivial R] (hv : LinearIndependent R v) : Injective v := by
  simpa [comp_def]
    using Injective.comp hv (Finsupp.single_left_injective one_ne_zero)

theorem LinearIndepOn.injOn [Nontrivial R] (hv : LinearIndepOn R v s) : InjOn v s :=
  injOn_iff_injective.2 <| LinearIndependent.injective hv

theorem LinearIndependent.ne_zero [Nontrivial R] (i : ι) (hv : LinearIndependent R v) :
    v i ≠ 0 := by
  intro h
  have := @hv (Finsupp.single i 1 : ι →₀ R) 0 (by simpa using h)
  simp at this

theorem LinearIndepOn.ne_zero [Nontrivial R] {i : ι} (hv : LinearIndepOn R v s) (hi : i ∈ s) :
    v i ≠ 0 :=
  LinearIndependent.ne_zero ⟨i, hi⟩ hv

theorem linearIndependent_empty_type [IsEmpty ι] : LinearIndependent R v :=
  injective_of_subsingleton _

@[simp]
theorem linearIndependent_zero_iff [Nontrivial R] : LinearIndependent R (0 : ι → M) ↔ IsEmpty ι :=
  ⟨fun h ↦ not_nonempty_iff.1 fun ⟨i⟩ ↦ (h.ne_zero i rfl).elim,
    fun _ ↦ linearIndependent_empty_type⟩

variable (R M) in
theorem linearIndependent_empty : LinearIndependent R (fun x => x : (∅ : Set M) → M) :=
  linearIndependent_empty_type

variable (R v) in
@[simp]
theorem linearIndepOn_empty : LinearIndepOn R v ∅ :=
  linearIndependent_empty_type ..

theorem linearIndependent_set_coe_iff :
    LinearIndependent R (fun x : s ↦ v x) ↔ LinearIndepOn R v s := Iff.rfl

@[deprecated (since := "2025-02-20")] alias
  linearIndependent_set_subtype := linearIndependent_set_coe_iff

theorem linearIndependent_subtype_iff {s : Set M} :
    LinearIndependent R (Subtype.val : s → M) ↔ LinearIndepOn R id s := Iff.rfl

theorem linearIndependent_comp_subtype_iff :
    LinearIndependent R (v ∘ Subtype.val : s → M) ↔ LinearIndepOn R v s := Iff.rfl

/-- A subfamily of a linearly independent family (i.e., a composition with an injective map) is a
linearly independent family. -/
theorem LinearIndependent.comp (h : LinearIndependent R v) (f : ι' → ι) (hf : Injective f) :
    LinearIndependent R (v ∘ f) := by
  simpa [comp_def] using Injective.comp h (Finsupp.mapDomain_injective hf)

/-- A set of linearly independent vectors in a module `M` over a semiring `K` is also linearly
independent over a subring `R` of `K`.
The implementation uses minimal assumptions about the relationship between `R`, `K` and `M`.
The version where `K` is an `R`-algebra is `LinearIndependent.restrict_scalars_algebras`.
TODO : `LinearIndepOn` version.  -/
theorem LinearIndependent.restrict_scalars [Semiring K] [SMulWithZero R K] [Module K M]
    [IsScalarTower R K M] (hinj : Injective fun r : R ↦ r • (1 : K))
    (li : LinearIndependent K v) : LinearIndependent R v := by
  intro x y hxy
  let f := fun r : R => r • (1 : K)
  have := @li (x.mapRange f (by simp [f])) (y.mapRange f (by simp [f])) ?_
  · ext i
    exact hinj congr($this i)
  simpa [Finsupp.linearCombination, f, Finsupp.sum_mapRange_index]

@[deprecated (since := "2024-08-29")] alias linearIndependent_iff_injective_total :=
  linearIndependent_iff_injective_linearCombination

@[deprecated (since := "2024-08-29")] alias LinearIndependent.injective_total :=
  LinearIndependent.injective_linearCombination

-- This version makes `l₁` and `l₂` explicit.
theorem linearIndependent_iffₛ :
    LinearIndependent R v ↔
      ∀ l₁ l₂, Finsupp.linearCombination R v l₁ = Finsupp.linearCombination R v l₂ → l₁ = l₂ :=
  Iff.rfl

open Finset in
theorem linearIndependent_iff'ₛ :
    LinearIndependent R v ↔
      ∀ s : Finset ι, ∀ f g : ι → R, ∑ i ∈ s, f i • v i = ∑ i ∈ s, g i • v i → ∀ i ∈ s, f i = g i :=
  linearIndependent_iffₛ.trans
    ⟨fun hv s f g eq i his ↦ by
      have h :=
        hv (∑ i ∈ s, Finsupp.single i (f i)) (∑ i ∈ s, Finsupp.single i (g i)) <| by
          simpa only [map_sum, Finsupp.linearCombination_single] using eq
      have (f : ι → R) : f i = (∑ j ∈ s, Finsupp.single j (f j)) i :=
        calc
          f i = (Finsupp.lapply i : (ι →₀ R) →ₗ[R] R) (Finsupp.single i (f i)) := by
            { rw [Finsupp.lapply_apply, Finsupp.single_eq_same] }
          _ = ∑ j ∈ s, (Finsupp.lapply i : (ι →₀ R) →ₗ[R] R) (Finsupp.single j (f j)) :=
            Eq.symm <|
              Finset.sum_eq_single i
                (fun j _hjs hji => by rw [Finsupp.lapply_apply, Finsupp.single_eq_of_ne hji])
                fun hnis => hnis.elim his
          _ = (∑ j ∈ s, Finsupp.single j (f j)) i := (map_sum ..).symm
      rw [this f, this g, h],
      fun hv f g hl ↦
      Finsupp.ext fun _ ↦ by
        classical
        refine _root_.by_contradiction fun hni ↦ hni <| hv (f.support ∪ g.support) f g ?_ _ ?_
        · rwa [← sum_subset subset_union_left, ← sum_subset subset_union_right] <;>
            rintro i - hi <;> rw [Finsupp.not_mem_support_iff.mp hi, zero_smul]
        · contrapose! hni
          simp_rw [not_mem_union, Finsupp.not_mem_support_iff] at hni
          rw [hni.1, hni.2]⟩

theorem linearIndependent_iff''ₛ :
    LinearIndependent R v ↔
      ∀ (s : Finset ι) (f g : ι → R), (∀ i ∉ s, f i = g i) →
        ∑ i ∈ s, f i • v i = ∑ i ∈ s, g i • v i → ∀ i, f i = g i := by
  classical
  exact linearIndependent_iff'ₛ.trans
    ⟨fun H s f g eq hv i ↦ if his : i ∈ s then H s f g hv i his else eq i his,
      fun H s f g eq i hi ↦ by
      convert
        H s (fun j ↦ if j ∈ s then f j else 0) (fun j ↦ if j ∈ s then g j else 0)
          (fun j hj ↦ (if_neg hj).trans (if_neg hj).symm)
          (by simp_rw [ite_smul, zero_smul, Finset.sum_extend_by_zero, eq]) i <;>
      exact (if_pos hi).symm⟩

theorem not_linearIndependent_iffₛ :
    ¬LinearIndependent R v ↔ ∃ s : Finset ι,
      ∃ f g : ι → R, ∑ i ∈ s, f i • v i = ∑ i ∈ s, g i • v i ∧ ∃ i ∈ s, f i ≠ g i := by
  rw [linearIndependent_iff'ₛ]
  simp only [exists_prop, not_forall]

theorem Fintype.linearIndependent_iffₛ [Fintype ι] :
    LinearIndependent R v ↔ ∀ f g : ι → R, ∑ i, f i • v i = ∑ i, g i • v i → ∀ i, f i = g i := by
  simp_rw [Fintype.linearIndependent_iff_injective,
    Injective, Fintype.linearCombination_apply, funext_iff]

/-- A finite family of vectors `v i` is linear independent iff the linear map that sends
`c : ι → R` to `∑ i, c i • v i` is injective. -/
theorem Fintype.linearIndependent_iff'ₛ [Fintype ι] [DecidableEq ι] :
    LinearIndependent R v ↔
      Injective (LinearMap.lsum R (fun _ ↦ R) ℕ fun i ↦ LinearMap.id.smulRight (v i)) := by
  simp [Fintype.linearIndependent_iffₛ, Injective, funext_iff]

theorem Fintype.not_linearIndependent_iffₛ [Fintype ι] :
    ¬LinearIndependent R v ↔ ∃ f g : ι → R, ∑ i, f i • v i = ∑ i, g i • v i ∧ ∃ i, f i ≠ g i := by
  simpa using not_iff_not.2 Fintype.linearIndependent_iffₛ

lemma LinearIndependent.pair_iffₛ {x y : M} :
    LinearIndependent R ![x, y] ↔
      ∀ (s t s' t' : R), s • x + t • y = s' • x + t' • y → s = s' ∧ t = t' := by
  simp [Fintype.linearIndependent_iffₛ, Fin.forall_fin_two, ← FinVec.forall_iff]; rfl

lemma LinearIndependent.eq_of_pair {x y : M} (h : LinearIndependent R ![x, y])
    {s t s' t' : R} (h' : s • x + t • y = s' • x + t' • y) : s = s' ∧ t = t' :=
  pair_iffₛ.mp h _ _ _ _ h'

lemma LinearIndependent.eq_zero_of_pair' {x y : M} (h : LinearIndependent R ![x, y])
    {s t : R} (h' : s • x = t • y) : s = 0 ∧ t = 0 := by
  suffices H : s = 0 ∧ 0 = t from ⟨H.1, H.2.symm⟩
  exact h.eq_of_pair (by simpa using h')

lemma LinearIndependent.eq_zero_of_pair {x y : M} (h : LinearIndependent R ![x, y])
    {s t : R} (h' : s • x + t • y = 0) : s = 0 ∧ t = 0 := by
  replace h := @h (.single 0 s + .single 1 t) 0 ?_
  · exact ⟨by simpa using congr($h 0), by simpa using congr($h 1)⟩
  simpa

/-- A family is linearly independent if and only if all of its finite subfamily is
linearly independent. -/
theorem linearIndependent_iff_finset_linearIndependent :
    LinearIndependent R v ↔ ∀ (s : Finset ι), LinearIndependent R (v ∘ (Subtype.val : s → ι)) :=
  ⟨fun H _ ↦ H.comp _ Subtype.val_injective, fun H ↦ linearIndependent_iff'ₛ.2 fun s f g eq i hi ↦
    Fintype.linearIndependent_iffₛ.1 (H s) (f ∘ Subtype.val) (g ∘ Subtype.val)
      (by simpa only [← s.sum_coe_sort] using eq) ⟨i, hi⟩⟩

/-- If `v` is an injective family of vectors such that `f ∘ v` is linearly independent, then `v`
    spans a submodule disjoint from the kernel of `f`.
TODO : `LinearIndepOn` version. -/
theorem Submodule.range_ker_disjoint {f : M →ₗ[R] M'}
    (hv : LinearIndependent R (f ∘ v)) :
    Disjoint (span R (range v)) (LinearMap.ker f) := by
  rw [LinearIndependent, Finsupp.linearCombination_linear_comp] at hv
  rw [disjoint_iff_inf_le, ← Set.image_univ, Finsupp.span_image_eq_map_linearCombination,
    map_inf_eq_map_inf_comap, (LinearMap.ker_comp _ _).symm.trans
      (LinearMap.ker_eq_bot_of_injective hv), inf_bot_eq, map_bot]

/-- If `M / R` and `M' / R'` are modules, `i : R' → R` is a map, `j : M →+ M'` is a monoid map,
such that they are both injective, and compatible with the scalar
multiplications on `M` and `M'`, then `j` sends linearly independent families of vectors to
linearly independent families of vectors. As a special case, taking `R = R'`
it is `LinearIndependent.map_injOn`.
TODO : `LinearIndepOn` version.  -/
theorem LinearIndependent.map_of_injective_injectiveₛ {R' M' : Type*}
    [Semiring R'] [AddCommMonoid M'] [Module R' M'] (hv : LinearIndependent R v)
    (i : R' → R) (j : M →+ M') (hi : Injective i) (hj : Injective j)
    (hc : ∀ (r : R') (m : M), j (i r • m) = r • j m) : LinearIndependent R' (j ∘ v) := by
  rw [linearIndependent_iff'ₛ] at hv ⊢
  intro S r₁ r₂ H s hs
  simp_rw [comp_apply, ← hc, ← map_sum] at H
  exact hi <| hv _ _ _ (hj H) s hs

/-- If `M / R` and `M' / R'` are modules, `i : R → R'` is a surjective map,
and `j : M →+ M'` is an injective monoid map, such that the scalar multiplications
on `M` and `M'` are compatible, then `j` sends linearly independent families
of vectors to linearly independent families of vectors. As a special case, taking `R = R'`
it is `LinearIndependent.map_injOn`.
TODO : `LinearIndepOn` version.  -/
theorem LinearIndependent.map_of_surjective_injectiveₛ {R' M' : Type*}
    [Semiring R'] [AddCommMonoid M'] [Module R' M'] (hv : LinearIndependent R v)
    (i : R → R') (j : M →+ M') (hi : Surjective i) (hj : Injective j)
    (hc : ∀ (r : R) (m : M), j (r • m) = i r • j m) : LinearIndependent R' (j ∘ v) := by
  obtain ⟨i', hi'⟩ := hi.hasRightInverse
  refine hv.map_of_injective_injectiveₛ i' j (fun _ _ h ↦ ?_) hj fun r m ↦ ?_
  · apply_fun i at h
    rwa [hi', hi'] at h
  rw [hc (i' r) m, hi']

/-- If the image of a family of vectors under a linear map is linearly independent, then so is
the original family. -/
theorem LinearIndependent.of_comp (f : M →ₗ[R] M') (hfv : LinearIndependent R (f ∘ v)) :
    LinearIndependent R v := by
  rw [LinearIndependent, Finsupp.linearCombination_linear_comp, LinearMap.coe_comp] at hfv
  exact hfv.of_comp

theorem LinearIndepOn.of_comp (f : M →ₗ[R] M') (hfv : LinearIndepOn R (f ∘ v) s) :
    LinearIndepOn R v s :=
  LinearIndependent.of_comp f hfv

/-- If `f` is a linear map injective on the span of the range of `v`, then the family `f ∘ v`
is linearly independent if and only if the family `v` is linearly independent.
See `LinearMap.linearIndependent_iff_of_disjoint` for the version with `Set.InjOn` replaced
by `Disjoint` when working over a ring. -/
protected theorem LinearMap.linearIndependent_iff_of_injOn (f : M →ₗ[R] M')
    (hf_inj : Set.InjOn f (span R (Set.range v))) :
    LinearIndependent R (f ∘ v) ↔ LinearIndependent R v := by
  simp_rw [LinearIndependent, Finsupp.linearCombination_linear_comp, coe_comp]
  rw [hf_inj.injective_iff]
  rw [← Finsupp.range_linearCombination, LinearMap.range_coe]

protected theorem LinearMap.linearIndepOn_iff_of_injOn (f : M →ₗ[R] M')
    (hf_inj : Set.InjOn f (span R (v '' s))) :
    LinearIndepOn R (f ∘ v) s ↔ LinearIndepOn R v s :=
  f.linearIndependent_iff_of_injOn (by rwa [← image_eq_range]) (v := fun i : s ↦ v i)

/-- If a linear map is injective on the span of a family of linearly independent vectors, then
the family stays linearly independent after composing with the linear map.
See `LinearIndependent.map` for the version with `Set.InjOn` replaced by `Disjoint`
when working over a ring. -/
theorem LinearIndependent.map_injOn (hv : LinearIndependent R v) (f : M →ₗ[R] M')
    (hf_inj : Set.InjOn f (span R (Set.range v))) : LinearIndependent R (f ∘ v) :=
  (f.linearIndependent_iff_of_injOn hf_inj).mpr hv

theorem LinearIndepOn.map_injOn (hv : LinearIndepOn R v s) (f : M →ₗ[R] M')
    (hf_inj : Set.InjOn f (span R (v '' s))) : LinearIndepOn R (f ∘ v) s :=
  (f.linearIndepOn_iff_of_injOn hf_inj).mpr hv

-- TODO : Rename this `LinearIndependent.of_subsingleton`.
@[nontriviality]
theorem linearIndependent_of_subsingleton [Subsingleton R] : LinearIndependent R v :=
  linearIndependent_iffₛ.2 fun _l _l' _hl => Subsingleton.elim _ _

@[nontriviality]
theorem LinearIndepOn.of_subsingleton [Subsingleton R] : LinearIndepOn R v s :=
  linearIndependent_of_subsingleton

theorem linearIndependent_equiv (e : ι ≃ ι') {f : ι' → M} :
    LinearIndependent R (f ∘ e) ↔ LinearIndependent R f :=
  ⟨fun h ↦ comp_id f ▸ e.self_comp_symm ▸ h.comp _ e.symm.injective,
    fun h ↦ h.comp _ e.injective⟩

theorem linearIndependent_equiv' (e : ι ≃ ι') {f : ι' → M} {g : ι → M} (h : f ∘ e = g) :
    LinearIndependent R g ↔ LinearIndependent R f :=
  h ▸ linearIndependent_equiv e

theorem linearIndepOn_equiv (e : ι ≃ ι') {f : ι' → M} {s : Set ι} :
    LinearIndepOn R (f ∘ e) s ↔ LinearIndepOn R f (e '' s) :=
  linearIndependent_equiv' (e.image s) <| by simp [funext_iff]

@[simp]
theorem linearIndepOn_univ : LinearIndepOn R v univ ↔ LinearIndependent R v :=
  linearIndependent_equiv' (Equiv.Set.univ ι) rfl

alias ⟨_, LinearIndependent.linearIndepOn⟩ := linearIndepOn_univ

theorem linearIndepOn_iff_image {ι} {s : Set ι} {f : ι → M} (hf : Set.InjOn f s) :
    LinearIndepOn R f s ↔ LinearIndepOn R id (f '' s) :=
  linearIndependent_equiv' (Equiv.Set.imageOfInjOn _ _ hf) rfl

@[deprecated (since := "2025-02-14")] alias linearIndependent_image := linearIndepOn_iff_image

theorem linearIndepOn_range_iff {ι} {f : ι → ι'} (hf : Injective f) (g : ι' → M) :
    LinearIndepOn R g (range f) ↔ LinearIndependent R (g ∘ f) :=
  Iff.symm <| linearIndependent_equiv' (Equiv.ofInjective f hf) rfl

alias ⟨LinearIndependent.of_linearIndepOn_range, _⟩ := linearIndepOn_range_iff

theorem linearIndepOn_id_range_iff {ι} {f : ι → M} (hf : Injective f) :
    LinearIndepOn R id (range f) ↔ LinearIndependent R f :=
  linearIndepOn_range_iff hf id

alias ⟨LinearIndependent.of_linearIndepOn_id_range, _⟩ := linearIndepOn_id_range_iff

@[deprecated (since := "2025-02-15")] alias linearIndependent_subtype_range :=
    linearIndepOn_id_range_iff

@[deprecated (since := "2025-02-15")] alias LinearIndependent.of_subtype_range :=
    LinearIndependent.of_linearIndepOn_id_range

theorem LinearIndependent.linearIndepOn_id (i : LinearIndependent R v) :
    LinearIndepOn R id (range v) := by
  simpa using i.comp _ (rangeSplitting_injective v)

@[deprecated (since := "2025-02-15")] alias LinearIndependent.to_subtype_range :=
    LinearIndependent.linearIndepOn_id

@[deprecated (since := "2025-02-14")] alias
  LinearIndependent.coe_range := LinearIndependent.linearIndepOn_id

/-- A version of `LinearIndependent.linearIndepOn_id` with the set range equality as a hypothesis.-/
theorem LinearIndependent.linearIndepOn_id' (hv : LinearIndependent R v) {t : Set M}
    (ht : Set.range v = t) : LinearIndepOn R id t :=
  ht ▸ hv.linearIndepOn_id

@[deprecated (since := "2025-02-16")] alias LinearIndependent.to_subtype_range' :=
    LinearIndependent.linearIndepOn_id'

theorem LinearIndepOn.comp_of_image {s : Set ι'} {f : ι' → ι} (h : LinearIndepOn R v (f '' s))
    (hf : InjOn f s) : LinearIndepOn R (v ∘ f) s :=
  LinearIndependent.comp h _ (Equiv.Set.imageOfInjOn _ _ hf).injective

@[deprecated (since := "2025-02-14")] alias
  LinearIndependent.comp_of_image := LinearIndepOn.comp_of_image

theorem LinearIndepOn.image_of_comp (f : ι → ι') (g : ι' → M) (hs : LinearIndepOn R (g ∘ f) s) :
    LinearIndepOn R g (f '' s) := by
  nontriviality R
  have : InjOn f s := injOn_iff_injective.2 hs.injective.of_comp
  exact (linearIndependent_equiv' (Equiv.Set.imageOfInjOn f s this) rfl).1 hs

@[deprecated (since := "2025-02-14")] alias
  LinearIndependent.image_of_comp := LinearIndepOn.image_of_comp

theorem LinearIndepOn.id_image (hs : LinearIndepOn R v s) : LinearIndepOn R id (v '' s) :=
  LinearIndepOn.image_of_comp v id hs

@[deprecated (since := "2025-02-14")] alias
  LinearIndependent.image := LinearIndepOn.id_image

theorem LinearIndependent.group_smul {G : Type*} [hG : Group G] [DistribMulAction G R]
    [DistribMulAction G M] [IsScalarTower G R M] [SMulCommClass G R M] {v : ι → M}
    (hv : LinearIndependent R v) (w : ι → G) : LinearIndependent R (w • v) := by
  rw [linearIndependent_iff''ₛ] at hv ⊢
  intro s g₁ g₂ hgs hsum i
  refine (Group.isUnit (w i)).smul_left_cancel.mp ?_
  refine hv s (fun i ↦ w i • g₁ i) (fun i ↦ w i • g₂ i) (fun i hi ↦ ?_) ?_ i
  · simp_rw [hgs i hi]
  · simpa only [smul_assoc, smul_comm] using hsum

@[simp]
theorem LinearIndependent.group_smul_iff {G : Type*} [hG : Group G] [DistribMulAction G R]
    [DistribMulAction G M] [IsScalarTower G R M] [SMulCommClass G R M] (v : ι → M) (w : ι → G) :
    LinearIndependent R (w • v) ↔ LinearIndependent R v := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.group_smul w⟩
  convert h.group_smul (fun i ↦ (w i)⁻¹)
  simp [funext_iff]

-- This lemma cannot be proved with `LinearIndependent.group_smul` since the action of
-- `Rˣ` on `R` is not commutative.
theorem LinearIndependent.units_smul {v : ι → M} (hv : LinearIndependent R v) (w : ι → Rˣ) :
    LinearIndependent R (w • v) := by
  rw [linearIndependent_iff''ₛ] at hv ⊢
  intro s g₁ g₂ hgs hsum i
  rw [← (w i).mul_left_inj]
  refine hv s (fun i ↦ g₁ i • w i) (fun i ↦ g₂ i • w i) (fun i hi ↦ ?_) ?_ i
  · simp_rw [hgs i hi]
  · simpa only [smul_eq_mul, mul_smul, Pi.smul_apply'] using hsum

@[simp]
theorem LinearIndependent.units_smul_iff (v : ι → M) (w : ι → Rˣ) :
    LinearIndependent R (w • v) ↔ LinearIndependent R v := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.units_smul w⟩
  convert h.units_smul (fun i ↦ (w i)⁻¹)
  simp [funext_iff]

theorem linearIndependent_span (hs : LinearIndependent R v) :
    LinearIndependent R (M := span R (range v))
      (fun i : ι ↦ ⟨v i, subset_span (mem_range_self i)⟩) :=
  LinearIndependent.of_comp (span R (range v)).subtype hs

/-- Every finite subset of a linearly independent set is linearly independent. -/
theorem linearIndependent_finset_map_embedding_subtype (s : Set M)
    (li : LinearIndependent R ((↑) : s → M)) (t : Finset s) :
    LinearIndependent R ((↑) : Finset.map (Embedding.subtype s) t → M) :=
  li.comp (fun _ ↦ ⟨_, _⟩) <| by intro; aesop

section Indexed

theorem linearIndepOn_iffₛ : LinearIndepOn R v s ↔
      ∀ f ∈ Finsupp.supported R R s, ∀ g ∈ Finsupp.supported R R s,
        Finsupp.linearCombination R v f = Finsupp.linearCombination R v g → f = g := by
  simp only [LinearIndepOn, linearIndependent_iffₛ, (· ∘ ·), Finsupp.mem_supported,
    Finsupp.linearCombination_apply, Set.subset_def, Finset.mem_coe]
  refine ⟨fun h l₁ h₁ l₂ h₂ eq ↦ (Finsupp.subtypeDomain_eq_iff h₁ h₂).1 <| h _ _ <|
    (Finsupp.sum_subtypeDomain_index h₁).trans eq ▸ (Finsupp.sum_subtypeDomain_index h₂).symm,
    fun h l₁ l₂ eq ↦ ?_⟩
  refine Finsupp.embDomain_injective (Embedding.subtype s) <| h _ ?_ _ ?_ ?_
  iterate 2 simpa using fun _ h _ ↦ h
  simp_rw [Finsupp.embDomain_eq_mapDomain]
  rwa [Finsupp.sum_mapDomain_index, Finsupp.sum_mapDomain_index] <;>
    intros <;> simp only [zero_smul, add_smul]

@[deprecated (since := "2025-02-15")] alias linearIndependent_comp_subtypeₛ := linearIndepOn_iffₛ

/-- An indexed set of vectors is linearly dependent iff there are two distinct
`Finsupp.LinearCombination`s of the vectors with the same value. -/
theorem linearDepOn_iff'ₛ : ¬LinearIndepOn R v s ↔
      ∃ f g : ι →₀ R, f ∈ Finsupp.supported R R s ∧ g ∈ Finsupp.supported R R s ∧
        Finsupp.linearCombination R v f = Finsupp.linearCombination R v g ∧ f ≠ g := by
  simp [linearIndepOn_iffₛ, and_left_comm]

@[deprecated (since := "2025-02-15")] alias linearDependent_comp_subtype'ₛ := linearDepOn_iff'ₛ

/-- A version of `linearDepOn_iff'ₛ` with `Finsupp.linearCombination` unfolded. -/
theorem linearDepOn_iffₛ : ¬LinearIndepOn R v s ↔
      ∃ f g : ι →₀ R, f ∈ Finsupp.supported R R s ∧ g ∈ Finsupp.supported R R s ∧
        ∑ i ∈ f.support, f i • v i = ∑ i ∈ g.support, g i • v i ∧ f ≠ g :=
  linearDepOn_iff'ₛ

@[deprecated (since := "2025-02-15")] alias linearDependent_comp_subtypeₛ := linearDepOn_iffₛ

@[deprecated (since := "2025-02-15")] alias linearIndependent_subtypeₛ := linearIndepOn_iffₛ

theorem linearIndependent_restrict_iff :
    LinearIndependent R (s.restrict v) ↔ LinearIndepOn R v s := Iff.rfl

theorem LinearIndepOn.linearIndependent_restrict (hs : LinearIndepOn R v s) :
    LinearIndependent R (s.restrict v) :=
  hs

@[deprecated (since := "2025-02-15")] alias LinearIndependent.restrict_of_comp_subtype :=
    LinearIndepOn.linearIndependent_restrict

theorem linearIndepOn_iff_linearCombinationOnₛ :
    LinearIndepOn R v s ↔ Injective (Finsupp.linearCombinationOn ι M R v s) := by
  rw [← linearIndependent_restrict_iff]
  simp [LinearIndependent, Finsupp.linearCombination_restrict]

@[deprecated (since := "2025-02-15")] alias
  linearIndependent_iff_linearCombinationOnₛ := linearIndepOn_iff_linearCombinationOnₛ

theorem LinearIndepOn.mono {t s : Set ι} (hs : LinearIndepOn R v s) (h : t ⊆ s) :
    LinearIndepOn R v t :=
  hs.comp _ <| Set.inclusion_injective h

@[deprecated (since := "2025-02-15")] alias LinearIndependent.mono := LinearIndepOn.mono

theorem linearIndepOn_of_finite (s : Set ι) (H : ∀ t ⊆ s, Set.Finite t → LinearIndepOn R v t) :
    LinearIndepOn R v s :=
  linearIndepOn_iffₛ.2 fun f hf g hg eq ↦
    linearIndepOn_iffₛ.1 (H _ (union_subset hf hg) <| (Finset.finite_toSet _).union <|
      Finset.finite_toSet _) f Set.subset_union_left g Set.subset_union_right eq

@[deprecated (since := "2025-02-15")] alias linearIndependent_of_finite := linearIndepOn_of_finite

theorem linearIndepOn_iUnion_of_directed {η : Type*} {s : η → Set ι} (hs : Directed (· ⊆ ·) s)
    (h : ∀ i, LinearIndepOn R v (s i)) : LinearIndepOn R v (⋃ i, s i) := by
  by_cases hη : Nonempty η
  · refine linearIndepOn_of_finite (⋃ i, s i) fun t ht ft => ?_
    rcases finite_subset_iUnion ft ht with ⟨I, fi, hI⟩
    rcases hs.finset_le fi.toFinset with ⟨i, hi⟩
    exact (h i).mono (Subset.trans hI <| iUnion₂_subset fun j hj => hi j (fi.mem_toFinset.2 hj))
  · refine (linearIndepOn_empty R v).mono (t := iUnion (s ·)) ?_
    rintro _ ⟨_, ⟨i, _⟩, _⟩
    exact hη ⟨i⟩

@[deprecated (since := "2025-02-15")] alias
    linearIndependent_iUnion_of_directed := linearIndepOn_iUnion_of_directed

theorem linearIndepOn_sUnion_of_directed {s : Set (Set ι)} (hs : DirectedOn (· ⊆ ·) s)
    (h : ∀ a ∈ s, LinearIndepOn R v a) : LinearIndepOn R v (⋃₀ s) := by
  rw [sUnion_eq_iUnion]
  exact linearIndepOn_iUnion_of_directed hs.directed_val (by simpa using h)

@[deprecated (since := "2025-02-15")] alias
    linearIndependent_sUnion_of_directed := linearIndepOn_sUnion_of_directed

theorem linearIndepOn_biUnion_of_directed {η} {s : Set η} {t : η → Set ι}
    (hs : DirectedOn (t ⁻¹'o (· ⊆ ·)) s) (h : ∀ a ∈ s, LinearIndepOn R v (t a)) :
    LinearIndepOn R v (⋃ a ∈ s, t a) := by
  rw [biUnion_eq_iUnion]
  exact linearIndepOn_iUnion_of_directed (directed_comp.2 <| hs.directed_val) (by simpa using h)

@[deprecated (since := "2025-02-15")] alias
    linearIndependent_biUnion_of_directed := linearIndepOn_biUnion_of_directed

end Indexed

/-- Linear independent families are injective, even if you multiply either side. -/
theorem LinearIndependent.eq_of_smul_apply_eq_smul_apply {M : Type*} [AddCommMonoid M] [Module R M]
    {v : ι → M} (li : LinearIndependent R v) (c d : R) (i j : ι) (hc : c ≠ 0)
    (h : c • v i = d • v j) : i = j := by
  have h_single_eq : Finsupp.single i c = Finsupp.single j d :=
    li <| by simpa [Finsupp.linearCombination_apply] using h
  rcases (Finsupp.single_eq_single_iff ..).mp h_single_eq with (⟨H, _⟩ | ⟨hc, _⟩)
  · exact H
  · contradiction

section Subtype

/-! The following lemmas use the subtype defined by a set in `M` as the index set `ι`. -/

theorem LinearIndependent.disjoint_span_image (hv : LinearIndependent R v) {s t : Set ι}
    (hs : Disjoint s t) : Disjoint (Submodule.span R <| v '' s) (Submodule.span R <| v '' t) := by
  simp only [disjoint_def, Finsupp.mem_span_image_iff_linearCombination]
  rintro _ ⟨l₁, hl₁, rfl⟩ ⟨l₂, hl₂, H⟩
  rw [hv.injective_linearCombination.eq_iff] at H; subst l₂
  have : l₁ = 0 := Submodule.disjoint_def.mp (Finsupp.disjoint_supported_supported hs) _ hl₁ hl₂
  simp [this]

theorem LinearIndependent.not_mem_span_image [Nontrivial R] (hv : LinearIndependent R v) {s : Set ι}
    {x : ι} (h : x ∉ s) : v x ∉ Submodule.span R (v '' s) := by
  have h' : v x ∈ Submodule.span R (v '' {x}) := by
    rw [Set.image_singleton]
    exact mem_span_singleton_self (v x)
  intro w
  apply LinearIndependent.ne_zero x hv
  refine disjoint_def.1 (hv.disjoint_span_image ?_) (v x) h' w
  simpa using h

theorem LinearIndependent.linearCombination_ne_of_not_mem_support [Nontrivial R]
    (hv : LinearIndependent R v) {x : ι} (f : ι →₀ R) (h : x ∉ f.support) :
    Finsupp.linearCombination R v f ≠ v x := by
  replace h : x ∉ (f.support : Set ι) := h
  have p := hv.not_mem_span_image h
  intro w
  rw [← w] at p
  rw [Finsupp.span_image_eq_map_linearCombination] at p
  simp only [not_exists, not_and, mem_map] at p -- Porting note: `mem_map` isn't currently triggered
  exact p f (f.mem_supported_support R) rfl

@[deprecated (since := "2024-08-29")] alias LinearIndependent.total_ne_of_not_mem_support :=
  LinearIndependent.linearCombination_ne_of_not_mem_support

end Subtype

section repr

/-- Canonical isomorphism between linear combinations and the span of linearly independent vectors.
-/
@[simps (config := { rhsMd := default }) symm_apply]
def LinearIndependent.linearCombinationEquiv (hv : LinearIndependent R v) :
    (ι →₀ R) ≃ₗ[R] span R (range v) := by
  refine LinearEquiv.ofBijective (LinearMap.codRestrict (span R (range v))
                                 (Finsupp.linearCombination R v) ?_) ⟨hv.codRestrict _, ?_⟩
  · simp_rw [← Finsupp.range_linearCombination]; exact fun c ↦ ⟨c, rfl⟩
  rw [← LinearMap.range_eq_top, LinearMap.range_eq_map, LinearMap.map_codRestrict,
    ← LinearMap.range_le_iff_comap, range_subtype, Submodule.map_top,
    Finsupp.range_linearCombination]

@[deprecated (since := "2024-08-29")] noncomputable alias LinearIndependent.totalEquiv :=
  LinearIndependent.linearCombinationEquiv

-- Porting note: The original theorem generated by `simps` was
--               different from the theorem on Lean 3, and not simp-normal form.
@[simp]
theorem LinearIndependent.linearCombinationEquiv_apply_coe (hv : LinearIndependent R v)
    (l : ι →₀ R) : hv.linearCombinationEquiv l = Finsupp.linearCombination R v l := rfl

@[deprecated (since := "2024-08-29")] alias LinearIndependent.totalEquiv_apply_coe :=
  LinearIndependent.linearCombinationEquiv_apply_coe
/-- Linear combination representing a vector in the span of linearly independent vectors.

Given a family of linearly independent vectors, we can represent any vector in their span as
a linear combination of these vectors. These are provided by this linear map.
It is simply one direction of `LinearIndependent.linearCombinationEquiv`. -/
def LinearIndependent.repr (hv : LinearIndependent R v) : span R (range v) →ₗ[R] ι →₀ R :=
  hv.linearCombinationEquiv.symm

variable (hv : LinearIndependent R v)

@[simp]
theorem LinearIndependent.linearCombination_repr (x) :
    Finsupp.linearCombination R v (hv.repr x) = x :=
  Subtype.ext_iff.1 (LinearEquiv.apply_symm_apply hv.linearCombinationEquiv x)

@[deprecated (since := "2024-08-29")] alias LinearIndependent.total_repr :=
  LinearIndependent.linearCombination_repr

theorem LinearIndependent.linearCombination_comp_repr :
    (Finsupp.linearCombination R v).comp hv.repr = Submodule.subtype _ :=
  LinearMap.ext <| hv.linearCombination_repr

@[deprecated (since := "2024-08-29")] alias LinearIndependent.total_comp_repr :=
  LinearIndependent.linearCombination_comp_repr

theorem LinearIndependent.repr_ker : LinearMap.ker hv.repr = ⊥ := by
  rw [LinearIndependent.repr, LinearEquiv.ker]

theorem LinearIndependent.repr_range : LinearMap.range hv.repr = ⊤ := by
  rw [LinearIndependent.repr, LinearEquiv.range]

theorem LinearIndependent.repr_eq {l : ι →₀ R} {x : span R (range v)}
    (eq : Finsupp.linearCombination R v l = ↑x) : hv.repr x = l := by
  have :
    ↑((LinearIndependent.linearCombinationEquiv hv : (ι →₀ R) →ₗ[R] span R (range v)) l) =
      Finsupp.linearCombination R v l :=
    rfl
  have : (LinearIndependent.linearCombinationEquiv hv : (ι →₀ R) →ₗ[R] span R (range v)) l = x := by
    rw [eq] at this
    exact Subtype.ext_iff.2 this
  rw [← LinearEquiv.symm_apply_apply hv.linearCombinationEquiv l]
  rw [← this]
  rfl

theorem LinearIndependent.repr_eq_single (i) (x : span R (range v)) (hx : ↑x = v i) :
    hv.repr x = Finsupp.single i 1 := by
  apply hv.repr_eq
  simp [Finsupp.linearCombination_single, hx]

theorem LinearIndependent.span_repr_eq [Nontrivial R] (x) :
    Span.repr R (Set.range v) x =
      (hv.repr x).equivMapDomain (Equiv.ofInjective _ hv.injective) := by
  have p :
    (Span.repr R (Set.range v) x).equivMapDomain (Equiv.ofInjective _ hv.injective).symm =
      hv.repr x := by
    apply (LinearIndependent.linearCombinationEquiv hv).injective
    ext
    simp only [LinearIndependent.linearCombinationEquiv_apply_coe, Equiv.self_comp_ofInjective_symm,
      LinearIndependent.linearCombination_repr, Finsupp.linearCombination_equivMapDomain,
      Span.finsupp_linearCombination_repr]
  ext ⟨_, ⟨i, rfl⟩⟩
  simp [← p]

theorem LinearIndependent.not_smul_mem_span (hv : LinearIndependent R v) (i : ι) (a : R)
    (ha : a • v i ∈ span R (v '' (univ \ {i}))) : a = 0 := by
  rw [Finsupp.span_image_eq_map_linearCombination, mem_map] at ha
  rcases ha with ⟨l, hl, e⟩
  rw [linearIndependent_iffₛ.1 hv l (Finsupp.single i a) (by simp [e])] at hl
  by_contra hn
  exact (not_mem_of_mem_diff (hl <| by simp [hn])) (mem_singleton _)

/-- See also `iSupIndep_iff_linearIndependent_of_ne_zero`. -/
theorem LinearIndependent.iSupIndep_span_singleton (hv : LinearIndependent R v) :
    iSupIndep fun i => R ∙ v i := by
  refine iSupIndep_def.mp fun i => ?_
  rw [disjoint_iff_inf_le]
  intro m hm
  simp only [mem_inf, mem_span_singleton, iSup_subtype'] at hm
  rw [← span_range_eq_iSup] at hm
  obtain ⟨⟨r, rfl⟩, hm⟩ := hm
  suffices r = 0 by simp [this]
  apply hv.not_smul_mem_span i
  convert hm
  ext
  simp

@[deprecated (since := "2024-11-24")]
alias LinearIndependent.independent_span_singleton := LinearIndependent.iSupIndep_span_singleton

end repr

section union

open LinearMap Finsupp

theorem LinearIndepOn.id_imageₛ {s : Set M} {f : M →ₗ[R] M'} (hs : LinearIndepOn R id s)
    (hf_inj : Set.InjOn f (span R s)) : LinearIndepOn R id (f '' s) :=
  id_image <| hs.map_injOn f (by simpa using hf_inj)

@[deprecated (since := "2025-02-14")] alias
    LinearIndependent.image_subtypeₛ := LinearIndepOn.id_imageₛ

theorem linearIndependent_inl_union_inr' {v : ι → M} {v' : ι' → M'}
    (hv : LinearIndependent R v) (hv' : LinearIndependent R v') :
    LinearIndependent R (Sum.elim (inl R M M' ∘ v) (inr R M M' ∘ v')) := by
  have : linearCombination R (Sum.elim (inl R M M' ∘ v) (inr R M M' ∘ v')) =
      .prodMap (linearCombination R v) (linearCombination R v') ∘ₗ
      (sumFinsuppLEquivProdFinsupp R).toLinearMap := by
    ext (_ | _) <;> simp [linearCombination_comapDomain]
  rw [LinearIndependent, this]
  simpa [LinearMap.coe_prodMap] using ⟨hv, hv'⟩

theorem LinearIndependent.inl_union_inr {s : Set M} {t : Set M'}
    (hs : LinearIndependent R (fun x => x : s → M))
    (ht : LinearIndependent R (fun x => x : t → M')) :
    LinearIndependent R (fun x => x : ↥(inl R M M' '' s ∪ inr R M M' '' t) → M × M') := by
  nontriviality R
  let e : s ⊕ t ≃ ↥(inl R M M' '' s ∪ inr R M M' '' t) :=
    .ofBijective (Sum.elim (fun i ↦ ⟨_, .inl ⟨_, i.2, rfl⟩⟩) fun i ↦ ⟨_, .inr ⟨_, i.2, rfl⟩⟩)
      ⟨by rintro (_|_) (_|_) eq <;> simp [hs.ne_zero, ht.ne_zero] at eq <;> aesop,
        by rintro ⟨_, ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩⟩ <;> aesop⟩
  refine (linearIndependent_equiv' e ?_).mp (linearIndependent_inl_union_inr' hs ht)
  ext (_ | _) <;> rfl

end union

section Maximal

universe v w

/--
A linearly independent family is maximal if there is no strictly larger linearly independent family.
-/
@[nolint unusedArguments]
def LinearIndependent.Maximal {ι : Type w} {R : Type u} [Semiring R] {M : Type v} [AddCommMonoid M]
    [Module R M] {v : ι → M} (_i : LinearIndependent R v) : Prop :=
  ∀ (s : Set M) (_i' : LinearIndependent R ((↑) : s → M)) (_h : range v ≤ s), range v = s

/-- An alternative characterization of a maximal linearly independent family,
quantifying over types (in the same universe as `M`) into which the indexing family injects.
-/
theorem LinearIndependent.maximal_iff {ι : Type w} {R : Type u} [Semiring R] [Nontrivial R]
    {M : Type v} [AddCommMonoid M] [Module R M] {v : ι → M} (i : LinearIndependent R v) :
    i.Maximal ↔
      ∀ (κ : Type v) (w : κ → M) (_i' : LinearIndependent R w) (j : ι → κ) (_h : w ∘ j = v),
        Surjective j := by
  constructor
  · rintro p κ w i' j rfl
    specialize p (range w) i'.linearIndepOn_id (range_comp_subset_range _ _)
    rw [range_comp, ← image_univ (f := w)] at p
    exact range_eq_univ.mp (image_injective.mpr i'.injective p)
  · intro p w i' h
    specialize
      p w ((↑) : w → M) i' (fun i => ⟨v i, range_subset_iff.mp h i⟩)
        (by
          ext
          simp)
    have q := congr_arg (fun s => ((↑) : w → M) '' s) p.range_eq
    dsimp at q
    rw [← image_univ, image_image] at q
    simpa using q

variable (R)

/-- TODO : refactor to use `Maximal`. -/
theorem exists_maximal_linearIndepOn' (v : ι → M) :
    ∃ s : Set ι, (LinearIndepOn R v s) ∧ ∀ t : Set ι, s ⊆ t → (LinearIndepOn R v t) → s = t := by
  let indep : Set ι → Prop := fun s => LinearIndepOn R v s
  let X := { I : Set ι // indep I }
  let r : X → X → Prop := fun I J => I.1 ⊆ J.1
  have key : ∀ c : Set X, IsChain r c → indep (⋃ (I : X) (_ : I ∈ c), I) := by
    intro c hc
    dsimp [indep]
    rw [linearIndepOn_iffₛ]
    intro f hfsupp g hgsupp hsum
    rcases eq_empty_or_nonempty c with (rfl | hn)
    · rw [show f = 0 by simpa using hfsupp, show g = 0 by simpa using hgsupp]
    haveI : IsRefl X r := ⟨fun _ => Set.Subset.refl _⟩
    classical
    obtain ⟨I, _I_mem, hI⟩ : ∃ I ∈ c, (f.support ∪ g.support : Set ι) ⊆ I :=
      f.support.coe_union _ ▸ hc.directedOn.exists_mem_subset_of_finset_subset_biUnion hn <| by
        simpa using And.intro hfsupp hgsupp
    exact linearIndepOn_iffₛ.mp I.2 f (subset_union_left.trans hI)
      g (subset_union_right.trans hI) hsum
  have trans : Transitive r := fun I J K => Set.Subset.trans
  obtain ⟨⟨I, hli : indep I⟩, hmax : ∀ a, r ⟨I, hli⟩ a → r a ⟨I, hli⟩⟩ :=
    exists_maximal_of_chains_bounded
      (fun c hc => ⟨⟨⋃ I ∈ c, (I : Set ι), key c hc⟩, fun I => Set.subset_biUnion_of_mem⟩) @trans
  exact ⟨I, hli, fun J hsub hli => Set.Subset.antisymm hsub (hmax ⟨J, hli⟩ hsub)⟩

@[deprecated (since := "2025-02-15")] alias
  exists_maximal_independent' :=  exists_maximal_linearIndepOn'

end Maximal

theorem surjective_of_linearIndependent_of_span [Nontrivial R] (hv : LinearIndependent R v)
    (f : ι' ↪ ι) (hss : range v ⊆ span R (range (v ∘ f))) : Surjective f := by
  intro i
  let repr : (span R (range (v ∘ f)) : Type _) → ι' →₀ R := (hv.comp f f.injective).repr
  let l := (repr ⟨v i, hss (mem_range_self i)⟩).mapDomain f
  have h_total_l : Finsupp.linearCombination R v l = v i := by
    dsimp only [l]
    rw [Finsupp.linearCombination_mapDomain]
    rw [(hv.comp f f.injective).linearCombination_repr]
  have h_total_eq : Finsupp.linearCombination R v l = Finsupp.linearCombination R v
       (Finsupp.single i 1) := by
    rw [h_total_l, Finsupp.linearCombination_single, one_smul]
  have l_eq : l = _ := hv h_total_eq
  dsimp only [l] at l_eq
  rw [← Finsupp.embDomain_eq_mapDomain] at l_eq
  rcases Finsupp.single_of_embDomain_single (repr ⟨v i, _⟩) f i (1 : R) zero_ne_one.symm l_eq with
    ⟨i', hi'⟩
  use i'
  exact hi'.2

theorem eq_of_linearIndepOn_id_of_span_subtype [Nontrivial R] {s t : Set M}
    (hs : LinearIndepOn R id s) (h : t ⊆ s) (hst : s ⊆ span R t) : s = t := by
  let f : t ↪ s :=
    ⟨fun x => ⟨x.1, h x.2⟩, fun a b hab => Subtype.coe_injective (Subtype.mk.inj hab)⟩
  have h_surj : Surjective f := by
    apply surjective_of_linearIndependent_of_span hs f _
    convert hst <;> simp [f, comp_def]
  show s = t
  apply Subset.antisymm _ h
  intro x hx
  rcases h_surj ⟨x, hx⟩ with ⟨y, hy⟩
  convert y.mem
  rw [← Subtype.mk.inj hy]

@[deprecated (since := "2025-02-15")] alias
  eq_of_linearIndependent_of_span_subtype := eq_of_linearIndepOn_id_of_span_subtype

theorem le_of_span_le_span [Nontrivial R] {s t u : Set M} (hl : LinearIndepOn R id u)
    (hsu : s ⊆ u) (htu : t ⊆ u) (hst : span R s ≤ span R t) : s ⊆ t := by
  have :=
    eq_of_linearIndepOn_id_of_span_subtype (hl.mono (Set.union_subset hsu htu))
      Set.subset_union_right (Set.union_subset (Set.Subset.trans subset_span hst) subset_span)
  rw [← this]; apply Set.subset_union_left

theorem span_le_span_iff [Nontrivial R] {s t u : Set M} (hl : LinearIndependent R ((↑) : u → M))
    (hsu : s ⊆ u) (htu : t ⊆ u) : span R s ≤ span R t ↔ s ⊆ t :=
  ⟨le_of_span_le_span hl hsu htu, span_mono⟩

end Semiring

section Module

variable {v : ι → M}
variable [Ring R] [AddCommGroup M] [AddCommGroup M']
variable [Module R M] [Module R M']

theorem linearIndependent_iff_ker :
    LinearIndependent R v ↔ LinearMap.ker (Finsupp.linearCombination R v) = ⊥ :=
  LinearMap.ker_eq_bot.symm

theorem linearIndependent_iff :
    LinearIndependent R v ↔ ∀ l, Finsupp.linearCombination R v l = 0 → l = 0 := by
  simp [linearIndependent_iff_ker, LinearMap.ker_eq_bot']

theorem linearIndependent_iff' :
    LinearIndependent R v ↔
      ∀ s : Finset ι, ∀ g : ι → R, ∑ i ∈ s, g i • v i = 0 → ∀ i ∈ s, g i = 0 := by
  rw [linearIndependent_iff'ₛ]
  refine ⟨fun h s f ↦ ?_, fun h s f g ↦ ?_⟩
  · convert h s f 0; simp_rw [Pi.zero_apply, zero_smul, Finset.sum_const_zero]
  · rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
    convert h s (f - g) using 3 <;> simp only [Pi.sub_apply, sub_smul, sub_eq_zero]

theorem linearIndependent_iff'' :
    LinearIndependent R v ↔
      ∀ (s : Finset ι) (g : ι → R), (∀ i ∉ s, g i = 0) → ∑ i ∈ s, g i • v i = 0 → ∀ i, g i = 0 := by
  classical
  exact linearIndependent_iff'.trans
    ⟨fun H s g hg hv i => if his : i ∈ s then H s g hv i his else hg i his, fun H s g hg i hi => by
      convert
        H s (fun j => if j ∈ s then g j else 0) (fun j hj => if_neg hj)
          (by simp_rw [ite_smul, zero_smul, Finset.sum_extend_by_zero, hg]) i
      exact (if_pos hi).symm⟩

theorem not_linearIndependent_iff :
    ¬LinearIndependent R v ↔
      ∃ s : Finset ι, ∃ g : ι → R, ∑ i ∈ s, g i • v i = 0 ∧ ∃ i ∈ s, g i ≠ 0 := by
  rw [linearIndependent_iff']
  simp only [exists_prop, not_forall]

theorem Fintype.linearIndependent_iff [Fintype ι] :
    LinearIndependent R v ↔ ∀ g : ι → R, ∑ i, g i • v i = 0 → ∀ i, g i = 0 := by
  refine
    ⟨fun H g => by simpa using linearIndependent_iff'.1 H Finset.univ g, fun H =>
      linearIndependent_iff''.2 fun s g hg hs i => H _ ?_ _⟩
  rw [← hs]
  refine (Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_).symm
  rw [hg i hi, zero_smul]

/-- A finite family of vectors `v i` is linear independent iff the linear map that sends
`c : ι → R` to `∑ i, c i • v i` has the trivial kernel. -/
theorem Fintype.linearIndependent_iff' [Fintype ι] [DecidableEq ι] :
    LinearIndependent R v ↔
      LinearMap.ker (LinearMap.lsum R (fun _ ↦ R) ℕ fun i ↦ LinearMap.id.smulRight (v i)) = ⊥ := by
  simp [Fintype.linearIndependent_iff, LinearMap.ker_eq_bot', funext_iff]

theorem Fintype.not_linearIndependent_iff [Fintype ι] :
    ¬LinearIndependent R v ↔ ∃ g : ι → R, ∑ i, g i • v i = 0 ∧ ∃ i, g i ≠ 0 := by
  simpa using not_iff_not.2 Fintype.linearIndependent_iff

/-- Also see `LinearIndependent.pair_iff'` for a simpler version over fields. -/
lemma LinearIndependent.pair_iff {x y : M} :
    LinearIndependent R ![x, y] ↔ ∀ (s t : R), s • x + t • y = 0 → s = 0 ∧ t = 0 := by
  refine ⟨fun h s t hst ↦ h.eq_zero_of_pair hst, fun h ↦ ?_⟩
  apply Fintype.linearIndependent_iff.2
  intro g hg
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hg
  intro i
  fin_cases i
  exacts [(h _ _ hg).1, (h _ _ hg).2]

lemma LinearIndependent.pair_symm_iff {x y : M} :
    LinearIndependent R ![x, y] ↔ LinearIndependent R ![y, x] := by
  suffices ∀ x y : M, LinearIndependent R ![x, y] → LinearIndependent R ![y, x] by tauto
  simp only [LinearIndependent.pair_iff]
  intro x y h s t
  specialize h t s
  rwa [add_comm, and_comm]

/-- If the kernel of a linear map is disjoint from the span of a family of vectors,
then the family is linearly independent iff it is linearly independent after composing with
the linear map. -/
protected theorem LinearMap.linearIndependent_iff_of_disjoint (f : M →ₗ[R] M')
    (hf_inj : Disjoint (span R (Set.range v)) (LinearMap.ker f)) :
    LinearIndependent R (f ∘ v) ↔ LinearIndependent R v :=
  f.linearIndependent_iff_of_injOn <| LinearMap.injOn_of_disjoint_ker le_rfl hf_inj

open Finset in
/-- If `∑ i, f i • v i = ∑ i, g i • v i`, then for all `i`, `f i = g i`. -/
theorem LinearIndependent.eq_coords_of_eq [Fintype ι] {v : ι → M} (hv : LinearIndependent R v)
    {f : ι → R} {g : ι → R} (heq : ∑ i, f i • v i = ∑ i, g i • v i) (i : ι) : f i = g i := by
  rw [← sub_eq_zero, ← sum_sub_distrib] at heq
  simp_rw [← sub_smul] at heq
  exact sub_eq_zero.mp ((linearIndependent_iff'.mp hv) univ (fun i ↦ f i - g i) heq i (mem_univ i))

/-- If `v` is a linearly independent family of vectors and the kernel of a linear map `f` is
disjoint with the submodule spanned by the vectors of `v`, then `f ∘ v` is a linearly independent
family of vectors. See also `LinearIndependent.map'` for a special case assuming `ker f = ⊥`. -/
theorem LinearIndependent.map (hv : LinearIndependent R v) {f : M →ₗ[R] M'}
    (hf_inj : Disjoint (span R (range v)) (LinearMap.ker f)) : LinearIndependent R (f ∘ v) :=
  (f.linearIndependent_iff_of_disjoint hf_inj).mpr hv

/-- An injective linear map sends linearly independent families of vectors to linearly independent
families of vectors. See also `LinearIndependent.map` for a more general statement. -/
theorem LinearIndependent.map' (hv : LinearIndependent R v) (f : M →ₗ[R] M')
    (hf_inj : LinearMap.ker f = ⊥) : LinearIndependent R (f ∘ v) :=
  hv.map <| by simp_rw [hf_inj, disjoint_bot_right]

/-- If `M / R` and `M' / R'` are modules, `i : R' → R` is a map, `j : M →+ M'` is a monoid map,
such that they send non-zero elements to non-zero elements, and compatible with the scalar
multiplications on `M` and `M'`, then `j` sends linearly independent families of vectors to
linearly independent families of vectors. As a special case, taking `R = R'`
it is `LinearIndependent.map'`. -/
theorem LinearIndependent.map_of_injective_injective {R' M' : Type*}
    [Ring R'] [AddCommGroup M'] [Module R' M'] (hv : LinearIndependent R v)
    (i : R' → R) (j : M →+ M') (hi : ∀ r, i r = 0 → r = 0) (hj : ∀ m, j m = 0 → m = 0)
    (hc : ∀ (r : R') (m : M), j (i r • m) = r • j m) : LinearIndependent R' (j ∘ v) := by
  rw [linearIndependent_iff'] at hv ⊢
  intro S r' H s hs
  simp_rw [comp_apply, ← hc, ← map_sum] at H
  exact hi _ <| hv _ _ (hj _ H) s hs

/-- If `M / R` and `M' / R'` are modules, `i : R → R'` is a surjective map which maps zero to zero,
`j : M →+ M'` is a monoid map which sends non-zero elements to non-zero elements, such that the
scalar multiplications on `M` and `M'` are compatible, then `j` sends linearly independent families
of vectors to linearly independent families of vectors. As a special case, taking `R = R'`
it is `LinearIndependent.map'`. -/
theorem LinearIndependent.map_of_surjective_injective {R' M' : Type*}
    [Ring R'] [AddCommGroup M'] [Module R' M'] (hv : LinearIndependent R v)
    (i : R → R') (j : M →+ M') (hi : Surjective i) (hj : ∀ m, j m = 0 → m = 0)
    (hc : ∀ (r : R) (m : M), j (r • m) = i r • j m) : LinearIndependent R' (j ∘ v) :=
  hv.map_of_surjective_injectiveₛ i _ hi ((injective_iff_map_eq_zero _).mpr hj) hc

/-- If `f` is an injective linear map, then the family `f ∘ v` is linearly independent
if and only if the family `v` is linearly independent. -/
protected theorem LinearMap.linearIndependent_iff (f : M →ₗ[R] M') (hf_inj : LinearMap.ker f = ⊥) :
    LinearIndependent R (f ∘ v) ↔ LinearIndependent R v :=
  f.linearIndependent_iff_of_disjoint <| by simp_rw [hf_inj, disjoint_bot_right]

/-- See `LinearIndependent.fin_cons` for a family of elements in a vector space. -/
theorem LinearIndependent.fin_cons' {m : ℕ} (x : M) (v : Fin m → M) (hli : LinearIndependent R v)
    (x_ortho : ∀ (c : R) (y : Submodule.span R (Set.range v)), c • x + y = (0 : M) → c = 0) :
    LinearIndependent R (Fin.cons x v : Fin m.succ → M) := by
  rw [Fintype.linearIndependent_iff] at hli ⊢
  rintro g total_eq j
  simp_rw [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] at total_eq
  have : g 0 = 0 := by
    refine x_ortho (g 0) ⟨∑ i : Fin m, g i.succ • v i, ?_⟩ total_eq
    exact sum_mem fun i _ => smul_mem _ _ (subset_span ⟨i, rfl⟩)
  rw [this, zero_smul, zero_add] at total_eq
  exact Fin.cases this (hli _ total_eq) j

section LinearIndepOn

/-! The following give equivalent versions of `LinearIndepOn` and its negation. -/

theorem linearIndepOn_iff : LinearIndepOn R v s ↔
      ∀ l ∈ Finsupp.supported R R s, (Finsupp.linearCombination R v) l = 0 → l = 0 :=
  linearIndepOn_iffₛ.trans ⟨fun h l hl ↦ h l hl 0 (zero_mem _), fun h f hf g hg eq ↦
    sub_eq_zero.mp (h (f - g) (sub_mem hf hg) <| by rw [map_sub, eq, sub_self])⟩

@[deprecated (since := "2025-02-15")] alias linearIndependent_comp_subtype := linearIndepOn_iff

@[deprecated (since := "2025-02-15")] alias linearIndependent_subtype := linearIndepOn_iff

/-- An indexed set of vectors is linearly dependent iff there is a nontrivial
`Finsupp.linearCombination` of the vectors that is zero. -/
theorem linearDepOn_iff' : ¬LinearIndepOn R v s ↔
      ∃ f : ι →₀ R, f ∈ Finsupp.supported R R s ∧ Finsupp.linearCombination R v f = 0 ∧ f ≠ 0 := by
  simp [linearIndepOn_iff, and_left_comm]

@[deprecated (since := "2025-02-15")] alias linearDependent_comp_subtype' := linearDepOn_iff'

/-- A version of `linearDepOn_iff'` with `Finsupp.linearCombination` unfolded. -/
theorem linearDepOn_iff : ¬LinearIndepOn R v s ↔
      ∃ f : ι →₀ R, f ∈ Finsupp.supported R R s ∧ ∑ i ∈ f.support, f i • v i = 0 ∧ f ≠ 0 :=
  linearDepOn_iff'

@[deprecated (since := "2025-02-15")] alias linearDependent_comp_subtype := linearDepOn_iff

theorem linearIndepOn_iff_disjoint: LinearIndepOn R v s ↔
      Disjoint (Finsupp.supported R R s) (LinearMap.ker <| Finsupp.linearCombination R v) := by
  rw [linearIndepOn_iff, LinearMap.disjoint_ker]

@[deprecated (since := "2025-02-15")] alias linearIndependent_comp_subtype_disjoint :=
    linearIndepOn_iff_disjoint

@[deprecated (since := "2025-02-15")] alias linearIndependent_subtype_disjoint :=
    linearIndepOn_iff_disjoint

theorem linearIndepOn_iff_linearCombinationOn :
    LinearIndepOn R v s ↔ (LinearMap.ker <| Finsupp.linearCombinationOn ι M R v s) = ⊥ :=
  linearIndepOn_iff_linearCombinationOnₛ.trans <|
    LinearMap.ker_eq_bot (M := Finsupp.supported R R s).symm

@[deprecated (since := "2024-08-29")] alias linearIndependent_iff_totalOn :=
  linearIndepOn_iff_linearCombinationOn

@[deprecated (since := "2025-02-15")] alias linearIndependent_iff_linearCombinationOn :=
  linearIndepOn_iff_linearCombinationOn

end LinearIndepOn

end Module

/-! ### Properties which require `Ring R` -/


section Module

variable {v : ι → M}
variable [Ring R] [AddCommGroup M] [AddCommGroup M']
variable [Module R M] [Module R M']

/-- If two vectors `x` and `y` are linearly independent, so are their linear combinations
`a x + b y` and `c x + d y` provided the determinant `a * d - b * c` is nonzero. -/
lemma LinearIndependent.linear_combination_pair_of_det_ne_zero {R M : Type*} [CommRing R]
    [NoZeroDivisors R] [AddCommGroup M] [Module R M]
    {x y : M} (h : LinearIndependent R ![x, y])
    {a b c d : R} (h' : a * d - b * c ≠ 0) :
    LinearIndependent R ![a • x + b • y, c • x + d • y] := by
  apply LinearIndependent.pair_iff.2 (fun s t hst ↦ ?_)
  have H : (s * a + t * c) • x + (s * b + t * d) • y = 0 := by
    convert hst using 1
    module
  have I1 : s * a + t * c = 0 := (h.eq_zero_of_pair H).1
  have I2 : s * b + t * d = 0 := (h.eq_zero_of_pair H).2
  have J1 : (a * d - b * c) * s = 0 := by linear_combination d * I1 - c * I2
  have J2 : (a * d - b * c) * t = 0 := by linear_combination -b * I1 + a * I2
  exact ⟨by simpa [h'] using mul_eq_zero.1 J1, by simpa [h'] using mul_eq_zero.1 J2⟩

theorem linearIndependent_sum {v : ι ⊕ ι' → M} :
    LinearIndependent R v ↔
      LinearIndependent R (v ∘ Sum.inl) ∧
        LinearIndependent R (v ∘ Sum.inr) ∧
          Disjoint (Submodule.span R (range (v ∘ Sum.inl)))
            (Submodule.span R (range (v ∘ Sum.inr))) := by
  classical
  rw [range_comp v, range_comp v]
  refine ⟨?_, ?_⟩
  · intro h
    refine ⟨h.comp _ Sum.inl_injective, h.comp _ Sum.inr_injective, ?_⟩
    refine h.disjoint_span_image ?_
    -- Porting note: `isCompl_range_inl_range_inr.1` timeouts.
    exact IsCompl.disjoint isCompl_range_inl_range_inr
  rintro ⟨hl, hr, hlr⟩
  rw [linearIndependent_iff'] at *
  intro s g hg i hi
  have :
    ((∑ i ∈ s.preimage Sum.inl Sum.inl_injective.injOn, (fun x => g x • v x) (Sum.inl i)) +
        ∑ i ∈ s.preimage Sum.inr Sum.inr_injective.injOn, (fun x => g x • v x) (Sum.inr i)) =
      0 := by
    -- Porting note: `g` must be specified.
    rw [Finset.sum_preimage' (g := fun x => g x • v x),
      Finset.sum_preimage' (g := fun x => g x • v x), ← Finset.sum_union, ← Finset.filter_or]
    · simpa only [← mem_union, range_inl_union_range_inr, mem_univ, Finset.filter_True]
    · -- Porting note: Here was one `exact`, but timeouted.
      refine Finset.disjoint_filter.2 fun x _ hx =>
        disjoint_left.1 ?_ hx
      exact IsCompl.disjoint isCompl_range_inl_range_inr
  rw [← eq_neg_iff_add_eq_zero] at this
  rw [disjoint_def'] at hlr
  have A := by
    refine hlr _ (sum_mem fun i _ => ?_) _ (neg_mem <| sum_mem fun i _ => ?_) this
    · exact smul_mem _ _ (subset_span ⟨Sum.inl i, mem_range_self _, rfl⟩)
    · exact smul_mem _ _ (subset_span ⟨Sum.inr i, mem_range_self _, rfl⟩)
  rcases i with i | i
  · exact hl _ _ A i (Finset.mem_preimage.2 hi)
  · rw [this, neg_eq_zero] at A
    exact hr _ _ A i (Finset.mem_preimage.2 hi)

theorem LinearIndependent.sum_type {v' : ι' → M} (hv : LinearIndependent R v)
    (hv' : LinearIndependent R v')
    (h : Disjoint (Submodule.span R (range v)) (Submodule.span R (range v'))) :
    LinearIndependent R (Sum.elim v v') :=
  linearIndependent_sum.2 ⟨hv, hv', h⟩

-- TODO - generalize this to non-identity functions
theorem LinearIndepOn.id_union {s t : Set M} (hs : LinearIndepOn R id s)
    (ht : LinearIndepOn R id t) (hst : Disjoint (span R s) (span R t)) :
    LinearIndepOn R id (s ∪ t) := by
  have h := hs.linearIndependent.sum_type ht.linearIndependent (by simpa)
  simpa [id_eq] using h.linearIndepOn_id

@[deprecated (since := "2025-02-14")] alias LinearIndependent.union := LinearIndepOn.id_union

theorem linearIndepOn_id_iUnion_finite {f : ι → Set M} (hl : ∀ i, LinearIndepOn R id (f i))
    (hd : ∀ i, ∀ t : Set ι, t.Finite → i ∉ t → Disjoint (span R (f i)) (⨆ i ∈ t, span R (f i))) :
    LinearIndepOn R id (⋃ i, f i) := by
  classical
  rw [iUnion_eq_iUnion_finset f]
  apply linearIndepOn_iUnion_of_directed
  · apply directed_of_isDirected_le
    exact fun t₁ t₂ ht => iUnion_mono fun i => iUnion_subset_iUnion_const fun h => ht h
  intro t
  induction t using Finset.induction_on with
  | empty => simp
  | @insert i s his ih =>
    rw [Finset.set_biUnion_insert]
    refine (hl _).id_union ih ?_
    rw [span_iUnion₂]
    exact hd i s s.finite_toSet his

@[deprecated (since := "2025-02-15")] alias
    linearIndependent_iUnion_finite_subtype := linearIndepOn_id_iUnion_finite

theorem linearIndependent_iUnion_finite {η : Type*} {ιs : η → Type*} {f : ∀ j : η, ιs j → M}
    (hindep : ∀ j, LinearIndependent R (f j))
    (hd : ∀ i, ∀ t : Set η,
      t.Finite → i ∉ t → Disjoint (span R (range (f i))) (⨆ i ∈ t, span R (range (f i)))) :
    LinearIndependent R fun ji : Σ j, ιs j => f ji.1 ji.2 := by
  nontriviality R
  apply LinearIndependent.of_linearIndepOn_id_range
  · rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ hxy
    by_cases h_cases : x₁ = y₁
    · subst h_cases
      refine Sigma.eq rfl ?_
      rw [LinearIndependent.injective (hindep _) hxy]
    · have h0 : f x₁ x₂ = 0 := by
        apply
          disjoint_def.1 (hd x₁ {y₁} (finite_singleton y₁) fun h => h_cases (eq_of_mem_singleton h))
            (f x₁ x₂) (subset_span (mem_range_self _))
        rw [iSup_singleton]
        simp only at hxy
        rw [hxy]
        exact subset_span (mem_range_self y₂)
      exact False.elim ((hindep x₁).ne_zero _ h0)
  rw [range_sigma_eq_iUnion_range]
  apply linearIndepOn_id_iUnion_finite (fun j => (hindep j).linearIndepOn_id) hd

open LinearMap

theorem linearIndependent_iff_not_smul_mem_span :
    LinearIndependent R v ↔ ∀ (i : ι) (a : R), a • v i ∈ span R (v '' (univ \ {i})) → a = 0 :=
  ⟨fun hv ↦ hv.not_smul_mem_span, fun H =>
    linearIndependent_iff.2 fun l hl => by
      ext i; simp only [Finsupp.zero_apply]
      by_contra hn
      refine hn (H i _ ?_)
      refine (Finsupp.mem_span_image_iff_linearCombination R).2 ⟨Finsupp.single i (l i) - l, ?_, ?_⟩
      · rw [Finsupp.mem_supported']
        intro j hj
        have hij : j = i :=
          Classical.not_not.1 fun hij : j ≠ i =>
            hj ((mem_diff _).2 ⟨mem_univ _, fun h => hij (eq_of_mem_singleton h)⟩)
        simp [hij]
      · simp [hl]⟩

variable (R) in
theorem exists_maximal_linearIndepOn (v : ι → M) :
    ∃ s : Set ι, (LinearIndepOn R v s) ∧ ∀ i ∉ s, ∃ a : R, a ≠ 0 ∧ a • v i ∈ span R (v '' s) := by
  classical
    rcases exists_maximal_linearIndepOn' R v with ⟨I, hIlinind, hImaximal⟩
    use I, hIlinind
    intro i hi
    specialize hImaximal (I ∪ {i}) (by simp)
    set J := I ∪ {i} with hJ
    have memJ : ∀ {x}, x ∈ J ↔ x = i ∨ x ∈ I := by simp [hJ]
    have hiJ : i ∈ J := by simp [J]
    have h := by
      refine mt hImaximal ?_
      · intro h2
        rw [h2] at hi
        exact absurd hiJ hi
    obtain ⟨f, supp_f, sum_f, f_ne⟩ := linearDepOn_iff.mp h
    have hfi : f i ≠ 0 := by
      contrapose hIlinind
      refine linearDepOn_iff.mpr ⟨f, ?_, sum_f, f_ne⟩
      simp only [Finsupp.mem_supported, hJ] at supp_f ⊢
      rintro x hx
      refine (memJ.mp (supp_f hx)).resolve_left ?_
      rintro rfl
      exact hIlinind (Finsupp.mem_support_iff.mp hx)
    use f i, hfi
    have hfi' : i ∈ f.support := Finsupp.mem_support_iff.mpr hfi
    rw [← Finset.insert_erase hfi', Finset.sum_insert (Finset.not_mem_erase _ _),
      add_eq_zero_iff_eq_neg] at sum_f
    rw [sum_f]
    refine neg_mem (sum_mem fun c hc => smul_mem _ _ (subset_span ⟨c, ?_, rfl⟩))
    exact (memJ.mp (supp_f (Finset.erase_subset _ _ hc))).resolve_left (Finset.ne_of_mem_erase hc)

@[deprecated (since := "2025-02-15")] alias
  exists_maximal_independent := exists_maximal_linearIndepOn

theorem LinearIndepOn.image {s : Set M} {f : M →ₗ[R] M'}
    (hs : LinearIndepOn R id s) (hf_inj : Disjoint (span R s) (LinearMap.ker f)) :
    LinearIndepOn R id (f '' s) :=
  hs.id_imageₛ <| LinearMap.injOn_of_disjoint_ker le_rfl hf_inj

@[deprecated (since := "2025-02-15")] alias LinearIndependent.image_subtype :=
  LinearIndepOn.image

-- See, for example, Keith Conrad's note
--  <https://kconrad.math.uconn.edu/blurbs/galoistheory/linearchar.pdf>
/-- Dedekind's linear independence of characters -/
@[stacks 0CKL]
theorem linearIndependent_monoidHom (G : Type*) [Monoid G] (L : Type*) [CommRing L]
    [NoZeroDivisors L] : LinearIndependent L (M := G → L) (fun f => f : (G →* L) → G → L) := by
  -- Porting note: Some casts are required.
  letI := Classical.decEq (G →* L)
  letI : MulAction L L := DistribMulAction.toMulAction
  -- We prove linear independence by showing that only the trivial linear combination vanishes.
  exact linearIndependent_iff'.2
    -- To do this, we use `Finset` induction,
    -- Porting note: `False.elim` → `fun h => False.elim <| Finset.not_mem_empty _ h`
    fun s =>
      Finset.induction_on s
        (fun g _hg i h => False.elim <| Finset.not_mem_empty _ h) fun a s has ih g hg =>
        -- Here
        -- * `a` is a new character we will insert into the `Finset` of characters `s`,
        -- * `ih` is the fact that only the trivial linear combination of characters in `s` is zero
        -- * `hg` is the fact that `g` are the coefficients of a linear combination summing to zero
        -- and it remains to prove that `g` vanishes on `insert a s`.
        -- We now make the key calculation:
        -- For any character `i` in the original `Finset`, we have `g i • i = g i • a` as functions
        -- on the monoid `G`.
        have h1 : ∀ i ∈ s, (g i • (i : G → L)) = g i • (a : G → L) := fun i his =>
          funext fun x : G =>
            -- We prove these expressions are equal by showing
            -- the differences of their values on each monoid element `x` is zero
            eq_of_sub_eq_zero <|
            ih (fun j => g j * j x - g j * a x)
              (funext fun y : G => calc
                -- After that, it's just a chase scene.
                (∑ i ∈ s, ((g i * i x - g i * a x) • (i : G → L))) y =
                    ∑ i ∈ s, (g i * i x - g i * a x) * i y :=
                  Finset.sum_apply ..
                _ = ∑ i ∈ s, (g i * i x * i y - g i * a x * i y) :=
                  Finset.sum_congr rfl fun _ _ => sub_mul ..
                _ = (∑ i ∈ s, g i * i x * i y) - ∑ i ∈ s, g i * a x * i y :=
                  Finset.sum_sub_distrib
                _ =
                    (g a * a x * a y + ∑ i ∈ s, g i * i x * i y) -
                      (g a * a x * a y + ∑ i ∈ s, g i * a x * i y) := by
                  rw [add_sub_add_left_eq_sub]
                _ =
                    (∑ i ∈ insert a s, g i * i x * i y) -
                      ∑ i ∈ insert a s, g i * a x * i y := by
                  rw [Finset.sum_insert has, Finset.sum_insert has]
                _ =
                    (∑ i ∈ insert a s, g i * i (x * y)) -
                      ∑ i ∈ insert a s, a x * (g i * i y) := by
                  congrm ∑ i ∈ insert a s, ?_ - ∑ i ∈ insert a s, ?_
                  · rw [map_mul, mul_assoc]
                  · rw [mul_assoc, mul_left_comm]
                _ =
                    (∑ i ∈ insert a s, (g i • (i : G → L))) (x * y) -
                      a x * (∑ i ∈ insert a s, (g i • (i : G → L))) y := by
                  rw [Finset.sum_apply, Finset.sum_apply, Finset.mul_sum]; rfl
                _ = 0 - a x * 0 := by rw [hg]; rfl
                _ = 0 := by rw [mul_zero, sub_zero]
                )
              i his
        -- On the other hand, since `a` is not already in `s`, for any character `i ∈ s`
        -- there is some element of the monoid on which it differs from `a`.
        have h2 : ∀ i : G →* L, i ∈ s → ∃ y, i y ≠ a y := fun i his =>
          Classical.by_contradiction fun h =>
            have hia : i = a := MonoidHom.ext fun y =>
              Classical.by_contradiction fun hy => h ⟨y, hy⟩
            has <| hia ▸ his
        -- From these two facts we deduce that `g` actually vanishes on `s`,
        have h3 : ∀ i ∈ s, g i = 0 := fun i his =>
          let ⟨y, hy⟩ := h2 i his
          have h : g i • i y = g i • a y := congr_fun (h1 i his) y
          Or.resolve_right (mul_eq_zero.1 <| by rw [mul_sub, sub_eq_zero]; exact h)
            (sub_ne_zero_of_ne hy)
        -- And so, using the fact that the linear combination over `s` and over `insert a s` both
        -- vanish, we deduce that `g a = 0`.
        have h4 : g a = 0 :=
          calc
            g a = g a * 1 := (mul_one _).symm
            _ = (g a • (a : G → L)) 1 := by rw [← a.map_one]; rfl
            _ = (∑ i ∈ insert a s, (g i • (i : G → L))) 1 := by
              rw [Finset.sum_eq_single a]
              · intro i his hia
                rw [Finset.mem_insert] at his
                rw [h3 i (his.resolve_left hia), zero_smul]
              · intro haas
                exfalso
                apply haas
                exact Finset.mem_insert_self a s
            _ = 0 := by rw [hg]; rfl
        -- Now we're done; the last two facts together imply that `g` vanishes on every element
        -- of `insert a s`.
        (Finset.forall_mem_insert ..).2 ⟨h4, h3⟩

@[stacks 0CKM]
lemma linearIndependent_algHom_toLinearMap
    (K M L) [CommSemiring K] [Semiring M] [Algebra K M] [CommRing L] [IsDomain L] [Algebra K L] :
    LinearIndependent L (AlgHom.toLinearMap : (M →ₐ[K] L) → M →ₗ[K] L) := by
  apply LinearIndependent.of_comp (LinearMap.ltoFun K M L)
  exact (linearIndependent_monoidHom M L).comp
    (RingHom.toMonoidHom ∘ AlgHom.toRingHom)
    (fun _ _ e ↦ AlgHom.ext (DFunLike.congr_fun e :))

lemma linearIndependent_algHom_toLinearMap' (K M L) [CommRing K]
    [Semiring M] [Algebra K M] [CommRing L] [IsDomain L] [Algebra K L] [NoZeroSMulDivisors K L] :
    LinearIndependent K (AlgHom.toLinearMap : (M →ₐ[K] L) → M →ₗ[K] L) := by
  apply (linearIndependent_algHom_toLinearMap K M L).restrict_scalars
  simp_rw [Algebra.smul_def, mul_one]
  exact FaithfulSMul.algebraMap_injective K L

end Module

section Nontrivial

variable [Ring R] [Nontrivial R] [AddCommGroup M]
variable [Module R M] [NoZeroSMulDivisors R M]
variable {s t : Set M}

theorem linearIndependent_unique_iff (v : ι → M) [Unique ι] :
    LinearIndependent R v ↔ v default ≠ 0 := by
  simp only [linearIndependent_iff, Finsupp.linearCombination_unique, smul_eq_zero]
  refine ⟨fun h hv => ?_, fun hv l hl => Finsupp.unique_ext <| hl.resolve_right hv⟩
  have := h (Finsupp.single default 1) (Or.inr hv)
  exact one_ne_zero (Finsupp.single_eq_zero.1 this)

alias ⟨_, linearIndependent_unique⟩ := linearIndependent_unique_iff

theorem LinearIndepOn.singleton {v : ι → M} {i : ι} (hi : v i ≠ 0) : LinearIndepOn R v {i} :=
  linearIndependent_unique _ hi

variable (R) in
theorem LinearIndepOn.id_singleton {x : M} (hx : x ≠ 0) : LinearIndepOn R id {x} :=
  linearIndependent_unique Subtype.val hx

@[deprecated (since := "2025-02-15")] alias
    linearIndependent_singleton := LinearIndepOn.id_singleton

@[simp]
theorem linearIndependent_subsingleton_index_iff [Subsingleton ι] (f : ι → M) :
    LinearIndependent R f ↔ ∀ i, f i ≠ 0 := by
  obtain (he | he) := isEmpty_or_nonempty ι
  · simp [linearIndependent_empty_type]
  obtain ⟨_⟩ := (unique_iff_subsingleton_and_nonempty (α := ι)).2 ⟨by assumption, he⟩
  rw [linearIndependent_unique_iff]
  exact ⟨fun h i ↦ by rwa [Unique.eq_default i], fun h ↦ h _⟩

@[simp]
theorem linearIndependent_subsingleton_iff [Subsingleton M] (f : ι → M) :
    LinearIndependent R f ↔ IsEmpty ι := by
  obtain h | i := isEmpty_or_nonempty ι
  · simpa
  exact iff_of_false (fun hli ↦ hli.ne_zero i.some (Subsingleton.eq_zero (f i.some))) (by simp)

end Nontrivial

/-!
### Properties which require `DivisionRing K`

These can be considered generalizations of properties of linear independence in vector spaces.
-/


section Module

variable [DivisionRing K] [AddCommGroup V] [Module K V]
variable {v : ι → V} {s t : Set V} {x y : V}

open Submodule

/- TODO: some of the following proofs can generalized with a zero_ne_one predicate type class
   (instead of a data containing type class) -/
theorem mem_span_insert_exchange :
    x ∈ span K (insert y s) → x ∉ span K s → y ∈ span K (insert x s) := by
  simp only [mem_span_insert, forall_exists_index, and_imp]
  rintro a z hz rfl h
  refine ⟨a⁻¹, -a⁻¹ • z, smul_mem _ _ hz, ?_⟩
  have a0 : a ≠ 0 := by
    rintro rfl
    simp_all
  match_scalars <;> simp [a0]

theorem linearIndependent_iff_not_mem_span :
    LinearIndependent K v ↔ ∀ i, v i ∉ span K (v '' (univ \ {i})) := by
  apply linearIndependent_iff_not_smul_mem_span.trans
  constructor
  · intro h i h_in_span
    apply one_ne_zero (h i 1 (by simp [h_in_span]))
  · intro h i a ha
    by_contra ha'
    exact False.elim (h _ ((smul_mem_iff _ ha').1 ha))

protected theorem LinearIndepOn.insert (hs : LinearIndepOn K id s) (hx : x ∉ span K s) :
    LinearIndepOn K id (insert x s) := by
  rw [← union_singleton]
  have x0 : x ≠ 0 := mt (by rintro rfl; apply zero_mem (span K s)) hx
  apply hs.id_union (LinearIndepOn.singleton x0)
  rwa [disjoint_span_singleton' x0]

@[deprecated (since := "2025-02-15")] alias LinearIndependent.insert := LinearIndepOn.insert

theorem linearIndependent_option' :
    LinearIndependent K (fun o => Option.casesOn' o x v : Option ι → V) ↔
      LinearIndependent K v ∧ x ∉ Submodule.span K (range v) := by
  -- Porting note: Explicit universe level is required in `Equiv.optionEquivSumPUnit`.
  rw [← linearIndependent_equiv (Equiv.optionEquivSumPUnit.{u', _} ι).symm, linearIndependent_sum,
    @range_unique _ PUnit, @linearIndependent_unique_iff PUnit, disjoint_span_singleton]
  dsimp [(· ∘ ·)]
  refine ⟨fun h => ⟨h.1, fun hx => h.2.1 <| h.2.2 hx⟩, fun h => ⟨h.1, ?_, fun hx => (h.2 hx).elim⟩⟩
  rintro rfl
  exact h.2 (zero_mem _)

theorem LinearIndependent.option (hv : LinearIndependent K v)
    (hx : x ∉ Submodule.span K (range v)) :
    LinearIndependent K (fun o => Option.casesOn' o x v : Option ι → V) :=
  linearIndependent_option'.2 ⟨hv, hx⟩

theorem linearIndependent_option {v : Option ι → V} : LinearIndependent K v ↔
    LinearIndependent K (v ∘ (↑) : ι → V) ∧
      v none ∉ Submodule.span K (range (v ∘ (↑) : ι → V)) := by
  simp only [← linearIndependent_option', Option.casesOn'_none_coe]

theorem linearIndepOn_insert {s : Set ι} {a : ι} {f : ι → V} (has : a ∉ s) :
    LinearIndepOn K f (insert a s) ↔ LinearIndepOn K f s ∧ f a ∉ Submodule.span K (f '' s) := by
  classical
  rw [LinearIndepOn, LinearIndepOn, ← linearIndependent_equiv
    ((Equiv.optionEquivSumPUnit _).trans (Equiv.Set.insert has).symm), linearIndependent_option]
  simp only [comp_def]
  rw [range_comp']
  simp

@[deprecated (since := "2025-02-15")] alias linearIndependent_insert' := linearIndepOn_insert

theorem linearIndepOn_id_insert (hxs : x ∉ s) :
    LinearIndepOn K id (insert x s) ↔ LinearIndepOn K id s ∧ x ∉ Submodule.span K s :=
  (linearIndepOn_insert (f := id) hxs).trans <| by simp

@[deprecated (since := "2025-02-15")] alias linearIndependent_insert := linearIndepOn_insert

theorem linearIndepOn_id_pair {x y : V} (hx : x ≠ 0) (hy : ∀ a : K, a • x ≠ y) :
    LinearIndepOn K id {x, y} :=
  pair_comm y x ▸ (LinearIndepOn.id_singleton K hx).insert (x := y) <|
    mt mem_span_singleton.1 <| not_exists.2 hy

@[deprecated (since := "2025-02-15")] alias linearIndependent_pair := linearIndepOn_id_pair

/-- Also see `LinearIndependent.pair_iff` for the version over arbitrary rings. -/
theorem LinearIndependent.pair_iff' {x y : V} (hx : x ≠ 0) :
    LinearIndependent K ![x, y] ↔ ∀ a : K, a • x ≠ y := by
  rw [LinearIndependent.pair_iff]
  constructor
  · intro H a ha
    have := (H a (-1) (by simpa [← sub_eq_add_neg, sub_eq_zero])).2
    simp only [neg_eq_zero, one_ne_zero] at this
  · intro H s t hst
    by_cases ht : t = 0
    · exact ⟨by simpa [ht, hx] using hst, ht⟩
    apply_fun (t⁻¹ • ·) at hst
    simp only [smul_add, smul_smul, inv_mul_cancel₀ ht] at hst
    cases H (-(t⁻¹ * s)) <| by linear_combination (norm := match_scalars <;> noncomm_ring) -hst

theorem linearIndependent_fin_cons {n} {v : Fin n → V} :
    LinearIndependent K (Fin.cons x v : Fin (n + 1) → V) ↔
      LinearIndependent K v ∧ x ∉ Submodule.span K (range v) := by
  rw [← linearIndependent_equiv (finSuccEquiv n).symm, linearIndependent_option]
  exact Iff.rfl

theorem linearIndependent_fin_snoc {n} {v : Fin n → V} :
    LinearIndependent K (Fin.snoc v x : Fin (n + 1) → V) ↔
      LinearIndependent K v ∧ x ∉ Submodule.span K (range v) := by
  rw [Fin.snoc_eq_cons_rotate, ← Function.comp_def, linearIndependent_equiv,
    linearIndependent_fin_cons]

/-- See `LinearIndependent.fin_cons'` for an uglier version that works if you
only have a module over a semiring. -/
theorem LinearIndependent.fin_cons {n} {v : Fin n → V} (hv : LinearIndependent K v)
    (hx : x ∉ Submodule.span K (range v)) : LinearIndependent K (Fin.cons x v : Fin (n + 1) → V) :=
  linearIndependent_fin_cons.2 ⟨hv, hx⟩

theorem linearIndependent_fin_succ {n} {v : Fin (n + 1) → V} :
    LinearIndependent K v ↔
      LinearIndependent K (Fin.tail v) ∧ v 0 ∉ Submodule.span K (range <| Fin.tail v) := by
  rw [← linearIndependent_fin_cons, Fin.cons_self_tail]

theorem linearIndependent_fin_succ' {n} {v : Fin (n + 1) → V} : LinearIndependent K v ↔
    LinearIndependent K (Fin.init v) ∧ v (Fin.last _) ∉ Submodule.span K (range <| Fin.init v) := by
  rw [← linearIndependent_fin_snoc, Fin.snoc_init_self]

/-- Equivalence between `k + 1` vectors of length `n` and `k` vectors of length `n` along with a
vector in the complement of their span.
-/
def equiv_linearIndependent (n : ℕ) :
    { s : Fin (n + 1) → V // LinearIndependent K s } ≃
      Σ s : { s : Fin n → V // LinearIndependent K s },
        ((Submodule.span K (Set.range (s : Fin n → V)))ᶜ : Set V) where
  toFun s := ⟨⟨Fin.tail s.val, (linearIndependent_fin_succ.mp s.property).left⟩,
    ⟨s.val 0, (linearIndependent_fin_succ.mp s.property).right⟩⟩
  invFun s := ⟨Fin.cons s.2.val s.1.val,
    linearIndependent_fin_cons.mpr ⟨s.1.property, s.2.property⟩⟩
  left_inv _ := by simp only [Fin.cons_self_tail, Subtype.coe_eta]
  right_inv := fun ⟨_, _⟩ => by simp only [Fin.cons_zero, Subtype.coe_eta, Sigma.mk.inj_iff,
    Fin.tail_cons, heq_eq_eq, and_self]

theorem linearIndependent_fin2 {f : Fin 2 → V} :
    LinearIndependent K f ↔ f 1 ≠ 0 ∧ ∀ a : K, a • f 1 ≠ f 0 := by
  rw [linearIndependent_fin_succ, linearIndependent_unique_iff, range_unique, mem_span_singleton,
    not_exists, show Fin.tail f default = f 1 by rw [← Fin.succ_zero_eq_one]; rfl]

/-- TODO : generalize this and related results to non-identity functions -/
theorem exists_linearIndepOn_id_extension (hs : LinearIndepOn K id s) (hst : s ⊆ t) :
    ∃ b ⊆ t, s ⊆ b ∧ t ⊆ span K b ∧ LinearIndepOn K id b := by
  obtain ⟨b, sb, h⟩ := by
    refine zorn_subset_nonempty { b | b ⊆ t ∧ LinearIndepOn K id b} ?_ _ ⟨hst, hs⟩
    · refine fun c hc cc _c0 => ⟨⋃₀ c, ⟨?_, ?_⟩, fun x => ?_⟩
      · exact sUnion_subset fun x xc => (hc xc).1
      · exact linearIndepOn_sUnion_of_directed cc.directedOn fun x xc => (hc xc).2
      · exact subset_sUnion_of_mem
  refine ⟨b, h.prop.1, sb, fun x xt => by_contra fun hn ↦ hn ?_, h.prop.2⟩
  exact subset_span <| h.mem_of_prop_insert ⟨insert_subset xt h.prop.1, h.prop.2.insert hn⟩

@[deprecated (since := "2025-02-15")] alias exists_linearIndependent_extension :=
    exists_linearIndepOn_id_extension

variable (K t)

theorem exists_linearIndependent :
    ∃ b ⊆ t, span K b = span K t ∧ LinearIndependent K ((↑) : b → V) := by
  obtain ⟨b, hb₁, -, hb₂, hb₃⟩ :=
    exists_linearIndepOn_id_extension (linearIndependent_empty K V) (Set.empty_subset t)
  exact ⟨b, hb₁, (span_eq_of_le _ hb₂ (Submodule.span_mono hb₁)).symm, hb₃⟩

/-- Indexed version of `exists_linearIndependent`. -/
lemma exists_linearIndependent' (v : ι → V) :
    ∃ (κ : Type u') (a : κ → ι), Injective a ∧
      Submodule.span K (Set.range (v ∘ a)) = Submodule.span K (Set.range v) ∧
      LinearIndependent K (v ∘ a) := by
  obtain ⟨t, ht, hsp, hli⟩ := exists_linearIndependent K (Set.range v)
  choose f hf using ht
  let s : Set ι := Set.range (fun a : t ↦ f a.property)
  have hs {i : ι} (hi : i ∈ s) : v i ∈ t := by obtain ⟨a, rfl⟩ := hi; simp [hf]
  let f' (a : s) : t := ⟨v a.val, hs a.property⟩
  refine ⟨s, Subtype.val, Subtype.val_injective, hsp.symm ▸ by congr; aesop, ?_⟩
  · rw [← show Subtype.val ∘ f' = v ∘ Subtype.val by ext; simp [f']]
    apply hli.comp
    rintro ⟨i, x, rfl⟩ ⟨j, y, rfl⟩ hij
    simp only [Subtype.ext_iff, hf, f'] at hij
    simp [hij]

variable {K t}

/-- `LinearIndepOn.extend` adds vectors to a linear independent set `s ⊆ t` until it spans
all elements of `t`.
TODO - generalize the lemmas below to functions that aren't the identity. -/
noncomputable def LinearIndepOn.extend (hs : LinearIndepOn K id s) (hst : s ⊆ t) : Set V :=
  Classical.choose (exists_linearIndepOn_id_extension hs hst)

@[deprecated (since := "2025-02-15")] alias LinearIndependent.extend := LinearIndepOn.extend

theorem LinearIndepOn.extend_subset (hs : LinearIndepOn K id s) (hst : s ⊆ t) : hs.extend hst ⊆ t :=
  let ⟨hbt, _hsb, _htb, _hli⟩ := Classical.choose_spec (exists_linearIndepOn_id_extension hs hst)
  hbt

@[deprecated (since := "2025-02-15")] alias
  LinearIndependent.extend_subset := LinearIndepOn.extend_subset

theorem LinearIndepOn.subset_extend (hs : LinearIndepOn K id s) (hst : s ⊆ t) : s ⊆ hs.extend hst :=
  let ⟨_hbt, hsb, _htb, _hli⟩ := Classical.choose_spec (exists_linearIndepOn_id_extension hs hst)
  hsb

@[deprecated (since := "2025-02-15")] alias
  LinearIndependent.subset_extend := LinearIndepOn.subset_extend

theorem LinearIndepOn.subset_span_extend (hs : LinearIndepOn K id s) (hst : s ⊆ t) :
    t ⊆ span K (hs.extend hst) :=
  let ⟨_hbt, _hsb, htb, _hli⟩ := Classical.choose_spec (exists_linearIndepOn_id_extension hs hst)
  htb

@[deprecated (since := "2025-02-15")] alias
  LinearIndependent.subset_span_extend := LinearIndepOn.subset_span_extend

theorem LinearIndepOn.span_extend_eq_span (hs : LinearIndepOn K id s) (hst : s ⊆ t) :
    span K (hs.extend hst) = span K t :=
  le_antisymm (span_mono (hs.extend_subset hst)) (span_le.2 (hs.subset_span_extend hst))

@[deprecated (since := "2025-02-15")] alias
  LinearIndependent.span_extend_eq_span := LinearIndepOn.span_extend_eq_span

theorem LinearIndepOn.linearIndepOn_extend (hs : LinearIndepOn K id s) (hst : s ⊆ t) :
    LinearIndepOn K id (hs.extend hst) :=
  let ⟨_hbt, _hsb, _htb, hli⟩ := Classical.choose_spec (exists_linearIndepOn_id_extension hs hst)
  hli

@[deprecated (since := "2025-02-15")] alias
  LinearIndependent.linearIndependent_extend := LinearIndepOn.linearIndepOn_extend

-- TODO(Mario): rewrite?
theorem exists_of_linearIndepOn_of_finite_span {t : Finset V}
    (hs : LinearIndepOn K id s) (hst : s ⊆ (span K ↑t : Submodule K V)) :
    ∃ t' : Finset V, ↑t' ⊆ s ∪ ↑t ∧ s ⊆ ↑t' ∧ t'.card = t.card := by
  classical
  have :
    ∀ t : Finset V,
      ∀ s' : Finset V,
        ↑s' ⊆ s →
          s ∩ ↑t = ∅ →
            s ⊆ (span K ↑(s' ∪ t) : Submodule K V) →
              ∃ t' : Finset V, ↑t' ⊆ s ∪ ↑t ∧ s ⊆ ↑t' ∧ t'.card = (s' ∪ t).card :=
    fun t =>
    Finset.induction_on t
      (fun s' hs' _ hss' =>
        have : s = ↑s' := eq_of_linearIndepOn_id_of_span_subtype hs hs' <| by simpa using hss'
        ⟨s', by simp [this]⟩)
      fun b₁ t hb₁t ih s' hs' hst hss' =>
      have hb₁s : b₁ ∉ s := fun h => by
        have : b₁ ∈ s ∩ ↑(insert b₁ t) := ⟨h, Finset.mem_insert_self _ _⟩
        rwa [hst] at this
      have hb₁s' : b₁ ∉ s' := fun h => hb₁s <| hs' h
      have hst : s ∩ ↑t = ∅ :=
        eq_empty_of_subset_empty <|
          -- Porting note: `-inter_subset_left, -subset_inter_iff` required.
          Subset.trans
            (by simp [inter_subset_inter, Subset.refl, -inter_subset_left, -subset_inter_iff])
            (le_of_eq hst)
      Classical.by_cases (p := s ⊆ (span K ↑(s' ∪ t) : Submodule K V))
        (fun this =>
          let ⟨u, hust, hsu, Eq⟩ := ih _ hs' hst this
          have hb₁u : b₁ ∉ u := fun h => (hust h).elim hb₁s hb₁t
          ⟨insert b₁ u, by simp [insert_subset_insert hust], Subset.trans hsu (by simp), by
            simp [Eq, hb₁t, hb₁s', hb₁u]⟩)
        fun this =>
        let ⟨b₂, hb₂s, hb₂t⟩ := not_subset.mp this
        have hb₂t' : b₂ ∉ s' ∪ t := fun h => hb₂t <| subset_span h
        have : s ⊆ (span K ↑(insert b₂ s' ∪ t) : Submodule K V) := fun b₃ hb₃ => by
          have : ↑(s' ∪ insert b₁ t) ⊆ insert b₁ (insert b₂ ↑(s' ∪ t) : Set V) := by
            simp only [insert_eq, union_subset_union, Subset.refl,
              subset_union_right, Finset.union_insert, Finset.coe_insert]
          have hb₃ : b₃ ∈ span K (insert b₁ (insert b₂ ↑(s' ∪ t) : Set V)) :=
            span_mono this (hss' hb₃)
          have : s ⊆ (span K (insert b₁ ↑(s' ∪ t)) : Submodule K V) := by
            simpa [insert_eq, -singleton_union, -union_singleton] using hss'
          have hb₁ : b₁ ∈ span K (insert b₂ ↑(s' ∪ t)) :=
            mem_span_insert_exchange (this hb₂s) hb₂t
          rw [span_insert_eq_span hb₁] at hb₃; simpa using hb₃
        let ⟨u, hust, hsu, eq⟩ := ih _ (by simp [insert_subset_iff, hb₂s, hs']) hst this
        ⟨u, Subset.trans hust <| union_subset_union (Subset.refl _) (by simp [subset_insert]), hsu,
          by simp [eq, hb₂t', hb₁t, hb₁s']⟩
  have eq : ((t.filter fun x => x ∈ s) ∪ t.filter fun x => x ∉ s) = t := by
    ext1 x
    by_cases x ∈ s <;> simp [*]
  apply
    Exists.elim
      (this (t.filter fun x => x ∉ s) (t.filter fun x => x ∈ s) (by simp [Set.subset_def])
        (by simp +contextual [Set.ext_iff]) (by rwa [eq]))
  intro u h
  exact
    ⟨u, Subset.trans h.1 (by simp +contextual [subset_def, and_imp, or_imp]),
      h.2.1, by simp only [h.2.2, eq]⟩

@[deprecated (since := "2025-02-15")] alias
  exists_of_linearIndependent_of_finite_span := exists_of_linearIndepOn_of_finite_span

theorem exists_finite_card_le_of_finite_of_linearIndependent_of_span (ht : t.Finite)
    (hs : LinearIndepOn K id s) (hst : s ⊆ span K t) :
    ∃ h : s.Finite, h.toFinset.card ≤ ht.toFinset.card :=
  have : s ⊆ (span K ↑ht.toFinset : Submodule K V) := by simpa
  let ⟨u, _hust, hsu, Eq⟩ := exists_of_linearIndepOn_of_finite_span hs this
  have : s.Finite := u.finite_toSet.subset hsu
  ⟨this, by rw [← Eq]; exact Finset.card_le_card <| Finset.coe_subset.mp <| by simp [hsu]⟩

end Module

set_option linter.style.longFile 2000
