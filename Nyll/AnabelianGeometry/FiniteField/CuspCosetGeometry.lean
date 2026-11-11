/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Data.Set.Finite.Lattice

/-!
# Infinite directions in finite unions of subgroup cosets

An infinite subgroup coset contained in a finite union of subgroup cosets
with pairwise finite intersections lies in one of them. A finite set of
additional points does not change this assertion. The proof uses translates
of an infinite intersection, and requires neither finite index nor saturation.

An infinite direction contained in one component, with finite intersection
with every other component's subgroup, also recovers that whole component:
it consists exactly of the points whose translates by the direction stay in
the union. These are algebraic statements. Identifying their inputs with
native arithmetic coinvariants and wild inertia is a separate geometric task.
-/

@[expose] public section

open Set

namespace AnabelianGeometry.FiniteField.CuspCosetGeometry

universe u v w

variable {A : Type u} [CommGroup A]

/-- A literal left coset, with membership expressed in the original group. -/
def coset (a : A) (H : Subgroup A) : Set A := {x | a⁻¹ * x ∈ H}

theorem center_mem_coset (a : A) (H : Subgroup A) : a ∈ coset a H := by
  change a⁻¹ * a ∈ H
  rw [inv_mul_cancel]
  exact H.one_mem

private theorem difference_mem {a x y : A} {H : Subgroup A}
    (hx : x ∈ coset a H) (hy : y ∈ coset a H) : x⁻¹ * y ∈ H := by
  have h := H.mul_mem (H.inv_mem hx) hy
  simpa only [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left] using h

/-- Inclusion of nonempty subgroup cosets also includes their directions. -/
theorem direction_le_of_coset_subset {a b : A} {H K : Subgroup A}
    (h : coset a H ⊆ coset b K) : H ≤ K := by
  intro x hx
  have ha := h (center_mem_coset a H)
  have hax : a * x ∈ coset a H := by
    change a⁻¹ * (a * x) ∈ H
    rw [inv_mul_cancel_left]
    exact hx
  have hdiff := difference_mem ha (h hax)
  simpa only [inv_mul_cancel_left] using hdiff

/-- The subgroup direction is determined by the coset as an actual set. -/
theorem direction_eq_of_coset_eq {a b : A} {H K : Subgroup A}
    (h : coset a H = coset b K) : H = K :=
  le_antisymm (direction_le_of_coset_subset h.subset)
    (direction_le_of_coset_subset h.symm.subset)

/-- An actual group isomorphism sends a literal coset to the coset of its
actual subgroup image. -/
theorem image_coset {B : Type w} [CommGroup B] (e : A ≃* B)
    (a : A) (H : Subgroup A) :
    e '' coset a H = coset (e a) (H.map e.toMonoidHom) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨a⁻¹ * x, hx, by change e (a⁻¹ * x) = _; rw [map_mul, map_inv]⟩
  · rintro ⟨x, hx, hxy⟩
    refine ⟨a * x, ?_, ?_⟩
    · change a⁻¹ * (a * x) ∈ H
      rw [inv_mul_cancel_left]
      exact hx
    · change e x = (e a)⁻¹ * y at hxy
      rw [map_mul, hxy, mul_inv_cancel_left]

/-- Infinitude of a subgroup is preserved by its actual image under a
group isomorphism. -/
theorem subgroup_map_infinite {B : Type w} [CommGroup B] (e : A ≃* B)
    (H : Subgroup A) (hH : (H : Set A).Infinite) :
    ((H.map e.toMonoidHom : Subgroup B) : Set B).Infinite := by
  change (e '' (H : Set A)).Infinite
  exact hH.image (fun _ _ _ _ h => e.injective h)

/-- The intrinsic maximality condition on an infinite subgroup coset
inside an unlabelled set of group elements. -/
def IsMaximalInfiniteCoset (S : Set A) (a : A) (H : Subgroup A) : Prop :=
  (H : Set A).Infinite ∧ coset a H ⊆ S ∧
    ∀ (b : A) (J : Subgroup A), (J : Set A).Infinite →
      coset a H ⊆ coset b J → coset b J ⊆ S → coset b J = coset a H

/-- Intrinsic maximality is transported by the same group isomorphism
that transports the unlabelled ambient value set. -/
theorem IsMaximalInfiniteCoset.map {B : Type w} [CommGroup B]
    {S : Set A} {a : A} {H : Subgroup A}
    (h : IsMaximalInfiniteCoset S a H) (e : A ≃* B) :
    IsMaximalInfiniteCoset (e '' S) (e a) (H.map e.toMonoidHom) := by
  refine ⟨subgroup_map_infinite e H h.1, ?_, ?_⟩
  · rw [← image_coset e a H]
    exact Set.image_mono h.2.1
  · intro b J hJ hsup hsub
    let K := J.map e.symm.toMonoidHom
    have hK : (K : Set A).Infinite := subgroup_map_infinite e.symm J hJ
    have hsup' : coset a H ⊆ coset (e.symm b) K := by
      intro x hx
      have hx' : e x ∈ coset b J :=
        hsup ((image_coset e a H) ▸ (show e x ∈ e '' coset a H from ⟨x, hx, rfl⟩))
      have hpre := (image_coset e.symm b J) ▸
        (show e.symm (e x) ∈ e.symm '' coset b J from ⟨e x, hx', rfl⟩)
      simpa only [e.symm_apply_apply] using hpre
    have hsub' : coset (e.symm b) K ⊆ S := by
      intro x hx
      have hx' : x ∈ e.symm '' coset b J := (image_coset e.symm b J).symm ▸ hx
      obtain ⟨y, hy, hyx⟩ := hx'
      obtain ⟨z, hz, hzy⟩ := hsub hy
      have hzx : z = x := (e.symm_apply_apply z).symm.trans
        ((congrArg e.symm hzy).trans hyx)
      exact hzx ▸ hz
    have hmax := h.2.2 (e.symm b) K hK hsup' hsub'
    rw [← image_coset e a H]
    apply Set.Subset.antisymm
    · intro y hy
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      have hpre := (image_coset e.symm b J) ▸
        (show e.symm y ∈ e.symm '' coset b J from ⟨y, hy, rfl⟩)
      exact hmax ▸ hpre
    · intro y hy
      exact hsup ((image_coset e a H) ▸ hy)

private theorem coset_eq_of_mem {a b x : A} {H : Subgroup A}
    (ha : x ∈ coset a H) (hb : x ∈ coset b H) : coset a H = coset b H := by
  apply Set.Subset.antisymm
  · intro y hy
    have h := H.mul_mem hb (difference_mem ha hy)
    change _⁻¹ * y ∈ H
    simpa only [mul_assoc, mul_inv_cancel_left] using h
  · intro y hy
    have h := H.mul_mem ha (difference_mem hb hy)
    change _⁻¹ * y ∈ H
    simpa only [mul_assoc, mul_inv_cancel_left] using h

private theorem translate_mem_coset (g : A) {a x : A} {H : Subgroup A}
    (hx : x ∈ coset a H) : g * x ∈ coset (g * a) H := by
  change a⁻¹ * x ∈ H at hx
  change (g * a)⁻¹ * (g * x) ∈ H
  simpa only [mul_inv_rev, mul_assoc, inv_mul_cancel_left] using hx

/-- Translating an infinite subgroup gives an infinite coset. -/
theorem coset_infinite (a : A) (H : Subgroup A) (hH : (H : Set A).Infinite) :
    (coset a H).Infinite := by
  apply Set.Infinite.mono (s := (fun x : A => a * x) '' (H : Set A))
  · rintro _ ⟨x, hx, rfl⟩
    change a⁻¹ * (a * x) ∈ H
    rw [inv_mul_cancel_left]
    exact hx
  · exact hH.image (fun _ _ _ _ h => mul_left_cancel h)

/-- Finite intersections of the underlying subgroups imply finite
intersections of any two of their cosets. -/
theorem coset_inter_finite (a b : A) (H K : Subgroup A)
    (hHK : ((H ⊓ K : Subgroup A) : Set A).Finite) :
    (coset a H ∩ coset b K).Finite := by
  by_cases hne : (coset a H ∩ coset b K).Nonempty
  · obtain ⟨x, hx⟩ := hne
    apply (hHK.image (fun y : A => x * y)).subset
    intro y hy
    refine ⟨x⁻¹ * y, ⟨difference_mem hx.1 hy.1, difference_mem hx.2 hy.2⟩, ?_⟩
    exact mul_inv_cancel_left x y
  · have hempty : coset a H ∩ coset b K = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    rw [hempty]
    exact Set.finite_empty

omit [CommGroup A] in
private theorem exists_infinite_inter
    {ι : Type v} [Finite ι] (C : ι → Set A) (T E : Set A)
    (hT : T.Finite) (hE : E.Infinite) (hsub : E ⊆ T ∪ ⋃ i, C i) :
    ∃ i, (E ∩ C i).Infinite := by
  by_contra h
  have hfin (i : ι) : (E ∩ C i).Finite := by
    by_contra hi
    exact h ⟨i, hi⟩
  apply hE
  apply (hT.union (Set.finite_iUnion hfin)).subset
  intro x hx
  rcases hsub hx with ht | hc
  · exact Or.inl ht
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hc
    exact Or.inr (Set.mem_iUnion.mpr ⟨i, hx, hi⟩)

/-- An infinite subgroup coset cannot cross finitely many cosets whose
directions have pairwise finite intersection, even after adding finitely
many isolated points. -/
theorem coset_subset_one_of_finite_union
    {ι : Type v} [Finite ι] (b : ι → A) (I : ι → Subgroup A)
    (hI : ∀ i j, i ≠ j → ((I i ⊓ I j : Subgroup A) : Set A).Finite)
    (T : Set A) (hT : T.Finite) (a : A) (H : Subgroup A)
    (hH : (H : Set A).Infinite)
    (hsub : coset a H ⊆ T ∪ ⋃ i, coset (b i) (I i)) :
    ∃ i, coset a H ⊆ coset (b i) (I i) := by
  obtain ⟨i, hi⟩ := exists_infinite_inter (fun i => coset (b i) (I i))
    T (coset a H) hT (coset_infinite a H hH) hsub
  obtain ⟨x₀, hx₀⟩ := hi.nonempty
  refine ⟨i, ?_⟩
  intro x hx
  by_contra hxi
  let g : A := x * x₀⁻¹
  let E : Set A := (fun y : A => g * y) '' (coset a H ∩ coset (b i) (I i))
  have hg : g ∈ H := by
    change x * x₀⁻¹ ∈ H
    rw [mul_comm]
    exact difference_mem hx₀.1 hx
  have hgx : g * x₀ = x := by
    change (x * x₀⁻¹) * x₀ = x
    rw [mul_assoc, inv_mul_cancel, mul_one]
  have hEinf : E.Infinite := hi.image (fun _ _ _ _ h => mul_left_cancel h)
  have hEa : E ⊆ coset a H := by
    rintro _ ⟨y, hy, rfl⟩
    change a⁻¹ * (g * y) ∈ H
    rw [mul_left_comm a⁻¹ g y]
    exact H.mul_mem hg hy.1
  have hEi : E ⊆ coset (g * b i) (I i) := by
    rintro _ ⟨y, hy, rfl⟩
    exact translate_mem_coset g hy.2
  have hxi' : x ∈ coset (g * b i) (I i) := by
    rw [← hgx]
    exact translate_mem_coset g hx₀.2
  have hfin (j : ι) : (E ∩ coset (b j) (I j)).Finite := by
    by_cases hij : i = j
    · subst j
      have hempty : E ∩ coset (b i) (I i) = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro y ⟨hyE, hyI⟩
        have heq := coset_eq_of_mem (hEi hyE) hyI
        exact hxi (heq ▸ hxi')
      rw [hempty]
      exact Set.finite_empty
    · exact (coset_inter_finite (g * b i) (b j) (I i) (I j) (hI i j hij)).subset
        (fun _ h => ⟨hEi h.1, h.2⟩)
  obtain ⟨j, hj⟩ := exists_infinite_inter (fun j => coset (b j) (I j)) T E hT hEinf
    (hEa.trans hsub)
  exact hj (hfin j)

/-- If every component is infinite, these components are exactly the
maximal infinite subgroup cosets in the finite union with isolated points. -/
theorem maximal_infinite_coset_iff
    {ι : Type v} [Finite ι] (b : ι → A) (I : ι → Subgroup A)
    (hI : ∀ i j, i ≠ j → ((I i ⊓ I j : Subgroup A) : Set A).Finite)
    (hinf : ∀ i, (I i : Set A).Infinite)
    (T : Set A) (hT : T.Finite) (a : A) (H : Subgroup A)
    (hH : (H : Set A).Infinite)
    (hsub : coset a H ⊆ T ∪ ⋃ i, coset (b i) (I i)) :
    (∀ (c : A) (J : Subgroup A), (J : Set A).Infinite →
      coset a H ⊆ coset c J →
      coset c J ⊆ T ∪ ⋃ i, coset (b i) (I i) → coset c J = coset a H) ↔
      ∃ i, coset a H = coset (b i) (I i) := by
  constructor
  · intro hmax
    obtain ⟨i, hi⟩ := coset_subset_one_of_finite_union b I hI T hT a H hH hsub
    exact ⟨i, (hmax (b i) (I i) (hinf i) hi
      (fun _ hx => Or.inr (Set.mem_iUnion.mpr ⟨i, hx⟩))).symm⟩
  · rintro ⟨i, hi⟩ c J hJ hle hJsub
    obtain ⟨j, hj⟩ := coset_subset_one_of_finite_union b I hI T hT c J hJ hJsub
    have hij : i = j := by
      by_contra hne
      apply coset_infinite (b i) (I i) (hinf i)
      apply (coset_inter_finite (b i) (b j) (I i) (I j) (hI i j hne)).subset
      intro x hx
      exact ⟨hx, hj (hle (hi.symm ▸ hx))⟩
    subst j
    apply Set.Subset.antisymm
    · exact hj.trans hi.symm.subset
    · exact hle

/-- A distinguished infinite direction recovers the entire component
containing it, including directions not belonging to that subgroup. -/
theorem coset_saturation_eq_component
    {ι : Type v} [Finite ι] (b : ι → A) (I : ι → Subgroup A)
    (T : Set A) (hT : T.Finite) (i : ι) (W : Subgroup A)
    (hW : (W : Set A).Infinite) (hWI : W ≤ I i)
    (hother : ∀ j, i ≠ j → ((W ⊓ I j : Subgroup A) : Set A).Finite) :
    {z | coset z W ⊆ T ∪ ⋃ j, coset (b j) (I j)} = coset (b i) (I i) := by
  apply Set.ext
  intro z
  constructor
  · intro hz
    obtain ⟨j, hj⟩ := exists_infinite_inter (fun j => coset (b j) (I j))
      T (coset z W) hT (coset_infinite z W hW) hz
    have hij : i = j := by
      by_contra hne
      exact hj (coset_inter_finite z (b j) W (I j) (hother j hne))
    subst j
    obtain ⟨x, hx⟩ := hj.nonempty
    have hxI : x ∈ coset z (I i) := hWI hx.1
    have heq := coset_eq_of_mem hxI hx.2
    exact heq ▸ center_mem_coset z (I i)
  · intro hz x hx
    apply Or.inr
    apply Set.mem_iUnion.mpr
    refine ⟨i, ?_⟩
    have h := (I i).mul_mem hz (hWI hx)
    change (b i)⁻¹ * x ∈ I i
    simpa only [mul_assoc, mul_inv_cancel_left] using h

end AnabelianGeometry.FiniteField.CuspCosetGeometry
