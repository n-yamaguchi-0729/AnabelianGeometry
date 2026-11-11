/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Descent of actual points fixed by coefficient Frobenius

The roots of `X^q - X` are precisely the constants in the original finite
field. This descends each affine coordinate of an actual fixed scheme point.
An affine neighborhood of its unique image point then descends the original
scheme morphism. Faithful flatness of the field extension supplies uniqueness.

Thus rational points are identified with actual coefficient-Frobenius-fixed
points, including their original morphisms. No point-count or descent
comparison is assumed, and the scheme need not be proper or affine.
-/

@[expose] public section

universe uGeom

noncomputable section

open AlgebraicGeometry CategoryTheory NeronModelInfra

namespace AnabelianGeometry.FiniteField

variable (k K : Type uGeom) [Field k] [Fintype k] [Field K]
  [Algebra k K] [Algebra.IsAlgebraic k K]

/-- A value fixed by first coefficient Frobenius comes from the original
finite constant field. -/
theorem frobenius_fixed_iff_exists_algebraMap (z : K) :
    FiniteField.frobeniusAlgEquivOfAlgebraic k K z = z ↔
      ∃ a : k, algebraMap k K a = z := by
  constructor
  · intro hz
    let f : Polynomial k := Polynomial.X ^ Fintype.card k - Polynomial.X
    have hs : f.Splits := by
      change (Polynomial.X ^ Fintype.card k - Polynomial.X : Polynomial k).Splits
      rw [Polynomial.splits_iff_card_roots, FiniteField.roots_X_pow_card_sub_X,
        ← Finset.card_def, Finset.card_univ,
        FiniteField.X_pow_card_sub_X_natDegree_eq k Fintype.one_lt_card]
    have hf : f ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero k Fintype.one_lt_card
    have hr : (f.map (algebraMap k K)).IsRoot z := by
      change Polynomial.IsRoot
        ((Polynomial.X ^ Fintype.card k - Polynomial.X : Polynomial k).map (algebraMap k K)) z
      simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
        Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
      exact sub_eq_zero.mpr hz
    exact hs.mem_range_of_isRoot hf hr
  · rintro ⟨a, rfl⟩
    exact (FiniteField.frobeniusAlgEquivOfAlgebraic k K).commutes a

private theorem exists_ringHom_of_frobenius_fixed
    {A : Type*} [CommRing A] (f : A →+* K)
    (hf : ∀ a, FiniteField.frobeniusAlgEquivOfAlgebraic k K (f a) = f a) :
    ∃ g : A →+* k, (algebraMap k K).comp g = f := by
  classical
  have h (a : A) : ∃ b : k, algebraMap k K b = f a :=
    (frobenius_fixed_iff_exists_algebraMap k K (f a)).mp (hf a)
  let t (a : A) : k := (h a).choose
  have ht (a : A) : algebraMap k K (t a) = f a := (h a).choose_spec
  let g : A →+* k :=
    { toFun := t
      map_one' := by
        apply (algebraMap k K).injective
        simp only [ht, map_one]
      map_mul' := fun a b => by
        apply (algebraMap k K).injective
        simp only [ht, map_mul]
      map_zero' := by
        apply (algebraMap k K).injective
        simp only [ht, map_zero]
      map_add' := fun a b => by
        apply (algebraMap k K).injective
        simp only [ht, map_add] }
  refine ⟨g, RingHom.ext ht⟩

private theorem exists_affineMorphism_of_frobenius_fixed
    {X : Scheme.{uGeom}} [IsAffine X] (x : Spec (.of K) ⟶ X)
    (hx : Spec.map (CommRingCat.ofHom
      (FiniteField.frobeniusAlgEquivOfAlgebraic k K).toRingHom) ≫ x = x) :
    ∃ y : Spec (.of k) ⟶ X, Spec.algebraMap k K ≫ y = x := by
  let a := x ≫ X.isoSpec.hom
  let f := (Spec.preimage a).hom
  have hf (z : Γ(X, ⊤)) :
      FiniteField.frobeniusAlgEquivOfAlgebraic k K (f z) = f z := by
    have ha : Spec.map (CommRingCat.ofHom
        (FiniteField.frobeniusAlgEquivOfAlgebraic k K).toRingHom) ≫ a = a := by
      change _ ≫ (x ≫ X.isoSpec.hom) = x ≫ X.isoSpec.hom
      rw [← Category.assoc, hx]
    have h := congrArg Spec.preimage ha
    rw [Spec.preimage_comp, Spec.preimage_map] at h
    exact congrArg (fun ψ : Γ(X, ⊤) ⟶ CommRingCat.of K => ψ.hom z) h
  obtain ⟨g, hg⟩ := exists_ringHom_of_frobenius_fixed k K f hf
  let y := Spec.map (CommRingCat.ofHom g) ≫ X.isoSpec.inv
  refine ⟨y, ?_⟩
  have hga : Spec.algebraMap k K ≫ Spec.map (CommRingCat.ofHom g) = a := by
    rw [← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom ((algebraMap k K).comp g)) = a
    rw [hg]
    exact Spec.map_preimage a
  change Spec.algebraMap k K ≫ (Spec.map (CommRingCat.ofHom g) ≫ X.isoSpec.inv) = x
  rw [← Category.assoc, hga]
  change (x ≫ X.isoSpec.hom) ≫ X.isoSpec.inv = x
  rw [Category.assoc, X.isoSpec.hom_inv_id, Category.comp_id]

/-- A fixed morphism from the algebraic coefficient field descends on an
actual affine neighborhood, then maps back to the original scheme. -/
theorem exists_morphism_of_frobenius_fixed
    {X : Scheme.{uGeom}} (x : Spec (.of K) ⟶ X)
    (hx : Spec.map (CommRingCat.ofHom
      (FiniteField.frobeniusAlgEquivOfAlgebraic k K).toRingHom) ≫ x = x) :
    ∃ y : Spec (.of k) ⟶ X, Spec.algebraMap k K ≫ y = x := by
  classical
  let 𝒰 := X.affineCover
  let i := 𝒰.idx (x (IsLocalRing.closedPoint K))
  have hr : Set.range x ⊆ Set.range (𝒰.f i) := by
    rintro _ ⟨z, rfl⟩
    have hz : z = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    rw [hz]
    exact 𝒰.covers (x (IsLocalRing.closedPoint K))
  let l := IsOpenImmersion.lift (𝒰.f i) x hr
  have hl : l ≫ 𝒰.f i = x := IsOpenImmersion.lift_fac _ _ _
  have hfix : Spec.map (CommRingCat.ofHom
      (FiniteField.frobeniusAlgEquivOfAlgebraic k K).toRingHom) ≫ l = l := by
    apply (cancel_mono (𝒰.f i)).1
    rw [Category.assoc, hl, hx]
  obtain ⟨y, hy⟩ := exists_affineMorphism_of_frobenius_fixed k K l hfix
  refine ⟨y ≫ 𝒰.f i, ?_⟩
  rw [← Category.assoc, hy, hl]

/-- Descent preserves the specified original structure morphism and is unique. -/
theorem existsUnique_rationalPoint_of_frobenius_fixed
    {X : Scheme.{uGeom}} (c : X ⟶ Spec (.of k))
    (x : SchemeHomOver (Spec.algebraMap k K) c)
    (hx : Spec.map (CommRingCat.ofHom
      (FiniteField.frobeniusAlgEquivOfAlgebraic k K).toRingHom) ≫ x.val = x.val) :
    ∃! y : SchemeHomOver (𝟙 (Spec (.of k))) c,
      Spec.algebraMap k K ≫ y.val = x.val := by
  have : Surjective (Spec.algebraMap k K) :=
    ⟨fun z => ⟨IsLocalRing.closedPoint K, Subsingleton.elim _ z⟩⟩
  have : Epi (Spec.algebraMap k K) := Flat.epi_of_flat_of_surjective _
  obtain ⟨y, hy⟩ := exists_morphism_of_frobenius_fixed k K x.val hx
  have hc : y ≫ c = 𝟙 (Spec (.of k)) := by
    apply (cancel_epi (Spec.algebraMap k K)).1
    rw [← Category.assoc, hy, x.property, Category.comp_id]
  refine ⟨⟨y, hc⟩, hy, ?_⟩
  intro z hz
  apply Subtype.ext
  exact (cancel_epi (Spec.algebraMap k K)).1 (hz.trans hy.symm)

/-- Original rational points and actual coefficient-Frobenius-fixed points
are equivalent by base change and the proved unique descent. -/
def rationalPointFrobeniusEquiv {X : Scheme.{uGeom}} (c : X ⟶ Spec (.of k)) :
    SchemeHomOver (𝟙 (Spec (.of k))) c ≃
      {x : SchemeHomOver (Spec.algebraMap k K) c //
        Spec.map (CommRingCat.ofHom
          (FiniteField.frobeniusAlgEquivOfAlgebraic k K).toRingHom) ≫ x.val = x.val} := by
  let σ := FiniteField.frobeniusAlgEquivOfAlgebraic k K
  have hσ : Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ Spec.algebraMap k K =
      Spec.algebraMap k K := by
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    exact RingHom.ext σ.commutes
  let send (y : SchemeHomOver (𝟙 (Spec (.of k))) c) :
      {x : SchemeHomOver (Spec.algebraMap k K) c //
        Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x.val = x.val} :=
    ⟨⟨Spec.algebraMap k K ≫ y.val, by
      rw [Category.assoc, y.property, Category.comp_id]⟩, by
      rw [← Category.assoc, hσ]⟩
  apply Equiv.ofBijective send
  constructor
  · intro y z h
    have : Surjective (Spec.algebraMap k K) :=
      ⟨fun x => ⟨IsLocalRing.closedPoint K, Subsingleton.elim _ x⟩⟩
    have : Epi (Spec.algebraMap k K) := Flat.epi_of_flat_of_surjective _
    apply Subtype.ext
    exact (cancel_epi (Spec.algebraMap k K)).1
      (congrArg (fun t => t.val.val) h)
  · intro x
    obtain ⟨y, hy, _⟩ := existsUnique_rationalPoint_of_frobenius_fixed k K c x.val x.property
    refine ⟨y, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hy

/-- The forward map is literally base change of the original point. -/
theorem rationalPointFrobeniusEquiv_apply {X : Scheme.{uGeom}} (c : X ⟶ Spec (.of k))
    (y : SchemeHomOver (𝟙 (Spec (.of k))) c) :
    (rationalPointFrobeniusEquiv k K c y).val.val =
      Spec.algebraMap k K ≫ y.val := rfl

end AnabelianGeometry.FiniteField
