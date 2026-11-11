/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.FieldExtensions.FiniteFrobeniusFixed
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-!
# Rational points and Frobenius-fixed geometric points

Base extension along the specified finite field extension identifies its
rational points with the points fixed by the corresponding Frobenius power.
Residue-field factorization proves the inverse for any scheme; no finiteness,
separatedness, smoothness, or properness assumption is needed.
-/

@[expose] public section

noncomputable section

open CategoryTheory NeronModelInfra

namespace AlgebraicGeometry

universe u

variable (k E Ω : Type u) [Field k] [Fintype k] [Field E] [Finite E]
    [Algebra k E] [Field Ω] [Algebra k Ω] [Algebra E Ω] [IsScalarTower k E Ω]
    [Algebra.IsAlgebraic k Ω]
    (m : ℕ) (hm : Module.finrank k E = m)

include hm in
private theorem exists_ringHom_of_frobenius_pow_fixed
    (A : Type u) [CommRing A] (a : A →+* Ω)
    (ha : ∀ z, (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω ^ m) (a z) = a z) :
    ∃ b : A →+* E, (algebraMap E Ω).comp b = a := by
  let j := algebraMap E Ω
  let e : E ≃+* j.range := RingEquiv.ofBijective j.rangeRestrict
    ⟨fun x y h => j.injective (congrArg Subtype.val h), j.rangeRestrict_surjective⟩
  have hmem (z : A) : a z ∈ j.range :=
    (FiniteField.mem_range_algebraMap_iff_frobenius_pow_fixed k E Ω m hm (a z)).mpr
      (ha z)
  let b : A →+* E := e.symm.toRingHom.comp (a.codRestrict j.range hmem)
  refine ⟨b, ?_⟩
  ext z
  exact congrArg Subtype.val (e.apply_symm_apply ⟨a z, hmem z⟩)

include hm in
/-- A point fixed by the given Frobenius power descends to the specified finite field. -/
theorem exists_schemeHom_of_frobenius_pow_fixed
    (X : Scheme.{u}) (p : Spec (.of Ω) ⟶ X)
    (hp : Spec.map (CommRingCat.ofHom
      (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω ^ m).toRingHom) ≫ p = p) :
    ∃ q : Spec (.of E) ⟶ X, Spec.algebraMap E Ω ≫ q = p := by
  obtain ⟨⟨x, a⟩, rfl⟩ := (Scheme.SpecToEquivOfField Ω X).symm.surjective p
  simp only [Scheme.SpecToEquivOfField_symm_apply] at hp ⊢
  have ha : a ≫ CommRingCat.ofHom
      (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω ^ m).toRingHom = a := by
    apply Spec.map_injective
    apply (cancel_mono (X.fromSpecResidueField x)).mp
    simpa only [Spec.map_comp, Category.assoc] using hp
  obtain ⟨b, hb⟩ := exists_ringHom_of_frobenius_pow_fixed k E Ω m hm
    (X.residueField x) a.hom
    (fun z => congrArg (fun v : X.residueField x ⟶ CommRingCat.of Ω => v.hom z) ha)
  have hbcat : CommRingCat.ofHom b ≫ CommRingCat.ofHom (algebraMap E Ω) = a :=
    CommRingCat.hom_ext hb
  refine ⟨Spec.map (CommRingCat.ofHom b) ≫ X.fromSpecResidueField x, ?_⟩
  rw [← Category.assoc, ← Spec.map_comp, hbcat]

/-- Extension of the specified finite constant field gives the actual bijection
between rational points and points fixed by the corresponding Frobenius power. -/
def finiteFieldPointsEquivFrobeniusPowFixed
    (X : Scheme.{u}) (c : X ⟶ Spec (.of k)) :
    SchemeHomOver (Spec.algebraMap k E) c ≃
      {p : SchemeHomOver (Spec.algebraMap k Ω) c //
        Spec.map (CommRingCat.ofHom
          (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω ^ m).toRingHom) ≫ p.val = p.val} := by
  have hj : Spec.algebraMap E Ω ≫ Spec.algebraMap k E = Spec.algebraMap k Ω := by
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    exact (IsScalarTower.algebraMap_eq k E Ω).symm
  have hfixed : Spec.map (CommRingCat.ofHom
      (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω ^ m).toRingHom) ≫
      Spec.algebraMap E Ω = Spec.algebraMap E Ω := by
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    ext z
    exact (FiniteField.mem_range_algebraMap_iff_frobenius_pow_fixed k E Ω m hm
      (algebraMap E Ω z)).mp ⟨z, rfl⟩
  let extend : SchemeHomOver (Spec.algebraMap k E) c →
      {p : SchemeHomOver (Spec.algebraMap k Ω) c //
        Spec.map (CommRingCat.ofHom
          (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω ^ m).toRingHom) ≫ p.val = p.val} :=
    fun q => ⟨⟨Spec.algebraMap E Ω ≫ q.val, by
      rw [Category.assoc, q.property, hj]⟩, by
      rw [← Category.assoc, hfixed]⟩
  have : Epi (Spec.algebraMap E Ω) := Flat.epi_of_flat_of_surjective _
  refine Equiv.ofBijective extend ⟨?_, ?_⟩
  · intro p q hpq
    apply Subtype.ext
    apply (cancel_epi (Spec.algebraMap E Ω)).mp
    exact congrArg (fun z => z.val.val) hpq
  · intro p
    obtain ⟨q, hq⟩ := exists_schemeHom_of_frobenius_pow_fixed k E Ω m hm
      X p.val.val p.property
    have hqc : q ≫ c = Spec.algebraMap k E := by
      apply (cancel_epi (Spec.algebraMap E Ω)).mp
      rw [← Category.assoc, hq, p.val.property, hj]
    refine ⟨⟨q, hqc⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hq

/-- The point equivalence uses the original extension-of-constants morphism. -/
theorem finiteFieldPointsEquivFrobeniusPowFixed_apply
    (X : Scheme.{u}) (c : X ⟶ Spec (.of k))
    (p : SchemeHomOver (Spec.algebraMap k E) c) :
    (finiteFieldPointsEquivFrobeniusPowFixed k E Ω m hm X c p).val.val =
      Spec.algebraMap E Ω ≫ p.val := rfl

end AlgebraicGeometry
