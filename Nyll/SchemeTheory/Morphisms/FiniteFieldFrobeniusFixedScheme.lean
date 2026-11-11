/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Morphisms.AffineFixedPointEqualizer
public import Nyll.SchemeTheory.Morphisms.FrobeniusOver
public import Nyll.SchemeTheory.RingTheory.Etale.FiniteFieldFrobeniusFixedQuotient
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.MorphismProperty.Basic
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.RingHom.Finite

/-!
# The original Frobenius fixed-point scheme is finite étale

The actual scheme equalizer, not an assumed coordinate-ring model, is
identified with the finite étale Frobenius fixed quotient. The endomorphism
is the native categorical power of the original scheme Frobenius.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

variable (k A : Type u) [Field k] [Fintype k] [CommRing A] [Algebra k A]

/-- The scalar structure used for Frobenius on the affine spectrum. -/
@[instance_reducible]
def specOver :
    (Spec (CommRingCat.of A)).Over (Spec (CommRingCat.of k)) :=
  ⟨Spec.algebraMap k A⟩

attribute [local instance] specOver

/-- Native powers of affine scheme Frobenius are the spectra of the
corresponding powers of the original algebra endomorphism. -/
theorem finiteFieldFrobenius_pow_spec (m : ℕ) :
    ((End.of ((Spec (CommRingCat.of A)).finiteFieldFrobenius k)) ^ m).asHom =
      Spec.map (CommRingCat.ofHom (FiniteField.frobeniusAlgHom k A ^ m).toRingHom) := by
  induction m with
  | zero =>
      change 𝟙 (Spec (CommRingCat.of A)) = Spec.map (𝟙 (CommRingCat.of A))
      exact (Spec.map_id _).symm
  | succ m ih =>
      rw [pow_succ', End.mul_asHom]
      change ((End.of ((Spec (CommRingCat.of A)).finiteFieldFrobenius k)) ^ m).asHom ≫
        (Spec (CommRingCat.of A)).finiteFieldFrobenius k = _
      rw [ih, Scheme.finiteFieldFrobenius_spec, ← Spec.map_comp]
      apply congrArg Spec.map
      apply CommRingCat.hom_ext
      ext a
      change (FiniteField.frobeniusAlgHom k A ^ m)
          (FiniteField.frobeniusAlgHom k A a) =
        (FiniteField.frobeniusAlgHom k A ^ (m + 1)) a
      rw [pow_succ]
      rfl

omit [Fintype k] in
private theorem fixedPointQuotientSpecIsoEqualizer_hom_structure
    (h : A →ₐ[k] A) :
    (fixedPointQuotientSpecIsoEqualizer h.toRingHom).hom ≫
        equalizer.ι (Spec.map (CommRingCat.ofHom h.toRingHom))
          (𝟙 (Spec (CommRingCat.of A))) ≫ Spec.algebraMap k A =
      Spec.algebraMap k (A ⧸ h.toRingHom.fixedPointIdeal) := by
  rw [← Category.assoc, fixedPointQuotientSpecIsoEqualizer_hom_ι,
    ← Spec.map_comp]
  rfl

/-- The actual affine equalizer of every positive Frobenius power and the
identity is finite étale over the original finite field. -/
theorem finiteFieldFrobenius_fixedScheme_finite_etale
    [Algebra.FiniteType k A] (m : ℕ) (hm : 0 < m) :
    IsFinite (equalizer.ι
        (((End.of ((Spec (CommRingCat.of A)).finiteFieldFrobenius k)) ^ m).asHom)
        (𝟙 (Spec (CommRingCat.of A))) ≫ Spec.algebraMap k A) ∧
      Etale (equalizer.ι
        (((End.of ((Spec (CommRingCat.of A)).finiteFieldFrobenius k)) ^ m).asHom)
        (𝟙 (Spec (CommRingCat.of A))) ≫ Spec.algebraMap k A) := by
  rw [finiteFieldFrobenius_pow_spec]
  let h := FiniteField.frobeniusAlgHom k A ^ m
  let e := fixedPointQuotientSpecIsoEqualizer h.toRingHom
  obtain ⟨hfinite, hetale, _⟩ :=
    FiniteField.frobeniusFixedQuotient_finite_etale_reduced k A m hm
  let q := equalizer.ι (Spec.map (CommRingCat.ofHom h.toRingHom))
    (𝟙 (Spec (CommRingCat.of A))) ≫ Spec.algebraMap k A
  let s := Spec.algebraMap k (A ⧸ h.toRingHom.fixedPointIdeal)
  have he : e.hom ≫ q = s :=
    fixedPointQuotientSpecIsoEqualizer_hom_structure k A h
  have hq : q = e.inv ≫ s := by
    rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  have : IsFinite s :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr hfinite)
  have : Etale s :=
    (HasRingHomProperty.Spec_iff (P := (@Etale : MorphismProperty Scheme.{u}))).mpr
      (RingHom.etale_algebraMap.mpr hetale)
  change IsFinite q ∧ Etale q
  rw [hq]
  exact ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry
