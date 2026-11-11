/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Morphisms.FiniteFieldFrobeniusFixedScheme
public import Nyll.SchemeTheory.Morphisms.FrobeniusBaseChangePoints
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Equalizer
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# The actual relative Frobenius fixed scheme over geometric constants

The native equalizer/base-change comparison identifies the relative fixed
scheme with the base change of the original finite étale fixed scheme.
In particular no equation for a hypothetical fixed-locus model is assumed.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

private theorem finite_etale_equalizer_pullback
    {X S T : Scheme.{u}} (f : X ⟶ S) (b : T ⟶ S)
    (v : X ⟶ X) (hv : v ≫ f = f)
    (hfinite : IsFinite (equalizer.ι v (𝟙 X) ≫ f))
    (hetale : Etale (equalizer.ι v (𝟙 X) ≫ f)) :
    let v' := pullback.map f b f b v (𝟙 T) (𝟙 S)
      (by rw [Category.comp_id, hv]) (by rw [Category.comp_id, Category.id_comp])
    let id' := pullback.map f b f b (𝟙 X) (𝟙 T) (𝟙 S)
      (by rw [Category.comp_id, Category.id_comp])
      (by rw [Category.comp_id, Category.id_comp])
    IsFinite (equalizer.ι v' id' ≫ pullback.snd f b) ∧
      Etale (equalizer.ι v' id' ≫ pullback.snd f b) := by
  intro v' id'
  let e := equalizerPullbackMapIso hv (Category.id_comp f) b
  let e' := pullbackRightPullbackFstIso f b (equalizer.ι v (𝟙 X))
  have he : e.hom ≫ e'.hom ≫ pullback.snd (equalizer.ι v (𝟙 X) ≫ f) b =
      equalizer.ι v' id' ≫ pullback.snd f b := by
    rw [pullbackRightPullbackFstIso_hom_snd, ← Category.assoc,
      equalizerPullbackMapIso_hom_snd]
  constructor
  · rw [← he]
    infer_instance
  · rw [← he]
    infer_instance

namespace Scheme

variable (k Ω : Type u) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [Algebra.IsAlgebraic k Ω] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]

local notation "b" => Spec.algebraMap k Ω
local notation "f" => (X ↘ Spec (CommRingCat.of k))
local notation "Y" => pullback f b
local notation "F" => constantBaseChangeFrobenius k Ω X
local notation "F₀" => X.finiteFieldFrobenius k

private theorem finiteFieldFrobenius_pow_over (m : ℕ) :
    ((End.of F₀) ^ m).asHom ≫ f = f := by
  induction m with
  | zero => exact Category.id_comp f
  | succ m ih =>
      rw [pow_succ', End.mul_asHom, Category.assoc,
        finiteFieldFrobenius_comp_over, ih]

private theorem constantBaseChangeFrobenius_pow_fst (m : ℕ) :
    ((End.of F) ^ m).asHom ≫ pullback.fst f b =
      pullback.fst f b ≫ ((End.of F₀) ^ m).asHom := by
  induction m with
  | zero => exact (Category.id_comp _).trans (Category.comp_id _).symm
  | succ m ih =>
      rw [pow_succ', End.mul_asHom, Category.assoc,
        constantBaseChangeFrobenius_fst, ← Category.assoc, ih,
        Category.assoc, pow_succ', End.mul_asHom]

/-- The actual fixed scheme of relative Frobenius is finite étale whenever
the original Frobenius fixed scheme is finite étale over the finite field. -/
theorem constantBaseChangeFrobenius_fixedScheme_finite_etale
    (m : ℕ)
    (hfinite : IsFinite
      (equalizer.ι (((End.of F₀) ^ m).asHom) (𝟙 X) ≫ f))
    (hetale : Etale
      (equalizer.ι (((End.of F₀) ^ m).asHom) (𝟙 X) ≫ f)) :
    IsFinite (equalizer.ι (((End.of F) ^ m).asHom) (𝟙 Y) ≫ pullback.snd f b) ∧
      Etale (equalizer.ι (((End.of F) ^ m).asHom) (𝟙 Y) ≫ pullback.snd f b) := by
  let v' := pullback.map f b f b (((End.of F₀) ^ m).asHom)
    (𝟙 (Spec (.of Ω))) (𝟙 (Spec (.of k)))
    (by rw [Category.comp_id, finiteFieldFrobenius_pow_over])
    (by rw [Category.comp_id, Category.id_comp])
  let id' := pullback.map f b f b (𝟙 X)
    (𝟙 (Spec (.of Ω))) (𝟙 (Spec (.of k)))
    (by rw [Category.comp_id, Category.id_comp])
    (by rw [Category.comp_id, Category.id_comp])
  have hv : ((End.of F) ^ m).asHom = v' := by
    apply pullback.hom_ext
    · simpa only [v', pullback.map, pullback.lift_fst] using
        constantBaseChangeFrobenius_pow_fst k Ω X m
    · simpa only [v', pullback.map, pullback.lift_snd, Category.comp_id] using
        constantBaseChangeFrobenius_pow_snd k Ω X m
  have hid : id' = 𝟙 Y := by
    apply pullback.hom_ext
    · simp only [id', pullback.map, pullback.lift_fst, Category.comp_id, Category.id_comp]
    · simp only [id', pullback.map, pullback.lift_snd, Category.comp_id, Category.id_comp]
  have h := finite_etale_equalizer_pullback f b (((End.of F₀) ^ m).asHom)
    (finiteFieldFrobenius_pow_over k X m) hfinite hetale
  change IsFinite (equalizer.ι v' id' ≫ pullback.snd f b) ∧
    Etale (equalizer.ι v' id' ≫ pullback.snd f b) at h
  let P : (Y ⟶ Y) → (Y ⟶ Y) → Prop := fun a c =>
    IsFinite (equalizer.ι a c ≫ pullback.snd f b) ∧
      Etale (equalizer.ι a c ≫ pullback.snd f b)
  exact (congrArg₂ P hv.symm hid).mp h

end Scheme

variable (k A Ω : Type u) [Field k] [Fintype k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] [Field Ω] [Algebra k Ω] [Algebra.IsAlgebraic k Ω]

attribute [local instance] specOver

/-- The canonical fixed scheme of a positive relative-Frobenius power on
the actual geometric base change of a finite-type affine scheme is finite
étale over the extended constants. -/
theorem finiteFieldRelativeFrobenius_fixedScheme_finite_etale (m : ℕ) (hm : 0 < m) :
    let Y := pullback (Spec.algebraMap k A) (Spec.algebraMap k Ω)
    let F := Scheme.constantBaseChangeFrobenius k Ω (Spec (CommRingCat.of A))
    let g := pullback.snd (Spec.algebraMap k A) (Spec.algebraMap k Ω)
    IsFinite (equalizer.ι (((End.of F) ^ m).asHom) (𝟙 Y) ≫ g) ∧
      Etale (equalizer.ι (((End.of F) ^ m).asHom) (𝟙 Y) ≫ g) := by
  intro Y F g
  obtain ⟨hfinite, hetale⟩ := finiteFieldFrobenius_fixedScheme_finite_etale k A m hm
  exact Scheme.constantBaseChangeFrobenius_fixedScheme_finite_etale
    k Ω (Spec (CommRingCat.of A)) m hfinite hetale

end AlgebraicGeometry
