/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GeometricFiber.CoefficientBaseChangeIso
public import Nyll.SchemeTheory.Morphisms.FiniteFieldConstantAction

/-!
# Coefficient actions in the two actual base-change presentations

The original pullback symmetry intertwines the coefficient isomorphism with
the constant-field twist. Its inverse carries the inverse field automorphism.
These geometric squares retain both projections and can be used directly by
the original cohomological pullback functoriality.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace AlgebraicGeometry.FiniteEtale

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  (X : Scheme.{u}) [X.Over (Spec (.of k))]

local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap k K))
local notation "f" => (X ↘ Spec (CommRingCat.of k))

/-- The positive coefficient action commutes with the literal pullback symmetry. -/
@[reassoc] theorem coefficientBaseChangeIso_hom_pullbackSymmetry (σ : K ≃ₐ[k] K) :
    (coefficientBaseChangeIso k K f σ).hom ≫ (pullbackSymmetry b f).hom =
      (pullbackSymmetry b f).hom ≫ Scheme.constantFieldTwist k K X σ := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullbackSymmetry_hom_comp_fst,
      coefficientBaseChangeIso_hom_snd, Scheme.constantFieldTwist_fst]
  · simp only [Category.assoc, pullbackSymmetry_hom_comp_snd,
      coefficientBaseChangeIso_hom_fst, Scheme.constantFieldTwist_snd,
      pullbackSymmetry_hom_comp_snd_assoc]

/-- Inverse coefficient pullback corresponds to the actual inverse arithmetic
twist after changing the presentation of constant base change. -/
@[reassoc] theorem coefficientBaseChangeIso_inv_pullbackSymmetry (σ : K ≃ₐ[k] K) :
    (coefficientBaseChangeIso k K f σ).inv ≫ (pullbackSymmetry b f).hom =
      (pullbackSymmetry b f).hom ≫ Scheme.constantFieldTwist k K X σ.symm := by
  let e := coefficientBaseChangeIso k K f σ
  let s := pullbackSymmetry b f
  let t := Scheme.constantFieldTwistIso k K X σ
  have hsquare : e.hom ≫ s.hom = s.hom ≫ t.hom :=
    coefficientBaseChangeIso_hom_pullbackSymmetry k K X σ
  change e.inv ≫ s.hom = s.hom ≫ t.inv
  apply (cancel_epi e.hom).1
  rw [← Category.assoc e.hom e.inv s.hom, e.hom_inv_id, Category.id_comp,
    ← Category.assoc e.hom s.hom t.inv, hsquare, Category.assoc,
    t.hom_inv_id, Category.comp_id]

/-- The inverse of the original coefficient isomorphism is the original
isomorphism belonging to the inverse coefficient automorphism. -/
theorem coefficientBaseChangeIso_inv_eq_hom_symm (σ : K ≃ₐ[k] K) :
    (coefficientBaseChangeIso k K f σ).inv =
      (coefficientBaseChangeIso k K f σ.symm).hom := by
  apply (cancel_mono (pullbackSymmetry b f).hom).1
  exact (coefficientBaseChangeIso_inv_pullbackSymmetry k K X σ).trans
    (coefficientBaseChangeIso_hom_pullbackSymmetry k K X σ.symm).symm

end AlgebraicGeometry.FiniteEtale
