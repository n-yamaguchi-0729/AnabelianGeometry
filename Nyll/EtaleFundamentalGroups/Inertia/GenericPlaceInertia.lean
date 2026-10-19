/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup
import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldSourceGalois
import Nyll.EtaleFundamentalGroups.Inertia.OriginalNormalizationInertiaAction
import Mathlib.Algebra.Algebra.Tower

/-!
# Place inertia in the actual geometric fundamental group

Take the original inertia subgroup of the normalization, pull it back along
restriction of function-field scalars, and map it through the actual generic
geometric monodromy homomorphism. This construction uses no character or
residue condition to define inertia.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicCurve
open SchemeTheory EtaleFundamentalGroups.Inertia

namespace AnabelianGeometry.WeightFiltration

variable {K F : Type} [Field K] [Field F] [Algebra K F]
  (X : Scheme) [IsIntegral X] [Algebra F X.functionField]
  {Ω : Type} [Field Ω] [Algebra X.functionField Ω] [Algebra F Ω]
  [IsScalarTower F X.functionField Ω]
  [IsSepClosed Ω] [IsSepClosure X.functionField Ω] [IsSepClosure F Ω]
  (p : Place K F) [Algebra p.toValuationSubring Ω]
  [IsScalarTower p.toValuationSubring F Ω]
  (Q : Ideal (normalizationCommAlgCat p.toValuationSubring Ω))

/-- The image of the original normalization inertia in the geometric fundamental group. -/
def genericPlaceInertia :
    let η := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω))
    Subgroup (Aut (FiniteEtale.fiber (η ≫ X.fromSpecStalk (genericPoint X)))) := by
  intro η
  let ι : actualNormalizationInertiaGroup p.toValuationSubring F Ω Q →* (Ω ≃ₐ[F] Ω) :=
    { toFun := actualNormalizationInertiaElement p.toValuationSubring F Ω Q
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  exact (ι.range.comap (AlgEquiv.restrictScalarsHom F)).map
    ((FiniteEtale.fundamentalGroupHom (X.fromSpecStalk (genericPoint X)) η).toMonoidHom.comp
      (toAut (FiniteEtale.fiber η) (Ω ≃ₐ[X.functionField] Ω)))

/-- Killing this image is exactly killing all original inertia elements under generic monodromy. -/
theorem genericPlaceInertia_le_ker_iff
    {G : Type} [Group G]
    (χ : Aut (FiniteEtale.fiber
      (Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) ≫
        X.fromSpecStalk (genericPoint X))) →* G) :
    let η := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω))
    genericPlaceInertia X p Q ≤ χ.ker ↔
      ∀ σ : Ω ≃ₐ[X.functionField] Ω,
        (∃ τ : actualNormalizationInertiaGroup p.toValuationSubring F Ω Q,
          actualNormalizationInertiaElement p.toValuationSubring F Ω Q τ =
            σ.restrictScalars F) →
        χ (FiniteEtale.fundamentalGroupHom (X.fromSpecStalk (genericPoint X)) η
          (toAut (FiniteEtale.fiber η) (Ω ≃ₐ[X.functionField] Ω) σ)) = 1 := by
  intro η
  constructor
  · intro h σ hσ
    exact h ⟨σ, hσ, rfl⟩
  · intro h g hg
    obtain ⟨σ, hσ, rfl⟩ := hg
    exact h σ hσ

end AnabelianGeometry.WeightFiltration
