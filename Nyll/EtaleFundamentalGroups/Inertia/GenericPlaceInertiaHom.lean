/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.GenericPlaceInertia
import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldSourceGalois
import Nyll.EtaleFundamentalGroups.Inertia.ActualNormalizationInertiaTopology
import Nyll.GaloisCohomology.Topology.FiniteExtensionGalois
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The continuous actual place-inertia map

The original inertia inclusion, the existing change-of-scalars equivalence,
and the existing geometric generic-point homomorphism form a continuous map.
Its range is the already defined actual place-inertia subgroup.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicCurve
open SchemeTheory EtaleFundamentalGroups.Inertia

namespace AnabelianGeometry.WeightFiltration

variable {k F : Type} [Field k] [Field F] [Algebra k F]
  (X : Scheme) [IsIntegral X] [Algebra F X.functionField]
  {Ω : Type} [Field Ω] [Algebra X.functionField Ω] [Algebra F Ω]
  [IsScalarTower F X.functionField Ω]
  [IsSepClosed Ω] [IsSepClosure X.functionField Ω] [IsSepClosure F Ω]
  (p : Place k F) [Algebra p.toValuationSubring Ω]
  [IsScalarTower p.toValuationSubring F Ω]
  (Q : Ideal (normalizationCommAlgCat p.toValuationSubring Ω))
  (hsurj : Function.Surjective (algebraMap F X.functionField))

/-- The original place inertia acts continuously on the geometric generic fiber. -/
def genericPlaceInertiaHom :
    let η := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω))
    (actualNormalizationInertiaGroup p.toValuationSubring F Ω Q).carrier →ₜ*
      Aut (FiniteEtale.fiber (η ≫ X.fromSpecStalk (genericPoint X))) := by
  intro η
  let e := AlgEquiv.extendScalarsHomOfSurjective (A := Ω) hsurj
  have hi : Continuous e.symm :=
    GaloisCohomology.continuous_galoisRestrictScalars F X.functionField Ω
  have hc : Continuous e :=
    Continuous.continuous_symm_of_equiv_compact_to_t2 (f := e.symm.toEquiv) hi
  let ec : (Ω ≃ₐ[F] Ω) →ₜ* (Ω ≃ₐ[X.functionField] Ω) := ⟨e.toMonoidHom, hc⟩
  let ι : (actualNormalizationInertiaGroup p.toValuationSubring F Ω Q).carrier →ₜ*
      (Ω ≃ₐ[F] Ω) :=
    { toMonoidHom :=
        { toFun := actualNormalizationInertiaElement p.toValuationSubring F Ω Q
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
      continuous_toFun := continuous_subtype_val }
  exact (FiniteEtale.fieldSourceAbsoluteGaloisHom X.functionField Ω
    (X.fromSpecStalk (genericPoint X))).comp (ec.comp ι)

/-- Evaluation uses precisely the original generic monodromy and scalar extension. -/
theorem genericPlaceInertiaHom_apply
    (τ : (actualNormalizationInertiaGroup p.toValuationSubring F Ω Q).carrier) :
    let η := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω))
    genericPlaceInertiaHom X p Q hsurj τ =
      FiniteEtale.fundamentalGroupHom (X.fromSpecStalk (genericPoint X)) η
        (toAut (FiniteEtale.fiber η) (Ω ≃ₐ[X.functionField] Ω)
          (AlgEquiv.extendScalarsHomOfSurjective (A := Ω) hsurj
            (actualNormalizationInertiaElement p.toValuationSubring F Ω Q τ))) := by
  intro η
  change FiniteEtale.fundamentalGroupHom (X.fromSpecStalk (genericPoint X)) η
    (toAutHomeo (FiniteEtale.fiber η) (Ω ≃ₐ[X.functionField] Ω)
      (AlgEquiv.extendScalarsHomOfSurjective (A := Ω) hsurj
        (actualNormalizationInertiaElement p.toValuationSubring F Ω Q τ))) = _
  rw [toAutHomeo_apply]

/-- The continuous map has exactly the previously defined original inertia subgroup as range. -/
theorem genericPlaceInertiaHom_range :
    (genericPlaceInertiaHom X p Q hsurj).toMonoidHom.range = genericPlaceInertia X p Q := by
  let e := AlgEquiv.extendScalarsHomOfSurjective (A := Ω) hsurj
  let η := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω))
  let q :=
    (FiniteEtale.fundamentalGroupHom (X.fromSpecStalk (genericPoint X)) η).toMonoidHom.comp
      (toAut (FiniteEtale.fiber η) (Ω ≃ₐ[X.functionField] Ω))
  ext g
  constructor
  · rintro ⟨τ, rfl⟩
    refine ⟨e (actualNormalizationInertiaElement p.toValuationSubring F Ω Q τ), ?_, ?_⟩
    · exact ⟨τ, (e.symm_apply_apply _).symm⟩
    · exact (genericPlaceInertiaHom_apply X p Q hsurj τ).symm
  · rintro ⟨σ, ⟨τ, hτ⟩, rfl⟩
    refine ⟨τ, ?_⟩
    have he : e (actualNormalizationInertiaElement p.toValuationSubring F Ω Q τ) = σ :=
      (congrArg e hτ).trans (e.apply_symm_apply σ)
    exact (genericPlaceInertiaHom_apply X p Q hsurj τ).trans (congrArg q he)

end AnabelianGeometry.WeightFiltration
