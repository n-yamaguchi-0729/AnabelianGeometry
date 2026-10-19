/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.FieldChartBoundaryCentralizer
import Nyll.AnabelianGeometry.WeightFiltration.FieldChartBoundaryPrimeTransport

/-! # Transporting the original boundary normalization-prime family

The target family is assembled only from the normalization-comap transport of
its original family under the exact field-chart boundary equivalence. Both
inertia subgroups live at the unchanged generic point and in the same Ω.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open SchemeTheory EtaleFundamentalGroups.Inertia

namespace AnabelianGeometry.WeightFiltration

attribute [local instance] placeBaseAmbientAlgebra placeBaseAmbientTower

/-- Transport every specified boundary normalization prime to the corresponding
place of the reparametrized model. Each existence witness comes from the actual
normalization-comap theorem; no inertia equality is required as a premise. -/
theorem exists_fieldChart_boundaryNormalizationPrimeFamily_same_inertia
    {κ F Ω : Type} [Field κ] [Field F] [Algebra κ F]
    (X : Scheme) [IsIntegral X]
    [Algebra κ X.functionField] [Algebra F X.functionField]
    [Field Ω] [Algebra X.functionField Ω] [Algebra F Ω]
    [IsScalarTower F X.functionField Ω]
    [IsSepClosed Ω] [IsSepClosure X.functionField Ω] [IsSepClosure F Ω]
    (e : F ≃ₐ[κ] X.functionField)
    (he : ∀ a : F, e a = algebraMap F X.functionField a)
    (M : CurveModel κ F) (j : X ⟶ M.C)
    (Q : ∀ p : M.openBoundaryPlaces j,
      Ideal (normalizationCommAlgCat p.val.toValuationSubring Ω))
    [∀ p, (Q p).IsMaximal] :
    ∃ Q' : ∀ w : (M.reparametrizeField e).openBoundaryPlaces j,
        Ideal (normalizationCommAlgCat w.val.toValuationSubring Ω),
      (∀ w, (Q' w).IsMaximal) ∧
        ∀ p : M.openBoundaryPlaces j,
          genericPlaceInertia X p.val (Q p) =
            genericPlaceInertia X ((M.reparametrizeFieldBoundaryEquiv e j) p).val
              (Q' ((M.reparametrizeFieldBoundaryEquiv e j) p)) := by
  classical
  let E := M.reparametrizeFieldBoundaryEquiv e j
  have htransport (w : (M.reparametrizeField e).openBoundaryPlaces j) :
      ∃ Qw : Ideal (normalizationCommAlgCat w.val.toValuationSubring Ω),
        Qw.IsMaximal ∧
          genericPlaceInertia X (E.symm w).val (Q (E.symm w)) =
            genericPlaceInertia X w.val Qw := by
    obtain ⟨p, rfl⟩ := E.surjective w
    obtain ⟨Qw, hQw, hp⟩ :=
      exists_fieldChart_normalizationPrime_same_inertia X e he p.val (Q p)
    refine ⟨Qw, hQw, ?_⟩
    have hsource := congrArg
      (fun r : M.openBoundaryPlaces j => genericPlaceInertia X r.val (Q r))
      (E.symm_apply_apply p)
    exact hsource.trans hp
  choose Q' hQ' hI using htransport
  refine ⟨Q', hQ', ?_⟩
  intro p
  have hsource := congrArg
    (fun r : M.openBoundaryPlaces j => genericPlaceInertia X r.val (Q r))
    (E.symm_apply_apply p)
  exact hsource.symm.trans (hI (E p))

end AnabelianGeometry.WeightFiltration
