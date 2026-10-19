/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GeometricFiber.SourceIsoGalois

/-! # The quotient determined by the actual coefficient embedding

The chosen comparison of field fibers and the comparison from the supplied
coefficient embedding differ by an explicit Galois element. The formula below
retains that element and applies to every fundamental-group element, not only
to automorphisms induced from the source field.
-/

noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory
open AlgebraicGeometry AlgebraicGeometry.FiniteEtale

namespace AnabelianGeometry.ArithmeticIsomorphisms

universe u

variable (k L Ω : Type u) [Field k] [Field L] [Field Ω]
  [Algebra k L] [IsSepClosure k L] [IsSepClosed L]
  [Algebra L Ω] [Algebra k Ω] [IsScalarTower k L Ω] [IsSepClosed Ω]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (xi : Spec (.of Ω) ⟶ X)
  (hbase : xi ≫ f = ξ k Ω)

/-- The field-fiber comparison induced by the supplied embedding of constants. -/
def coefficientFiberComparison : fiber (xi ≫ f) ≅ fib k L :=
  eqToIso (congrArg fiber hbase) ≪≫ (fieldFiberExtensionIso k L Ω).symm

/-- The arithmetic quotient using the actual coefficient embedding. -/
def coefficientProjection : π₁ᵉᵗ(xi) →ₜ* Gal(L/k) :=
  (ContinuousMonoidHom.toContinuousMonoidHom
    (suppliedGaloisEquivFundamentalGroup k L).symm).comp
    ((ContinuousMonoidHom.toContinuousMonoidHom
      (continuousConjAut (coefficientFiberComparison k L Ω f xi hbase))).comp
        (fundamentalGroupHom f xi))

/-- The discrepancy between the original chosen field-fiber comparison and
the comparison induced by the actual coefficient embedding. -/
def coefficientProjectionConjugator : Gal(L/k) :=
  (suppliedGaloisEquivFundamentalGroup k L).symm
    ((coefficientFiberComparison k L Ω f xi hbase).symm ≪≫
      (nonempty_fiber_iso (xi ≫ f) (ξ k L)).some)

/-- The exact change of arithmetic quotient, for every group element. -/
theorem arithmeticFundamentalGroupHom_eq_conjugate_coefficientProjection
    (g : π₁ᵉᵗ(xi)) :
    arithmeticFundamentalGroupHom k L f xi g =
      coefficientProjectionConjugator k L Ω f xi hbase *
        coefficientProjection k L Ω f xi hbase g *
        (coefficientProjectionConjugator k L Ω f xi hbase)⁻¹ := by
  let ε := suppliedGaloisEquivFundamentalGroup k L
  let tc := coefficientFiberComparison k L Ω f xi hbase
  let t : fiber (xi ≫ f) ≅ fib k L :=
    (nonempty_fiber_iso (xi ≫ f) (ξ k L)).some
  let δ : Aut (fib k L) := tc.symm ≪≫ t
  have h := continuousConjAut_eq_conj tc t (fundamentalGroupHom f xi g)
  change t.conjAut (fundamentalGroupHom f xi g) =
    δ * tc.conjAut (fundamentalGroupHom f xi g) * δ⁻¹ at h
  change ε.symm (t.conjAut (fundamentalGroupHom f xi g)) =
    ε.symm δ * ε.symm (tc.conjAut (fundamentalGroupHom f xi g)) * (ε.symm δ)⁻¹
  rw [h, map_mul, map_mul, map_inv]

/-- For the actual coefficient quotient, a source automorphism has its exact
coefficient label, with no residual conjugator. -/
theorem coefficientProjection_sourceAction
    (e : Spec (.of Ω) ≅ Spec (.of Ω)) (ρ : Ω →+* Ω)
    (he : e.hom = Spec.map (CommRingCat.ofHom ρ))
    (σ : Gal(L/k))
    (hρ : ρ.comp (algebraMap L Ω) = (algebraMap L Ω).comp σ.toRingHom)
    (hsource : e.hom ≫ xi = xi) :
    coefficientProjection k L Ω f xi hbase
      (fiberSourceIso xi e ≪≫ eqToIso (congrArg fiber hsource)) = σ := by
  let ε := suppliedGaloisEquivFundamentalGroup k L
  let E := fieldFiberExtensionIso k L Ω
  let q := eqToIso (congrArg fiber hbase)
  let g : Aut (fiber xi) := fiberSourceIso xi e ≪≫ eqToIso (congrArg fiber hsource)
  have hfield := fundamentalGroupHom_sourceAction_eq_extendedGalois
    k L Ω f xi e ρ he σ hρ hsource hbase
  have hc : (q ≪≫ E.symm).conjAut (fundamentalGroupHom f xi g) = ε σ := by
    rw [Iso.trans_conjAut, hfield]
    change E.symm.conjAut (E.conjAut (ε σ)) = ε σ
    apply Aut.ext
    simp only [Iso.conjAut_hom, Iso.symm_self_conj]
  change ε.symm ((q ≪≫ E.symm).conjAut (fundamentalGroupHom f xi g)) = σ
  exact (congrArg ε.symm hc).trans (ε.symm_apply_apply σ)

end AnabelianGeometry.ArithmeticIsomorphisms
