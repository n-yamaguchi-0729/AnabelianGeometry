/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.BoundaryInertiaRelations
import Nyll.JacobianVarieties.Kummer.AbelJacobiTate
import Nyll.AlgebraicCurves.Geometry.Picard.Representability.AbelJacobiPicardRepresentability

/-!
# The actual geometric boundary sequence with full Tate endpoint

Compose the original compactification map with the existing Abel--Jacobi
Tate equivalence, already proved by finite-character duality. The previously
proved inertia image and diagonal relation give the exact sequence without
constructing a second comparison.
-/

noncomputable section

open AlgebraicGeometry AlgebraicGeometry.RelPicard CategoryTheory AlgebraicCurve
open NeronModelInfra GoodReductionJacobian
open SchemeTheory EtaleFundamentalGroups.Inertia
open ProCGroups.Abelian

namespace AnabelianGeometry.WeightFiltration

variable
    {K F : Type} [Field K] [CharZero K] [IsAlgClosed K] [Field F] [Algebra K F]
    [Algebra.EssFiniteType K F] [IsCurveOver K F]
    (M : CurveModel K F)
    {X : Scheme} [IsIntegral X] [CompactSpace X]
    (j : X ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
    [Algebra F X.functionField]
    (hfield : algebraMap F X.functionField = (j.functionFieldMap hj).comp M.ffEquiv.toRingHom)
    {Ω : Type} [Field Ω] [Algebra X.functionField Ω] [Algebra F Ω]
    [IsScalarTower F X.functionField Ω]
    [IsSepClosed Ω] [IsSepClosure X.functionField Ω] [IsSepClosure F Ω]
    [∀ p : M.openBoundaryPlaces j, Algebra p.val.toValuationSubring Ω]
    [∀ p : M.openBoundaryPlaces j, IsScalarTower p.val.toValuationSubring F Ω]
    [Algebra K Ω]
    [∀ p : M.openBoundaryPlaces j, IsScalarTower K p.val.toValuationSubring Ω]
    (Q : ∀ p : M.openBoundaryPlaces j,
      Ideal (normalizationCommAlgCat p.val.toValuationSubring Ω))
    [∀ p, (Q p).IsMaximal]
    [Fintype (M.openBoundaryPlaces j)]

/-- The boundary sequence ends in the actual Jacobian full Tate module. -/
theorem exists_boundary_fullTate_sequence
    [GeometricallyIntegral M.toBase]
    (ε : SchemeHomOver (𝟙 (Spec (.of K))) M.toBase)
    (D : RelativePic0Designation K M.toBase)
    (hD : RepresentsRelSubPic M.toBase ε (algEquivZeroCut M.toBase ε) D)
    [Smooth D.toBase] [IsProper D.toBase] [GeometricallyConnected D.toBase] :
    let G := RepresentsRelSubPic.relativeGroupLaw
      (P := algEquivZeroGroupCut M.toBase ε) hD
    let hc : G.IsCommutative := RepresentsRelSubPic.relativeGroupLaw_isCommutative
      (P := algEquivZeroGroupCut M.toBase ε) hD
    let η := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω))
    let ξ := η ≫ X.fromSpecStalk (genericPoint X)
    ∃ e : TopologicalAbelianization (Aut (FiniteEtale.fiber (ξ ≫ j))) ≃ₜ*
        Multiplicative (ProCGroups.FullTateModule (G.AlgPoints hc K)),
      let τ := (ContinuousMonoidHom.toContinuousMonoidHom e).comp
        (compactificationAbelianizationMap j ξ)
      Function.Surjective τ ∧
        (boundaryInertiaMap M j hj hfield Q).toMonoidHom.range = τ.toMonoidHom.ker ∧
        (boundaryInertiaMap M j hj hfield Q).toMonoidHom.ker =
          (Pi.constMonoidHom (M.openBoundaryPlaces j)
            (primeToRootsSystem K K).inverseLimit).range := by
  intro G hc η ξ
  obtain ⟨aj, _, hclass⟩ :=
    exists_abelJacobi_of_representsRelSubPic K M.toBase ε D hD
  obtain ⟨e, _⟩ := JacobianVarieties.Kummer.exists_abelJacobi_fullTate_equiv
    M ε D hD aj hclass Ω (ξ ≫ j)
  refine ⟨e, ?_⟩
  dsimp only
  have : Smooth M.toBase := SmoothOfRelativeDimension.smooth 1 M.toBase
  have : IsIntegrallyClosed Γ(Spec (.of K), ⊤) := IsIntegrallyClosed.of_equiv
    (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv
  have : IsNormalIntegral M.C := IsNormalIntegral.of_stalks M.C
    (fun z => (Smooth.isDomain_and_isIntegrallyClosed_stalk M.toBase z).2)
  have : IsLocallyNoetherian M.C := LocallyOfFiniteType.isLocallyNoetherian M.toBase
  refine ⟨e.surjective.comp (compactificationAbelianizationMap_surjective j ξ), ?_,
    boundaryInertiaMap_ker M j hj hfield Q⟩
  rw [boundaryInertiaMap_range M j hj hfield Q]
  ext x
  change compactificationAbelianizationMap j ξ x = 1 ↔
    e (compactificationAbelianizationMap j ξ x) = 1
  exact e.map_eq_one_iff.symm

end AnabelianGeometry.WeightFiltration
