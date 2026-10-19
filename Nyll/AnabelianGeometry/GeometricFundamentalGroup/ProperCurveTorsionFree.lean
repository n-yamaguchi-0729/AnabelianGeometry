/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Kummer.AbelJacobiTate
import Nyll.JacobianVarieties.Picard.Representability.CurveModelPicardRepresentabilityAbelJacobi
import Nyll.AlgebraicCurves.Models.Points.RationalPointExistence
import Nyll.AlgebraicCurves.Geometry.Curves.GeometricallyIntegralAlgClosed
import Nyll.EtaleFundamentalGroups.GaloisCovers.ConnectedCurveModel
import Nyll.EtaleFundamentalGroups.GaloisCovers.OpenSubgroupFundamentalGroup
import Nyll.EtaleFundamentalGroups.GeometricFiber.PullbackEquivalence
import Nyll.ProCGroups.FiniteStepSolvableQuotients.SlimnessAndTorsion

/-!
# Torsion-freeness of actual proper-curve fundamental groups

The constructed Picard scheme and Abel--Jacobi map identify the actual
abelianized fundamental group with an actual full Tate module. Every actual
open subgroup comes from a connected finite etale cover, itself a smooth
proper curve. The existing profinite-group theorem then gives torsion-freeness
of the entire fundamental group. No K(pi,1) or cohomological-dimension
hypothesis is assumed.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve NeronModelInfra
open CategoryTheory.PreGaloisCategory EtaleFundamentalGroups
open ProCGroups.FiniteStepSolvableQuotients

namespace AnabelianGeometry

/-- The actual topological abelianization of a smooth proper curve's
fundamental group is torsion-free, via the constructed Abel--Jacobi map. -/
theorem isMulTorsionFree_abelianization_fundamentalGroup_proper_curve
    {K F : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F] [Algebra K F] [IsCurveOver K F]
    (M : CurveModel K F)
    {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (geom : Spec (.of Ω) ⟶ M.C) :
    IsMulTorsionFree (TopologicalAbelianization (Aut (FiniteEtale.fiber geom))) := by
  have : GeometricallyIntegral M.toBase := geometricallyIntegral_of_isAlgClosed M.toBase
  obtain ⟨ε⟩ := M.nonempty_rationalPoint
  obtain ⟨D, hD, aj, hs, hp, hg, _, hclass, _⟩ :=
    M.exists_representsRelSubPic_abelJacobi_of_isAlgClosed K F ε
  have : Smooth D.toBase := hs
  have : IsProper D.toBase := hp
  have : GeometricallyConnected D.toBase := hg
  obtain ⟨e, _⟩ :=
    JacobianVarieties.Kummer.exists_abelJacobi_fullTate_equiv M ε D hD aj hclass Ω geom
  exact e.symm.isMulTorsionFree

/-- Every actual open subgroup has torsion-free topological abelianization.
The covering curve and its Picard representation are constructed. -/
theorem isAbTorsionFree_fundamentalGroup_proper_curve
    {K F : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F] [Algebra K F] [IsCurveOver K F]
    (M : CurveModel K F)
    {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (geom : Spec (.of Ω) ⟶ M.C) :
    IsAbTorsionFree (Aut (FiniteEtale.fiber geom)) := by
  intro H
  have : IsTopologicalGroup H := by
    change IsTopologicalGroup ↥(H : Subgroup (Aut (FiniteEtale.fiber geom)))
    infer_instance
  obtain ⟨A, hA, geomA, _, eA, _⟩ :=
    FiniteEtale.exists_connectedCover_lift_fundamentalGroup_equiv_openSubgroup geom H
  have : IsConnected A := FiniteEtale.isConnected_of_connectedSpace_left A
  have : Smooth M.toBase := SmoothOfRelativeDimension.smooth 1 M.toBase
  have : IsIntegrallyClosed Γ(Spec (.of K), ⊤) :=
    IsIntegrallyClosed.of_equiv (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv
  have : IsNormalIntegral M.C := IsNormalIntegral.of_stalks M.C
    (fun x => (Smooth.isDomain_and_isIntegrallyClosed_stalk M.toBase x).2)
  have : IsIntegral A.left := isIntegral_left_of_isConnected_finiteEtale A
  let : Algebra K A.left.functionField :=
    (baseToFunctionField (show A.left ⟶ Spec (.of K) from A.hom ≫ M.toBase)).toAlgebra
  obtain ⟨hC, hFT, N, i, _, _⟩ := exists_curveModel_of_connected_finiteEtale M A
  let E : FiniteEtale N.C ≌ FiniteEtale A.left :=
    MorphismProperty.Over.pullbackIso
      (@IsFiniteEtale : MorphismProperty Scheme) ⊤ i
  have : (FiniteEtale.pullback i.inv).IsEquivalence := E.isEquivalence_functor
  let e : H ≃ₜ* Aut (FiniteEtale.fiber (geomA ≫ i.inv)) :=
    eA.symm.trans (FiniteEtale.fundamentalGroupEquivOfPullbackEquivalence i.inv geomA)
  have : IsMulTorsionFree
      (TopologicalAbelianization (Aut (FiniteEtale.fiber (geomA ≫ i.inv)))) :=
    isMulTorsionFree_abelianization_fundamentalGroup_proper_curve N (geomA ≫ i.inv)
  exact (ProCGroups.Abelian.TopologicalAbelianization.congr e).symm.isMulTorsionFree

/-- The actual etale fundamental group of a smooth proper curve over an
algebraically closed characteristic-zero field has no nontrivial finite-order
element. This applies to every genus. -/
theorem isTorsionFreeGroup_fundamentalGroup_proper_curve
    {K F : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F] [Algebra K F] [IsCurveOver K F]
    (M : CurveModel K F)
    {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (geom : Spec (.of Ω) ⟶ M.C) :
    IsTorsionFreeGroup (Aut (FiniteEtale.fiber geom)) :=
  isTorsionFreeGroup_of_isAbTorsionFree
    (isAbTorsionFree_fundamentalGroup_proper_curve M geom)

end AnabelianGeometry
