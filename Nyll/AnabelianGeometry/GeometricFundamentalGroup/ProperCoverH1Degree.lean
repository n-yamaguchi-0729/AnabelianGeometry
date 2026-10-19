/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.FunctionFields.Transcendence.EssFiniteTypeFunctionField
import Nyll.AnabelianGeometry.GeometricFundamentalGroup.CoverCohomologyTransport
import Nyll.JacobianVarieties.Kummer.FiniteH1Cardinality
import Nyll.AlgebraicCurves.Models.Points.RationalPointExistence
import Nyll.AlgebraicCurves.Geometry.Curves.GeometricallyIntegralAlgClosed
import Nyll.AlgebraicCurves.Models.Ramification.FiniteEtaleRiemannHurwitz
import Nyll.EtaleFundamentalGroups.GaloisCovers.ConnectedCurveModel
import Nyll.EtaleFundamentalGroups.GaloisCovers.OpenCoverDegree
import Nyll.EtaleFundamentalGroups.GaloisCovers.FunctionFieldAutomorphisms
import Nyll.EtaleFundamentalGroups.GeometricFiber.PullbackEquivalence
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# First cohomology and degree of an actual proper-curve cover

The actual connected covering scheme is realized as a smooth proper curve.
Its H¹ cardinality and Riemann--Hurwitz formula give an exponent whose Euler
characteristic is multiplied by the original geometric fiber degree.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve NeronModelInfra
open CategoryTheory.PreGaloisCategory EtaleFundamentalGroups

namespace AnabelianGeometry.GeometricFundamentalGroup

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

/-- The H¹ exponent of an actual finite étale Galois cover of a proper curve
satisfies Riemann--Hurwitz with its actual fiber degree. This includes genus
zero and one, and the trivial cover. -/
theorem exists_finiteH1_exponent_proper_cover
    {K F : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F] [Algebra K F] [IsCurveOver K F]
    (M : CurveModel K F) (W : FiniteEtale M.C) [IsGalois W]
    {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ M.C) (ξW : Spec (.of Ω) ⟶ W.left) (n : ℕ+) :
    ∃ q : ℕ,
      Nat.card (Sheaf.H.{0}
        ((constantSheaf W.left.smallEtaleTopology AddCommGrpCat.{0}).obj
          (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K)))) 1) = (n : ℕ) ^ q ∧
      (q : ℤ) - 2 = (Nat.card ((FiniteEtale.fiber ξ).obj W) : ℤ) *
        (2 * (genusFF K F : ℤ) - 2) := by
  have : ConnectedSpace W.left := FiniteEtale.connectedSpace_left_of_isConnected W
  have : IsLocallyNoetherian M.C := LocallyOfFiniteType.isLocallyNoetherian M.toBase
  have : Smooth M.toBase := SmoothOfRelativeDimension.smooth 1 M.toBase
  have : IsIntegrallyClosed Γ(Spec (.of K), ⊤) :=
    IsIntegrallyClosed.of_equiv (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv
  have : IsNormalIntegral M.C := IsNormalIntegral.of_stalks M.C
    (fun x => (Smooth.isDomain_and_isIntegrallyClosed_stalk M.toBase x).2)
  have : IsIntegral W.left := isIntegral_left_of_isConnected_finiteEtale W
  let : Algebra K W.left.functionField :=
    (baseToFunctionField (show W.left ⟶ Spec (.of K) from W.hom ≫ M.toBase)).toAlgebra
  obtain ⟨hC, hFT, N, i, hi, _⟩ := exists_curveModel_of_connected_finiteEtale M W
  let d : N.C ⟶ M.C := i.hom ≫ W.hom
  have hd : d ≫ M.toBase = N.toBase := (Category.assoc _ _ _).trans hi
  have : IsFiniteEtale i.hom := ⟨⟩
  have : IsFiniteEtale d := by dsimp only [d]; infer_instance
  have : Surjective d := IsFiniteEtale.surjective d
  have hsquare : i.inv ≫ d = W.hom ≫ 𝟙 M.C := by
    exact (i.inv_hom_id_assoc W.hom).trans (Category.comp_id W.hom).symm
  let : Algebra M.C.functionField W.left.functionField := finiteEtaleFunctionFieldAlgebra W
  have hdegree : finrankAlong K (M.finiteEtaleFieldMap N d hd) =
      Nat.card ((FiniteEtale.fiber ξ).obj W) := by
    change finrankAlong K (M.finiteCurveFieldMap N d hd d.surjective) = _
    calc
      finrankAlong K (M.finiteCurveFieldMap N d hd d.surjective) =
          Module.finrank M.C.functionField W.left.functionField :=
        finrankAlong_openCover_eq_actual M N (𝟙 M.C) W d hd d.surjective i.inv hsquare
      _ = Nat.card (Aut W) :=
        (natCard_finiteEtaleAut_eq_finrank_functionField_of_isGalois W inferInstance).symm
      _ = Nat.card ((FiniteEtale.fiber ξ).obj W) :=
        (isGalois_iff_card_aut_eq_card_fiber (FiniteEtale.fiber ξ) W).mp inferInstance
  let E : FiniteEtale N.C ≌ FiniteEtale W.left :=
    MorphismProperty.Over.pullbackIso
      (@IsFiniteEtale : MorphismProperty Scheme) ⊤ i
  have : (FiniteEtale.pullback i.inv).IsEquivalence := E.isEquivalence_functor
  let eG := FiniteEtale.fundamentalGroupEquivOfPullbackEquivalence i.inv ξW
  have : GeometricallyIntegral N.toBase := geometricallyIntegral_of_isAlgClosed N.toBase
  obtain ⟨εN⟩ := N.nonempty_rationalPoint
  have : NeZero ((n : ℕ) : K) := ⟨Nat.cast_ne_zero.mpr n.ne_zero⟩
  let C := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
  have hH : Nat.card (Sheaf.H.{0}
      ((constantSheaf W.left.smallEtaleTopology AddCommGrpCat.{0}).obj C) 1) =
      (n : ℕ) ^ (2 * genusFF K W.left.functionField) :=
    (Nat.card_congr
      (finiteH1EquivOfFundamentalGroupEquiv ξW (ξW ≫ i.inv) eG C).toEquiv).trans
        (N.natCard_finiteH1_eq_pow_genus εN n (ξW ≫ i.inv))
  have : Algebra.EssFiniteType K F := by
    let : Algebra K M.C.functionField := M.functionFieldAlgebra
    exact (Algebra.EssFiniteType.iff_of_algEquiv M.ffAlgEquiv).mpr
      (essFiniteType_functionField M.toBase)
  obtain ⟨t, ht, hf, _⟩ :=
    IsCurveOver.exists_separating_transcendental (K := K) (F := F)
  have hRH := M.two_mul_genus_sub_two_eq_finiteEtale N d hd ⟨t, ht, hf⟩
  rw [hdegree] at hRH
  refine ⟨2 * genusFF K W.left.functionField, hH, ?_⟩
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hRH

end AnabelianGeometry.GeometricFundamentalGroup
