/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.KummerCoefficientReduction

/-!
# Residues commute with the actual coefficient transitions

The transition is the derived cohomology map induced by the power map on
roots of unity, not a map defined by transport through a divisorial model.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory AlgebraicCurve

namespace AnabelianGeometry.WeightFiltration

/-- Boundary residues commute with the geometric coefficient reduction. -/
theorem finiteResidue_coefficientReduction
    {K F : Type} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    (M : CurveModel K F) (m k : ℕ+)
    {X : Scheme} [IsIntegral X] [CompactSpace X]
    (j : X ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
    (hm : IsUnit ((m : ℕ) : K)) (hmk : IsUnit (((m * k : ℕ+) : ℕ) : K))
    {Ω : Type} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ X)
    (c : FiniteKummerH1 K X (m * k)) (v : M.openBoundaryPlaces j) :
    finiteResidue M m j hj hm xi
      (Sheaf.H.map ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{0}).map
        (kummerCoefficientReduction K m k)) 1 c) v =
      ZMod.castHom (dvd_mul_right (m : ℕ) (k : ℕ)) (ZMod (m : ℕ))
        (finiteResidue M (m * k) j hj hmk xi c v) := by
  obtain ⟨q, rfl⟩ :=
    (CurveModel.OpenKummer.quotientCohomologyEquiv M (m * k) j hj hmk xi).surjective c
  obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective q.toMul
  have hq : q = Additive.ofMul (QuotientGroup.mk u) := hu.symm
  rw [hq]
  let S := M.openBoundaryPlaces j
  let um := openKummerUnitsReduce S (dvd_mul_right (m : ℕ) (k : ℕ)) u
  change finiteResidue M m j hj hm xi
    (Sheaf.H.map ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{0}).map
      (kummerCoefficientReduction K m k)) 1
      (CurveModel.OpenKummer.kummerEtaleClass M S (m * k) u j hj
        (M.place_not_mem_openBoundaryPlaces j) hmk xi)) v = _
  rw [openKummerEtaleClass_coefficientReduction]
  change finiteResidue M m j hj hm xi
    (CurveModel.OpenKummer.quotientCohomologyEquiv M m j hj hm xi
      (Additive.ofMul (QuotientGroup.mk um))) v = _
  rw [finiteResidue_comparison, finiteResidue_comparison]
  exact openKummerResidueQuotient_reduce S (dvd_mul_right (m : ℕ) (k : ℕ))
    (QuotientGroup.mk u) v

end AnabelianGeometry.WeightFiltration
