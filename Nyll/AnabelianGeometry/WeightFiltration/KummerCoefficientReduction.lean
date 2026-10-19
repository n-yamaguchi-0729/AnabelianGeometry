/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.KummerRootPower
import Nyll.AnabelianGeometry.WeightFiltration.ResidueBasePointIndependence
import Nyll.EtaleFundamentalGroups.Cohomology.GenericPointCharacterDetection
import Nyll.EtaleFundamentalGroups.Cohomology.H1Naturality

/-!
# Coefficient reduction of actual Kummer cohomology classes

The power map on roots of unity induces the expected transition on genuine
étale H¹: the representing function is unchanged, while the exponent is reduced.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicCurve
open EtaleFundamentalGroups.Cohomology

namespace AnabelianGeometry.WeightFiltration

/-- The power map as a morphism of finite abelian coefficient groups. -/
def kummerCoefficientReduction (K : Type) [Field K] (m k : ℕ+) :
    AddCommGrpCat.of (Additive (rootsOfUnity ((m * k : ℕ+) : ℕ) K)) ⟶
      AddCommGrpCat.of (Additive (rootsOfUnity (m : ℕ) K)) :=
  AddCommGrpCat.ofHom (EtaleFundamentalGroups.Inertia.rootsOfUnityPowerTransition K
    (dvd_mul_right (m : ℕ) (k : ℕ))).toAdditive

/-- The actual coefficient map takes a Kummer class to the class of the
same function for the smaller exponent. -/
theorem openKummerEtaleClass_coefficientReduction
    {K F : Type} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    (M : CurveModel K F) (m k : ℕ+)
    {X : Scheme} [IsIntegral X] [CompactSpace X]
    (j : X ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
    (hm : IsUnit ((m : ℕ) : K)) (hmk : IsUnit (((m * k : ℕ+) : ℕ) : K))
    {Ω : Type} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ X)
    (u : Pic0.openKummerUnits K F (M.openBoundaryPlaces j) (m * k)) :
    Sheaf.H.map ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{0}).map
      (kummerCoefficientReduction K m k)) 1
      (CurveModel.OpenKummer.kummerEtaleClass M (M.openBoundaryPlaces j) (m * k)
        u j hj (M.place_not_mem_openBoundaryPlaces j) hmk xi) =
    CurveModel.OpenKummer.kummerEtaleClass M (M.openBoundaryPlaces j) m
      (openKummerUnitsReduce (M.openBoundaryPlaces j) (dvd_mul_right (m : ℕ) (k : ℕ)) u)
      j hj (M.place_not_mem_openBoundaryPlaces j) hm xi := by
  have : Smooth M.toBase := SmoothOfRelativeDimension.smooth 1 M.toBase
  have : Smooth (j ≫ M.toBase) := inferInstance
  have : IsIntegrallyClosed Γ(Spec (.of K), ⊤) := IsIntegrallyClosed.of_equiv
    (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv
  have : IsNormalIntegral X := IsNormalIntegral.of_stalks X
    (fun z => (Smooth.isDomain_and_isIntegrallyClosed_stalk (j ≫ M.toBase) z).2)
  let Ωg := SeparableClosure X.functionField
  let η := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ωg))
  let ξ := η ≫ X.fromSpecStalk (genericPoint X)
  let S := M.openBoundaryPlaces j
  let um := openKummerUnitsReduce S (dvd_mul_right (m : ℕ) (k : ℕ)) u
  rw [openKummerEtaleClass_basePoint M (m * k) j hj hmk xi ξ u,
    openKummerEtaleClass_basePoint M m j hj hm xi ξ um]
  have : NeZero (m : ℕ) := ⟨m.ne_zero⟩
  have : NeZero ((m * k : ℕ+) : ℕ) := ⟨(m * k).ne_zero⟩
  have : NeZero ((m : ℕ) : K) := ⟨hm.ne_zero⟩
  have : NeZero (((m * k : ℕ+) : ℕ) : K) := ⟨hmk.ne_zero⟩
  let ι : K →+* Ωg := (algebraMap X.functionField Ωg).comp
    (baseToFunctionField (j ≫ M.toBase))
  have hng : IsUnit (((m * k : ℕ+) : ℕ) : Ωg) := by
    simpa only [map_natCast] using hmk.map ι
  have : NeZero (((m * k : ℕ+) : ℕ) : Ωg) := ⟨hng.ne_zero⟩
  obtain ⟨β, hβ⟩ := IsSepClosed.exists_pow_nat_eq
    (algebraMap X.functionField Ωg (j.functionFieldMap hj (M.ffEquiv (u.val : F))))
    ((m * k : ℕ+) : ℕ)
  have hβ0 : β ≠ 0 := by
    intro hzero
    have hz := hβ
    rw [hzero, zero_pow (m * k).ne_zero] at hz
    exact (map_ne_zero (algebraMap X.functionField Ωg)).mpr
      ((map_ne_zero (j.functionFieldMap hj)).mpr
        ((map_ne_zero M.ffEquiv).mpr (Units.ne_zero u.val))) hz.symm
  let A := AddCommGrpCat.of (Additive (rootsOfUnity ((m * k : ℕ+) : ℕ) K))
  let B := AddCommGrpCat.of (Additive (rootsOfUnity (m : ℕ) K))
  let : TopologicalSpace (Multiplicative A) := ⊥
  let : TopologicalSpace (Multiplicative B) := ⊥
  have : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
  have : DiscreteTopology (Multiplicative B) := ⟨rfl⟩
  apply finiteH1_ext_genericFieldAction X Ωg B
  intro σ
  let g := FiniteEtale.fundamentalGroupHom (X.fromSpecStalk (genericPoint X)) η
    (toAut (FiniteEtale.fiber η) (Ωg ≃ₐ[X.functionField] Ωg) σ)
  have hc := congrArg (fun χ => χ g) (h1Character_naturality
    (kummerCoefficientReduction K m k) ξ
    (CurveModel.OpenKummer.kummerEtaleClass M S (m * k) u j hj
      (M.place_not_mem_openBoundaryPlaces j) hmk ξ))
  change h1Character B ξ _ g = h1Character B ξ _ g
  rw [← hc]
  change EtaleFundamentalGroups.Inertia.rootsOfUnityPowerTransition K
    (dvd_mul_right (m : ℕ) (k : ℕ)) (h1Character A ξ _ g) = h1Character B ξ _ g
  rw [h1Character_openKummer, h1Character_openKummer]
  exact (openKummerCharacter_generic_power M S m k u j hj
    (M.place_not_mem_openBoundaryPlaces j) hm hmk (Units.mk0 β hβ0) hβ σ).symm

end AnabelianGeometry.WeightFiltration
