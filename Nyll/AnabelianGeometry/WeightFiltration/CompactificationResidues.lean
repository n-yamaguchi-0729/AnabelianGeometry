/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.OpenKummerPullback
import Nyll.AnabelianGeometry.WeightFiltration.OpenCurveResidues
import Nyll.JacobianVarieties.Kummer.DivisorClassCohomologyComparison

/-!
# Compactification pullback and boundary residues

At compatible geometric generic points, the residue kernel is the image of
actual cohomological pullback from the compactification. No Kummer root is
part of the input: its existence follows from separable closedness.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory AlgebraicCurve

namespace AnabelianGeometry.WeightFiltration

variable {K F : Type} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
  [Algebra.EssFiniteType K F] [IsCurveOver K F]
  (M : CurveModel K F) (n : ℕ+) (hn : IsUnit ((n : ℕ) : K))

/-- Every proper finite Kummer cohomology class has a divisorial representative. -/
theorem finiteKummerH1_exists_representative
    {Ω : Type} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ M.C)
    (c : FiniteKummerH1 K M.C n) :
    ∃ u : Pic0.kummerUnits K F n, M.kummerEtaleClass n u hn xi = c := by
  obtain ⟨a, ha⟩ := M.kummerTorsionCohomology_surjective n hn xi c
  obtain ⟨u, hu⟩ := Pic0.kummerClass_surjective (K := K) (F := F) n
    (Multiplicative.ofAdd a)
  refine ⟨u, ?_⟩
  rw [← M.kummerTorsionCohomology_kummerClass n hn xi u, hu]
  exact ha

variable {X : Scheme} [IsIntegral X] [IsNormalIntegral X] [CompactSpace X]
  (j : X ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
  [Algebra M.C.functionField X.functionField]
  (hfield : algebraMap M.C.functionField X.functionField = j.functionFieldMap hj)
  {Ω : Type} [Field Ω] [Algebra X.functionField Ω]
  [hMp : Algebra M.C.functionField Ω]
  [htower : IsScalarTower M.C.functionField X.functionField Ω]
  [IsSepClosed Ω] [hsepP : IsSepClosure M.C.functionField Ω]
  [hsepO : IsSepClosure X.functionField Ω]

include hfield hMp htower hsepP hsepO

omit [Algebra.EssFiniteType K F] [IsCurveOver K F] in
/-- The compactification pullback on Kummer representatives, with no chosen root. -/
theorem properKummer_pullback_generic (u : Pic0.kummerUnits K F n) :
    let ξp := Spec.map (CommRingCat.ofHom (algebraMap M.C.functionField Ω)) ≫
      M.C.fromSpecStalk (genericPoint M.C)
    let ξo := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) ≫
      X.fromSpecStalk (genericPoint X)
    EtaleFundamentalGroups.Cohomology.constantCohomologyPullback j
      (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))) 1
      (M.kummerEtaleClass n u hn ξp) =
        properKummerToFiniteH1 M n j hj hn ξo
          (Additive.ofMul (QuotientGroup.mk u)) := by
  intro ξp ξo
  let ι : K →+* Ω := (algebraMap M.C.functionField Ω).comp
    (baseToFunctionField M.toBase)
  have hnΩ : IsUnit ((n : ℕ) : Ω) := by
    simpa only [map_natCast] using hn.map ι
  have : NeZero ((n : ℕ) : Ω) := ⟨hnΩ.ne_zero⟩
  obtain ⟨β, hβ⟩ := IsSepClosed.exists_pow_nat_eq
    (algebraMap M.C.functionField Ω (M.ffEquiv (u.val : F))) (n : ℕ)
  exact properKummer_pullback_eq_openKummer M (M.openBoundaryPlaces j) n u
    j hj (M.place_not_mem_openBoundaryPlaces j) hfield β hβ hn

/-- The boundary residues vanish precisely on actual compactification pullbacks. -/
theorem finiteResidue_eq_zero_iff_exists_pullback
    (x : FiniteKummerH1 K X n) :
    let ξo := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) ≫
      X.fromSpecStalk (genericPoint X)
    finiteResidue M n j hj hn ξo x = 0 ↔
      ∃ c : FiniteKummerH1 K M.C n,
        EtaleFundamentalGroups.Cohomology.constantCohomologyPullback j
          (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))) 1 c = x := by
  intro ξo
  let ξp := Spec.map (CommRingCat.ofHom (algebraMap M.C.functionField Ω)) ≫
    M.C.fromSpecStalk (genericPoint M.C)
  rw [finiteResidue_eq_zero_iff]
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective q.toMul
    have heq : q = Additive.ofMul (QuotientGroup.mk u) := hu.symm
    refine ⟨M.kummerEtaleClass n u hn ξp, ?_⟩
    rw [properKummer_pullback_generic M n hn j hj hfield u, ← heq]
    exact hq
  · rintro ⟨c, hc⟩
    obtain ⟨u, rfl⟩ := finiteKummerH1_exists_representative M n hn ξp c
    refine ⟨Additive.ofMul (QuotientGroup.mk u), ?_⟩
    rw [← properKummer_pullback_generic M n hn j hj hfield u]
    exact hc

end AnabelianGeometry.WeightFiltration
