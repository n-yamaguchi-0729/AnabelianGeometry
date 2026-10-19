/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.FunctionFields.Transcendence.EssFiniteTypeFunctionField
import Nyll.AnabelianGeometry.GeometricFundamentalGroup.PositiveGenusCover
import Nyll.EtaleFundamentalGroups.GaloisCovers.ConnectedCurveModel
import Nyll.EtaleFundamentalGroups.GaloisCovers.OpenCoverDegree
import Nyll.EtaleFundamentalGroups.GaloisCovers.FunctionFieldAutomorphisms
import Nyll.EtaleFundamentalGroups.GaloisCovers.Basic
import Nyll.AlgebraicCurves.Models.Ramification.FiniteEtaleRiemannHurwitz
import Nyll.AlgebraicCurves.Models.Ramification.OpenCoverRiemannHurwitz
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Tactic.Linarith

/-!
# Actual finite étale covers with growing genus or boundary

Prime-degree proper covers exist in positive genus. Their actual proper
Riemann--Hurwitz formula gives arbitrarily large genus when g is at least
two. Subtracting proper and open Riemann--Hurwitz proves that pulling back
an open multiplies its boundary count by the same covering degree. Thus a
positive-genus punctured curve has covers with arbitrarily many punctures,
including when its original boundary has only one point.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve NeronModelInfra
open CategoryTheory.PreGaloisCategory EtaleFundamentalGroups

namespace AnabelianGeometry.GeometricFundamentalGroup

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

/-- Prime-degree proper covers, as actual maps of curve models over the
original coefficient field. The source field and model are constructed. -/
theorem exists_primeDegree_properCurve_cover
    {K F : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F] [Algebra K F] (M : CurveModel K F) (hg : 0 < genusFF K F)
    (p : ℕ) (hp : p.Prime) :
    ∃ (E : Type) (_ : Field E) (_ : Algebra K E) (N : CurveModel K E)
      (d : N.C ⟶ M.C) (hd : d ≫ M.toBase = N.toBase) (_ : IsFiniteEtale d),
      finrankAlong K (M.finiteEtaleFieldMap N d hd) = p := by
  have : IsCurveOver K F :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one M.toBase
      M.ffEquiv M.ffEquiv_algebraMap
  obtain ⟨ε⟩ := M.nonempty_rationalPoint
  obtain ⟨W, hW, _ξW, _hξW, hWdegree⟩ :=
    exists_primeDegree_finiteEtale_cover_of_genus_pos M hg ε.1 p hp
  have : IsGalois W := hW
  have : IsLocallyNoetherian M.C := LocallyOfFiniteType.isLocallyNoetherian M.toBase
  have : Smooth M.toBase := SmoothOfRelativeDimension.smooth 1 M.toBase
  have : IsIntegrallyClosed Γ(Spec (.of K), ⊤) := IsIntegrallyClosed.of_equiv
    (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv
  have : IsNormalIntegral M.C := IsNormalIntegral.of_stalks M.C
    (fun x => (Smooth.isDomain_and_isIntegrallyClosed_stalk M.toBase x).2)
  have : IsIntegral W.left := isIntegral_left_of_isConnected_finiteEtale W
  let : Algebra K W.left.functionField :=
    (baseToFunctionField (show W.left ⟶ Spec (.of K) from W.hom ≫ M.toBase)).toAlgebra
  obtain ⟨_hC, _hFT, N, i, hi, _⟩ := exists_curveModel_of_connected_finiteEtale M W
  let d : N.C ⟶ M.C := i.hom ≫ W.hom
  have hd : d ≫ M.toBase = N.toBase := (Category.assoc _ _ _).trans hi
  have : IsFiniteEtale i.hom := ⟨⟩
  have : IsFiniteEtale d := by dsimp only [d]; infer_instance
  have : Surjective d := IsFiniteEtale.surjective d
  have hsquare : i.inv ≫ d = W.hom ≫ 𝟙 M.C := by
    exact (i.inv_hom_id_assoc W.hom).trans (Category.comp_id W.hom).symm
  let : Algebra M.C.functionField W.left.functionField := finiteEtaleFunctionFieldAlgebra W
  refine ⟨W.left.functionField, inferInstance, inferInstance, N, d, hd, inferInstance, ?_⟩
  change finrankAlong K (M.finiteCurveFieldMap N d hd d.surjective) = p
  calc
    finrankAlong K (M.finiteCurveFieldMap N d hd d.surjective) =
        Module.finrank M.C.functionField W.left.functionField :=
      finrankAlong_openCover_eq_actual M N (𝟙 M.C) W d hd d.surjective i.inv hsquare
    _ = Nat.card (Aut W) :=
      (natCard_finiteEtaleAut_eq_finrank_functionField_of_isGalois W hW).symm
    _ = Nat.card ((FiniteEtale.fiber ε.1).obj W) :=
      (isGalois_iff_card_aut_eq_card_fiber (FiniteEtale.fiber ε.1) W).mp hW
    _ = p := hWdegree

/-- Proper hyperbolic curves admit actual finite étale covers with genus
above every prescribed bound. No cover or degree hypothesis is supplied. -/
theorem exists_finiteEtale_cover_genus_ge
    {K F : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F] [Algebra K F] (M : CurveModel K F) (hg : 2 ≤ genusFF K F) (b : ℕ) :
    ∃ (E : Type) (_ : Field E) (_ : Algebra K E) (N : CurveModel K E)
      (d : N.C ⟶ M.C), d ≫ M.toBase = N.toBase ∧ IsFiniteEtale d ∧ b ≤ genusFF K E := by
  obtain ⟨p, hbp, hp⟩ := Nat.exists_infinite_primes b
  obtain ⟨E, hE, aE, N, d, hd, het, hdegree⟩ :=
    exists_primeDegree_properCurve_cover M (by omega) p hp
  have : IsCurveOver K F :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one M.toBase
      M.ffEquiv M.ffEquiv_algebraMap
  have : Algebra.EssFiniteType K F := by
    let : Algebra K M.C.functionField := M.functionFieldAlgebra
    exact (Algebra.EssFiniteType.iff_of_algEquiv M.ffAlgEquiv).mpr
      (essFiniteType_functionField M.toBase)
  obtain ⟨t, ht, hf, _⟩ :=
    IsCurveOver.exists_separating_transcendental (K := K) (F := F)
  have hRH := M.two_mul_genus_sub_two_eq_finiteEtale N d hd ⟨t, ht, hf⟩
  rw [hdegree] at hRH
  refine ⟨E, hE, aE, N, d, hd, het, ?_⟩
  have hgZ : (2 : ℤ) ≤ genusFF K F := by exact_mod_cast hg
  have hpZ : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hbpZ : (b : ℤ) ≤ p := by exact_mod_cast hbp
  have hbound : (b : ℤ) ≤ genusFF K E := by nlinarith
  exact_mod_cast hbound

/-- Pullback along an actual proper finite étale map multiplies the
number of punctures by its degree. It is the difference of the proper
and open Riemann--Hurwitz formulas for the same map. -/
theorem natCard_openBoundary_preimage_eq_degree_mul
    {K F E : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F] [Field E] [Algebra K F] [Algebra K E]
    (M : CurveModel K F) (N : CurveModel K E)
    (d : N.C ⟶ M.C) (hd : d ≫ M.toBase = N.toBase) [IsFiniteEtale d]
    (U : M.C.Opens) (hU : (U : Set M.C).Nonempty) :
    Nat.card (N.openBoundaryPlaces (d ⁻¹ᵁ U).ι) =
      finrankAlong K (M.finiteEtaleFieldMap N d hd) * Nat.card (M.openBoundaryPlaces U.ι) := by
  classical
  have : Nonempty U := hU.to_subtype
  have : Surjective d := IsFiniteEtale.surjective d
  have hV : (d ⁻¹ᵁ U : Set N.C).Nonempty := by
    obtain ⟨x, hx⟩ := hU
    obtain ⟨y, hy⟩ := d.surjective x
    exact ⟨y, by change d y ∈ (U : Set M.C); rw [hy]; exact hx⟩
  have : Nonempty (d ⁻¹ᵁ U) := hV.to_subtype
  have : IsCurveOver K F :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one M.toBase
      M.ffEquiv M.ffEquiv_algebraMap
  have : Algebra.EssFiniteType K F := by
    let : Algebra K M.C.functionField := M.functionFieldAlgebra
    exact (Algebra.EssFiniteType.iff_of_algEquiv M.ffAlgEquiv).mpr
      (essFiniteType_functionField M.toBase)
  obtain ⟨t, ht, hf, _⟩ :=
    IsCurveOver.exists_separating_transcendental (K := K) (F := F)
  have hproper := M.two_mul_genus_sub_two_eq_finiteEtale N d hd ⟨t, ht, hf⟩
  have hb (y : N.C) : y ∉ Set.range (d ⁻¹ᵁ U).ι ↔ d y ∉ Set.range U.ι := by
    rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    rfl
  have hopen := M.two_mul_genus_add_openBoundary_sub_two_eq
    N d hd d.surjective U.ι (d ⁻¹ᵁ U).ι hb
  let : Fintype (M.openBoundaryPlaces U.ι) := (M.openBoundaryPlaces_finite U.ι).fintype
  let : Fintype (N.openBoundaryPlaces (d ⁻¹ᵁ U).ι) :=
    (N.openBoundaryPlaces_finite (d ⁻¹ᵁ U).ι).fintype
  rw [Set.Finite.card_toFinset, Set.Finite.card_toFinset,
    ← Nat.card_eq_fintype_card (α := N.openBoundaryPlaces (d ⁻¹ᵁ U).ι),
    ← Nat.card_eq_fintype_card (α := M.openBoundaryPlaces U.ι)] at hopen
  change 2 * (genusFF K E : ℤ) + Nat.card (N.openBoundaryPlaces (d ⁻¹ᵁ U).ι) - 2 =
    (finrankAlong K (M.finiteEtaleFieldMap N d hd) : ℤ) *
      (2 * (genusFF K F : ℤ) + Nat.card (M.openBoundaryPlaces U.ι) - 2) at hopen
  have h : (Nat.card (N.openBoundaryPlaces (d ⁻¹ᵁ U).ι) : ℤ) =
      finrankAlong K (M.finiteEtaleFieldMap N d hd) * Nat.card (M.openBoundaryPlaces U.ι) := by
    nlinarith [hproper, hopen]
  exact_mod_cast h

/-- A positive-genus curve with nonempty boundary has actual finite étale
covers with arbitrarily many punctures. The cover extends étale over the
proper compactification, so this also handles the one-puncture case. -/
theorem exists_finiteEtale_cover_boundary_ge
    {K F : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F] [Algebra K F] (M : CurveModel K F) (hg : 0 < genusFF K F)
    (U : M.C.Opens) (hU : (U : Set M.C).Nonempty)
    (hboundary : (M.openBoundaryPlaces U.ι).Nonempty) (b : ℕ) :
    ∃ (E : Type) (_ : Field E) (_ : Algebra K E) (N : CurveModel K E)
      (d : N.C ⟶ M.C), d ≫ M.toBase = N.toBase ∧ IsFiniteEtale d ∧
      (d ⁻¹ᵁ U : Set N.C).Nonempty ∧ b ≤ Nat.card (N.openBoundaryPlaces (d ⁻¹ᵁ U).ι) := by
  classical
  have : Nonempty U := hU.to_subtype
  obtain ⟨p, hbp, hp⟩ := Nat.exists_infinite_primes b
  obtain ⟨E, hE, aE, N, d, hd, het, hdegree⟩ :=
    exists_primeDegree_properCurve_cover M hg p hp
  have : Surjective d := IsFiniteEtale.surjective d
  have hV : (d ⁻¹ᵁ U : Set N.C).Nonempty := by
    obtain ⟨x, hx⟩ := hU
    obtain ⟨y, hy⟩ := d.surjective x
    exact ⟨y, by change d y ∈ (U : Set M.C); rw [hy]; exact hx⟩
  have hcard := natCard_openBoundary_preimage_eq_degree_mul M N d hd U hU
  rw [hdegree] at hcard
  let : Fintype (M.openBoundaryPlaces U.ι) := (M.openBoundaryPlaces_finite U.ι).fintype
  have hr : 0 < Nat.card (M.openBoundaryPlaces U.ι) := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_pos_iff.mpr hboundary.to_subtype
  refine ⟨E, hE, aE, N, d, hd, het, hV, ?_⟩
  rw [hcard]
  exact hbp.trans (by nlinarith)

/-- For a punctured curve of genus at least two, a single actual cover
simultaneously exceeds any prescribed genus and boundary bounds. -/
theorem exists_finiteEtale_cover_genus_boundary_ge
    {K F : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F] [Algebra K F] (M : CurveModel K F) (hg : 2 ≤ genusFF K F)
    (U : M.C.Opens) (hU : (U : Set M.C).Nonempty)
    (hboundary : (M.openBoundaryPlaces U.ι).Nonempty) (bg br : ℕ) :
    ∃ (E : Type) (_ : Field E) (_ : Algebra K E) (N : CurveModel K E)
      (d : N.C ⟶ M.C), d ≫ M.toBase = N.toBase ∧ IsFiniteEtale d ∧
      (d ⁻¹ᵁ U : Set N.C).Nonempty ∧ bg ≤ genusFF K E ∧
      br ≤ Nat.card (N.openBoundaryPlaces (d ⁻¹ᵁ U).ι) := by
  classical
  have : Nonempty U := hU.to_subtype
  obtain ⟨p, hbp, hp⟩ := Nat.exists_infinite_primes (max bg br)
  obtain ⟨E, hE, aE, N, d, hd, het, hdegree⟩ :=
    exists_primeDegree_properCurve_cover M (by omega) p hp
  have : Surjective d := IsFiniteEtale.surjective d
  have hV : (d ⁻¹ᵁ U : Set N.C).Nonempty := by
    obtain ⟨x, hx⟩ := hU
    obtain ⟨y, hy⟩ := d.surjective x
    exact ⟨y, by change d y ∈ (U : Set M.C); rw [hy]; exact hx⟩
  have : IsCurveOver K F :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one M.toBase
      M.ffEquiv M.ffEquiv_algebraMap
  have : Algebra.EssFiniteType K F := by
    let : Algebra K M.C.functionField := M.functionFieldAlgebra
    exact (Algebra.EssFiniteType.iff_of_algEquiv M.ffAlgEquiv).mpr
      (essFiniteType_functionField M.toBase)
  obtain ⟨t, ht, hf, _⟩ :=
    IsCurveOver.exists_separating_transcendental (K := K) (F := F)
  have hRH := M.two_mul_genus_sub_two_eq_finiteEtale N d hd ⟨t, ht, hf⟩
  rw [hdegree] at hRH
  have hcard := natCard_openBoundary_preimage_eq_degree_mul M N d hd U hU
  rw [hdegree] at hcard
  let : Fintype (M.openBoundaryPlaces U.ι) := (M.openBoundaryPlaces_finite U.ι).fintype
  have hr : 0 < Nat.card (M.openBoundaryPlaces U.ι) := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_pos_iff.mpr hboundary.to_subtype
  have hgZ : (2 : ℤ) ≤ genusFF K F := by exact_mod_cast hg
  have hpZ : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hbgZ : (bg : ℤ) ≤ p := by exact_mod_cast (le_max_left bg br).trans hbp
  have hgenus : (bg : ℤ) ≤ genusFF K E := by nlinarith
  refine ⟨E, hE, aE, N, d, hd, het, hV, ?_, ?_⟩
  · exact_mod_cast hgenus
  · rw [hcard]
    exact ((le_max_right bg br).trans hbp).trans (by nlinarith)

end AnabelianGeometry.GeometricFundamentalGroup
