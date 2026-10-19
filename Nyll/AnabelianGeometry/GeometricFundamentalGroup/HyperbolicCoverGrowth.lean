/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.GeometricFundamentalGroup.GenusZeroRamifiedCover
import Nyll.AnabelianGeometry.GeometricFundamentalGroup.GenusOneCoverGrowth
import Nyll.AnabelianGeometry.GeometricFundamentalGroup.ProperCoverGrowth
import Nyll.EtaleFundamentalGroups.GaloisCovers.OpenCoverInvariants
import Mathlib.AlgebraicGeometry.Restrict

/-! # Simultaneous genus and boundary growth

Every punctured hyperbolic curve over an algebraically closed field of
characteristic zero has an actual connected finite étale cover exceeding
any prescribed genus and boundary bounds. In genus zero or one, an initial
Kummer cover raises the genus to at least two. A proper finite étale cover
then increases both invariants, and the two maps are composed.

Proper curves are handled by exists_finiteEtale_cover_genus_ge: their
finite étale covers remain proper, so their boundary cannot grow.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve

namespace AnabelianGeometry.GeometricFundamentalGroup

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

/-- The same actual finite étale cover of a punctured hyperbolic curve
has genus and boundary cardinality above the two prescribed bounds.
All intermediate fields, compactifications and covers are constructed. -/
theorem exists_finiteEtale_openCover_genus_boundary_ge
    {K F : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F] [Algebra K F] (M : CurveModel K F)
    (U : M.C.Opens) (hU : (U : Set M.C).Nonempty)
    (hhyperbolic : 2 < 2 * genusFF K F + Nat.card (M.openBoundaryPlaces U.ι))
    (hboundary : (M.openBoundaryPlaces U.ι).Nonempty) (bg br : ℕ) :
    ∃ (E : Type) (_ : Field E) (_ : Algebra K E) (N : CurveModel K E)
      (d : N.C ⟶ M.C),
      d ≫ M.toBase = N.toBase ∧ IsFinite d ∧ Surjective d ∧
      IsFiniteEtale (morphismRestrict d U) ∧
      (d ⁻¹ᵁ U : Set N.C).Nonempty ∧ bg ≤ genusFF K E ∧
      br ≤ Nat.card (N.openBoundaryPlaces (d ⁻¹ᵁ U).ι) := by
  have hfirst :
      ∃ (E : Type) (_ : Field E) (_ : Algebra K E) (N : CurveModel K E)
        (d : N.C ⟶ M.C),
        d ≫ M.toBase = N.toBase ∧ IsFinite d ∧ Surjective d ∧
        IsFiniteEtale (morphismRestrict d U) ∧
        (d ⁻¹ᵁ U : Set N.C).Nonempty ∧ 2 ≤ genusFF K E := by
    by_cases hg0 : genusFF K F = 0
    · obtain ⟨E, hE, aE, N, d, hd, hfinite, _hflat, hsurj, het, hV, hgN⟩ :=
        exists_finiteEtale_openCover_genus_ge_two_of_genus_zero M U hU hg0 (by omega)
      exact ⟨E, hE, aE, N, d, hd, hfinite, hsurj, het, hV, hgN⟩
    · by_cases hg1 : genusFF K F = 1
      · obtain ⟨E, hE, aE, N, d, hd, hfinite, _hflat, hsurj, het, hV, hgN⟩ :=
          exists_finiteEtale_openCover_genus_ge_two_of_genus_one M U hU hg1 hboundary
        exact ⟨E, hE, aE, N, d, hd, hfinite, hsurj, het, hV, hgN⟩
      · refine ⟨F, inferInstance, inferInstance, M, 𝟙 M.C, Category.id_comp _,
          inferInstance, inferInstance, ?_, ?_, by omega⟩
        · exact MorphismProperty.of_isIso
            (show MorphismProperty Scheme from @IsFiniteEtale) _
        · exact hU
  obtain ⟨E, hE, aE, N, d, hd, hfinite, hsurj, het, hV, hgN⟩ := hfirst
  have : IsFinite d := hfinite
  have : Surjective d := hsurj
  have : IsFiniteEtale (morphismRestrict d U) := het
  have hb (y : N.C) : y ∉ Set.range (d ⁻¹ᵁ U).ι ↔ d y ∉ Set.range U.ι := by
    rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    rfl
  have hboundaryN : (N.openBoundaryPlaces (d ⁻¹ᵁ U).ι).Nonempty :=
    EtaleFundamentalGroups.openBoundary_nonempty_of_finite_square
      M N d hd hsurj.surj U.ι (d ⁻¹ᵁ U).ι hb hboundary
  obtain ⟨L, hL, aL, P, f, hf, hfet, hW, hgP, hrP⟩ :=
    exists_finiteEtale_cover_genus_boundary_ge N hgN (d ⁻¹ᵁ U) hV hboundaryN bg br
  have : IsFiniteEtale f := hfet
  have : Surjective f := IsFiniteEtale.surjective f
  have hcomp : (f ≫ d) ≫ M.toBase = P.toBase := by
    rw [Category.assoc, hd, hf]
  have hcompEtale : IsFiniteEtale (morphismRestrict (f ≫ d) U) := by
    rw [morphismRestrict_comp]
    exact MorphismProperty.IsStableUnderComposition.comp_mem
      (P := (show MorphismProperty Scheme from @IsFiniteEtale)) _ _
      (MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := (show MorphismProperty Scheme from @IsFiniteEtale))
        (isPullback_morphismRestrict f (d ⁻¹ᵁ U)).flip hfet) het
  exact ⟨L, hL, aL, P, f ≫ d, hcomp, inferInstance, inferInstance,
    hcompEtale, hW, hgP, hrP⟩

end AnabelianGeometry.GeometricFundamentalGroup
