/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.KernelPoints
public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLawEtaleSchemeNsmul
public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLawSmoothOfRelativeDimension
public import Nyll.SchemeTheory.Morphisms.ProperIntegralGlobalSections
public import Nyll.SchemeTheory.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver

/-!
# Constancy of torsion points over a proper integral scheme

A point killed by an invertible integer factors through the actual finite
multiplication kernel. On a proper integral scheme over an algebraically
closed field, this affine-valued map comes from a rational torsion point.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

namespace GoodReductionJacobian.RelativeGroupLaw

variable {K : Type u} [Field K] [IsAlgClosed K]
  {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}
  [IsProper f] [Smooth f] (G : RelativeGroupLaw K f) (hc : G.IsCommutative)

include hc in
/-- An actual torsion point over a proper integral scheme is the pullback
of a torsion point over the original field of constants. -/
theorem isTorsionPoint_exists_constant
    {W : Scheme.{u}} [IsIntegral W]
    (w : W ⟶ Spec (CommRingCat.of K)) [IsProper w]
    (n : ℕ) (hn : IsUnit (n : K)) (x : SchemeHomOver w f)
    (hx : G.IsTorsionPoint w n x) :
    ∃ τ : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f,
      G.IsTorsionPoint (𝟙 (Spec (CommRingCat.of K))) n τ ∧
        GoodReductionJacobian.schemeHomOverComp w (Category.comp_id w) τ = x := by
  obtain ⟨d, hd⟩ := G.exists_smoothOfRelativeDimension_of_smooth_of_isLocalRing
  have : SmoothOfRelativeDimension d f := hd
  have : Etale (G.schemeNsmul n) :=
    G.etale_schemeNsmul_of_isUnit_of_smoothOfRelativeDimension hc d n hn
  have : IsProper (G.schemeNsmul n ≫ f) := by
    rw [G.schemeNsmul_over]
    infer_instance
  have : IsProper (G.schemeNsmul n) := IsProper.of_comp _ f
  have : LocallyQuasiFinite (G.schemeNsmul n) :=
    LocallyQuasiFinite.of_formallyUnramified_of_locallyOfFiniteType _
  have : IsFinite (G.schemeNsmul n) :=
    IsFinite.of_isProper_of_locallyQuasiFinite _
  have : IsFinite (G.schemeKerStr n) := inferInstance
  have : IsAffine (G.schemeKer n) := isAffine_of_isAffineHom (G.schemeKerStr n)
  let z : SchemeHomOver w (G.schemeKerStr n) :=
    G.torsionSubsetEquivSchemeKerPoints w n ⟨x, hx⟩
  obtain ⟨p, ⟨hp, hwp⟩, _⟩ :=
    properIntegralHomOverToAffine_existsUnique w (G.schemeKerStr n) z.1 z.2
  let e : G.torsionSubset (𝟙 (Spec (CommRingCat.of K))) n ≃
      SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (G.schemeKerStr n) :=
    G.torsionSubsetEquivSchemeKerPoints (𝟙 (Spec (CommRingCat.of K))) n
  let τ : G.torsionSubset (𝟙 (Spec (CommRingCat.of K))) n := e.symm ⟨p, hp⟩
  have hτ : p ≫ pullback.fst (G.schemeNsmul n)
      (G.one (𝟙 (Spec (CommRingCat.of K)))).1 = τ.1.1 := by
    have h := G.torsionSubsetEquivSchemeKerPoints_comp_fst
      (𝟙 (Spec (CommRingCat.of K))) n τ
    change (e (e.symm ⟨p, hp⟩)).1 ≫ _ = τ.1.1 at h
    rw [e.apply_symm_apply] at h
    exact h
  refine ⟨τ.1, τ.2, ?_⟩
  apply Subtype.ext
  change w ≫ τ.1.1 = x.1
  rw [← hτ, ← Category.assoc, hwp]
  exact G.torsionSubsetEquivSchemeKerPoints_comp_fst w n ⟨x, hx⟩

end GoodReductionJacobian.RelativeGroupLaw
