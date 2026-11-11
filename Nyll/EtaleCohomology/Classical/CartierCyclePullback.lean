/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.CartierCycleClass
public import Nyll.EtaleCohomology.Classical.CartierOpenGenericComparison
public import Nyll.EtaleCohomology.Classical.CartierOpenUnitSections
public import Nyll.EtaleCohomology.Classical.KummerPullback
public import Nyll.EtaleCohomology.Classical.OpenUnitQuotientEquations
public import Nyll.EtaleCohomology.Classical.UnitQuotientFunctoriality
public import Nyll.EtaleCohomology.Classical.UnitQuotientPullbackSections
public import Nyll.EtaleCohomology.Classical.ZariskiH0Ext
public import Nyll.SchemeTheory.Divisors.Basic
public import Nyll.SchemeTheory.Sheaves.IdealSheafComap
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Actual Cartier cycle classes commute with scheme pullback

The pullback ideal is computed by the original structure-sheaf maps.
Its actual local equations are the actual pulled-back equations, so the
original open-unit quotient H⁰ classes agree. The actual unit boundary
and actual Kummer boundary then give naturality in the original H¹(Gm)
and original H²(μₙ), including for nondominant graph morphisms.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

/-- The original ideal-sheaf pullback has the literal inverse-image
open complement. -/
theorem idealSheafComap_complement_preimage
    {X Y : Scheme.{u}} (I : X.IdealSheafData) (f : Y ⟶ X) :
    (I.comap f).support.compl = f ⁻¹ᵁ I.support.compl :=
  congrArg TopologicalSpace.Closeds.compl (I.support_comap f)

/-- The genuinely glued open-unit class of the actual pullback Cartier
ideal is the native H⁰ pullback of the original class. -/
theorem effectiveCartierOpenUnitH0_pullback
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : Y ⟶ X) (D : Scheme.EffectiveCartierDivisor X)
    (hD : (D.1.comap f).IsEffectiveCartier)
    (O : X.Opens) (P : Y.Opens) (hO : O ≤ D.1.support.compl)
    (hP : P ≤ (D.1.comap f).support.compl)
    (g : P.toScheme ⟶ O.toScheme) (hg : g ≫ O.ι = P.ι ≫ f) :
    etaleUnitQuotientCohomologySquareMap O.ι f P.ι g hg 0
        (effectiveCartierOpenUnitH0 D O hO) =
      effectiveCartierOpenUnitH0 ⟨D.1.comap f, hD⟩ P hP := by
  let E : Scheme.EffectiveCartierDivisor Y := ⟨D.1.comap f, hD⟩
  apply etaleAbelianH0_ext_zariski Y (etaleUnitQuotient P.ι)
  intro y
  obtain ⟨U, hyU, s, hreg, hI⟩ := D.2 (f y)
  obtain ⟨W, hW, hyW, hWU⟩ :=
    exists_isAffineOpen_mem_and_subset (X := Y) (U := f ⁻¹ᵁ U.1) hyU
  have : Nonempty U.1 := ⟨⟨f y, hyU⟩⟩
  have : Nonempty W := ⟨⟨y, hyW⟩⟩
  let t := f.appLE U.1 W hWU s
  have hE : E.1.ideal ⟨W, hW⟩ = Ideal.span {t} := by
    change (D.1.comap f).ideal ⟨W, hW⟩ = _
    rw [Scheme.IdealSheafData.ideal_comap_of_le D.1 f U ⟨W, hW⟩ hWU,
      hI, Ideal.map_span, Set.image_singleton]
  let hs := idealGenerator_avoidingOpen_le_basicOpen X D.1 O hO U s hI
  let ht := idealGenerator_avoidingOpen_le_basicOpen Y E.1 P hP ⟨W, hW⟩ t hE
  refine ⟨W, hyW, ?_⟩
  exact (etaleUnitQuotientCohomologySquareMap_zero_equation f O P g hg U.1 W hWU
    s hs ht (effectiveCartierOpenUnitH0 D O hO)
      (effectiveCartierOpenUnitH0_section D O hO U s hI)).trans
        (effectiveCartierOpenUnitH0_section E P hP ⟨W, hW⟩ t hE).symm

/-- Pullback of the original Cartier H¹(Gm) class is the original class
of the actual pulled-back ideal. Its Cartier regularity is the only
transversality condition. -/
theorem effectiveCartierMultiplicativeGroupH1_pullback
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : Y ⟶ X) (D : Scheme.EffectiveCartierDivisor X)
    (hD : (D.1.comap f).IsEffectiveCartier) :
    etaleMultiplicativeGroupCohomologyPullback f 1
        (effectiveCartierMultiplicativeGroupH1 D) =
      effectiveCartierMultiplicativeGroupH1 ⟨D.1.comap f, hD⟩ := by
  let E : Scheme.EffectiveCartierDivisor Y := ⟨D.1.comap f, hD⟩
  let O : X.Opens := D.1.support.compl
  let P : Y.Opens := E.1.support.compl
  have : Nonempty O := effectiveCartier_complement_nonempty D
  have : Nonempty P := effectiveCartier_complement_nonempty E
  have hP : P ≤ f ⁻¹ᵁ O := (idealSheafComap_complement_preimage D.1 f).le
  let g := f.resLE O P hP
  let hg : g ≫ O.ι = P.ι ≫ f := f.resLE_comp_ι hP
  have : Mono (etaleMultiplicativeGroupToPushforward O.ι) :=
    etaleMultiplicativeGroupToNonemptyOpen_mono X O
  have : Mono (etaleMultiplicativeGroupToPushforward P.ι) :=
    etaleMultiplicativeGroupToNonemptyOpen_mono Y P
  let a := effectiveCartierOpenUnitH0 D O le_rfl
  have ha := effectiveCartierOpenUnitH0_pullback f D hD O P le_rfl le_rfl g hg
  have hboundary :
      etaleMultiplicativeGroupCohomologyPullback f 1
          (Sheaf.H.δ (etaleNonemptyOpenUnitShortComplex_shortExact X O) 0 1 rfl a) =
        Sheaf.H.δ (etaleNonemptyOpenUnitShortComplex_shortExact Y P) 0 1 rfl
          (etaleUnitQuotientCohomologySquareMap O.ι f P.ι g hg 0 a) :=
    etaleUnitBoundary_zero_pullback_square O.ι f P.ι g hg a
  exact (congrArg (etaleMultiplicativeGroupCohomologyPullback f 1)
    (effectiveCartierOpenUnitH0_boundary D O le_rfl).symm).trans
      (hboundary.trans
        ((congrArg (Sheaf.H.δ
          (etaleNonemptyOpenUnitShortComplex_shortExact Y P) 0 1 rfl) ha).trans
            (effectiveCartierOpenUnitH0_boundary E P le_rfl)))

/-- The original roots-of-unity cycle class commutes with actual scheme
pullback whenever the original inverse-image ideal remains Cartier. -/
theorem effectiveCartierCycleClass_pullback
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : Y ⟶ X) (D : Scheme.EffectiveCartierDivisor X)
    (hD : (D.1.comap f).IsEffectiveCartier) {n : ℕ}
    (hn : 0 < n) (hnX : IsUnit (n : Γ(X, ⊤))) (hnY : IsUnit (n : Γ(Y, ⊤))) :
    etaleRootsOfUnityCohomologyPullback f n 2 (effectiveCartierCycleClass D hn hnX) =
      effectiveCartierCycleClass ⟨D.1.comap f, hD⟩ hn hnY := by
  unfold effectiveCartierCycleClass
  rw [etaleKummerBoundary_one_pullback f hn hnX,
    effectiveCartierMultiplicativeGroupH1_pullback f D hD]

end EtaleCohomology
