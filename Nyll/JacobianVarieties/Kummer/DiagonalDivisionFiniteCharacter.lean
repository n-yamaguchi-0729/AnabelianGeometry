/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Geometry.Picard.DivisionPullback
public import Nyll.AlgebraicCurves.Geometry.Picard.Representability.Pic0EquivPointsPicardRepresentability
public import Nyll.AlgebraicCurves.Models.Kummer.AdicH1TateComparison
public import Nyll.AlgebraicCurves.Models.Kummer.CurveNativeAdicH1Comparison
public import Nyll.AlgebraicCurves.Models.Kummer.CurveNativeH1Picard
public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleFundamentalGroups.Cohomology.H1Character
public import Nyll.EtaleFundamentalGroups.Cohomology.H1CharacterComposition
public import Nyll.EtaleFundamentalGroups.Cohomology.H1Naturality
public import Nyll.EtaleFundamentalGroups.Cohomology.KummerPowerCoefficients
public import Nyll.EtaleFundamentalGroups.GeometricFiber.AbelianUnitMonodromy
public import Nyll.JacobianVarieties.Kummer.AbelJacobiWeilCohomology
public import Nyll.JacobianVarieties.Kummer.CohomologyPullback
public import Nyll.JacobianVarieties.Kummer.DiagonalDivisionMonodromy
public import Nyll.SchemeTheory.LocalGeometry.SmoothStalks
public import Nyll.SchemeTheory.Normalization.Normal
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Nyll.ProCGroups.Abelian.FullTateModule

/-!
# Original finite H¹ characters on the retained division cover

The constructed Weil classes identify every original finite H¹ character
with the actual multiplication monodromy, in the original coherent roots
coordinates. The divisor class in this identity is the original native
Kummer image. Consequently these characters kill the stabilizers of points
of the specified division cover. The same Picard and torsion identifications
are retained for the subsequent calculation on overlaps.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.PreGaloisCategory
open AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve
open NeronModelInfra GoodReductionJacobian EtaleCohomology.Classical
open EtaleFundamentalGroups.Cohomology
open JacobianVarieties.Picard.Proofs.Pic0PointsAbelJacobi.AlgebraicGeometry.RelPicard

namespace JacobianVarieties.Kummer

attribute [local instance] IsCurveOver.toHasPrincipalDivisors
  CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

/-- The same geometric Picard coordinates compute every original finite
character by the Weil pairing and show its vanishing on the stabilizers of
the retained division cover. Both comparisons are supplied from geometry. -/
theorem exists_diagonalDivision_finiteLevelCharacters
    {K F : Type u} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    [IsCurveOver K F] (M : CurveModel K F) [GeometricallyIntegral M.toBase]
    (ε : SchemeHomOver (𝟙 (Spec (.of K))) M.toBase)
    (D : RelativePic0Designation K M.toBase)
    (hD : RepresentsRelSubPic M.toBase ε (algEquivZeroCut M.toBase ε) D)
    [Smooth D.toBase] [IsProper D.toBase] [GeometricallyConnected D.toBase]
    (aj : SchemeHomOver M.toBase D.toBase)
    (hclass : ∀ (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of K))
      (x : SchemeHomOver t M.toBase),
      Nonempty ((hD.poincare.pullbackAlong
        ⟨x.1 ≫ aj.1, (Category.assoc _ _ _).trans
          ((congrArg (x.1 ≫ ·) aj.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint M.toBase x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint M.toBase (t ≫ ε.1)
            ((Category.assoc _ _ _).trans
              ((congrArg (t ≫ ·) ε.2).trans (Category.comp_id t)))).idealModule))
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K)) (n : ℕ)
    (Y : FiniteEtale M.C)
    (i : Y.left ⟶ hD.divisionPullback
      (P := algEquivZeroGroupCut M.toBase ε) aj (ℓ ^ (n + 1)))
    (hi : i ≫ hD.divisionProjection
      (P := algEquivZeroGroupCut M.toBase ε) aj (ℓ ^ (n + 1)) = Y.hom) :
    let N : ℕ+ := ⟨ℓ ^ (n + 1), pow_pos (Fact.out : ℓ.Prime).pos (n + 1)⟩
    let hn : IsUnit ((N : ℕ) : K) := by
      change IsUnit ((ℓ ^ (n + 1) : ℕ) : K)
      simpa only [Nat.cast_pow] using hℓ.pow (n + 1)
    let G := RepresentsRelSubPic.relativeGroupLaw
      (P := algEquivZeroGroupCut M.toBase ε) hD
    let hc : G.IsCommutative := RepresentsRelSubPic.relativeGroupLaw_isCommutative
      (P := algEquivZeroGroupCut M.toBase ε) hD
    let _ : Algebra K M.C.functionField := M.functionFieldAlgebra
    let Ω := AlgebraicClosure M.C.functionField
    let η := Spec.map (CommRingCat.ofHom (algebraMap M.C.functionField Ω))
    let q := M.C.fromSpecStalk (genericPoint M.C)
    let ξ := η ≫ q
    let _ : NeZero (ℓ ^ (n + 1)) := ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
    let A := ellPowerCoefficients.{u} ℓ n
    let : TopologicalSpace (Multiplicative A) := ⊥
    ∃ e : Pic0 K F ≃+ G.AlgPoints hc K,
      (∀ x : SchemeHomOver (𝟙 (Spec (.of K))) M.toBase,
        ∃ Dv : Divisor.degZero (K := K) (F := F),
          (Dv : Divisor K F) = Finsupp.single (M.pointEquivPlace x) 1 -
            Finsupp.single (M.pointEquivPlace ε) 1 ∧
          (RelativeGroupLaw.AlgPoints.toPoint (e (Pic0.mk Dv))).1 = x.1 ≫ aj.1) ∧
      ∃ τ : Pic0.torsion K F (ℓ ^ (n + 1)) ≃+
          ProCGroups.torsionLevel (G.AlgPoints hc K) N,
        (∀ x, (τ x).1 = e x.1) ∧
        (∀ x, (G.torsionLevelEquivSchemeKerPoints hc N (τ x)).1 ≫
          pullback.fst (G.schemeNsmul (N : ℕ)) (G.one (𝟙 (Spec (.of K)))).1 =
            (RelativeGroupLaw.AlgPoints.toPoint (e x.1)).1) ∧
        ∃ w : DivisorialWeilPairingData K F (ℓ ^ (n + 1)),
          (∀ (y : finiteLevelCohomology M.C ℓ n 1)
            (path : FiniteEtale.fiber (η ≫ q ≫ aj.1) ≅
              FiniteEtale.fiber (G.one (𝟙 (Spec (.of K)))).1)
            (σ : Ω ≃ₐ[M.C.functionField] Ω),
            (((ellPowerRootsCoefficientEquiv K ℓ hℓ n
              (h1Character A ξ y (FiniteEtale.fundamentalGroupHom q η
                (toAut (FiniteEtale.fiber η) (Ω ≃ₐ[M.C.functionField] Ω) σ))).toAdd).toMul :
                  Kˣ) : K) =
              w.pair (M.nativeFiniteLevelH1PicardTorsionEquiv ℓ hℓ n y)
                (τ.symm (RelativeGroupLaw.UnitMultiplication.monodromy G hc ⟨N, hn⟩
                  (continuousConjAut path (FiniteEtale.fundamentalGroupHom (q ≫ aj.1) η
                    (toAut (FiniteEtale.fiber η) (Ω ≃ₐ[M.C.functionField] Ω) σ)))))) ∧
          ∀ (y : finiteLevelCohomology M.C ℓ n 1)
            (z : (FiniteEtale.fiber ξ).obj Y) (g : Aut (FiniteEtale.fiber ξ)),
            g • z = z → h1Character A ξ y g = 1 := by
  intro N hn G hc hbase Ω η q ξ hN A htop
  classical
  have : Algebra.EssFiniteType K F := DictGlue.essFiniteType_of_curveModel M
  have : Smooth M.toBase := SmoothOfRelativeDimension.smooth 1 M.toBase
  have : IsIntegrallyClosed Γ(Spec (.of K), ⊤) := IsIntegrallyClosed.of_equiv
    (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv
  have : IsNormalIntegral M.C := IsNormalIntegral.of_stalks M.C
    (fun x => (Smooth.isDomain_and_isIntegrallyClosed_stalk M.toBase x).2)
  have : ConnectedSpace D.P :=
    GeometricallyConnected.connectedSpace D.toBase D.toBase.isOpenMap
  let B := AddCommGrpCat.of (Additive (rootsOfUnity (ℓ ^ (n + 1)) K))
  let : TopologicalSpace (rootsOfUnity (ℓ ^ (n + 1)) K) := ⊥
  have : DiscreteTopology (rootsOfUnity (ℓ ^ (n + 1)) K) := ⟨rfl⟩
  let : TopologicalSpace (Multiplicative B) := ⊥
  have : DiscreteTopology (Multiplicative B) := ⟨rfl⟩
  obtain ⟨e, hpoint, τ, hτ, hker, w, ν, hν, hpull⟩ :=
    exists_abelJacobi_weil_cohomology_pullback M ε D hD aj hclass N hn
  let coeff := ellPowerRootsCoefficientEquiv K ℓ hℓ n
  let α : A ⟶ B := AddCommGrpCat.ofHom coeff.toAddMonoidHom
  have hroots (y : finiteLevelCohomology M.C ℓ n 1) :
      Sheaf.H.map ((constantSheaf M.C.smallEtaleTopology AddCommGrpCat.{u}).map α) 1 y =
        constantCohomologyPullback aj.1 B 1
          (ν (M.nativeFiniteLevelH1PicardTorsionEquiv ℓ hℓ n y)) := by
    have hnative :=
      M.nativeFiniteLevelH1PicardTorsionEquiv_eq_kummerEllPowerCohomologyEquiv_symm ξ ℓ hℓ n y
    have hforward := (congrArg (M.kummerEllPowerCohomologyEquiv ξ ℓ hℓ n) hnative).trans
      ((M.kummerEllPowerCohomologyEquiv ξ ℓ hℓ n).apply_symm_apply y)
    have hmap := congrArg
      (fun z : finiteLevelCohomology M.C ℓ n 1 =>
        Sheaf.H.map ((constantSheaf M.C.smallEtaleTopology AddCommGrpCat.{u}).map α) 1 z)
      hforward
    have hroot := M.kummerEllPowerCohomologyEquiv_roots ξ ℓ hℓ n
      (M.nativeFiniteLevelH1PicardTorsionEquiv ℓ hℓ n y)
    have hpullNative := hpull (M.nativeFiniteLevelH1PicardTorsionEquiv ℓ hℓ n y)
    exact hmap.symm.trans (hroot.trans hpullNative.symm)
  have hchars (y : finiteLevelCohomology M.C ℓ n 1) (g : Aut (FiniteEtale.fiber ξ)) :
      (coeff (h1Character A ξ y g).toAdd).toMul =
        h1Character B ξ (constantCohomologyPullback aj.1 B 1
          (ν (M.nativeFiniteLevelH1PicardTorsionEquiv ℓ hℓ n y))) g := by
    have h := congrArg (fun χ : Aut (FiniteEtale.fiber ξ) →ₜ* Multiplicative B => χ g)
      (h1Character_naturality α ξ y)
    change (coeff (h1Character A ξ y g).toAdd).toMul =
      h1Character B ξ (Sheaf.H.map
        ((constantSheaf M.C.smallEtaleTopology AddCommGrpCat.{u}).map α) 1 y) g at h
    rw [hroots y] at h
    exact h
  refine ⟨e, hpoint, τ, hτ, hker, w, ?_, ?_⟩
  · intro y path σ
    let γ := toAut (FiniteEtale.fiber η) (Ω ≃ₐ[M.C.functionField] Ω) σ
    rw [hchars y (FiniteEtale.fundamentalGroupHom q η γ)]
    let t := M.nativeFiniteLevelH1PicardTorsionEquiv ℓ hℓ n y
    have hchain := h1Character_pullback_fundamentalGroupHom_conj
      q aj.1 η (G.one (𝟙 (Spec (.of K)))).1 path B (ν t) γ
    exact (congrArg (fun ζ : rootsOfUnity (ℓ ^ (n + 1)) K => ζ.val.val)
      hchain).trans (hν t _)
  · intro y z g hg
    have hr := divisionWeilPullbackCharacter_eq_one_of_fixes
      (P := algEquivZeroGroupCut M.toBase ε) hD aj N hn Y i hi τ w ν hν
      (M.nativeFiniteLevelH1PicardTorsionEquiv ℓ hℓ n y) z g hg
    have hz := (hchars y g).trans hr
    apply Multiplicative.toAdd.injective
    change (h1Character A ξ y g).toAdd = 0
    apply coeff.injective
    rw [map_zero]
    exact congrArg (fun ζ : rootsOfUnity (ℓ ^ (n + 1)) K => Additive.ofMul ζ) hz

end JacobianVarieties.Kummer
