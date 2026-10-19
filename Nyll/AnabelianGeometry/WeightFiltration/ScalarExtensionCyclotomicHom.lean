/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.NumberFieldCyclotomicHomVanishing
import Nyll.AlgebraicCurves.Geometry.Picard.BaseChange.PicardRepresentabilityBaseChange
import Nyll.JacobianVarieties.Picard.GroupLaw.BaseChangeRelativeGroupLawMulCompat

/-!
# Cyclotomic Hom vanishing after extending the number field

Keep the original Jacobian point group and roots limit. Restrict its actual
coefficient action to a number-field extension and compare it with the
represented base-changed Jacobian using the literal pullback projection.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
open NeronModelInfra GoodReductionJacobian ProCGroups
open EtaleFundamentalGroups.Inertia

namespace AnabelianGeometry.WeightFiltration

variable (K L Ω : Type) [Field K]
  [Field L] [NumberField L] [Algebra K L]
  [Field Ω] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]
  [IsAlgClosure L Ω]

/-- Vanishing for the original point group requires equivariance only for
the Galois group of the extended number field. -/
theorem numberField_cyclotomicHom_eq_one_of_scalar_extension
    {C : Scheme} (c : C ⟶ Spec (.of K))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (.of K))) c)
    (D : RelativePic0Designation K c)
    (hD : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    [Smooth D.toBase] [IsProper D.toBase] [GeometricallyConnected D.toBase] :
    let G := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD
    let hc : G.IsCommutative :=
      RepresentsRelSubPic.relativeGroupLaw_isCommutative (P := algEquivZeroGroupCut c ε) hD
    ∀ φ : (primeToRootsSystem Ω Ω).inverseLimit →*
        Multiplicative (FullTateModule (G.AlgPoints hc Ω)),
      (∀ (σ : Ω ≃ₐ[L] Ω) t,
        φ (primeToRootsCoefficientMap Ω Ω σ.toRingHom t) =
          FullTateModule.mapHom
            (RelativeGroupLaw.AlgPoints.map (σ.restrictScalars K).toAlgHom) (φ t)) →
      φ = 1 := by
  intro G hc φ hφ
  let cL := baseChange K c L
  let εL := sectionBaseChange L ε
  let DL := D.baseChange L
  obtain ⟨hDL, hP⟩ := exists_representsRelSubPic_baseChange K c ε D hD L
  let J₁ := RepresentsRelSubPic.relativeGroupLaw
    (P := algEquivZeroGroupCut cL εL) hDL
  let hcL : J₁.IsCommutative :=
    RepresentsRelSubPic.relativeGroupLaw_isCommutative
      (P := algEquivZeroGroupCut cL εL) hDL
  let π := pullback.fst D.toBase (specMap K L)
  have hπ : IsPullback π DL.toBase D.toBase (specMap K L) :=
    IsPullback.of_hasPullback D.toBase (specMap K L)
  have hmul :
      ∀ (T : Scheme) (t : T ⟶ Spec (.of L)) (P Q : SchemeHomOver t DL.toBase),
        (J₁.mul t P Q).val ≫ π =
          (G.mul (t ≫ specMap K L)
            ⟨P.val ≫ π, by
              rw [Category.assoc, hπ.w, ← Category.assoc, P.property]⟩
            ⟨Q.val ≫ π, by
              rw [Category.assoc, hπ.w, ← Category.assoc, Q.property]⟩).val := by
    intro T t P Q
    exact baseChange_relativeGroupLaw_mul_compat
      K c ε D hD L hDL hP t P Q _ _ rfl rfl
  let e : J₁.AlgPoints hcL Ω ≃+ G.AlgPoints hc Ω :=
    G.algPointsPullbackEquiv hc J₁ hcL π hπ hmul Ω
  let eT := FullTateModule.mapEquiv e.symm
  let Φ := eT.toMonoidHom.comp φ
  have hΦ : ∀ (σ : Ω ≃ₐ[L] Ω) t,
      Φ (primeToRootsCoefficientMap Ω Ω σ.toRingHom t) =
        FullTateModule.mapHom (RelativeGroupLaw.AlgPoints.map σ.toAlgHom) (Φ t) := by
    intro σ t
    change eT (φ (primeToRootsCoefficientMap Ω Ω σ.toRingHom t)) = _
    rw [hφ]
    apply Multiplicative.toAdd.injective
    apply FullTateModule.ext
    intro n
    exact G.algPointsPullbackEquiv_symm_equivariant
      hc J₁ hcL π hπ hmul Ω σ
      (FullTateModule.evaluation _ n (Multiplicative.toAdd (φ t)))
  have hvan : Φ = 1 :=
    numberField_cyclotomicHom_eq_one L Ω cL εL DL hDL Φ hΦ
  apply MonoidHom.ext
  intro t
  apply eT.injective
  exact (DFunLike.congr_fun hvan t).trans eT.map_one.symm

end AnabelianGeometry.WeightFiltration
