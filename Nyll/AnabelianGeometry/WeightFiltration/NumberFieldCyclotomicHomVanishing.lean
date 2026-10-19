/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.NumberFieldGoodModel
import Nyll.AnabelianGeometry.WeightFiltration.AdicPicardWeightSeparation
import Nyll.AnabelianGeometry.WeightFiltration.CyclotomicHomCoordinates
import Nyll.AnabelianGeometry.WeightFiltration.GaloisCoefficientRestriction
import Nyll.JacobianVarieties.Picard.Points.ActualPicardPointGeometry
import Nyll.AbelianVarieties.Reduction.GoodModelPointComparison

/-!
# No cyclotomic homomorphism into the actual number-field Jacobian Tate module

For an arbitrary torsion coordinate n, choose a good model inverting n and
restrict to the powers of n. A single local Frobenius supplies both the roots
formula and weight separation on this restriction. Actual coefficient and
model maps return the vanishing to the original coordinate. No Weil weight
bound, common good place for all n, or scalar action on the full source is used.
-/

noncomputable section

open scoped NumberField
open NumberField IsDedekindDomain CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
open AlgebraicCurve NeronModelInfra GoodReductionJacobian ProCGroups
open EtaleFundamentalGroups.Inertia

namespace AnabelianGeometry.WeightFiltration

variable (K Ω : Type) [Field K] [NumberField K]
  [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
local notation "Kbar" => Ω

/-- The actual cyclotomic roots limit admits no equivariant homomorphism
to the full Tate module of the original represented Jacobian. -/
theorem numberField_cyclotomicHom_eq_one
    {C : Scheme} (c : C ⟶ Spec (.of K))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (.of K))) c)
    (D : RelativePic0Designation K c)
    (hD : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    [Smooth D.toBase] [IsProper D.toBase] [GeometricallyConnected D.toBase] :
    let G := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD
    let hc : G.IsCommutative :=
      RepresentsRelSubPic.relativeGroupLaw_isCommutative (P := algEquivZeroGroupCut c ε) hD
    ∀ φ : (primeToRootsSystem Kbar Kbar).inverseLimit →*
        Multiplicative (FullTateModule (G.AlgPoints hc Kbar)),
      (∀ (σ : Kbar ≃ₐ[K] Kbar) t,
        φ (primeToRootsCoefficientMap Kbar Kbar σ.toRingHom t) =
          FullTateModule.mapHom (RelativeGroupLaw.AlgPoints.map σ.toAlgHom) (φ t)) →
      φ = 1 := by
  intro G hc φ hφ
  have : IsAlgClosed Kbar := IsAlgClosure.isAlgClosed K
  have : CharZero Kbar := charZero_of_injective_algebraMap (algebraMap K Kbar).injective
  apply MonoidHom.ext
  intro t
  apply Multiplicative.toAdd.injective
  change Multiplicative.toAdd (φ t) = 0
  apply FullTateModule.ext
  intro n
  have hX : AbelianSchemePropertyBundle K D.toBase :=
    { smooth := inferInstance
      proper := inferInstance
      connectedFibres := fun s => D.toBase.isConnected_preimage_singleton s
      hasGroupLaw := ⟨G⟩ }
  obtain ⟨_, _, _, v, _, hnunit, Y, f₀, G₀, hY, hc₀, a, ha, hmul⟩ :=
    G.exists_numberField_good_model K hc hX (n : ℕ) n.ne_zero ∅
  let Kv := v.adicCompletion K
  let H := v.adicCompletionIntegers K
  let L := AlgebraicClosure Kv
  have : Smooth f₀ := hY.smooth
  have : IsProper f₀ := hY.proper
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace f₀
  let i : Kbar →ₐ[K] L := IsAlgClosed.lift
  let : Algebra Kbar L := i.toAlgebra
  have : IsScalarTower K Kbar L := IsScalarTower.of_algHom i
  let CL := pullback c (specMap K L)
  have : IsIntegral CL := isIntegral_pullback_Spec_field K c (specMap K L)
  let F := CL.functionField
  let : Algebra L F := (baseToFunctionField (pullback.snd c (specMap K L))).toAlgebra
  obtain ⟨hcurve, hfg, ePic, hePic⟩ :=
    JacobianVarieties.Picard.exists_actual_picard_point_geometry (L := L) c ε D hD
  have : IsCurveOver L F := hcurve
  let eModel : G.AlgPoints hc L ≃+ G₀.AlgPoints hc₀ L :=
    G.goodModelPointsEquiv hc G₀ hc₀ a ha hmul L
  let e : Pic0 L F ≃+ G₀.AlgPoints hc₀ L := ePic.trans eModel
  have he : ∀ σ : L ≃ₐ[Kv] L, ∃ g : SemilinearAut L F,
      SemilinearAut.baseAut g = σ.toRingEquiv ∧
      ∀ z : Pic0 L F, e (g • z) =
        RelativeGroupLaw.AlgPoints.map (σ.restrictScalars H).toAlgHom (e z) := by
    intro σ
    obtain ⟨g, hg, hge⟩ := hePic (σ.restrictScalars K)
    refine ⟨g, hg, ?_⟩
    intro z
    exact (congrArg eModel (hge z)).trans
      (G.goodModelPointsEquiv_equivariant hc G₀ hc₀ a ha hmul L σ (ePic z))
  let I := Submonoid.powers n
  have hI (m : I) : IsUnit ((m.1 : ℕ) : H) := by
    obtain ⟨b, hb⟩ := m.property
    rw [← hb]
    change IsUnit (((n : ℕ) ^ b : ℕ) : H)
    rw [Nat.cast_pow]
    exact hnunit.pow b
  obtain ⟨σ, hroots, hsep⟩ :=
    exists_adic_picard_weight_separation K v G₀ hc₀ F hfg e he I hI
  let τ : Kbar ≃ₐ[K] Kbar := (σ.restrictScalars K).restrictNormal Kbar
  let P : G.AlgPoints hc Kbar →+ G₀.AlgPoints hc₀ L :=
    eModel.toAddMonoidHom.comp (RelativeGroupLaw.AlgPoints.map i)
  let Fσ : G₀.AlgPoints hc₀ L →+ G₀.AlgPoints hc₀ L :=
    RelativeGroupLaw.AlgPoints.map (σ.restrictScalars H).toAlgHom
  have hP (z : G.AlgPoints hc Kbar) :
      P (RelativeGroupLaw.AlgPoints.map τ.toAlgHom z) = Fσ (P z) := by
    have hcomp : i.comp τ.toAlgHom = (σ.restrictScalars K).toAlgHom.comp i :=
      AlgHom.ext (fun z => (σ.restrictScalars K).restrictNormal_commutes Kbar z)
    have hm : (RelativeGroupLaw.AlgPoints.map (L := G) (hc := hc) i).comp
          (RelativeGroupLaw.AlgPoints.map τ.toAlgHom) =
        (RelativeGroupLaw.AlgPoints.map (σ.restrictScalars K).toAlgHom).comp
          (RelativeGroupLaw.AlgPoints.map i) := by
      calc
        _ = RelativeGroupLaw.AlgPoints.map (L := G) (hc := hc) (i.comp τ.toAlgHom) :=
          (RelativeGroupLaw.AlgPoints.map_comp (L := G) (hc := hc) τ.toAlgHom i).symm
        _ = RelativeGroupLaw.AlgPoints.map (L := G) (hc := hc)
            ((σ.restrictScalars K).toAlgHom.comp i) :=
          congrArg (fun b : Kbar →ₐ[K] L =>
            RelativeGroupLaw.AlgPoints.map (L := G) (hc := hc) b) hcomp
        _ = _ := RelativeGroupLaw.AlgPoints.map_comp (L := G) (hc := hc)
          i (σ.restrictScalars K).toAlgHom
    exact (congrArg eModel (DFunLike.congr_fun hm z)).trans
      (G.goodModelPointsEquiv_equivariant hc G₀ hc₀ a ha hmul L σ
        (RelativeGroupLaw.AlgPoints.map i z))
  let Φ : (primeToRootsSystem Kbar Kbar).inverseLimit →*
      Multiplicative (FullTateModule (G₀.AlgPoints hc₀ L)) :=
    (FullTateModule.mapHom P).toMonoidHom.comp φ
  have hΦ (u : (primeToRootsSystem Kbar Kbar).inverseLimit) :
      Φ (primeToRootsCoefficientMap Kbar Kbar τ.toRingHom u) =
        Multiplicative.ofAdd (FullTateModule.map Fσ (Multiplicative.toAdd (Φ u))) := by
    apply Multiplicative.toAdd.injective
    apply FullTateModule.ext
    intro m
    have h := congrArg
      (fun z => P (FullTateModule.evaluation (G.AlgPoints hc Kbar) m
        (Multiplicative.toAdd z))) (hφ τ u)
    exact h.trans (hP _)
  let x := FullTateModule.restrict (G₀.AlgPoints hc₀ L) I (Multiplicative.toAdd (Φ t))
  have hx : x = 0 := by
    apply hsep x
    intro m
    apply Subtype.ext
    exact cyclotomicHom_coefficient_scalar_coordinate Φ m.1
      (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr m.1.ne_zero))
      τ.toRingHom Fσ (Nat.card (IsLocalRing.ResidueField H))
      (fun z hz => RelativeGroupLaw.normalRestriction_pow_of_pow
        (σ.restrictScalars K) (m.1 : ℕ) _ (hroots m) z hz) hΦ t
  have hmem : n ∈ I := ⟨1, pow_one n⟩
  have hz := congrArg
    (RestrictedTateModule.evaluation (G₀.AlgPoints hc₀ L) I ⟨n, hmem⟩) hx
  have hcoeff : G.torsionCoefficientMap hc i n
      (FullTateModule.projection (G.AlgPoints hc Kbar) n (Multiplicative.toAdd (φ t))) = 0 := by
    apply Subtype.ext
    apply eModel.injective
    exact hz.trans eModel.map_zero.symm
  have hnK : IsUnit ((n : ℕ) : K) :=
    isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr n.ne_zero)
  have hzero := (G.torsionCoefficientMap_bijective hc i n hnK).1
    (hcoeff.trans (G.torsionCoefficientMap hc i n).map_zero.symm)
  exact congrArg Subtype.val hzero

end AnabelianGeometry.WeightFiltration
