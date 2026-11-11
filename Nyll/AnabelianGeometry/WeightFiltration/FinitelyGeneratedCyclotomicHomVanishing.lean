/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AnabelianGeometry.WeightFiltration.FinitelyGeneratedNormalGoodModel
public import Nyll.AnabelianGeometry.WeightFiltration.NormalLocalPicardWeightSeparation
public import Nyll.AnabelianGeometry.WeightFiltration.CyclotomicHomCoordinates
public import Nyll.JacobianVarieties.Picard.Points.ActualPicardPointGeometry
public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.AlgebraicPointsPullback
public import Nyll.SchemeTheory.RingTheory.Localization.Fraction.FieldLocalization

/-!
# No cyclotomic homomorphism into the actual finitely generated-field Jacobian Tate module

For an arbitrary torsion coordinate n, choose a good model inverting n and
restrict to the powers of n. A single local Frobenius supplies both the roots
formula and weight separation on this restriction. Actual coefficient and
model maps return the vanishing to the original coordinate. No Weil weight
bound, common good place for all n, or scalar action on the full source is used.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
open AlgebraicCurve NeronModelInfra GoodReductionJacobian ProCGroups
open EtaleFundamentalGroups.Inertia

namespace AnabelianGeometry.WeightFiltration

variable (K Ω : Type) [Field K] [CharZero K] [Field.FG K]
  [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
local notation "Kbar" => Ω

/-- The actual cyclotomic roots limit admits no equivariant homomorphism
to the full Tate module of the original represented Jacobian. -/
theorem finitelyGenerated_cyclotomicHom_eq_one
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
  obtain ⟨T, _, _, hfrac, m, hm, hmodel⟩ :=
    G.exists_finitelyGenerated_normal_local_good_model K inferInstance hc hX
      (n : ℕ) n.ne_zero
  have : IsFractionRing T K := hfrac
  have : m.IsMaximal := hm
  let H := Localization.AtPrime m
  let : Algebra H K :=
    EtaleFundamentalGroups.localizationAtPrimeToFractionFieldAlgebra (K := K) m
  obtain ⟨hdom, hlocal, _, hnormal, hfracH, hfinite, hnunit, _, _,
      Y, f₀, G₀, a, ha, hY, hc₀, hmul⟩ := hmodel
  have : IsDomain H := hdom
  have : IsLocalRing H := hlocal
  have : IsIntegrallyClosed H := hnormal
  have : IsFractionRing H K := hfracH
  have : Finite (IsLocalRing.ResidueField H) := hfinite
  let : Algebra H Kbar := ((algebraMap K Kbar).comp (algebraMap H K)).toAlgebra
  have : IsScalarTower H K Kbar :=
    IsScalarTower.of_algebraMap_eq' (R := H) (S := K) (A := Kbar) rfl
  have : Smooth f₀ := hY.smooth
  have : IsProper f₀ := hY.proper
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace f₀
  let CL := pullback c (specMap K Kbar)
  have : IsIntegral CL := isIntegral_pullback_Spec_field K c (specMap K Kbar)
  let F := CL.functionField
  let : Algebra Kbar F :=
    (baseToFunctionField (pullback.snd c (specMap K Kbar))).toAlgebra
  obtain ⟨hcurve, hfg, ePic, hePic⟩ :=
    JacobianVarieties.Picard.exists_actual_picard_point_geometry (L := Kbar) c ε D hD
  have : IsCurveOver Kbar F := hcurve
  let eModel : G.AlgPoints hc Kbar ≃+ G₀.AlgPoints hc₀ Kbar :=
    G₀.algPointsPullbackEquiv hc₀ G hc a ha hmul Kbar
  let e : Pic0 Kbar F ≃+ G₀.AlgPoints hc₀ Kbar := ePic.trans eModel
  have he : ∀ σ : Kbar ≃ₐ[K] Kbar, ∃ g : SemilinearAut Kbar F,
      SemilinearAut.baseAut g = σ.toRingEquiv ∧
      ∀ z : Pic0 Kbar F, e (g • z) =
        RelativeGroupLaw.AlgPoints.map (σ.restrictScalars H).toAlgHom (e z) := by
    intro σ
    obtain ⟨g, hg, hge⟩ := hePic σ
    refine ⟨g, hg, ?_⟩
    intro z
    exact (congrArg eModel (hge z)).trans
      (G₀.algPointsPullbackEquiv_equivariant hc₀ G hc a ha hmul Kbar σ (ePic z))
  let I := Submonoid.powers n
  have hI (m : I) : IsUnit ((m.1 : ℕ) : H) := by
    obtain ⟨b, hb⟩ := m.property
    rw [← hb]
    change IsUnit (((n : ℕ) ^ b : ℕ) : H)
    rw [Nat.cast_pow]
    exact hnunit.pow b
  obtain ⟨σ, hroots, hsep⟩ :=
    exists_normalLocal_picard_weight_separation_with_roots H K Kbar G₀ hc₀ F hfg e he I hI
  let P := eModel.toAddMonoidHom
  let Fσ : G₀.AlgPoints hc₀ Kbar →+ G₀.AlgPoints hc₀ Kbar :=
    RelativeGroupLaw.AlgPoints.map (σ.restrictScalars H).toAlgHom
  let Φ : (primeToRootsSystem Kbar Kbar).inverseLimit →*
      Multiplicative (FullTateModule (G₀.AlgPoints hc₀ Kbar)) :=
    (FullTateModule.mapHom P).toMonoidHom.comp φ
  have hΦ (u : (primeToRootsSystem Kbar Kbar).inverseLimit) :
      Φ (primeToRootsCoefficientMap Kbar Kbar σ.toRingHom u) =
        Multiplicative.ofAdd (FullTateModule.map Fσ (Multiplicative.toAdd (Φ u))) := by
    apply Multiplicative.toAdd.injective
    apply FullTateModule.ext
    intro m
    have h := congrArg
      (fun z => P (FullTateModule.evaluation (G.AlgPoints hc Kbar) m
        (Multiplicative.toAdd z))) (hφ σ u)
    exact h.trans
      (G₀.algPointsPullbackEquiv_equivariant hc₀ G hc a ha hmul Kbar σ _)
  let x := FullTateModule.restrict (G₀.AlgPoints hc₀ Kbar) I (Multiplicative.toAdd (Φ t))
  have hx : x = 0 := by
    apply hsep x
    intro m
    apply Subtype.ext
    exact cyclotomicHom_coefficient_scalar_coordinate Φ m.1
      (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr m.1.ne_zero))
      σ.toRingHom Fσ (Nat.card (IsLocalRing.ResidueField H)) (hroots m) hΦ t
  have hmem : n ∈ I := ⟨1, pow_one n⟩
  have hz := congrArg
    (RestrictedTateModule.evaluation (G₀.AlgPoints hc₀ Kbar) I ⟨n, hmem⟩) hx
  apply eModel.injective
  exact hz.trans eModel.map_zero.symm

end AnabelianGeometry.WeightFiltration
