/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_CurveModel_exists_curveModel_iso_ffEquiv_symm_germToFunctionField_eq_of_algEquiv.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Models.Ramification.OpenBoundary
import Nyll.AlgebraicCurves.Models.FunctionFields.FieldReparametrization
import Nyll.AlgebraicCurves.Places.Rational.Basic
import Nyll.AnabelianGeometry.WeightFiltration.GenericPlaceInertiaRingEquiv
import Nyll.AnabelianGeometry.WeightFiltration.BoundaryInertiaEmbedding
import Nyll.AnabelianGeometry.CuspidalInertia.BoundaryInertiaCentralizer

/-! # The original roots centralizer in a field chart

The same-C constructor is provided by the upstream curve-model owner
AlgebraicCurves.Models.FieldReparametrization. All inertia comparison uses the
same ambient field and Q.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open CategoryTheory.PreGaloisCategory AlgebraicGeometry.FiniteEtale
open SchemeTheory EtaleFundamentalGroups.Inertia


namespace AnabelianGeometry.WeightFiltration
attribute [local instance] placeBaseAmbientAlgebra placeBaseAmbientTower
  placeConstantAmbientTower

/-- Source inertia in an arbitrary actual field chart has the already proved
literal-function-field centralizer. The point, ambient field, and prime remain
fixed throughout; the new prime is explicitly the normalization comap. -/
theorem fieldChart_boundaryInertia_centralizer_eq
    {κ F : Type} [Field κ] [CharZero κ] [IsAlgClosed κ]
    [Field F] [Algebra κ F]
    {U : Scheme} [IsIntegral U] [IsNormalIntegral U]
    [IsLocallyNoetherian U] [ConnectedSpace U] [CompactSpace U]
    [Algebra κ U.functionField] [Algebra F U.functionField]
    [IsScalarTower κ F U.functionField]
    {Ω : Type} [Field Ω] [Algebra U.functionField Ω] [Algebra F Ω]
    [IsScalarTower F U.functionField Ω]
    [IsSepClosure U.functionField Ω] [IsSepClosure F Ω] [IsSepClosed Ω]
    [Algebra κ Ω] [IsScalarTower κ U.functionField Ω]
    (M : CurveModel κ F)
    (j : U ⟶ M.C) [hjOpen : IsOpenImmersion j]
    [hjQC : QuasiCompact j] [hjQS : QuasiSeparated j]
    (hj : DenseRange j)
    (hfield : algebraMap F U.functionField =
      (j.functionFieldMap hj).comp M.ffEquiv.toRingHom)
    (hthree : 3 ≤ Nat.card (M.openBoundaryPlaces j))
    (v : M.openBoundaryPlaces j)
    [Algebra v.val.toValuationSubring Ω]
    [IsScalarTower v.val.toValuationSubring F Ω]
    (Q : Ideal (normalizationCommAlgCat v.val.toValuationSubring Ω)) [hQ : Q.IsMaximal]
    {x : π₁ᵉᵗ(U.genericExtensionMorphism Ω)}
    (hx : x ∈ genericPlaceInertia U v.val Q) (hx1 : x ≠ 1) :
    Subgroup.centralizer ({x} : Set (π₁ᵉᵗ(U.genericExtensionMorphism Ω))) =
      genericPlaceInertia U v.val Q := by
  classical
  let er : F ≃+* U.functionField :=
    M.ffEquiv.trans j.functionFieldRingEquivOfIsOpenImmersion
  have her (a : F) : er a = algebraMap F U.functionField a :=
    (DFunLike.congr_fun hfield a).symm
  let e : F ≃ₐ[κ] U.functionField :=
    { er with
      commutes' := by
        intro a
        exact (her (algebraMap κ F a)).trans
          (IsScalarTower.algebraMap_apply κ F U.functionField a).symm }
  let N := M.reparametrizeField e
  let E := M.reparametrizeFieldBoundaryEquiv e j
  let w : N.openBoundaryPlaces j := E v
  have hbase : algebraMap U.functionField U.functionField =
      (j.functionFieldMap hj).comp N.ffEquiv.toRingHom := by
    ext z
    change z = j.functionFieldMap hj (M.ffEquiv (e.symm z))
    exact (e.apply_symm_apply z).symm
  have hthree' : 3 ≤ Nat.card (N.openBoundaryPlaces j) := by
    rw [← Nat.card_congr E]
    exact hthree
  let : IsCurveOver κ U.functionField :=
    AlgebraicCurve.isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
      N.toBase N.ffEquiv N.ffEquiv_algebraMap
  let eV : v.val.toValuationSubring ≃+* w.val.toValuationSubring :=
    Place.congrValuationSubringEquiv e.toRingEquiv e.commutes v.val
  let : Algebra v.val.toValuationSubring w.val.toValuationSubring :=
    eV.toRingHom.toAlgebra
  let : IsScalarTower v.val.toValuationSubring w.val.toValuationSubring Ω := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    calc
      algebraMap v.val.toValuationSubring Ω a =
          algebraMap F Ω (a : F) :=
        IsScalarTower.algebraMap_apply v.val.toValuationSubring F Ω a
      _ = algebraMap U.functionField Ω (algebraMap F U.functionField (a : F)) :=
        IsScalarTower.algebraMap_apply F U.functionField Ω (a : F)
      _ = algebraMap U.functionField Ω (e (a : F)) :=
        congrArg (algebraMap U.functionField Ω) (her (a : F)).symm
      _ = algebraMap w.val.toValuationSubring Ω (eV a) :=
        (IsScalarTower.algebraMap_apply w.val.toValuationSubring U.functionField Ω
          (eV a)).symm
  let : Algebra.IsIntegral v.val.toValuationSubring w.val.toValuationSubring := by
    refine ⟨fun b => ?_⟩
    obtain ⟨a, rfl⟩ := eV.surjective b
    exact isIntegral_algebraMap
  let eN : normalizationCommAlgCat w.val.toValuationSubring Ω ≃+*
      normalizationCommAlgCat v.val.toValuationSubring Ω :=
    normalizationIntegralBaseRingEquiv
      v.val.toValuationSubring w.val.toValuationSubring Ω
  let Q' : Ideal (normalizationCommAlgCat w.val.toValuationSubring Ω) :=
    Q.comap eN.toRingHom
  let : Q'.IsMaximal := by
    let : Q.IsMaximal := hQ
    exact Ideal.comap_isMaximal_of_surjective eN.toRingHom eN.surjective
  have hI : genericPlaceInertia U v.val Q = genericPlaceInertia U w.val Q' := by
    exact genericPlaceInertia_eq_of_valuationRingEquiv U v.val w.val eV rfl Q
  -- Choose other primes only to satisfy the existing family's interface.
  -- Function.update retains precisely Q' at the chosen boundary place w.
  choose Q₀ hQ₀ using fun r : N.openBoundaryPlaces j => by
    let : Nontrivial (normalizationCommAlgCat r.val.toValuationSubring Ω) :=
      (inferInstance : Nontrivial (integralClosure r.val.toValuationSubring Ω))
    exact Ideal.exists_maximal (normalizationCommAlgCat r.val.toValuationSubring Ω)
  let Qfamily : ∀ r : N.openBoundaryPlaces j,
      Ideal (normalizationCommAlgCat r.val.toValuationSubring Ω) :=
    Function.update Q₀ w Q'
  let : ∀ r, (Qfamily r).IsMaximal := by
    intro r
    by_cases hr : r = w
    · subst r
      simpa only [Qfamily, Function.update_self] using (inferInstance : Q'.IsMaximal)
    · simpa only [Qfamily, Function.update_of_ne hr] using hQ₀ r
  have hw : Qfamily w = Q' := Function.update_self w Q' Q₀
  have hx' : x ∈ genericPlaceInertia U w.val (Qfamily w) := by
    rw [hw, ← hI]
    exact hx
  let jN : U ⟶ N.C := j
  let : IsOpenImmersion jN := hjOpen
  let : QuasiCompact jN := hjQC
  let : QuasiSeparated jN := hjQS
  have hc := boundaryInertia_centralizer_eq N jN hj hbase hthree' Qfamily w hx' hx1
  rw [hw, ← hI] at hc
  exact hc

/-- The centralizer input for transported-roots recognition, now proved for
the original roots map in its actual F-chart rather than assumed. -/
theorem fieldChart_boundaryPlaceInertiaLift_range_centralizer_eq
    {κ F : Type} [Field κ] [CharZero κ] [IsAlgClosed κ]
    [Field F] [Algebra κ F] [IsCurveOver κ F]
    {U : Scheme} [IsIntegral U] [IsNormalIntegral U]
    [IsLocallyNoetherian U] [ConnectedSpace U] [CompactSpace U]
    [Algebra κ U.functionField] [Algebra F U.functionField]
    [IsScalarTower κ F U.functionField]
    {Ω : Type} [Field Ω] [Algebra U.functionField Ω] [Algebra F Ω]
    [IsScalarTower F U.functionField Ω]
    [IsSepClosure U.functionField Ω] [IsSepClosure F Ω] [IsSepClosed Ω]
    [Algebra κ Ω] [IsScalarTower κ U.functionField Ω]
    (M : CurveModel κ F)
    (j : U ⟶ M.C) [IsOpenImmersion j] [QuasiCompact j] [QuasiSeparated j]
    (hj : DenseRange j)
    (hfield : algebraMap F U.functionField =
      (j.functionFieldMap hj).comp M.ffEquiv.toRingHom)
    [∀ p : M.openBoundaryPlaces j, Algebra p.val.toValuationSubring Ω]
    [∀ p : M.openBoundaryPlaces j, IsScalarTower p.val.toValuationSubring F Ω]
    [∀ p : M.openBoundaryPlaces j, IsScalarTower κ p.val.toValuationSubring Ω]
    [Finite (M.openBoundaryPlaces j)]
    (hthree : 3 ≤ Nat.card (M.openBoundaryPlaces j))
    (Qfamily : ∀ p : M.openBoundaryPlaces j,
      Ideal (normalizationCommAlgCat p.val.toValuationSubring Ω))
    [∀ p, (Qfamily p).IsMaximal]
    (v : M.openBoundaryPlaces j)
    {x : π₁ᵉᵗ(U.genericExtensionMorphism Ω)}
    (hx : x ∈ (boundaryPlaceInertiaLift M j hj hfield Qfamily v).toMonoidHom.range)
    (hx1 : x ≠ 1) :
    Subgroup.centralizer ({x} : Set (π₁ᵉᵗ(U.genericExtensionMorphism Ω))) =
      (boundaryPlaceInertiaLift M j hj hfield Qfamily v).toMonoidHom.range := by
  rw [boundaryPlaceInertiaLift_range] at hx ⊢
  exact fieldChart_boundaryInertia_centralizer_eq M j hj hfield hthree v
    (Qfamily v) hx hx1

end AnabelianGeometry.WeightFiltration
