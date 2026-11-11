/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_exists_smoothProperCurve_hom_comp_eq_of_ringKrullDim_eq_one.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.AlgebraicCurves.Geometry.Schemes.FunctionFields.PartialMapMemDomainToRationalMap
public import Nyll.AlgebraicCurves.Geometry.Schemes.Smooth.ValuationRingStalkSmoothOfRelativeDimensionOne
public import Nyll.SchemeTheory.RingTheory.Dimension.IdealHeightAddKrullDimensionQuotientEqKrullDimension
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.AlgebraicGeometry.Birational.RationalMap
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.NoetherNormalization
public import Nyll.AlgebraicCurves.Models.Construction.Basic
public import Nyll.AlgebraicCurves.Models.Construction.BasicPerfectField
public import Nyll.SchemeTheory.RingTheory.FieldExtensions.RingHomFiniteDimensionalAdjoinRange
public import Nyll.SchemeTheory.FunctionFields.StructureMorphism
public import Nyll.SchemeTheory.RingTheory.FieldExtensions.DimensionOneFractionField

/-!
# exists smooth Proper Curve hom comp eq of ring Krull Dim eq one
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.Geometry.Curves.Proofs.ProperCurveFactorization
attribute [-instance] AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase
  AlgebraicCurve.CurveModel.isFractionRing_overlap
  AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued
  AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued
  AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued
  AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing
  AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField
  AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU
  AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf
  AlgebraicCurve.CurveModel.isOpenImmersion_ιInf
  AlgebraicCurve.CurveModel.algebra_overlap_functionField
  AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin
  AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure
  AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime
  AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing
  AlgebraicCurve.CurveModel.isNoetherianRing_chartRing
  AlgebraicCurve.CurveModel.isScalarTower_base_adjoin
  AlgebraicCurve.CurveModel.isScalarTower_adjoin
  AlgebraicCurve.CurveModel.chartRing_finitePresentation
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.CurveModel.ιInf_gluedToBase
  AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces
  AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

universe u v

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

namespace P2mNormExt

section Spread

variable {X Y S : Scheme.{u}}

theorem fromSpecStalkOfMem_eq_of_specializes (U : X.Opens) {ξ x : X} (h : ξ ⤳ x)
    (hx : x ∈ U) (hξ : ξ ∈ U) :
    U.fromSpecStalkOfMem ξ hξ =
      Spec.map (X.presheaf.stalkSpecializes h) ≫ U.fromSpecStalkOfMem x hx :=
  open AlgebraicCurves.Geometry.Schemes.Proofs in
  open Scheme_PartialMap_mem_domain_toRationalMap_of_valuationRing_stalk in
  ValuativePartialMap.fromSpecStalkOfMem_eq_of_specializes U h hx hξ

theorem partialMap_fromSpecStalkOfMem_eq_of_specializes (f : X.PartialMap Y) {ξ x : X}
    (h : ξ ⤳ x) (hx : x ∈ f.domain) (hξ : ξ ∈ f.domain) :
    f.fromSpecStalkOfMem hξ =
      Spec.map (X.presheaf.stalkSpecializes h) ≫ f.fromSpecStalkOfMem hx :=
  open AlgebraicCurves.Geometry.Schemes.Proofs in
  open Scheme_PartialMap_mem_domain_toRationalMap_of_valuationRing_stalk in
  ValuativePartialMap.partialMap_fromSpecStalkOfMem_eq_of_specializes f h hx hξ

theorem partialMap_fromFunctionField_eq_of_mem [IrreducibleSpace X] (f : X.PartialMap Y)
    {x : X} (hx : x ∈ f.domain) :
    f.fromFunctionField =
      Spec.map (X.presheaf.stalkSpecializes (genericPoint_specializes x)) ≫
        f.fromSpecStalkOfMem hx :=
  open AlgebraicCurves.Geometry.Schemes.Proofs in
  open Scheme_PartialMap_mem_domain_toRationalMap_of_valuationRing_stalk in
  ValuativePartialMap.partialMap_fromFunctionField_eq_of_mem f hx

theorem ofHom_algebraMap_stalk_functionField [IrreducibleSpace X] (x : X) :
    CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField) =
      X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial) :=
  open AlgebraicCurves.Geometry.Schemes.Proofs in
  open Scheme_PartialMap_mem_domain_toRationalMap_of_valuationRing_stalk in
  ValuativePartialMap.ofHom_algebraMap_stalk_functionField x

theorem mem_domain_of_valuationRing (sX : X ⟶ S) (sY : Y ⟶ S) [IsIntegral X]
    [LocallyOfFiniteType sY] (hY : ValuativeCriterion.Existence sY) (f : X.PartialMap Y)
    (hf : f.hom ≫ sY = f.domain.ι ≫ sX) (x : X) (hx : ValuationRing (X.presheaf.stalk x)) :
    x ∈ f.toRationalMap.domain :=
  _root_.AlgebraicGeometry.Scheme.PartialMap.mem_domain_toRationalMap_of_valuationRing_stalk
    sX sY hY f hf x hx

end Spread

section LocalRings

theorem valuationRing_of_surjective {A B : Type*} [CommRing A] [IsDomain A]
    [ValuationRing A]
    [CommRing B] [IsDomain B] (f : A →+* B) (hf : Function.Surjective f) : ValuationRing B :=
  open AlgebraicCurves.Geometry.Schemes.Proofs in
  open valuationRing_stalk_of_smoothOfRelativeDimension_one in
  SmoothCurveStalk.valuationRing_of_surjective f hf

theorem valuationRing_localization_atPrime {R B : Type*} [CommRing R] [CommRing B]
    [Algebra R B] [IsDomain B] [IsNoetherianRing B] [Algebra.EssFiniteType R B]
    (q : Ideal B) [q.IsPrime] [Algebra.IsUnramifiedAt R q] (hp : (q.under R).IsPrincipal) :
    ValuationRing (Localization.AtPrime q) :=
  open AlgebraicCurves.Geometry.Schemes.Proofs in
  open valuationRing_stalk_of_smoothOfRelativeDimension_one in
  SmoothCurveStalk.valuationRing_localization_atPrime q hp

theorem isPrincipalIdealRing_mvPolynomial_fin_one (K : Type*) [Field K] :
    IsPrincipalIdealRing (MvPolynomial (Fin 1) K) :=
  open AlgebraicCurves.Geometry.Schemes.Proofs in
  open valuationRing_stalk_of_smoothOfRelativeDimension_one in
  SmoothCurveStalk.isPrincipalIdealRing_mvPolynomial_fin_one K

theorem valuationRing_stalk {K : Type u} [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) [IsIntegral C] [SmoothOfRelativeDimension 1 c] (x : C) :
    ValuationRing (C.presheaf.stalk x) :=
  _root_.AlgebraicGeometry.valuationRing_stalk_of_smoothOfRelativeDimension_one c x

end LocalRings

section Extend

variable {K : Type u} [Field K]

theorem fromSpecStalk_genericPoint_comp_eq {C : Scheme.{u}} [IsIntegral C]
    (c : C ⟶ Spec (CommRingCat.of K)) :
    C.fromSpecStalk (genericPoint C) ≫ c =
      Spec.map (CommRingCat.ofHom (baseToFunctionField c)) :=
  _root_.AlgebraicCurve.fromSpecStalk_genericPoint_comp_base c

theorem isSeparated_of_over {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of K))
    [IsSeparated g] : Y.IsSeparated :=
  ⟨by rw [← terminal.comp_from g]; infer_instance⟩

theorem existence_of_isProper {Y T : Scheme.{u}} (g : Y ⟶ T) [IsProper g] :
    ValuativeCriterion.Existence g := by
  have h : IsProper g := inferInstance
  rw [IsProper.eq_valuativeCriterion] at h
  exact h.1.1.1.existence

theorem exists_hom_of_generic {C Y : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [SmoothOfRelativeDimension 1 c] (y : Y ⟶ Spec (CommRingCat.of K))
    [IsProper y] (f : Spec C.functionField ⟶ Y)
    (hf : f ≫ y = C.fromSpecStalk (genericPoint C) ≫ c) :
    ∃ ψ : C ⟶ Y, ψ ≫ y = c ∧ C.fromSpecStalk (genericPoint C) ≫ ψ = f := by
  have : Y.IsSeparated := isSeparated_of_over y
  let f₀ : C.PartialMap Y := Scheme.PartialMap.ofFromSpecStalk c y f hf
  have hf₀ : f₀.hom ≫ y = f₀.domain.ι ≫ c := Scheme.PartialMap.ofFromSpecStalk_comp _ _ _ _
  have hη : genericPoint C ∈ f₀.domain := Scheme.PartialMap.mem_domain_ofFromSpecStalk _ _ _ _
  have hf₀η : f₀.fromSpecStalkOfMem hη = f :=
    Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk _ _ _ _
  have hdom : f₀.toRationalMap.domain = ⊤ := top_unique fun x _ =>
    mem_domain_of_valuationRing c y (existence_of_isProper y) f₀ hf₀ x (valuationRing_stalk c x)
  let g := f₀.toRationalMap.toPartialMap
  let ψ : C ⟶ Y := C.topIso.inv ≫ C.homOfLE hdom.ge ≫ g.hom
  have hι : f₀.domain.ι ≫ ψ = f₀.hom := by
    have key : C.homOfLE f₀.le_domain_toRationalMap ≫ g.hom = f₀.hom :=
      f₀.toPartialMap_toRationalMap_restrict
    have hmap : f₀.domain.ι ≫ C.topIso.inv ≫ C.homOfLE hdom.ge =
        C.homOfLE f₀.le_domain_toRationalMap := by
      apply (cancel_mono g.domain.ι).mp
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun q => f₀.domain.ι ≫ q)
          ((Category.assoc _ _ _).trans
            ((congrArg (fun q => C.topIso.inv ≫ q) (C.homOfLE_ι hdom.ge)).trans
              (Scheme.toIso_inv_ι C)))).trans
          (C.homOfLE_ι f₀.le_domain_toRationalMap).symm)
    exact (Category.assoc f₀.domain.ι (C.topIso.inv ≫ C.homOfLE hdom.ge) g.hom).symm.trans
      ((congrArg (fun q : (f₀.domain : Scheme.{u}) ⟶ (g.domain : Scheme.{u}) => q ≫ g.hom)
        hmap).trans key)
  refine ⟨ψ, ?_, ?_⟩
  · have : IsDominant f₀.domain.ι :=
      ⟨by rw [DenseRange, Scheme.Opens.range_ι]; exact f₀.dense_domain⟩
    refine ext_of_isDominant f₀.domain.ι ?_
    rw [reassoc_of% hι, hf₀]
  · rw [← Scheme.Opens.fromSpecStalkOfMem_ι f₀.domain (genericPoint C) hη, Category.assoc, hι]
    exact hf₀η

end Extend

section Ticket

open _root_.AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
open Ideal_height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType.P2mDimFormula

theorem ringKrullDim_eq_of_ringHom_isIntegral_of_injective {R S : Type*} [CommRing R]
    [CommRing S] (f : R →+* S) (hint : f.IsIntegral) (hinj : Function.Injective f) :
    ringKrullDim R = ringKrullDim S :=
  _root_.RingHom.ringKrullDim_eq_of_isIntegral_of_injective f hint hinj

theorem exists_transcendental_finiteDimensional (k : Type u) (A : Type v) [Field k] [CommRing A]
    [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] (hA : ringKrullDim A = 1) :
    ∃ x : FractionRing A, Transcendental k x ∧
      FiniteDimensional (IntermediateField.adjoin k ({x} : Set (FractionRing A)))
        (FractionRing A) :=
  _root_.FractionRing.exists_transcendental_finiteDimensional k A hA

end Ticket

section Main

theorem main {k : Type u} [Field k] [IsAlgClosed k] {Y : Scheme.{u}}
    (y : Y ⟶ Spec (CommRingCat.of k))
    [IsProper y] (A : Type u) [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    (hA : ringKrullDim A = 1) (φ : Spec (CommRingCat.of A) ⟶ Y)
    (hφ : φ ≫ y = Spec.map (CommRingCat.ofHom (algebraMap k A))) :
    ∃ (C : Scheme.{u}) (c : C ⟶ Spec (CommRingCat.of k)) (_ : IsProper c)
      (_ : SmoothOfRelativeDimension 1 c) (_ : IsIntegral C) (ψ : C ⟶ Y), ψ ≫ y = c ∧
      ∀ a : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A),
        a ≫ Spec.map (CommRingCat.ofHom (algebraMap k A)) = 𝟙 _ →
        ∃ p : Spec (CommRingCat.of k) ⟶ C, p ≫ c = 𝟙 _ ∧ p ≫ ψ = a ≫ φ := by
  let L := FractionRing A
  obtain ⟨M⟩ : Nonempty (CurveModel k L) :=
    CurveModel.nonempty_of_perfectField k L (exists_transcendental_finiteDimensional k A hA)
  let ρ : A →+* M.C.functionField := M.ffEquiv.toRingHom.comp (algebraMap A L)
  have hρ : Function.Injective ρ :=
    M.ffEquiv.injective.comp (IsFractionRing.injective A L)
  let f₀ : Spec M.C.functionField ⟶ Y := Spec.map (CommRingCat.ofHom ρ) ≫ φ
  have hf₀ : f₀ ≫ y = M.C.fromSpecStalk (genericPoint M.C) ≫ M.toBase := by
    rw [fromSpecStalk_genericPoint_comp_eq]
    have hρk : CommRingCat.ofHom (algebraMap k A) ≫ CommRingCat.ofHom ρ =
        CommRingCat.ofHom (baseToFunctionField M.toBase) := by
      ext a
      change M.ffEquiv (algebraMap A L (algebraMap k A a)) = baseToFunctionField M.toBase a
      rw [← IsScalarTower.algebraMap_apply, M.ffEquiv_algebraMap]
    exact (Category.assoc (Spec.map (CommRingCat.ofHom ρ)) φ y).trans
      ((congrArg (fun q => Spec.map (CommRingCat.ofHom ρ) ≫ q) hφ).trans
        ((Spec.map_comp (CommRingCat.ofHom (algebraMap k A))
          (CommRingCat.ofHom ρ)).symm.trans (congrArg Spec.map hρk)))
  obtain ⟨ψ, hψy, hψη⟩ := exists_hom_of_generic M.toBase y f₀ hf₀
  refine ⟨M.C, M.toBase, inferInstance, inferInstance, inferInstance, ψ, hψy, ?_⟩
  intro a ha
  have : UniversallyClosed ψ := by
    have : UniversallyClosed (ψ ≫ y) := by rw [hψy]; infer_instance
    exact UniversallyClosed.of_comp_of_isSeparated ψ y
  have : JacobsonSpace M.C := LocallyOfFiniteType.jacobsonSpace M.toBase
  let pt : Spec M.C.functionField := IsLocalRing.closedPoint M.C.functionField
  let ηA : Spec (CommRingCat.of A) := Spec.map (CommRingCat.ofHom ρ) pt
  let 𝔪 : Spec (CommRingCat.of A) := a (IsLocalRing.closedPoint k)
  have hgen : ψ (genericPoint M.C) = φ ηA := by
    have h1 : (M.C.fromSpecStalk (genericPoint M.C) ≫ ψ) pt = f₀ pt := by rw [hψη]
    rw [Scheme.Hom.comp_apply, Scheme.fromSpecStalk_closedPoint] at h1
    rw [h1]
    rfl
  have hsp : ηA ⤳ 𝔪 := by
    refine (PrimeSpectrum.le_iff_specializes (ηA : PrimeSpectrum A) 𝔪).mp ?_
    intro r hr
    have hr' : ρ r ∈ pt.asIdeal := hr
    have hr0 : ρ r = 0 := by
      by_contra hne
      exact (IsLocalRing.mem_maximalIdeal _).mp hr' (isUnit_iff_ne_zero.mpr hne)
    have : r = 0 := hρ (by rw [hr0, map_zero])
    rw [this]
    exact zero_mem _
  have hφy : (a ≫ φ) ≫ y = 𝟙 _ := by rw [Category.assoc, hφ, ha]
  have hclosed : IsClosed ({φ 𝔪} : Set Y) := by
    have h := (pointEquivClosedPoint y ⟨a ≫ φ, hφy⟩).2
    exact h
  have hmem : φ 𝔪 ∈ Set.range ψ := by
    have h1 : φ ηA ⤳ φ 𝔪 := hsp.map φ.continuous
    rw [← hgen] at h1
    exact h1.mem_closed ψ.isClosedMap.isClosed_range ⟨_, rfl⟩
  obtain ⟨x, hx⟩ := hmem
  obtain ⟨z, hxz, hz⟩ := nonempty_inter_closedPoints (Z := closure ({x} : Set M.C))
    ⟨x, subset_closure rfl⟩ isClosed_closure.isLocallyClosed
  have hxz' : x ⤳ z := specializes_iff_mem_closure.mpr hxz
  have hψz : ψ z = φ 𝔪 := by
    have h1 : ψ x ⤳ ψ z := hxz'.map ψ.continuous
    rw [hx] at h1
    exact h1.mem_closed hclosed rfl
  have hz' : IsClosed ({z} : Set M.C) := hz
  refine ⟨pointOfClosedPoint M.toBase z hz', pointOfClosedPoint_comp _ _ _, ?_⟩
  refine ext_of_apply_closedPoint_eq y ?_ hφy ?_
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun q => pointOfClosedPoint M.toBase z hz' ≫ q) hψy).trans
        (pointOfClosedPoint_comp M.toBase z hz'))
  · exact (Scheme.Hom.comp_apply (pointOfClosedPoint M.toBase z hz') ψ
      (IsLocalRing.closedPoint k)).trans
      ((congrArg ψ (pointOfClosedPoint_apply M.toBase z hz' (IsLocalRing.closedPoint k))).trans
        (hψz.trans (Scheme.Hom.comp_apply a φ (IsLocalRing.closedPoint k)).symm))

end Main

end P2mNormExt

end

open CategoryTheory AlgebraicGeometry in
theorem _root_.AlgebraicGeometry.exists_smoothProperCurve_hom_comp_eq_of_ringKrullDim_eq_one
    {k : Type u} [Field k] [IsAlgClosed k] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of k))
    [IsProper y] (A : Type u) [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    (hA : ringKrullDim A = 1) (φ : Spec (CommRingCat.of A) ⟶ Y)
    (hφ : φ ≫ y = Spec.map (CommRingCat.ofHom (algebraMap k A))) :
    ∃ (C : Scheme.{u}) (c : C ⟶ Spec (CommRingCat.of k)) (_ : IsProper c)
      (_ : SmoothOfRelativeDimension 1 c) (_ : IsIntegral C) (ψ : C ⟶ Y), ψ ≫ y = c ∧
      ∀ a : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A),
        a ≫ Spec.map (CommRingCat.ofHom (algebraMap k A)) = 𝟙 _ →
        ∃ p : Spec (CommRingCat.of k) ⟶ C, p ≫ c = 𝟙 _ ∧ p ≫ ψ = a ≫ φ :=
  P2mNormExt.main y A hA φ hφ
end AlgebraicCurves.Geometry.Curves.Proofs.ProperCurveFactorization
end ProofImplementation

attribute [-instance] AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral
  AlgebraicCurve.CurveModel.smooth
  AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv
  AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv
  AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv
  AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase
  AlgebraicCurve.CurveModel.isFractionRing_overlap
  AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued
  AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued
  AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued
  AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing
  AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField
  AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU
  AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf
  AlgebraicCurve.CurveModel.isOpenImmersion_ιInf
  AlgebraicCurve.CurveModel.algebra_overlap_functionField
  AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin
  AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure
  AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime
  AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing
  AlgebraicCurve.CurveModel.isNoetherianRing_chartRing
  AlgebraicCurve.CurveModel.isScalarTower_base_adjoin
  AlgebraicCurve.CurveModel.isScalarTower_adjoin
  AlgebraicCurve.CurveModel.chartRing_finitePresentation
attribute [-instance]
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec
  AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single
  AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring
  AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap
  AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply
  AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero
  AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add
  AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring
  AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.ι₀_gluedToBase
  AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
