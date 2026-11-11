/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_exists_smoothProperCurve_opens_hom_comp_eq_of_ringKrullDim_eq_one.lean
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
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.Unramified.LocalRing
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.Valuation.LocalSubring
public import Mathlib.RingTheory.NoetherNormalization
public import Mathlib.Tactic.Algebraize
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.RingHom.StandardSmooth
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.Order.KrullDimension
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Nyll.AlgebraicCurves.Models.Construction.Basic
public import Nyll.AlgebraicCurves.Models.Construction.BasicPerfectField
public import Nyll.SchemeTheory.RingTheory.FieldExtensions.RingHomFiniteDimensionalAdjoinRange
public import Nyll.SchemeTheory.FunctionFields.StructureMorphism
public import Nyll.SchemeTheory.RingTheory.FieldExtensions.DimensionOneFractionField

/-!
# Factoring closed points through an open part of a smooth proper curve
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.Geometry.Curves.Proofs.OpenCurveFactorization
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

namespace P2mNormOpen

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

theorem fromSpecStalk_comp_eq {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K)) (z : C) :
    C.fromSpecStalk z ≫ c =
      Spec.map (CommRingCat.ofHom ((C.presheaf.germ ⊤ z trivial).hom.comp
        (c.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom))) := by
  refine ext_of_isAffine ?_
  set θ : K →+* C.presheaf.stalk z := (C.presheaf.germ ⊤ z trivial).hom.comp
    (c.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)
  have h1 : (Spec.map (CommRingCat.ofHom θ)).appTop =
      (Scheme.ΓSpecIso (CommRingCat.of K)).hom ≫ CommRingCat.ofHom θ ≫
        (Scheme.ΓSpecIso (C.presheaf.stalk z)).inv := by
    rw [← Iso.inv_comp_eq]
    exact (Scheme.ΓSpecIso_inv_naturality _).symm
  have h2 : CommRingCat.ofHom θ =
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ c.appTop ≫ C.presheaf.germ ⊤ z trivial := by
    ext a
    rfl
  have h3 : (Spec (C.presheaf.stalk z)).presheaf.map
      (homOfLE (le_top : (⊤ : (Spec (C.presheaf.stalk z)).Opens) ≤ ⊤)).op = 𝟙 _ := by
    rw [show (homOfLE _).op = 𝟙 (Opposite.op ⊤) from Subsingleton.elim _ _]
    exact CategoryTheory.Functor.map_id _ _
  rw [Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop, h3, Category.comp_id, h1, h2]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

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

section Centre

variable {k : Type u} [Field k] {L : Type u} [Field L] [Algebra k L]

theorem exists_place_le_and_subset_nonunits (M : CurveModel k L) (A : Type u) [CommRing A]
    [Algebra k A] [Algebra A L] [IsScalarTower k A L]
    (hinj : Function.Injective (algebraMap A L)) (𝔪 : Ideal A) [h𝔪 : 𝔪.IsMaximal] (h𝔪0 : 𝔪 ≠ ⊥) :
    ∃ P : Place k L, (∀ a : A, algebraMap A L a ∈ P.toValuationSubring) ∧
      ∀ m ∈ 𝔪, algebraMap A L m ∈ P.toValuationSubring.nonunits := by
  classical
  set ι := algebraMap A L with hι
  let A' : Subring L := ι.range
  let e : A ≃+* A' := RingEquiv.ofBijective ι.rangeRestrict
    ⟨fun x y h => hinj (congrArg Subtype.val h), ι.rangeRestrict_surjective⟩
  let I : Ideal A' := 𝔪.comap e.symm.toRingHom
  have hI : I ≠ ⊤ := Ideal.comap_ne_top _ h𝔪.ne_top
  obtain ⟨V, hAV, hIV⟩ := Ideal.image_subset_nonunits_valuationSubring I hI
  have hAmem : ∀ a : A, ι a ∈ V := fun a => hAV ⟨a, rfl⟩
  have hmnon : ∀ m ∈ 𝔪, ι m ∈ V.nonunits := by
    intro m hm
    refine hIV ⟨e m, ?_, rfl⟩
    change e.symm.toRingHom (e m) ∈ 𝔪
    simpa using hm
  have hkV : ∀ a : k, algebraMap k L a ∈ V := fun a => by
    rw [IsScalarTower.algebraMap_apply k A L]; exact hAmem _
  obtain ⟨m, hm𝔪, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔪0
  have hVtop : V ≠ ⊤ := by
    intro hV
    have h1 : ι m ∈ V.nonunits := hmnon m hm𝔪
    rw [ValuationSubring.mem_nonunits_iff_or] at h1
    rcases h1 with h1 | h1
    · exact hm0 (hinj (by rw [h1, map_zero]))
    · exact h1 (hV ▸ ValuationSubring.mem_top _)
  let C := M.C
  let kV : k →+* V := (algebraMap k L).codRestrict V.toSubring hkV
  let i₂ : Spec (CommRingCat.of V) ⟶ Spec (CommRingCat.of k) := Spec.map (CommRingCat.ofHom kV)
  let eKL : C.presheaf.stalk (genericPoint C) ⟶ CommRingCat.of L :=
    CommRingCat.ofHom (M.ffEquiv.symm : C.functionField →+* L)
  let i₁ : Spec (CommRingCat.of L) ⟶ C := Spec.map eKL ≫ C.fromSpecStalk (genericPoint C)
  have hsq : i₁ ≫ M.toBase = Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ i₂ := by
    simp only [i₁, i₂, Category.assoc, fromSpecStalk_comp_eq, ← Spec.map_comp]
    congr 1
    ext a
    change M.ffEquiv.symm (baseToFunctionField M.toBase a) = algebraMap k L a
    rw [← M.ffEquiv_algebraMap, RingEquiv.symm_apply_apply]
  obtain ⟨l, hl₁, hl₂⟩ := (existence_of_isProper M.toBase
    { R := V, K := L, i₁ := i₁, i₂ := i₂, commSq := ⟨hsq⟩ }).exists_lift
  let θ := Scheme.stalkClosedPointTo l
  have : IsLocalHom θ.hom := inferInstanceAs (IsLocalHom (Scheme.stalkClosedPointTo l).hom)
  have hθl : Spec.map θ ≫ C.fromSpecStalk _ = l := Scheme.Spec_stalkClosedPointTo_fromSpecStalk l
  let g : C.presheaf.stalk (l (IsLocalRing.closedPoint V)) →+* L :=
    (M.ffEquiv.symm : C.functionField →+* L).comp
      (algebraMap (C.presheaf.stalk (l (IsLocalRing.closedPoint V))) C.functionField)
  have hg : Function.Injective g :=
    M.ffEquiv.symm.injective.comp
      (IsFractionRing.injective (C.presheaf.stalk (l (IsLocalRing.closedPoint V))) C.functionField)
  have hcompat : ∀ s, algebraMap V L (θ.hom s) = g s := by
    have key : θ ≫ CommRingCat.ofHom (algebraMap V L) =
        C.presheaf.stalkSpecializes (genericPoint_specializes (l (IsLocalRing.closedPoint V))) ≫
          eKL := by
      apply Spec.map_injective
      rw [← cancel_mono (C.fromSpecStalk (l (IsLocalRing.closedPoint V))), Spec.map_comp,
        Category.assoc, hθl, hl₁, Spec.map_comp, Category.assoc,
        Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    intro s
    have h1 := congrArg (fun φ : C.presheaf.stalk _ ⟶ CommRingCat.of L => φ.hom s) key
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at h1
    rw [h1]
    change M.ffEquiv.symm ((C.presheaf.stalkSpecializes
      (genericPoint_specializes (l (IsLocalRing.closedPoint V)))).hom s) = g s
    rw [← ofHom_algebraMap_stalk_functionField]
    rfl
  have hvz : ValuationRing (C.presheaf.stalk (l (IsLocalRing.closedPoint V))) :=
    valuationRing_stalk M.toBase _
  let W : ValuationSubring L :=
    { toSubring := g.range
      mem_or_inv_mem' := fun x => by
        rcases ValuationRing.isInteger_or_isInteger
          (C.presheaf.stalk (l (IsLocalRing.closedPoint V))) (M.ffEquiv x) with ⟨s, hs⟩ | ⟨s, hs⟩
        · refine Or.inl ⟨s, ?_⟩
          change M.ffEquiv.symm (algebraMap _ _ s) = x
          rw [hs, RingEquiv.symm_apply_apply]
        · refine Or.inr ⟨s, ?_⟩
          change M.ffEquiv.symm (algebraMap _ _ s) = x⁻¹
          rw [hs, ← map_inv₀, RingEquiv.symm_apply_apply] }
  have hsub : W.toSubring ≤ V.toSubring := by
    rintro _ ⟨s, rfl⟩
    rw [← hcompat]
    exact (θ.hom s).2
  have hWV : W.toLocalSubring ≤ V.toLocalSubring := by
    refine ⟨hsub, ⟨?_⟩⟩
    intro a hu
    obtain ⟨s, hs⟩ : (a : L) ∈ g.range := a.2
    have e0 : Subring.inclusion hsub a = θ.hom s := by
      apply Subtype.ext
      change (a : L) = algebraMap V L (θ.hom s)
      rw [hcompat, hs]
    have hu0 : IsUnit (θ.hom s) := by
      have hu' := e0 ▸ hu
      exact hu'
    have hs' : IsUnit s := (isUnit_map_iff θ.hom s).mp hu0
    rw [show a = g.rangeRestrict s from Subtype.ext hs.symm]
    exact hs'.map _
  have hVW : V.toLocalSubring ≤ W.toLocalSubring := W.isMax_toLocalSubring hWV
  have hVsub : ∀ v : V, (v : L) ∈ g.range := fun v => hVW.1 v.2
  have hθbij : Function.Bijective θ.hom := by
    constructor
    · intro s t hst
      apply hg
      rw [← hcompat, ← hcompat, hst]
    · intro v
      obtain ⟨s, hs⟩ := hVsub v
      exact ⟨s, Subtype.ext ((hcompat s).trans hs)⟩
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian M.toBase
  let eθ : C.presheaf.stalk (l (IsLocalRing.closedPoint V)) ≃+* V :=
    RingEquiv.ofBijective (θ.hom : C.presheaf.stalk (l (IsLocalRing.closedPoint V)) →+* V) hθbij
  have : IsNoetherianRing V := isNoetherianRing_of_ringEquiv _ eθ
  have hPIR : IsPrincipalIdealRing V :=
    IsPrincipalIdealRing.of_isNoetherianRing_of_isBezout (R := V)
  exact ⟨⟨V, hkV, hVtop, hPIR⟩, hAmem, hmnon⟩

end Centre

section Main

theorem isClosed_singleton_opens {X : Scheme.{u}} (U : X.Opens) (x : X) (hx : x ∈ U)
    (hcl : IsClosed ({x} : Set X)) : IsClosed ({(⟨x, hx⟩ : U)} : Set U) := by
  have : ({(⟨x, hx⟩ : U)} : Set U) = U.ι ⁻¹' {x} := by
    ext u
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    constructor
    · rintro rfl; rfl
    · intro h; exact Subtype.ext h
  rw [this]
  exact hcl.preimage U.ι.continuous

theorem main {k : Type u} [Field k] [IsAlgClosed k] {Y : Scheme.{u}}
    (y : Y ⟶ Spec (CommRingCat.of k))
    [IsSeparated y] [LocallyOfFiniteType y] (A : Type u) [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] (hA : ringKrullDim A = 1) (φ : Spec (CommRingCat.of A) ⟶ Y)
    (hφ : φ ≫ y = Spec.map (CommRingCat.ofHom (algebraMap k A))) :
    ∃ (C : Scheme.{u}) (c : C ⟶ Spec (CommRingCat.of k)) (_ : IsProper c)
      (_ : SmoothOfRelativeDimension 1 c) (_ : IsIntegral C) (U : C.Opens)
      (ψ : (U : Scheme.{u}) ⟶ Y), ψ ≫ y = U.ι ≫ c ∧
      ∀ a : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A),
        a ≫ Spec.map (CommRingCat.ofHom (algebraMap k A)) = 𝟙 _ →
        ∃ p : Spec (CommRingCat.of k) ⟶ (U : Scheme.{u}), p ≫ U.ι ≫ c = 𝟙 _ ∧ p ≫ ψ = a ≫ φ := by
  classical
  let L := FractionRing A
  obtain ⟨M⟩ : Nonempty (CurveModel k L) :=
    CurveModel.nonempty_of_perfectField k L (exists_transcendental_finiteDimensional k A hA)
  have : Y.IsSeparated := isSeparated_of_over y
  let ρ : A →+* M.C.functionField := (M.ffEquiv : L →+* M.C.functionField).comp (algebraMap A L)
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
  let f₁ : M.C.PartialMap Y := Scheme.PartialMap.ofFromSpecStalk M.toBase y f₀ hf₀
  have hf₁ : f₁.hom ≫ y = f₁.domain.ι ≫ M.toBase := Scheme.PartialMap.ofFromSpecStalk_comp _ _ _ _
  have hη : genericPoint M.C ∈ f₁.domain := Scheme.PartialMap.mem_domain_ofFromSpecStalk _ _ _ _
  have hf₁η : f₁.fromSpecStalkOfMem hη = f₀ :=
    Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk _ _ _ _
  let r : M.C ⤏ Y := f₁.toRationalMap
  let U : M.C.Opens := r.toPartialMap.domain
  let ψ : (U : Scheme.{u}) ⟶ Y := r.toPartialMap.hom
  have hψ : ψ ≫ y = U.ι ≫ M.toBase := by
    have hle : f₁.domain ≤ U := f₁.le_domain_toRationalMap
    have : IsDominant (M.C.homOfLE hle) := Opens.isDominant_homOfLE f₁.dense_domain hle
    have : IsReduced (U : Scheme.{u}) := isReduced_of_isOpenImmersion U.ι
    apply ext_of_isDominant (M.C.homOfLE hle)
    have key : M.C.homOfLE hle ≫ ψ = f₁.hom := f₁.toPartialMap_toRationalMap_restrict
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun q => q ≫ y) key).trans
        (hf₁.trans ((congrArg (fun q => q ≫ M.toBase) (M.C.homOfLE_ι hle)).symm.trans
          (Category.assoc _ _ _))))
  refine ⟨M.C, M.toBase, inferInstance, inferInstance, inferInstance, U, ψ, hψ, ?_⟩
  intro a ha
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k A))) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  let 𝔪pt : Spec (CommRingCat.of A) := a (IsLocalRing.closedPoint k)
  have h𝔪 : 𝔪pt.asIdeal.IsMaximal := by
    exact (PrimeSpectrum.isClosed_singleton_iff_isMaximal 𝔪pt).mp
      ((pointEquivClosedPoint (Spec.map (CommRingCat.ofHom (algebraMap k A)))) ⟨a, ha⟩).2
  have h𝔪0 : 𝔪pt.asIdeal ≠ ⊥ := by
    intro hbot
    have h1 : (1 : WithBot ℕ∞) ≤ ringKrullDim A := by rw [hA]
    rw [ringKrullDim, Order.one_le_krullDim_iff] at h1
    obtain ⟨p, q, hpq⟩ := h1
    have hp : p.asIdeal = ⊥ := by
      have := h𝔪.eq_of_le p.isPrime.ne_top (hbot ▸ bot_le)
      rw [← this, hbot]
    have hq : q.asIdeal = ⊥ := by
      have := h𝔪.eq_of_le q.isPrime.ne_top (hbot ▸ bot_le)
      rw [← this, hbot]
    exact (ne_of_lt hpq) (PrimeSpectrum.ext (hp.trans hq.symm))
  obtain ⟨P, hAP, hmP⟩ := exists_place_le_and_subset_nonunits M A
    (IsFractionRing.injective A L) 𝔪pt.asIdeal h𝔪0
  obtain ⟨x, hxP⟩ := M.placeOfPoint_bijective.2 P
  let gx : M.C.presheaf.stalk x.1 →+* L :=
    (M.ffEquiv.symm : M.C.functionField →+* L).comp
      (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField)
  have hgx : Function.Injective gx :=
    M.ffEquiv.symm.injective.comp (IsFractionRing.injective (M.C.presheaf.stalk x.1)
      M.C.functionField)
  have hst : gx.range = P.toValuationSubring.toSubring := by
    have := M.range_stalk_eq x
    rw [hxP] at this
    exact this
  have hAr : ∀ a' : A, algebraMap A L a' ∈ gx.range := fun a' => by rw [hst]; exact hAP a'
  have hVr : ∀ s, gx s ∈ P.toValuationSubring := fun s => by
    have : gx s ∈ gx.range := ⟨s, rfl⟩
    rw [hst] at this
    exact this
  let eg : M.C.presheaf.stalk x.1 ≃+* gx.range := RingEquiv.ofBijective gx.rangeRestrict
    ⟨fun s t h => hgx (congrArg Subtype.val h), gx.rangeRestrict_surjective⟩
  let α : A →+* M.C.presheaf.stalk x.1 :=
    eg.symm.toRingHom.comp ((algebraMap A L).codRestrict gx.range hAr)
  have hα : ∀ a' : A, gx (α a') = algebraMap A L a' := fun a' => by
    have h1 : eg (eg.symm ((algebraMap A L).codRestrict gx.range hAr a')) =
        (algebraMap A L).codRestrict gx.range hAr a' := eg.apply_symm_apply _
    exact congrArg Subtype.val h1
  have hcomap : Ideal.comap α (IsLocalRing.maximalIdeal _) = 𝔪pt.asIdeal := by
    symm
    refine h𝔪.eq_of_le (Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top) ?_
    intro m hm
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    let gV : M.C.presheaf.stalk x.1 →+* P.toValuationSubring :=
      gx.codRestrict P.toValuationSubring.toSubring hVr
    have hu' : IsUnit (gV (α m)) := hu.map gV
    have hnon : (gV (α m) : L) ∈ P.toValuationSubring.nonunits := by
      change gx (α m) ∈ _
      rw [hα]
      exact hmP m hm
    rw [ValuationSubring.coe_mem_nonunits_iff, IsLocalRing.mem_maximalIdeal] at hnon
    exact hnon hu'
  let lx : Spec (M.C.presheaf.stalk x.1) ⟶ Y := Spec.map (CommRingCat.ofHom α) ≫ φ
  have hgerm : ∀ t : k, gx ((M.C.presheaf.germ ⊤ x.1 trivial).hom
      (M.toBase.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom t))) = algebraMap k L t :=
        by
    intro t
    change M.ffEquiv.symm (algebraMap _ M.C.functionField ((M.C.presheaf.germ ⊤ x.1 trivial).hom
      _)) = _
    have h1 : algebraMap (M.C.presheaf.stalk x.1) M.C.functionField
        ((M.C.presheaf.germ ⊤ x.1 trivial).hom
          (M.toBase.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom t))) =
        baseToFunctionField M.toBase t := by
      have he := TopCat.Presheaf.germ_stalkSpecializes M.C.presheaf
        (U := ⊤) (y := x.1) trivial (genericPoint_specializes x.1)
      exact (congrArg (fun q : M.C.presheaf.stalk x.1 ⟶ M.C.functionField =>
        q.hom ((M.C.presheaf.germ ⊤ x.1 trivial).hom
          (M.toBase.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom t))))
            (ofHom_algebraMap_stalk_functionField x.1)).trans
        (congrArg (fun q : Γ(M.C, ⊤) ⟶ M.C.functionField =>
          q.hom (M.toBase.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom t))) he)
    rw [h1, ← M.ffEquiv_algebraMap, RingEquiv.symm_apply_apply]
  have hlx : lx ≫ y = M.C.fromSpecStalk x.1 ≫ M.toBase := by
    have hαk : CommRingCat.ofHom (algebraMap k A) ≫ CommRingCat.ofHom α =
        CommRingCat.ofHom ((M.C.presheaf.germ ⊤ x.1 trivial).hom.comp
          (M.toBase.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)) := by
      ext t
      apply hgx
      change gx (α (algebraMap k A t)) = gx ((M.C.presheaf.germ ⊤ x.1 trivial).hom
        (M.toBase.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom t)))
      rw [hα, hgerm, ← IsScalarTower.algebraMap_apply]
    exact (Category.assoc (Spec.map (CommRingCat.ofHom α)) φ y).trans
      ((congrArg (fun q => Spec.map (CommRingCat.ofHom α) ≫ q) hφ).trans
        ((Spec.map_comp (CommRingCat.ofHom (algebraMap k A)) (CommRingCat.ofHom α)).symm.trans
          ((congrArg Spec.map hαk).trans (fromSpecStalk_comp_eq M.toBase x.1).symm)))
  let g₁ : M.C.PartialMap Y := Scheme.PartialMap.ofFromSpecStalk M.toBase y lx hlx
  have hxg₁ : x.1 ∈ g₁.domain := Scheme.PartialMap.mem_domain_ofFromSpecStalk _ _ _ _
  have hg₁x : g₁.fromSpecStalkOfMem hxg₁ = lx :=
    Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk _ _ _ _
  have hg₁r : g₁.toRationalMap = r := by
    apply Scheme.RationalMap.eq_of_fromFunctionField_eq
    rw [Scheme.RationalMap.fromFunctionField_toRationalMap,
      Scheme.RationalMap.fromFunctionField_toRationalMap,
      partialMap_fromFunctionField_eq_of_mem g₁ hxg₁, hg₁x,
      partialMap_fromFunctionField_eq_of_mem f₁ hη, hf₁η]
    have hspec : M.C.presheaf.stalkSpecializes (genericPoint_specializes (genericPoint M.C)) = 𝟙 _
      :=
      TopCat.Presheaf.stalkSpecializes_refl _ _
    have hαρ : CommRingCat.ofHom α ≫
        M.C.presheaf.stalkSpecializes (genericPoint_specializes x.1) = CommRingCat.ofHom ρ := by
      ext a'
      apply M.ffEquiv.symm.injective
      change M.ffEquiv.symm
        ((M.C.presheaf.stalkSpecializes (genericPoint_specializes x.1)).hom (α a')) =
          M.ffEquiv.symm (M.ffEquiv (algebraMap A L a'))
      rw [RingEquiv.symm_apply_apply, ← hα a', ← ofHom_algebraMap_stalk_functionField]
      rfl
    have hl : Spec.map (M.C.presheaf.stalkSpecializes (genericPoint_specializes x.1)) ≫ lx = f₀ :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (fun q => q ≫ φ)
          ((Spec.map_comp (CommRingCat.ofHom α)
            (M.C.presheaf.stalkSpecializes (genericPoint_specializes x.1))).symm.trans
              (congrArg Spec.map hαρ))))
    have hr : Spec.map
        (M.C.presheaf.stalkSpecializes (genericPoint_specializes (genericPoint M.C))) ≫ f₀ = f₀ :=
          by
      rw [hspec, Spec.map_id, Category.id_comp]
    exact hl.trans hr.symm
  have hxU : x.1 ∈ U := by
    have : x.1 ∈ g₁.toRationalMap.domain := g₁.le_domain_toRationalMap hxg₁
    rw [hg₁r] at this
    exact this
  have hψx : ψ ⟨x.1, hxU⟩ = φ 𝔪pt := by
    have key : ∀ (r' : M.C ⤏ Y) (hr : g₁.toRationalMap = r') (h : g₁.domain ≤
      r'.toPartialMap.domain),
        M.C.homOfLE h ≫ r'.toPartialMap.hom = g₁.hom := by
      rintro _ rfl h
      exact g₁.toPartialMap_toRationalMap_restrict
    have hle : g₁.domain ≤ U := fun z hz => by
      have : z ∈ g₁.toRationalMap.domain := g₁.le_domain_toRationalMap hz
      rw [hg₁r] at this
      exact this
    have h1 : ψ ⟨x.1, hxU⟩ = (M.C.homOfLE hle ≫ ψ) ⟨x.1, hxg₁⟩ :=
      ((Scheme.Hom.comp_apply (M.C.homOfLE hle) ψ ⟨x.1, hxg₁⟩).trans
        (congrArg ψ (Subtype.ext (Scheme.homOfLE_apply hle ⟨x.1, hxg₁⟩)))).symm
    have h2' : g₁.domain.ι (g₁.domain.fromSpecStalkOfMem x.1 hxg₁
        (IsLocalRing.closedPoint _)) = x.1 :=
      (Scheme.Hom.comp_apply (g₁.domain.fromSpecStalkOfMem x.1 hxg₁) g₁.domain.ι
        (IsLocalRing.closedPoint _)).symm.trans
          ((congrArg (fun q : Spec (M.C.presheaf.stalk x.1) ⟶ M.C =>
            q (IsLocalRing.closedPoint _)) (Scheme.Opens.fromSpecStalkOfMem_ι _ _ _)).trans
              Scheme.fromSpecStalk_closedPoint)
    have h2 : (⟨x.1, hxg₁⟩ : g₁.domain) =
        g₁.domain.fromSpecStalkOfMem x.1 hxg₁ (IsLocalRing.closedPoint _) :=
      Subtype.ext h2'.symm
    have hαpt : Spec.map (CommRingCat.ofHom α) (IsLocalRing.closedPoint _) = 𝔪pt :=
      PrimeSpectrum.ext hcomap
    exact h1.trans
      ((congrArg (fun q : (g₁.domain : Scheme.{u}) ⟶ Y => q ⟨x.1, hxg₁⟩)
        (key r hg₁r hle)).trans
          ((congrArg g₁.hom h2).trans
            ((Scheme.Hom.comp_apply (g₁.domain.fromSpecStalkOfMem x.1 hxg₁) g₁.hom
              (IsLocalRing.closedPoint _)).symm.trans
                ((congrArg (fun q : Spec (M.C.presheaf.stalk x.1) ⟶ Y =>
                  q (IsLocalRing.closedPoint _)) hg₁x).trans
                    ((Scheme.Hom.comp_apply (Spec.map (CommRingCat.ofHom α)) φ
                      (IsLocalRing.closedPoint _)).trans (congrArg φ hαpt))))))
  have hxcl : IsClosed ({(⟨x.1, hxU⟩ : U)} : Set U) := isClosed_singleton_opens U x.1 hxU x.2
  refine ⟨pointOfClosedPoint (U.ι ≫ M.toBase) ⟨x.1, hxU⟩ hxcl, pointOfClosedPoint_comp _ _ _, ?_⟩
  have hφy : (a ≫ φ) ≫ y = 𝟙 _ := by rw [Category.assoc, hφ, ha]
  refine ext_of_apply_closedPoint_eq y ?_ hφy ?_
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun q => pointOfClosedPoint (U.ι ≫ M.toBase) ⟨x.1, hxU⟩ hxcl ≫ q) hψ).trans
        (pointOfClosedPoint_comp (U.ι ≫ M.toBase) ⟨x.1, hxU⟩ hxcl))
  · exact (Scheme.Hom.comp_apply
      (pointOfClosedPoint (U.ι ≫ M.toBase) ⟨x.1, hxU⟩ hxcl) ψ (IsLocalRing.closedPoint k)).trans
        ((congrArg ψ (pointOfClosedPoint_apply (U.ι ≫ M.toBase) ⟨x.1, hxU⟩ hxcl
          (IsLocalRing.closedPoint k))).trans
            (hψx.trans (Scheme.Hom.comp_apply a φ (IsLocalRing.closedPoint k)).symm))

end Main

end P2mNormOpen

end

open CategoryTheory AlgebraicGeometry in
theorem _root_.AlgebraicGeometry.exists_smoothProperCurve_opens_hom_comp_eq_of_ringKrullDim_eq_one
    {k : Type u} [Field k] [IsAlgClosed k] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of k))
    [IsSeparated y] [LocallyOfFiniteType y] (A : Type u) [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] (hA : ringKrullDim A = 1) (φ : Spec (CommRingCat.of A) ⟶ Y)
    (hφ : φ ≫ y = Spec.map (CommRingCat.ofHom (algebraMap k A))) :
    ∃ (C : Scheme.{u}) (c : C ⟶ Spec (CommRingCat.of k)) (_ : IsProper c)
      (_ : SmoothOfRelativeDimension 1 c) (_ : IsIntegral C) (U : C.Opens)
      (ψ : (U : Scheme.{u}) ⟶ Y), ψ ≫ y = U.ι ≫ c ∧
      ∀ a : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A),
        a ≫ Spec.map (CommRingCat.ofHom (algebraMap k A)) = 𝟙 _ →
        ∃ p : Spec (CommRingCat.of k) ⟶ (U : Scheme.{u}), p ≫ U.ι ≫ c = 𝟙 _ ∧ p ≫ ψ = a ≫ φ :=
  P2mNormOpen.main y A hA φ hφ
end AlgebraicCurves.Geometry.Curves.Proofs.OpenCurveFactorization
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
