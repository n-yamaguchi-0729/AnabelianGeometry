/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Tactic.Set
public import Nyll.SchemeTheory.Modules.Sections.SectionsAlgebra
public import Nyll.SchemeTheory.RingTheory.Smooth.DifferentialCriteria

/-!
# Smoothness defect along a discrete valuation ring point

The length of torsion in pulled-back differentials measures the smoothness defect. If the
image of the generic point is smooth, this length vanishes exactly when the closed point
is smooth. Stalk and section maps connect the invariant to affine cotangent ranks.
-/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_NeronModelInfra_SmoothnessDefect.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

namespace NeronModelInfra

/-- The base ring homomorphism to the stalk induced by a structural morphism. -/
def stalkAlgebraMap {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (x : X) : R →+* X.presheaf.stalk x :=
  (X.presheaf.germ ⊤ x trivial).hom.comp
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)

theorem stalkAlgebraMap_apply {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (x : X) (r : R) :
    stalkAlgebraMap f x r =
      (X.presheaf.germ ⊤ x trivial).hom
        (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) :=
  rfl

/-- The base algebra on a stalk induced by the structural morphism. -/
abbrev stalkAlgebra {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (x : X) : Algebra R (X.presheaf.stalk x) :=
  (stalkAlgebraMap f x).toAlgebra

/-- The stalk algebra on the local ring defining a scheme-valued point. -/
abbrev pointAlgebra {X : Scheme.{u}} {R' : Type u} [CommRing R'] [IsLocalRing R']
    (a : Spec (CommRingCat.of R') ⟶ X) :
    Algebra (X.presheaf.stalk (a (IsLocalRing.closedPoint R'))) R' :=
  (Scheme.stalkClosedPointTo a).hom.toAlgebra

/-- The length of torsion in the differentials pulled back along a local point. -/
def smoothnessDefect {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    {R' : Type u} [CommRing R'] [IsLocalRing R'] (a : Spec (CommRingCat.of R') ⟶ X) : ℕ∞ :=
  letI : Algebra R (X.presheaf.stalk (a (IsLocalRing.closedPoint R'))) :=
    stalkAlgebra f (a (IsLocalRing.closedPoint R'))
  letI : Algebra (X.presheaf.stalk (a (IsLocalRing.closedPoint R'))) R' := pointAlgebra a
  Module.length R'
    (Submodule.torsion R'
      (R' ⊗[X.presheaf.stalk (a (IsLocalRing.closedPoint R'))]
        Ω[X.presheaf.stalk (a (IsLocalRing.closedPoint R'))⁄R]))

theorem smoothnessDefect_def {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R))
    {R' : Type u} [CommRing R'] [IsLocalRing R'] (a : Spec (CommRingCat.of R') ⟶ X) :
    smoothnessDefect f a =
      (letI : Algebra R (X.presheaf.stalk (a (IsLocalRing.closedPoint R'))) :=
        stalkAlgebra f (a (IsLocalRing.closedPoint R'))
      letI : Algebra (X.presheaf.stalk (a (IsLocalRing.closedPoint R'))) R' := pointAlgebra a
      Module.length R'
        (Submodule.torsion R'
          (R' ⊗[X.presheaf.stalk (a (IsLocalRing.closedPoint R'))]
            Ω[X.presheaf.stalk (a (IsLocalRing.closedPoint R'))⁄R]))) :=
  rfl

section Gate

variable (R : Type u) [CommRing R]

theorem stalkAlgebraMap_id (p : PrimeSpectrum R) :
    stalkAlgebraMap (𝟙 (Spec (CommRingCat.of R))) p = (StructureSheaf.toStalk R p).hom := by
  apply RingHom.ext
  intro r
  simp only [stalkAlgebraMap, Scheme.Hom.id_appTop, RingHom.coe_comp, Function.comp_apply,
    CommRingCat.hom_id, RingHom.id_apply, StructureSheaf.toStalk, Scheme.ΓSpecIso_inv]
  rfl

theorem smoothnessDefect_id {R' : Type u} [CommRing R'] [IsLocalRing R']
    (a : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)) :
    smoothnessDefect (𝟙 (Spec (CommRingCat.of R))) a = 0 := by
  rw [smoothnessDefect_def]
  set p : PrimeSpectrum R := a (IsLocalRing.closedPoint R') with hp
  let iRB : Algebra R ((Spec (CommRingCat.of R)).presheaf.stalk p) :=
    stalkAlgebra (𝟙 (Spec (CommRingCat.of R))) p
  let : Algebra ((Spec (CommRingCat.of R)).presheaf.stalk p) R' := pointAlgebra a
  have hAlg : iRB = StructureSheaf.stalkAlgebra R p := by
    refine Algebra.algebra_ext _ _ fun r => ?_
    change stalkAlgebraMap (𝟙 (Spec (CommRingCat.of R))) p r = _
    rw [stalkAlgebraMap_id]
    rfl
  have hunr : @Algebra.FormallyUnramified R
      ((Spec (CommRingCat.of R)).presheaf.stalk p) _ _ iRB := by
    rw [hAlg]
    exact @Algebra.FormallyUnramified.of_isLocalization _ _ _ _ p.asIdeal.primeCompl _
      (StructureSheaf.IsLocalization.to_stalk R p)
  have : Subsingleton Ω[(Spec (CommRingCat.of R)).presheaf.stalk p⁄R] :=
    Algebra.FormallyUnramified.subsingleton_kaehlerDifferential
  have : Subsingleton
      (R' ⊗[(Spec (CommRingCat.of R)).presheaf.stalk p]
        Ω[(Spec (CommRingCat.of R)).presheaf.stalk p⁄R]) :=
    inferInstance
  exact Module.length_eq_zero

end Gate

end NeronModelInfra

end

end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_smoothnessDefect_eq_zero_iff_apply_closedPoint_mem_smoothLocus.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace SchemeTheory.LocalGeometry.SmoothnessDefect

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct NeronModelInfra

universe u

section SmoothLocus

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))

theorem stalkMap_toStalk (x : X) (r : R) :
    (f.stalkMap x).hom ((StructureSheaf.toStalk R (f x)).hom r) = stalkAlgebraMap f x r := by
  rw [stalkAlgebraMap_apply]
  have h := Scheme.Hom.germ_stalkMap f ⊤ x trivial
  have h2 := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) h
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h2
  exact h2

theorem mem_smoothLocus_iff [LocallyOfFinitePresentation f] (x : X) :
    x ∈ f.smoothLocus ↔
      @Algebra.FormallySmooth R (X.presheaf.stalk x) _ _ (stalkAlgebra f x) := by
  rw [Scheme.Hom.mem_smoothLocus]
  let : Algebra R (X.presheaf.stalk x) := stalkAlgebra f x
  let iRL : Algebra R ((Spec (CommRingCat.of R)).presheaf.stalk (f x)) :=
    StructureSheaf.stalkAlgebra R (f x)
  have : (f x).asIdeal.IsPrime := (show PrimeSpectrum R from f x).isPrime
  have : IsLocalization.AtPrime ((Spec (CommRingCat.of R)).presheaf.stalk (f x)) (f x).asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R (f x)
  let : Algebra ((Spec (CommRingCat.of R)).presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  have : IsScalarTower R ((Spec (CommRingCat.of R)).presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq fun r => (stalkMap_toStalk f x r).symm
  have : Algebra.FormallyEtale R ((Spec (CommRingCat.of R)).presheaf.stalk (f x)) :=
    Algebra.FormallyEtale.of_isLocalization (M := (f x).asIdeal.primeCompl)
  change Algebra.FormallySmooth ((Spec (CommRingCat.of R)).presheaf.stalk (f x))
    (X.presheaf.stalk x) ↔ _
  exact (Algebra.FormallySmooth.iff_restrictScalars (R := R)
    (A := (Spec (CommRingCat.of R)).presheaf.stalk (f x)) (B := X.presheaf.stalk x)).symm

theorem sectionsAlgebra_isScalarTower (V : X.Opens) (x : X) (hxV : x ∈ V) :
    let : Algebra R Γ(X, V) := f.sectionsAlgebra V
    let : Algebra R (X.presheaf.stalk x) := stalkAlgebra f x
    let : Algebra Γ(X, V) (X.presheaf.stalk x) :=
      X.presheaf.algebra_section_stalk (⟨x, hxV⟩ : V)
    IsScalarTower R Γ(X, V) (X.presheaf.stalk x) := by
  intro sectionsAlgebra stalkBaseAlgebra stalkSectionAlgebra
  refine IsScalarTower.of_algebraMap_eq fun r => ?_
  change stalkAlgebraMap f x r = (X.presheaf.germ V x hxV).hom
    ((f.appLE ⊤ V le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))
  exact congrArg (fun α : Γ(X, ⊤) ⟶ X.presheaf.stalk x =>
    α.hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)))
      (X.presheaf.germ_res (homOfLE (show V ≤ (⊤ : X.Opens) from le_top)) x hxV).symm

theorem finiteType_sectionsAlgebra [LocallyOfFiniteType f] (V : X.Opens) (hV : IsAffineOpen V) :
    letI : Algebra R Γ(X, V) := f.sectionsAlgebra V
    Algebra.FiniteType R Γ(X, V) := by
  have h1 : (f.appLE ⊤ V le_top).hom.FiniteType :=
    f.finiteType_appLE (isAffineOpen_top _) hV le_top
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.FiniteType :=
    RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.surjective
  exact h1.comp h2

end SmoothLocus

section Chart

variable {X : Scheme.{u}} {R' : Type u} [CommRing R'] [IsLocalRing R']
  (a : Spec (CommRingCat.of R') ⟶ X) {V : X.Opens} (hV : IsAffineOpen V)
  (hxV : a (IsLocalRing.closedPoint R') ∈ V)

/-- The map from affine sections to the local ring of a scheme-valued point. -/
noncomputable def pointHom : Γ(X, V) →+* R' :=
  (Scheme.stalkClosedPointTo a).hom.comp (X.presheaf.germ V _ hxV).hom

theorem eq_specMap_pointHom_comp_fromSpec :
    a = Spec.map (CommRingCat.ofHom (pointHom a hxV)) ≫ hV.fromSpec := by
  rw [pointHom, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, CommRingCat.ofHom_hom,
    CommRingCat.ofHom_hom]
  change a = Spec.map (Scheme.stalkClosedPointTo a) ≫ hV.fromSpecStalk hxV
  rw [IsAffineOpen.fromSpecStalk_eq_fromSpecStalk, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]

theorem primeIdealOf_apply (P : PrimeSpectrum R') (hP : a P ∈ V) :
    hV.primeIdealOf ⟨a P, hP⟩ = PrimeSpectrum.comap (pointHom a hxV) P := by
  apply hV.fromSpec.isOpenEmbedding.injective
  rw [IsAffineOpen.fromSpec_primeIdealOf]
  change a P = (Spec.map (CommRingCat.ofHom (pointHom a hxV)) ≫ hV.fromSpec) P
  rw [← eq_specMap_pointHom_comp_fromSpec]

end Chart

section Ranks

theorem finrank_tensor_eq_finrank_residueField_tensor
    {A : Type*} [CommRing A] (M : Type*) [AddCommGroup M] [Module A M]
    (p : Ideal A) [p.IsPrime] (F : Type*) [Field F] [Algebra A F]
    (hker : RingHom.ker (algebraMap A F) = p) :
    Module.finrank F (F ⊗[A] M) =
      Module.finrank p.ResidueField (p.ResidueField ⊗[A] M) := by
  have hinj : Function.Injective (Ideal.Quotient.lift p (algebraMap A F)
      (fun a ha => by rw [← RingHom.mem_ker, hker]; exact ha)) := by
    rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
    intro a ha
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Ideal.Quotient.lift_mk] at ha
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hker ▸ ha)
  let g : p.ResidueField →+* F := IsFractionRing.lift (K := p.ResidueField) hinj
  let : Algebra p.ResidueField F := g.toAlgebra
  have : IsScalarTower A p.ResidueField F := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap A F a = g (algebraMap A p.ResidueField a)
    rw [← Ideal.algebraMap_quotient_residueField_mk (I := p)]
    change _ = IsFractionRing.lift hinj _
    rw [IsFractionRing.lift_algebraMap, Ideal.Quotient.lift_mk]
  have e : F ⊗[A] M ≃ₗ[F] F ⊗[p.ResidueField] (p.ResidueField ⊗[A] M) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange A p.ResidueField F F M).symm
  rw [e.finrank_eq, Module.finrank_baseChange]

theorem finrank_tensor_kaehler_eq_of_free
    {R A B R' : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing R'] [Nontrivial R']
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B] [Algebra.FormallyEtale A B]
    [Algebra B R'] [Algebra A R'] [IsScalarTower A B R']
    [Module.Free R' (R' ⊗[B] Ω[B⁄R])]
    (F : Type u) [Field F] [Algebra R' F] [Algebra B F] [Algebra A F]
    [IsScalarTower B R' F] [IsScalarTower A B F] :
    Module.finrank F (F ⊗[A] Ω[A⁄R]) = Module.finrank R' (R' ⊗[B] Ω[B⁄R]) := by
  have eΩ : B ⊗[A] Ω[A⁄R] ≃ₗ[B] Ω[B⁄R] :=
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A B
  have e1 : F ⊗[R'] (R' ⊗[B] Ω[B⁄R]) ≃ₗ[F] F ⊗[B] Ω[B⁄R] :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange B R' F F Ω[B⁄R]
  have e2 : F ⊗[B] Ω[B⁄R] ≃ₗ[F] F ⊗[B] (B ⊗[A] Ω[A⁄R]) := eΩ.symm.baseChange B F _ _
  have e3 : F ⊗[B] (B ⊗[A] Ω[A⁄R]) ≃ₗ[F] F ⊗[A] Ω[A⁄R] :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange A B F F Ω[A⁄R]
  rw [← (e1 ≪≫ₗ e2 ≪≫ₗ e3).finrank_eq, Module.finrank_baseChange]

end Ranks

theorem _root_.NeronModelInfra.smoothnessDefect_eq_zero_iff_apply_closedPoint_mem_smoothLocus
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f]
    {R' : Type u} [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    (a : Spec (CommRingCat.of R') ⟶ X)
    (hgen : a (⊥ : PrimeSpectrum R') ∈ f.smoothLocus) :
    smoothnessDefect f a = 0 ↔ a (IsLocalRing.closedPoint R') ∈ f.smoothLocus := by
  set x : X := a (IsLocalRing.closedPoint R') with hx
  let iRS : Algebra R (X.presheaf.stalk x) := stalkAlgebra f x
  let iSR' : Algebra (X.presheaf.stalk x) R' := pointAlgebra a
  rw [smoothnessDefect_def, Module.length_eq_zero_iff, mem_smoothLocus_iff]
  change Subsingleton (Submodule.torsion R' (R' ⊗[X.presheaf.stalk x] Ω[X.presheaf.stalk x⁄R])) ↔
    Algebra.FormallySmooth R (X.presheaf.stalk x)
  constructor
  swap
  · intro hsm
    have : Module.Flat R' (R' ⊗[X.presheaf.stalk x] Ω[X.presheaf.stalk x⁄R]) := inferInstance
    have : Module.IsTorsionFree R' (R' ⊗[X.presheaf.stalk x] Ω[X.presheaf.stalk x⁄R]) :=
      inferInstance
    rw [(Submodule.isTorsionFree_iff_torsion_eq_bot).mp this]
    infer_instance
  · intro hδ
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    set y : X := a (⊥ : PrimeSpectrum R') with hy
    have hyx : y ⤳ x :=
      ((PrimeSpectrum.le_iff_specializes ⊥ (IsLocalRing.closedPoint R')).mp bot_le).map a.continuous
    have hyV : y ∈ V := hyx.mem_open V.2 hxV
    let iRA : Algebra R Γ(X, V) := f.sectionsAlgebra V
    let iAS : Algebra Γ(X, V) (X.presheaf.stalk x) :=
      X.presheaf.algebra_section_stalk (⟨x, hxV⟩ : V)
    have : IsScalarTower R Γ(X, V) (X.presheaf.stalk x) := sectionsAlgebra_isScalarTower f V x hxV
    have : Algebra.FiniteType R Γ(X, V) := finiteType_sectionsAlgebra f V hV
    let iAR' : Algebra Γ(X, V) R' :=
      ((algebraMap (X.presheaf.stalk x) R').comp
        (algebraMap Γ(X, V) (X.presheaf.stalk x))).toAlgebra
    have : IsScalarTower Γ(X, V) (X.presheaf.stalk x) R' :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    set p : Ideal Γ(X, V) := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal with hp
    set q : Ideal Γ(X, V) := (hV.primeIdealOf ⟨y, hyV⟩).asIdeal with hq
    have hp' : p = Ideal.comap (algebraMap Γ(X, V) R') (IsLocalRing.maximalIdeal R') := by
      change (hV.primeIdealOf ⟨a (IsLocalRing.closedPoint R'), hxV⟩).asIdeal = _
      rw [primeIdealOf_apply a hV hxV (IsLocalRing.closedPoint R') hxV]; rfl
    have hq' : q = RingHom.ker (algebraMap Γ(X, V) R') := by
      change (hV.primeIdealOf ⟨a (⊥ : PrimeSpectrum R'), hyV⟩).asIdeal = _
      rw [primeIdealOf_apply a hV hxV (⊥ : PrimeSpectrum R') hyV]; rfl
    have hqp : q ≤ p := by
      rw [hp', hq']
      exact fun b hb => by
        rw [RingHom.mem_ker] at hb
        change algebraMap Γ(X, V) R' b ∈ IsLocalRing.maximalIdeal R'
        rw [hb]
        exact Ideal.zero_mem _
    have : IsLocalization.AtPrime (X.presheaf.stalk x) p := hV.isLocalization_stalk ⟨x, hxV⟩
    have : Algebra.FormallyEtale Γ(X, V) (X.presheaf.stalk x) :=
      Algebra.FormallyEtale.of_isLocalization (M := p.primeCompl)
    have : Algebra.IsSmoothAt R q := by
      let iRSy : Algebra R (X.presheaf.stalk y) := stalkAlgebra f y
      let iASy : Algebra Γ(X, V) (X.presheaf.stalk y) :=
        X.presheaf.algebra_section_stalk (⟨y, hyV⟩ : V)
      have : IsScalarTower R Γ(X, V) (X.presheaf.stalk y) :=
        sectionsAlgebra_isScalarTower f V y hyV
      have : IsLocalization.AtPrime (X.presheaf.stalk y) q := hV.isLocalization_stalk ⟨y, hyV⟩
      have hsm : Algebra.FormallySmooth R (X.presheaf.stalk y) :=
        (mem_smoothLocus_iff f y).mp hgen
      exact Algebra.FormallySmooth.of_equiv
        ((IsLocalization.algEquiv q.primeCompl (X.presheaf.stalk y)
          (Localization.AtPrime q)).restrictScalars R)
    have : Module.Finite (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄R] :=
      Module.Finite.equiv (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R Γ(X, V) _)
    have : Module.IsTorsionFree R' (R' ⊗[X.presheaf.stalk x] Ω[X.presheaf.stalk x⁄R]) := by
      rw [Submodule.isTorsionFree_iff_torsion_eq_bot, ← Submodule.subsingleton_iff_eq_bot]
      exact hδ
    have : Module.Free R' (R' ⊗[X.presheaf.stalk x] Ω[X.presheaf.stalk x⁄R]) :=
      Module.free_of_finite_type_torsion_free'
    have hrank : ∀ (F : Type u) [Field F] [Algebra R' F],
        Module.finrank F (letI : Algebra Γ(X, V) F :=
            ((algebraMap R' F).comp (algebraMap Γ(X, V) R')).toAlgebra
          F ⊗[Γ(X, V)] Ω[Γ(X, V)⁄R]) =
        Module.finrank R' (R' ⊗[X.presheaf.stalk x] Ω[X.presheaf.stalk x⁄R]) := by
      intro F _ _
      let : Algebra (X.presheaf.stalk x) F :=
        ((algebraMap R' F).comp (algebraMap (X.presheaf.stalk x) R')).toAlgebra
      let : Algebra Γ(X, V) F := ((algebraMap R' F).comp (algebraMap Γ(X, V) R')).toAlgebra
      have : IsScalarTower (X.presheaf.stalk x) R' F :=
        IsScalarTower.of_algebraMap_eq fun _ => rfl
      have : IsScalarTower Γ(X, V) (X.presheaf.stalk x) F :=
        IsScalarTower.of_algebraMap_eq fun _ => rfl
      exact finrank_tensor_kaehler_eq_of_free F
    have h₁ : Module.finrank p.ResidueField (p.ResidueField ⊗[Γ(X, V)] Ω[Γ(X, V)⁄R]) =
        Module.finrank R' (R' ⊗[X.presheaf.stalk x] Ω[X.presheaf.stalk x⁄R]) := by
      let : Algebra Γ(X, V) (IsLocalRing.ResidueField R') :=
        ((algebraMap R' (IsLocalRing.ResidueField R')).comp (algebraMap Γ(X, V) R')).toAlgebra
      have hker : RingHom.ker (algebraMap Γ(X, V) (IsLocalRing.ResidueField R')) = p := by
        have hres : RingHom.ker (algebraMap R' (IsLocalRing.ResidueField R')) =
            IsLocalRing.maximalIdeal R' := IsLocalRing.ker_residue (R := R')
        rw [RingHom.algebraMap_toAlgebra, hp', ← RingHom.comap_ker, hres]
      rw [← finrank_tensor_eq_finrank_residueField_tensor Ω[Γ(X, V)⁄R] p
        (IsLocalRing.ResidueField R') hker]
      exact hrank (IsLocalRing.ResidueField R')
    have h₂ : Module.finrank q.ResidueField (q.ResidueField ⊗[Γ(X, V)] Ω[Γ(X, V)⁄R]) =
        Module.finrank R' (R' ⊗[X.presheaf.stalk x] Ω[X.presheaf.stalk x⁄R]) := by
      let : Algebra Γ(X, V) (FractionRing R') :=
        ((algebraMap R' (FractionRing R')).comp (algebraMap Γ(X, V) R')).toAlgebra
      have hker : RingHom.ker (algebraMap Γ(X, V) (FractionRing R')) = q := by
        rw [RingHom.algebraMap_toAlgebra, hq', ← RingHom.comap_ker,
          (RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective R' (FractionRing R')),
          ← RingHom.ker_eq_comap_bot]
      rw [← finrank_tensor_eq_finrank_residueField_tensor Ω[Γ(X, V)⁄R] q (FractionRing R') hker]
      exact hrank (FractionRing R')
    have : Algebra.IsSmoothAt R p :=
      Algebra.isSmoothAt_of_le_of_finrank_tensorProduct_kaehlerDifferential_eq
        p q hqp (h₁.trans h₂.symm)
    exact Algebra.FormallySmooth.of_equiv
      ((IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p)
        (X.presheaf.stalk x)).restrictScalars R)

end SchemeTheory.LocalGeometry.SmoothnessDefect
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_NeronModelInfra_OmegaMinimalComponentData.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace NeronModelInfra

section StalkAlgebra

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R)) (y : Y)

theorem ofHom_stalkAlgebraMap_eq :
    CommRingCat.ofHom (stalkAlgebraMap f y) =
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
        (Spec (CommRingCat.of R)).presheaf.germ ⊤ (f.base y) trivial) ≫ f.stalkMap y := by
  ext r
  exact (SchemeTheory.LocalGeometry.SmoothnessDefect.stalkMap_toStalk f y r).symm

theorem fromSpecStalk_comp_eq_specMap_algebraMap_stalkAlgebra :
    let : Algebra R (Y.presheaf.stalk y) := stalkAlgebra f y
    Y.fromSpecStalk y ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk y))) := by
  intro stalkBaseAlgebra
  change Y.fromSpecStalk y ≫ f = Spec.map (CommRingCat.ofHom (stalkAlgebraMap f y))
  rw [ofHom_stalkAlgebraMap_eq, Spec.map_comp, ← Scheme.SpecMap_stalkMap_fromSpecStalk f,
    Spec.fromSpecStalk_eq]

end StalkAlgebra

end NeronModelInfra
end
end
