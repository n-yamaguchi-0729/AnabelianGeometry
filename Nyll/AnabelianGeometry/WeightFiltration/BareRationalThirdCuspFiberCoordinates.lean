/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.BareRationalArithmeticRootFieldAction
import Nyll.AnabelianGeometry.WeightFiltration.BareRationalThirdCuspRootSpecialization
import Nyll.AnabelianGeometry.WeightFiltration.BareRationalCuspDecompositionProjection

/-!
# One arithmetic correction for all original third-cusp fiber coordinates

Unpack the supplied coordinate on the actual finite cover only once. Choose
the source-action correction at the original bare point only once, before any
third cusp. At every third cusp, compose this same coordinate with the literal
specialization at the same chosen normalization prime and with that fixed
correction. This proves the actual arithmetic decomposition action and the
twisted full-root scaling on the unchanged finite-cover fiber.
-/

noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.FiniteEtale AlgebraicGeometry.ProjSpace SchemeTheory
open EtaleFundamentalGroups.Inertia AnabelianGeometry.KummerTheory
open scoped RatFunc FintypeCatDiscrete

namespace AnabelianGeometry.WeightFiltration

attribute [local instance] Classical.propDecidable
  MvPolynomial.gradedAlgebra Polynomial.algebra
  rationalConfigurationGeometricFieldAlgebra rationalConfigurationGeometricConstantAlgebra
  rationalConfigurationGeometricField_scalarTower
  rationalConfigurationOriginalFieldAlgebra rationalConfigurationOriginalConstantAlgebra
  placeBaseAmbientAlgebra placeBaseAmbientTower placeConstantAmbientTower
  normalizationCommAlgGaloisAction

local instance (priority := 2000) thirdCuspFiberSMulRatFunc
    {A E : Type*} [CommSemiring A] [Field E] [Algebra A (RatFunc E)] :
    SMul A (RatFunc E) := (inferInstance : Algebra A (RatFunc E)).toSMul

/-- Compose the retained root coordinates and prove the actual source-action
formula over abstract fields and an abstract normalization subgroup. -/
private theorem corrected_specialization_coordinates
    (k F κ Ω : Type) [Field k] [Field F] [Field κ] [Field Ω]
    [Algebra k F] [Algebra k κ] [Algebra k Ω] [Algebra F Ω] [Algebra κ Ω]
    [IsScalarTower k F Ω] [IsScalarTower k κ Ω]
    [IsSepClosure k κ] [IsSepClosure F Ω] [IsSepClosed Ω]
    (X : Scheme) [IsIntegral X] (f : X ⟶ Spec (.of k))
    (x : Spec (.of Ω) ⟶ X) (j : Spec (.of F) ⟶ X)
    (n : ℕ) (w : F) (v : k) (W : FiniteEtale X)
    (ts : Torsor (rootsOfUnity n κ) ((fiber x).obj W))
    (α : Gal(κ/k))
    (hα : ∀ (e : Spec (.of Ω) ≅ Spec (.of Ω)) (ρ : Ω →+* Ω)
      (_he : e.hom = Spec.map (CommRingCat.ofHom ρ)) (σ : Gal(κ/k))
      (_hρ : ρ.comp (algebraMap κ Ω) = (algebraMap κ Ω).comp σ.toRingHom)
      (hsource : e.hom ≫ x = x),
      arithmeticFundamentalGroupHom k κ f x
          (fiberSourceIso x e ≪≫ eqToIso (congrArg fiber hsource)) = α * σ * α⁻¹)
    (eBare : (fiber x).obj W ≃ {z : Ω // z ^ n = algebraMap F Ω w})
    (hscale : ∀ (ζ : rootsOfUnity n κ) y,
      (eBare (ts.toMulAction.toSMul.smul ζ y)).val =
        algebraMap κ Ω (ζ.val : κ) * (eBare y).val)
    (hchart : Spec.map (CommRingCat.ofHom (algebraMap F Ω)) ≫ j = x)
    (hfield : ∀ σ : Gal(Ω/F),
      let e := Scheme.Spec.mapIso σ.toRingEquiv.toCommRingCatIso.op
      ∃ hsource : e.hom ≫ x = x,
        (∀ y : (fiber x).obj W,
          (eBare ((show π₁ᵉᵗ(x) from
            fiberSourceIso x e ≪≫ eqToIso (congrArg fiber hsource)) • y)).val =
            σ (eBare y).val) ∧
        continuousConjAut (eqToIso (congrArg fiber hchart))
            (fieldSourceAbsoluteGaloisHom F Ω j σ) =
          fiberSourceIso x e ≪≫ eqToIso (congrArg fiber hsource))
    (D : Subgroup π₁ᵉᵗ(x)) (R : Subgroup Gal(Ω/F))
    (hraw : ∀ γ : π₁ᵉᵗ(x), γ ∈ D → ∃ δ : R,
      continuousConjAut (eqToIso (congrArg fiber hchart))
        (fieldSourceAbsoluteGaloisHom F Ω j δ.val) = γ)
    (Esp : {z : Ω // z ^ n = algebraMap F Ω w} ≃
      {z : κ // z ^ n = algebraMap k κ v})
    (hEspScale : ∀ (ζ : rootsOfUnity n κ)
      (z : {z : Ω // z ^ n = algebraMap F Ω w}),
      (Esp ⟨algebraMap κ Ω (ζ.val : κ) * z.val, by
        have hζ : (ζ.val : κ) ^ n = 1 :=
          congrArg (fun t : κˣ => (t : κ)) ((mem_rootsOfUnity _ _).mp ζ.property)
        rw [mul_pow, ← map_pow, hζ, map_one, one_mul, z.property]⟩).val =
          (ζ.val : κ) * (Esp z).val)
    (hEspAction : ∀ (δ : R) (z : {z : Ω // z ^ n = algebraMap F Ω w}),
      (Esp ⟨δ.val z.val, by rw [← map_pow δ.val, z.property, δ.val.commutes]⟩).val =
        ((δ.val.restrictScalars k).restrictNormal κ) (Esp z).val) :
    ∃ S : (fiber x).obj W → κ,
      (∀ y, S y ^ n = algebraMap k κ v) ∧
      (∀ (ζ : rootsOfUnity n κ) y,
        S (ts.toMulAction.toSMul.smul ζ y) = α (ζ.val : κ) * S y) ∧
      ∀ γ : π₁ᵉᵗ(x), γ ∈ D → ∀ y,
        S (γ • y) = arithmeticFundamentalGroupHom k κ f x γ (S y) := by
  let S : (fiber x).obj W → κ := fun y => α (Esp (eBare y)).val
  refine ⟨S, ?_, ?_, ?_⟩
  · intro y
    change α (Esp (eBare y)).val ^ n = _
    rw [← map_pow α, (Esp (eBare y)).property, α.commutes]
  · intro ζ y
    let z' : {z : Ω // z ^ n = algebraMap F Ω w} :=
      ⟨algebraMap κ Ω (ζ.val : κ) * (eBare y).val, by
        have hζ : (ζ.val : κ) ^ n = 1 :=
          congrArg (fun z : κˣ => (z : κ)) ((mem_rootsOfUnity _ _).mp ζ.property)
        rw [mul_pow, ← map_pow, hζ, map_one, one_mul, (eBare y).property]⟩
    have hz : eBare (ts.toMulAction.toSMul.smul ζ y) = z' := Subtype.ext (hscale ζ y)
    have hspec : (Esp z').val = (ζ.val : κ) * (Esp (eBare y)).val :=
      hEspScale ζ (eBare y)
    change α (Esp (eBare (ts.toMulAction.toSMul.smul ζ y))).val =
      α (ζ.val : κ) * α (Esp (eBare y)).val
    rw [hz, hspec, map_mul α]
  · intro γ hγ y
    obtain ⟨δ, hδ⟩ := hraw γ hγ
    obtain ⟨hsource, heval, haction⟩ := hfield δ.val
    let e := Scheme.Spec.mapIso δ.val.toRingEquiv.toCommRingCatIso.op
    have hγsource : fiberSourceIso x e ≪≫ eqToIso (congrArg fiber hsource) = γ :=
      haction.symm.trans hδ
    let ρ : Gal(κ/k) := (δ.val.restrictScalars k).restrictNormal κ
    have hρ : δ.val.toRingHom.comp (algebraMap κ Ω) =
        (algebraMap κ Ω).comp ρ.toRingHom := by
      ext z
      exact ((δ.val.restrictScalars k).restrictNormal_commutes κ z).symm
    have hlabel : arithmeticFundamentalGroupHom k κ f x γ = α * ρ * α⁻¹ := by
      rw [← hγsource]
      exact hα e δ.val.toRingHom rfl ρ hρ hsource
    have hy : (eBare (γ • y)).val = δ.val (eBare y).val := by
      rw [← hγsource]
      exact heval y
    let z' : {z : Ω // z ^ n = algebraMap F Ω w} :=
      ⟨δ.val (eBare y).val, by rw [← map_pow δ.val, (eBare y).property, δ.val.commutes]⟩
    have hz : eBare (γ • y) = z' := Subtype.ext hy
    have hspec : (Esp z').val = ρ (Esp (eBare y)).val := hEspAction δ (eBare y)
    change α (Esp (eBare (γ • y))).val =
      arithmeticFundamentalGroupHom k κ f x γ (α (Esp (eBare y)).val)
    rw [hz, hspec, hlabel]
    change α (ρ (Esp (eBare y)).val) =
      α (ρ (α.symm (α (Esp (eBare y)).val)))
    rw [α.symm_apply_apply]

/-- The existing coordinate and the source-action comparison, kept together
only to keep concrete supplier proof terms out of the final caller. -/
private def FixedRootSourceData
    (k F κ Ω : Type) [Field k] [Field F] [Field κ] [Field Ω]
    [Algebra k κ] [Algebra F Ω] [Algebra κ Ω]
    [IsSepClosure k κ] [IsSepClosure F Ω] [IsSepClosed Ω]
    (X : Scheme) [IsIntegral X] (f : X ⟶ Spec (.of k))
    (x : Spec (.of Ω) ⟶ X) (j : Spec (.of F) ⟶ X)
    (n : ℕ) (W : FiniteEtale X) (b : Ω)
    (ts : Torsor (rootsOfUnity n κ) ((fiber x).obj W))
    (α : Gal(κ/k)) (eBare : (fiber x).obj W ≃ {z : Ω // z ^ n = b}) : Prop :=
  (∀ (ζ : rootsOfUnity n κ) y,
    (eBare (ts.toMulAction.toSMul.smul ζ y)).val =
      algebraMap κ Ω (ζ.val : κ) * (eBare y).val) ∧
  ∃ hchart : Spec.map (CommRingCat.ofHom (algebraMap F Ω)) ≫ j = x,
    (∀ σ : Gal(Ω/F),
      let e := Scheme.Spec.mapIso σ.toRingEquiv.toCommRingCatIso.op
      ∃ hsource : e.hom ≫ x = x,
        (∀ y : (fiber x).obj W,
          (eBare ((show π₁ᵉᵗ(x) from
            fiberSourceIso x e ≪≫ eqToIso (congrArg fiber hsource)) • y)).val =
            σ (eBare y).val) ∧
        continuousConjAut (eqToIso (congrArg fiber hchart))
            (fieldSourceAbsoluteGaloisHom F Ω j σ) =
          fiberSourceIso x e ≪≫ eqToIso (congrArg fiber hsource)) ∧
    ∀ (e : Spec (.of Ω) ≅ Spec (.of Ω)) (ρ : Ω →+* Ω)
      (_he : e.hom = Spec.map (CommRingCat.ofHom ρ)) (σ : Gal(κ/k))
      (_hρ : ρ.comp (algebraMap κ Ω) = (algebraMap κ Ω).comp σ.toRingHom)
      (hsource : e.hom ≫ x = x),
      arithmeticFundamentalGroupHom k κ f x
          (fiberSourceIso x e ≪≫ eqToIso (congrArg fiber hsource)) = α * σ * α⁻¹

/-- Eliminate canonical-coordinate witnesses while every scheme and field is
still abstract. The concrete caller supplies the two existing point owners. -/
private theorem fixed_root_source_data_of_suppliers
    (k F κ Ω : Type) [Field k] [Field F] [Field κ] [Field Ω]
    [Algebra k κ] [Algebra k Ω] [Algebra F Ω] [Algebra κ Ω]
    [IsScalarTower k κ Ω] [IsSepClosure k κ] [IsSepClosure F Ω] [IsSepClosed Ω]
    (X : Scheme) [IsIntegral X] [Algebra F X.functionField]
    [Algebra X.functionField Ω] [IsScalarTower F X.functionField Ω]
    [IsSepClosure X.functionField Ω]
    (E : F ≃+* X.functionField) (hfield : algebraMap F X.functionField = E.toRingHom)
    (f : X ⟶ Spec (.of k)) (x : Spec (.of Ω) ⟶ X)
    (n : ℕ) (W : FiniteEtale X) (b : Ω)
    (ts : Torsor (rootsOfUnity n κ) ((fiber x).obj W))
    (hbaseCan : X.genericExtensionMorphism Ω ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap k Ω)))
    (H : ArithmeticFiberRootCoordinate κ X Ω n W x b (algebraMap κ Ω) ts) :
    ∃ α : Gal(κ/k), ∃ eBare : (fiber x).obj W ≃ {z : Ω // z ^ n = b},
      FixedRootSourceData k F κ Ω X f x (X.functionFieldChartPoint E) n W b ts α eBare := by
  obtain ⟨hp, eCan, hCan, eBare, hscale, hBare⟩ := H
  have hbase : x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k Ω)) :=
    (congrArg (fun y : Spec (.of Ω) ⟶ X => y ≫ f) hp).trans hbaseCan
  obtain ⟨α, hα⟩ := arithmeticFundamentalGroupHom_sourceAction k κ Ω f x hbase
  obtain ⟨hchart, haction⟩ := fieldChart_arithmeticRootCoordinate_fieldSource_eval
    F Ω X E hfield n W b x hp eCan hCan eBare hBare
  exact ⟨α, eBare, hscale, hchart, haction, hα⟩

/-- Eliminate specialization and decomposition witnesses before substituting
concrete normalization rings. Their retained lift assertion is an arbitrary
predicate here and is never expanded by the composition proof. -/
private theorem corrected_coordinates_of_suppliers
    (k F κ Ω : Type) [Field k] [Field F] [Field κ] [Field Ω]
    [Algebra k F] [Algebra k κ] [Algebra k Ω] [Algebra F Ω] [Algebra κ Ω]
    [IsScalarTower k F Ω] [IsScalarTower k κ Ω]
    [IsSepClosure k κ] [IsSepClosure F Ω] [IsSepClosed Ω]
    (X : Scheme) [IsIntegral X] (f : X ⟶ Spec (.of k))
    (x : Spec (.of Ω) ⟶ X) (j : Spec (.of F) ⟶ X)
    (n : ℕ) (w : F) (W : FiniteEtale X)
    (ts : Torsor (rootsOfUnity n κ) ((fiber x).obj W))
    (α : Gal(κ/k))
    (eBare : (fiber x).obj W ≃ {z : Ω // z ^ n = algebraMap F Ω w})
    (hdata : FixedRootSourceData k F κ Ω X f x j n W (algebraMap F Ω w) ts α eBare)
    (D : Subgroup π₁ᵉᵗ(x)) (R : Subgroup Gal(Ω/F))
    (P : Prop) (v : P → k)
    (Lift : ∀ h : P, ({z : Ω // z ^ n = algebraMap F Ω w} ≃
      {z : κ // z ^ n = algebraMap k κ (v h)}) → Prop)
    (hspec : ∃ h : P, ∃ Esp : {z : Ω // z ^ n = algebraMap F Ω w} ≃
      {z : κ // z ^ n = algebraMap k κ (v h)},
      Lift h Esp ∧
      (∀ (ζ : rootsOfUnity n κ) (z : {z : Ω // z ^ n = algebraMap F Ω w}),
        (Esp ⟨algebraMap κ Ω (ζ.val : κ) * z.val, by
          have hζ : (ζ.val : κ) ^ n = 1 :=
            congrArg (fun t : κˣ => (t : κ)) ((mem_rootsOfUnity _ _).mp ζ.property)
          rw [mul_pow, ← map_pow, hζ, map_one, one_mul, z.property]⟩).val =
            (ζ.val : κ) * (Esp z).val) ∧
      ∀ (δ : R) (z : {z : Ω // z ^ n = algebraMap F Ω w}),
        (Esp ⟨δ.val z.val, by rw [← map_pow δ.val, z.property, δ.val.commutes]⟩).val =
          ((δ.val.restrictScalars k).restrictNormal κ) (Esp z).val)
    (hprojection : ∃ hpoint : x = Spec.map (CommRingCat.ofHom (algebraMap F Ω)) ≫ j,
      ∀ γ : π₁ᵉᵗ(x), γ ∈ D ↔ ∃ δ : R,
        continuousConjAut (eqToIso (congrArg fiber hpoint.symm))
          (fieldSourceAbsoluteGaloisHom F Ω j δ.val) = γ) :
    ∃ h : P, ∃ S : (fiber x).obj W → κ,
      (∀ y, S y ^ n = algebraMap k κ (v h)) ∧
      (∀ (ζ : rootsOfUnity n κ) y,
        S (ts.toMulAction.toSMul.smul ζ y) = α (ζ.val : κ) * S y) ∧
      ∀ γ : π₁ᵉᵗ(x), γ ∈ D → ∀ y,
        S (γ • y) = arithmeticFundamentalGroupHom k κ f x γ (S y) := by
  obtain ⟨hscale, hchart, hfield, hα⟩ := hdata
  obtain ⟨h, Esp, _hLift, hEspScale, hEspAction⟩ := hspec
  obtain ⟨hpoint, hraw⟩ := hprojection
  refine ⟨h, ?_⟩
  exact corrected_specialization_coordinates k F κ Ω X f x j n w (v h) W ts
    α hα eBare hscale hchart hfield D R
    (fun γ hγ => (hraw γ).mp hγ) Esp hEspScale hEspAction

/-- Choose the original coordinate and the single correction before any
normalization prime or third cusp is introduced. -/
private theorem bare_fixed_root_source_data
    (k κ : Type) [Field k] [NumberField k]
    [Field κ] [CharZero κ] [IsAlgClosed κ] [Algebra k κ] [IsAlgClosure k κ]
    (s : Finset (Projectivization k (k × k)))
    (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    [Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ω]
    [IsAlgClosure (rationalConfigurationGeometricScheme k κ s).functionField Ω]
    (n : ℕ) (b : Ω) (W : FiniteEtale (rationalConfigurationOpen s : Scheme))
    (ts : Torsor (rootsOfUnity n κ)
      ((fiber (rationalConfigurationArithmeticBasePoint k κ s Ω)).obj W)) :
    let X : Scheme := (rationalConfigurationOpen s : Scheme)
    letI : Algebra X.functionField Ω := rationalConfigurationOriginalAmbientAlgebra k κ s Ω
    letI : Algebra (RatFunc k) Ω := rationalConfigurationArithmeticAmbientAlgebra k κ s Ω
    letI : Algebra κ Ω := rationalConfigurationConstantAmbientAlgebra k κ s Ω
    letI : IsSepClosure X.functionField Ω :=
      (rationalConfigurationOriginalField_suppliers k κ s Ω).2.2.2.2.1
    letI : IsAlgClosure (RatFunc k) Ω :=
      rationalConfigurationAmbient_isAlgClosure_arithmetic k κ s Ω
    letI : IsSepClosure (RatFunc k) Ω := inferInstance
    let x := rationalConfigurationArithmeticBasePoint k κ s Ω
    ArithmeticFiberRootCoordinate κ X Ω n W x b (algebraMap κ Ω) ts →
    ∃ α : Gal(κ/k), ∃ eBare : (fiber x).obj W ≃ {z : Ω // z ^ n = b},
      FixedRootSourceData k (RatFunc k) κ Ω X
        ((rationalConfigurationOpen s).ι ≫ π k 1) x
        (rationalConfigurationArithmeticGenericPoint k s) n W b ts α eBare := by
  intro X
  let : Algebra X.functionField Ω := rationalConfigurationOriginalAmbientAlgebra k κ s Ω
  let : Algebra (RatFunc k) Ω := rationalConfigurationArithmeticAmbientAlgebra k κ s Ω
  let : Algebra κ Ω := rationalConfigurationConstantAmbientAlgebra k κ s Ω
  let : IsSepClosure X.functionField Ω :=
    (rationalConfigurationOriginalField_suppliers k κ s Ω).2.2.2.2.1
  let : IsAlgClosure (RatFunc k) Ω :=
    rationalConfigurationAmbient_isAlgClosure_arithmetic k κ s Ω
  let : IsSepClosure (RatFunc k) Ω := inferInstance
  intro x H
  let : Algebra k Ω := rationalConfigurationBaseAmbientAlgebra k κ s Ω
  let : IsScalarTower k κ Ω :=
    (rationalConfigurationAmbient_scalarTowers k κ s Ω).2.2.2.2.1
  let : IsScalarTower (RatFunc k) X.functionField Ω :=
    (rationalConfigurationOriginalField_suppliers k κ s Ω).1
  exact fixed_root_source_data_of_suppliers k (RatFunc k) κ Ω X
    (rationalConfigurationArithmeticFunctionFieldEquiv k s) rfl
    ((rationalConfigurationOpen s).ι ≫ π k 1) x n W b ts
    (rationalConfigurationOriginalField_suppliers k κ s Ω).2.2.2.2.2.2.1 H

/-- Use the prescribed correction and coordinate at one third cusp. This
phase alone instantiates the original normalization-prime suppliers. -/
private theorem bare_third_cusp_from_fixed_source
    (k κ : Type) [Field k] [NumberField k]
    [Field κ] [CharZero κ] [IsAlgClosed κ] [Algebra k κ] [IsAlgClosure k κ]
    (s : Finset (Projectivization k (k × k))) (a b c : s)
    (hca : c ≠ a) (hcb : c ≠ b)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    [Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ω]
    [IsAlgClosure (rationalConfigurationGeometricScheme k κ s).functionField Ω]
    (m : ℤ) (n : ℕ+)
    (u : Pic0.openKummerUnits k (RatFunc k)
      ((projectiveLineRatFuncModel k).openBoundaryPlaces (rationalConfigurationOpen s).ι) n)
    (hgeom : ∀ P : Place κ (RatFunc κ),
      P.ord (algebraMap (RatFunc k) (RatFunc κ) (u.val : RatFunc k)) =
        m * ((if P = (rationalConfigurationBoundaryPlace k κ s a).val then 1 else 0) -
          (if P = (rationalConfigurationBoundaryPlace k κ s b).val then 1 else 0)))
    (W : FiniteEtale (rationalConfigurationOpen s : Scheme))
    (ts : Torsor (rootsOfUnity (n : ℕ) κ)
      ((fiber (rationalConfigurationArithmeticBasePoint k κ s Ω)).obj W)) :
    let X : Scheme := (rationalConfigurationOpen s : Scheme)
    letI : Algebra (RatFunc k) Ω := rationalConfigurationArithmeticAmbientAlgebra k κ s Ω
    letI : Algebra κ Ω := rationalConfigurationConstantAmbientAlgebra k κ s Ω
    letI : IsAlgClosure (RatFunc k) Ω :=
      rationalConfigurationAmbient_isAlgClosure_arithmetic k κ s Ω
    letI : IsSepClosure (RatFunc k) Ω := inferInstance
    let x := rationalConfigurationArithmeticBasePoint k κ s Ω
    let q := arithmeticFundamentalGroupHom k κ ((rationalConfigurationOpen s).ι ≫ π k 1) x
    ∀ (α : Gal(κ/k))
      (eBare : (fiber x).obj W ≃
        {z : Ω // z ^ (n : ℕ) = algebraMap (RatFunc k) Ω (u.val : RatFunc k)}),
    FixedRootSourceData k (RatFunc k) κ Ω X
        ((rationalConfigurationOpen s).ι ≫ π k 1) x
        (rationalConfigurationArithmeticGenericPoint k s) (n : ℕ) W
        (algebraMap (RatFunc k) Ω (u.val : RatFunc k)) ts α eBare →
      let p := rationalConfigurationBoundaryPlace k κ s c
      let V := (rationalConfiguration_every_boundaryPlace_exists_rationalPlace k κ s p).choose
      let hV : V.IsRational :=
        (rationalConfiguration_every_boundaryPlace_exists_rationalPlace k κ s p).choose_spec.1
      ∃ hu0 : V.ord (u.val : RatFunc k) = 0,
      ∃ S : (fiber x).obj W → κ,
        (∀ y, S y ^ (n : ℕ) = algebraMap k κ (V.ordZeroValue hV u.val hu0 : k)) ∧
        (∀ (ζ : rootsOfUnity (n : ℕ) κ) y,
          S (ts.toMulAction.toSMul.smul ζ y) = α (ζ.val : κ) * S y) ∧
        ∀ (γ : rationalConfigurationArithmeticGroup k κ s Ω),
          γ ∈ rationalConfigurationChosenDecomposition k κ s Ω p →
          ∀ y, S (γ • y) = q γ (S y) := by
  intro X
  let : Algebra (RatFunc k) Ω := rationalConfigurationArithmeticAmbientAlgebra k κ s Ω
  let : Algebra κ Ω := rationalConfigurationConstantAmbientAlgebra k κ s Ω
  let : IsAlgClosure (RatFunc k) Ω :=
    rationalConfigurationAmbient_isAlgClosure_arithmetic k κ s Ω
  let : IsSepClosure (RatFunc k) Ω := inferInstance
  intro x q α eBare hdata p V hV
  let : Algebra (RatFunc κ) Ω := rationalConfigurationGeometricAmbientAlgebra k κ s Ω
  let : Algebra k Ω := rationalConfigurationBaseAmbientAlgebra k κ s Ω
  let ambient := rationalConfigurationAmbient_scalarTowers k κ s Ω
  let : IsScalarTower (RatFunc κ)
      (rationalConfigurationGeometricScheme k κ s).functionField Ω := ambient.1
  let : IsScalarTower κ (RatFunc κ) Ω := ambient.2.1
  let : IsScalarTower κ
      (rationalConfigurationGeometricScheme k κ s).functionField Ω := ambient.2.2.1
  let : IsScalarTower (RatFunc k) (RatFunc κ) Ω := ambient.2.2.2.1
  let : IsScalarTower k κ Ω := ambient.2.2.2.2.1
  let : IsScalarTower k (RatFunc k) Ω := ambient.2.2.2.2.2
  let : IsGalois (RatFunc k) Ω := inferInstance
  exact corrected_coordinates_of_suppliers k (RatFunc k) κ Ω X
    ((rationalConfigurationOpen s).ι ≫ π k 1) x
    (rationalConfigurationArithmeticGenericPoint k s) (n : ℕ) (u.val : RatFunc k) W ts
    α eBare hdata (rationalConfigurationChosenDecomposition k κ s Ω p) _
    (V.ord (u.val : RatFunc k) = 0) (fun hu0 => (V.ordZeroValue hV u.val hu0 : k)) _
    (rationalConfiguration_pair_thirdChosenPrime_rootSpecialization
      k κ s a b c hca hcb Ω m n u hgeom)
    (rationalConfigurationChosenDecomposition_mem_iff_exists_raw k κ s Ω p)

/-- The same actual arithmetic fiber admits root coordinates at all third
cusps, with one fixed arithmetic correction. All values, prime choices and
arithmetic actions are supplied by the original geometric constructions. -/
theorem rationalConfiguration_pair_thirdCusp_fiberCoordinates
    (k κ : Type) [Field k] [NumberField k]
    [Field κ] [CharZero κ] [IsAlgClosed κ] [Algebra k κ] [IsAlgClosure k κ]
    (s : Finset (Projectivization k (k × k))) (a b : s)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    [Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ω]
    [IsAlgClosure (rationalConfigurationGeometricScheme k κ s).functionField Ω]
    (m : ℤ) (n : ℕ+)
    (u : Pic0.openKummerUnits k (RatFunc k)
      ((projectiveLineRatFuncModel k).openBoundaryPlaces (rationalConfigurationOpen s).ι) n)
    (hgeom : ∀ P : Place κ (RatFunc κ),
      P.ord (algebraMap (RatFunc k) (RatFunc κ) (u.val : RatFunc k)) =
        m * ((if P = (rationalConfigurationBoundaryPlace k κ s a).val then 1 else 0) -
          (if P = (rationalConfigurationBoundaryPlace k κ s b).val then 1 else 0)))
    (W : FiniteEtale (rationalConfigurationOpen s : Scheme))
    (ts : Torsor (rootsOfUnity (n : ℕ) κ)
      ((fiber (rationalConfigurationArithmeticBasePoint k κ s Ω)).obj W)) :
    let X : Scheme := (rationalConfigurationOpen s : Scheme)
    letI : Algebra X.functionField Ω := rationalConfigurationOriginalAmbientAlgebra k κ s Ω
    letI : Algebra (RatFunc k) Ω := rationalConfigurationArithmeticAmbientAlgebra k κ s Ω
    letI : Algebra κ Ω := rationalConfigurationConstantAmbientAlgebra k κ s Ω
    letI : IsSepClosure X.functionField Ω :=
      (rationalConfigurationOriginalField_suppliers k κ s Ω).2.2.2.2.1
    let x := rationalConfigurationArithmeticBasePoint k κ s Ω
    let q := arithmeticFundamentalGroupHom k κ ((rationalConfigurationOpen s).ι ≫ π k 1) x
    ArithmeticFiberRootCoordinate κ X Ω (n : ℕ) W x
      (algebraMap (RatFunc k) Ω (u.val : RatFunc k)) (algebraMap κ Ω) ts →
    ∃ α : Gal(κ/k), ∀ (c : s), c ≠ a → c ≠ b →
      let p := rationalConfigurationBoundaryPlace k κ s c
      let V := (rationalConfiguration_every_boundaryPlace_exists_rationalPlace k κ s p).choose
      let hV : V.IsRational :=
        (rationalConfiguration_every_boundaryPlace_exists_rationalPlace k κ s p).choose_spec.1
      ∃ hu0 : V.ord (u.val : RatFunc k) = 0,
      ∃ S : (fiber x).obj W → κ,
        (∀ y, S y ^ (n : ℕ) = algebraMap k κ (V.ordZeroValue hV u.val hu0 : k)) ∧
        (∀ (ζ : rootsOfUnity (n : ℕ) κ) y,
          S (ts.toMulAction.toSMul.smul ζ y) = α (ζ.val : κ) * S y) ∧
        ∀ (γ : rationalConfigurationArithmeticGroup k κ s Ω),
          γ ∈ rationalConfigurationChosenDecomposition k κ s Ω p →
          ∀ y, S (γ • y) = q γ (S y) := by
  intro X
  let : Algebra X.functionField Ω := rationalConfigurationOriginalAmbientAlgebra k κ s Ω
  let : Algebra (RatFunc k) Ω := rationalConfigurationArithmeticAmbientAlgebra k κ s Ω
  let : Algebra κ Ω := rationalConfigurationConstantAmbientAlgebra k κ s Ω
  let : IsSepClosure X.functionField Ω :=
    (rationalConfigurationOriginalField_suppliers k κ s Ω).2.2.2.2.1
  intro x q H
  let : IsAlgClosure (RatFunc k) Ω :=
    rationalConfigurationAmbient_isAlgClosure_arithmetic k κ s Ω
  let : IsSepClosure (RatFunc k) Ω := inferInstance
  obtain ⟨α, eBare, hdata⟩ := bare_fixed_root_source_data k κ s Ω (n : ℕ)
    (algebraMap (RatFunc k) Ω (u.val : RatFunc k)) W ts H
  refine ⟨α, ?_⟩
  intro c hca hcb
  exact bare_third_cusp_from_fixed_source k κ s a b c hca hcb Ω m n u hgeom W ts
    α eBare hdata

end AnabelianGeometry.WeightFiltration
