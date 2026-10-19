/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GeometricFiber.ArithmeticKernelEquivalence
import Nyll.AnabelianGeometry.WeightFiltration.OriginalGeometricCuspNormalizer
import Nyll.AnabelianGeometry.WeightFiltration.RationalBoundaryInertiaConjugation
import Mathlib.Topology.Algebra.OpenSubgroup

/-! # The actual transported cusp as arithmetic input

The target closed subgroup is the literal arithmetic image of the transported
original roots parameter. Its normalizer and conjugation law are proved from
the source normalizer and the arithmetic equivalence. No target cusp,
inertia-preservation theorem, or target kernel test is an input.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory AlgebraicCurve
open AlgebraicGeometry.FiniteEtale SchemeTheory EtaleFundamentalGroups.Inertia
open AlgebraicGeometry.SmoothProperCurve

namespace AnabelianGeometry.WeightFiltration

private theorem transported_mem_map_iff
    {P₁ P₂ : Type*} [Group P₁] [Group P₂]
    (e : P₁ ≃* P₂) (H : Subgroup P₁) (x : P₁) :
    e x ∈ H.map e.toMonoidHom ↔ x ∈ H := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    exact e.injective hyx ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

private theorem transported_normalizer_map_iff
    {P₁ P₂ : Type*} [Group P₁] [Group P₂]
    (e : P₁ ≃* P₂) (H : Subgroup P₁) (γ : P₁) :
    e γ ∈ Subgroup.normalizer (H.map e.toMonoidHom : Set P₂) ↔
      γ ∈ Subgroup.normalizer (H : Set P₁) := by
  constructor
  · intro hγ
    apply Subgroup.mem_set_normalizer_iff.mpr
    intro x
    have hx := Subgroup.mem_set_normalizer_iff.mp hγ (e x)
    have hconj : e (γ * x * γ⁻¹) = e γ * e x * (e γ)⁻¹ := by
      simp only [map_mul, map_inv]
    change (e x ∈ H.map e.toMonoidHom ↔
      e γ * e x * (e γ)⁻¹ ∈ H.map e.toMonoidHom) at hx
    rw [← hconj] at hx
    exact (transported_mem_map_iff e H x).symm.trans
      (hx.trans (transported_mem_map_iff e H (γ * x * γ⁻¹)))
  · intro hγ
    apply Subgroup.mem_set_normalizer_iff.mpr
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    have hx := Subgroup.mem_set_normalizer_iff.mp hγ x
    have hconj : e (γ * x * γ⁻¹) = e γ * e x * (e γ)⁻¹ := by
      simp only [map_mul, map_inv]
    change (e x ∈ H.map e.toMonoidHom ↔
      e γ * e x * (e γ)⁻¹ ∈ H.map e.toMonoidHom)
    rw [← hconj]
    exact (transported_mem_map_iff e H x).trans
      (hx.trans (transported_mem_map_iff e H (γ * x * γ⁻¹)).symm)

/-- Transport the original roots map without changing its domain or parameter.
`J` is both the arithmetic range of that map and the `eP`-image of the original
arithmetic inertia. Its normalizer has full quotient image, and its literal
cyclotomic conjugation is obtained for every target normalizer element. -/
theorem transported_originalRoots_arithmetic_data
    {P₁ P₂ G₁ G₂ R Γ : Type*}
    [Group P₁] [TopologicalSpace P₁]
    [Group P₂] [TopologicalSpace P₂] [T2Space P₂]
    [Group G₁] [TopologicalSpace G₁]
    [Group G₂] [TopologicalSpace G₂]
    [Group R] [TopologicalSpace R] [CompactSpace R]
    [Group Γ] [TopologicalSpace Γ]
    (eP : P₁ ≃ₜ* P₂) (eΔ : G₁ ≃ₜ* G₂)
    (i₁ : G₁ →ₜ* P₁) (i₂ : G₂ →ₜ* P₂)
    (p₁ : P₁ →* Γ) (p₂ : P₂ →* Γ)
    (heval : ∀ v, i₂ (eΔ v) = eP (i₁ v))
    (hP : ∀ γ, p₂ (eP γ) = p₁ γ)
    (I₁ : Subgroup G₁) (f₁ : R →ₜ* G₁)
    (hf₁ : f₁.toMonoidHom.range = I₁)
    (rho : Γ → R → R)
    (hfull : ∀ σ : Γ, ∃ γ : P₁,
      γ ∈ Subgroup.normalizer (I₁.map i₁.toMonoidHom : Set P₁) ∧ p₁ γ = σ)
    (hcycl₁ : ∀ γ ∈ Subgroup.normalizer (I₁.map i₁.toMonoidHom : Set P₁),
      ∀ t : R, i₁ (f₁ (rho (p₁ γ) t)) = γ * i₁ (f₁ t) * γ⁻¹) :
    let psi : R →* G₂ := eΔ.toMonoidHom.comp f₁.toMonoidHom
    ∃ J : ClosedSubgroup P₂,
      (J : Subgroup P₂) = (I₁.map i₁.toMonoidHom).map eP.toMonoidHom ∧
      (J : Subgroup P₂) = psi.range.map i₂.toMonoidHom ∧
      (Subgroup.normalizer (J : Set P₂)).map p₂ = ⊤ ∧
      IsOpen (((Subgroup.normalizer (J : Set P₂)).map p₂ : Subgroup Γ) : Set Γ) ∧
      ∀ γ ∈ Subgroup.normalizer (J : Set P₂), ∀ t : R,
        i₂ (psi (rho (p₂ γ) t)) = γ * i₂ (psi t) * γ⁻¹ := by
  intro psi
  let a : R →ₜ* P₂ :=
    { toMonoidHom := i₂.toMonoidHom.comp psi
      continuous_toFun :=
        i₂.continuous_toFun.comp (eΔ.continuous_toFun.comp f₁.continuous_toFun) }
  let J : ClosedSubgroup P₂ :=
    ⟨a.toMonoidHom.range, a.continuous_toFun.isClosedMap.isClosed_range⟩
  have hJ : (J : Subgroup P₂) = (I₁.map i₁.toMonoidHom).map eP.toMonoidHom := by
    apply Subgroup.ext
    intro y
    constructor
    · rintro ⟨t, rfl⟩
      have ht : f₁ t ∈ I₁ := by
        rw [← hf₁]
        exact ⟨t, rfl⟩
      exact ⟨i₁ (f₁ t), ⟨f₁ t, ht, rfl⟩, (heval (f₁ t)).symm⟩
    · rintro ⟨b, ⟨v, hv, rfl⟩, rfl⟩
      rw [← hf₁] at hv
      obtain ⟨t, rfl⟩ := hv
      exact ⟨t, heval (f₁ t)⟩
  have hJrange : (J : Subgroup P₂) = psi.range.map i₂.toMonoidHom := by
    apply Subgroup.ext
    intro y
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨psi t, ⟨t, rfl⟩, rfl⟩
    · rintro ⟨v, ⟨t, rfl⟩, rfl⟩
      exact ⟨t, rfl⟩
  have hnorm (γ : P₁) :
      eP γ ∈ Subgroup.normalizer (J : Set P₂) ↔
        γ ∈ Subgroup.normalizer (I₁.map i₁.toMonoidHom : Set P₁) := by
    change eP γ ∈ Subgroup.normalizer ((J : Subgroup P₂) : Set P₂) ↔ _
    rw [hJ]
    exact transported_normalizer_map_iff eP.toMulEquiv (I₁.map i₁.toMonoidHom) γ
  have htop : (Subgroup.normalizer (J : Set P₂)).map p₂ = ⊤ := by
    apply top_unique
    intro σ _
    obtain ⟨γ, hγ, hσ⟩ := hfull σ
    exact ⟨eP γ, (hnorm γ).mpr hγ, (hP γ).trans hσ⟩
  refine ⟨J, hJ, hJrange, htop, ?_, ?_⟩
  · rw [htop]
    change IsOpen (Set.univ : Set Γ)
    exact isOpen_univ
  · intro γ hγ t
    obtain ⟨δ, rfl⟩ := eP.surjective γ
    have hδ := (hnorm δ).mp hγ
    change i₂ (eΔ (f₁ (rho (p₂ (eP δ)) t))) =
      eP δ * i₂ (eΔ (f₁ t)) * (eP δ)⁻¹
    calc
      i₂ (eΔ (f₁ (rho (p₂ (eP δ)) t))) =
          eP (i₁ (f₁ (rho (p₂ (eP δ)) t))) := heval _
      _ = eP (i₁ (f₁ (rho (p₁ δ) t))) := by rw [hP δ]
      _ = eP (δ * i₁ (f₁ t) * δ⁻¹) := congrArg eP (hcycl₁ δ hδ t)
      _ = eP δ * eP (i₁ (f₁ t)) * (eP δ)⁻¹ := by
        simp only [map_mul, map_inv]
      _ = eP δ * i₂ (eΔ (f₁ t)) * (eP δ)⁻¹ := by rw [heval]

/-- Re-express the source owner's pointed arithmetic group at the canonical
composite point. This is equality transport of a point, not a group-theoretic
inertia-preservation assumption. -/
private theorem normalizer_full_image_at_canonical_point
    (k κ : Type) [Field k] [Field κ] [Algebra k κ] [IsSepClosure k κ]
    {X Y : Scheme} (f : X ⟶ Spec (.of k)) (u : Y ⟶ X)
    {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶ Y) (z : Spec (.of Ω) ⟶ X) (hz : xi ≫ u = z)
    (I : Subgroup (Aut (fiber xi)))
    (hfull : ∀ τ : Gal(κ/k), ∃ γ : Aut (fiber z),
      γ ∈ Subgroup.normalizer
        (I.map (pointedFundamentalGroupHom u xi z hz).toMonoidHom : Set _) ∧
      arithmeticFundamentalGroupHom k κ f z γ = τ) :
    ∀ τ : Gal(κ/k), ∃ γ : Aut (fiber (xi ≫ u)),
      γ ∈ Subgroup.normalizer
        (I.map (fundamentalGroupHom u xi).toMonoidHom : Set _) ∧
      arithmeticFundamentalGroupHom k κ f (xi ≫ u) γ = τ := by
  subst z
  exact hfull

section ActualRationalSource

open scoped RatFunc
attribute [local instance] Polynomial.algebra

local instance (priority := 2000) transportedCuspArithmeticDataSMulRatFunc
    {A E : Type*} [CommSemiring A] [Field E]
    [Algebra A (RatFunc E)] : SMul A (RatFunc E) :=
  (inferInstance : Algebra A (RatFunc E)).toSMul

variable
    (k κ : Type) [Field k] [Field κ] [CharZero κ] [IsAlgClosed κ]
    [Algebra k κ] [IsSepClosure k κ] [IsAlgClosure k κ]
    {C X₁ : Scheme} [IsIntegral C] [IsIntegral X₁]
    [CompactSpace X₁] [QuasiSeparatedSpace X₁]
    (c : C ⟶ Spec (.of k)) (i : X₁ ⟶ C)

variable
    [IsIntegral (Limits.pullback (specMap k κ) (i ≫ c))]
    [CompactSpace ↥(Limits.pullback (specMap k κ) (i ≫ c) : Scheme)]
    [ConnectedSpace ↥(Limits.pullback (specMap k κ) (i ≫ c) : Scheme)]
    (M : CurveModel κ (RatFunc κ))
    (eC : M.C ≅ Limits.pullback c (specMap k κ))
    (heC : eC.hom ≫ Limits.pullback.snd c (specMap k κ) = M.toBase)
    (j : (Limits.pullback (specMap k κ) (i ≫ c)) ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
    (hproj : j ≫ eC.hom ≫ Limits.pullback.fst c (specMap k κ) = (Limits.pullback.snd (specMap k κ)
      (i ≫ c)) ≫ i)
    (hbase : j ≫ M.toBase = Limits.pullback.fst (specMap k κ) (i ≫ c))
    [Algebra (RatFunc κ) (Limits.pullback (specMap k κ) (i ≫ c)).functionField]
    (hfield : algebraMap (RatFunc κ) (Limits.pullback (specMap k κ) (i ≫ c)).functionField =
      (j.functionFieldMap hj).comp M.ffEquiv.toRingHom)
    {Ω : Type} [Field Ω] [IsSepClosed Ω]
    [Algebra (Limits.pullback (specMap k κ) (i ≫ c)).functionField Ω] [Algebra (RatFunc κ) Ω]
    [IsScalarTower (RatFunc κ) (Limits.pullback (specMap k κ) (i ≫ c)).functionField Ω]
    [IsSepClosure (Limits.pullback (specMap k κ) (i ≫ c)).functionField Ω]
    [IsSepClosure (RatFunc κ) Ω]
    [∀ p : M.openBoundaryPlaces j, Algebra p.val.toValuationSubring Ω]
    [∀ p : M.openBoundaryPlaces j, IsScalarTower p.val.toValuationSubring (RatFunc κ) Ω]
    [Algebra κ Ω]
    [∀ p : M.openBoundaryPlaces j, IsScalarTower κ p.val.toValuationSubring Ω]
    (Q : ∀ p : M.openBoundaryPlaces j,
      Ideal (normalizationCommAlgCat p.val.toValuationSubring Ω))
    [∀ p, (Q p).IsMaximal]
    [Finite (M.openBoundaryPlaces j)] [Nontrivial (M.openBoundaryPlaces j)]

local instance transportedCuspArithmeticDataCurve :
    IsCurveOver κ (RatFunc κ) := AlgebraicCurve.instIsCurveOverRatFunc κ

variable
    [Algebra (RatFunc k) Ω] [IsScalarTower (RatFunc k) (RatFunc κ) Ω]
    [Algebra k Ω] [IsScalarTower k κ Ω] [IsScalarTower k (RatFunc k) Ω]
    [IsScalarTower κ (RatFunc κ) Ω]
    [IsGalois (RatFunc k) Ω] [Algebra.IsAlgebraic (RatFunc κ) Ω]
    [IsSepClosure (RatFunc k) Ω]
    (V : Place k (RatFunc k)) (hV : V.IsRational)
    [Algebra V.toValuationSubring Ω]
    [IsScalarTower V.toValuationSubring (RatFunc k) Ω]

include eC heC hproj hbase hV in
/-- Starting with the actual arithmetic fundamental-group equivalence and an
original rational cusp, construct the exact input expected by
`candidate_originalRoots_all_open_relative_tests` on the target.

Both source facts are proved by their geometric owners inside this theorem:
`original_ratFuncPlace_normalizer_full_image` and
`rational_boundaryPlaceInertiaLift_conjugate`. The geometric equivalence is
obtained from `exists_geometricEquiv_equivariant_of_arithmeticEquiv`.
-/
theorem exists_transported_rationalCusp_arithmetic_data
    (hπ : DenseRange (eC.hom ≫ Limits.pullback.fst c (specMap k κ)))
    (e0 : RatFunc k ≃+* C.functionField)
    (hchart : ∀ x : RatFunc k,
      (eC.hom ≫ Limits.pullback.fst c (specMap k κ)).functionFieldMap hπ (e0 x) =
        M.ffEquiv (algebraMap (RatFunc k) (RatFunc κ) x))
    (p : M.openBoundaryPlaces j)
    (hord : ∀ x : RatFunc k,
      p.val.ord (algebraMap (RatFunc k) (RatFunc κ) x) = V.ord x)
    (jgeom : Spec (.of (RatFunc κ)) ⟶ (Limits.pullback (specMap k κ) (i ≫ c)))
    (jarith : Spec (.of (RatFunc k)) ⟶ X₁)
    (hchartpoint : ((Limits.pullback (specMap k κ) (i ≫ c)).genericExtensionMorphism Ω) ≫ 𝟙
      (Limits.pullback (specMap k κ) (i ≫ c)) =
      Spec.map (CommRingCat.ofHom (algebraMap (RatFunc κ) Ω)) ≫ jgeom)
    (hpoint : (Spec.map (CommRingCat.ofHom (algebraMap (RatFunc κ) Ω)) ≫ jgeom) ≫
      (Limits.pullback.snd (specMap k κ) (i ≫ c)) =
      Spec.map (CommRingCat.ofHom (algebraMap (RatFunc k) Ω)) ≫ jarith)
    (hbasearith : (Spec.map (CommRingCat.ofHom (algebraMap (RatFunc k) Ω)) ≫ jarith) ≫
      (i ≫ c) = Spec.map (CommRingCat.ofHom (algebraMap k Ω)))
    (X₂ : Scheme) [CompactSpace X₂] [QuasiSeparatedSpace X₂]
    (f₂ : X₂ ⟶ Spec (.of k))
    [ConnectedSpace ↥(Limits.pullback (specMap k κ) f₂ : Scheme)]
    {Ω₂ : Type} [Field Ω₂] [IsSepClosed Ω₂]
    (xi₂ : Spec (.of Ω₂) ⟶ Limits.pullback (specMap k κ) f₂)
    (eP : Aut (fiber (((Limits.pullback (specMap k κ) (i ≫ c)).genericExtensionMorphism Ω) ≫
      (Limits.pullback.snd (specMap k κ) (i ≫ c)))) ≃ₜ*
      Aut (fiber (xi₂ ≫ Limits.pullback.snd (specMap k κ) f₂)))
    (hP : ∀ γ, arithmeticFundamentalGroupHom k κ f₂
      (xi₂ ≫ Limits.pullback.snd (specMap k κ) f₂) (eP γ) =
        arithmeticFundamentalGroupHom k κ (i ≫ c) (((Limits.pullback (specMap k κ) (i ≫
          c)).genericExtensionMorphism Ω) ≫ (Limits.pullback.snd (specMap k κ) (i ≫ c))) γ) :
    ∃ eΔ : Aut (fiber ((Limits.pullback (specMap k κ) (i ≫ c)).genericExtensionMorphism Ω)) ≃ₜ*
      Aut (fiber xi₂),
      (∀ v, fundamentalGroupHom (Limits.pullback.snd (specMap k κ) f₂) xi₂ (eΔ v) =
        eP (fundamentalGroupHom (Limits.pullback.snd (specMap k κ) (i ≫ c)) ((Limits.pullback
          (specMap k κ) (i ≫ c)).genericExtensionMorphism Ω) v)) ∧
      let psi := eΔ.toMonoidHom.comp (boundaryPlaceInertiaLift M j hj hfield Q p).toMonoidHom
      ∃ J : ClosedSubgroup (Aut (fiber (xi₂ ≫ Limits.pullback.snd (specMap k κ) f₂))),
        (J : Subgroup _) = ((genericPlaceInertia (Limits.pullback (specMap k κ) (i ≫ c)) p.val (Q
          p)).map
          (fundamentalGroupHom (Limits.pullback.snd (specMap k κ) (i ≫ c)) ((Limits.pullback
            (specMap k κ) (i ≫ c)).genericExtensionMorphism Ω)).toMonoidHom).map eP.toMonoidHom ∧
        (J : Subgroup _) = psi.range.map
          (fundamentalGroupHom (Limits.pullback.snd (specMap k κ) f₂) xi₂).toMonoidHom ∧
        (Subgroup.normalizer (J : Set _)).map
          (arithmeticFundamentalGroupHom k κ f₂
            (xi₂ ≫ Limits.pullback.snd (specMap k κ) f₂)).toMonoidHom = ⊤ ∧
        IsOpen (((Subgroup.normalizer (J : Set _)).map
          (arithmeticFundamentalGroupHom k κ f₂
            (xi₂ ≫ Limits.pullback.snd (specMap k κ) f₂)).toMonoidHom :
              Subgroup Gal(κ/k)) : Set Gal(κ/k)) ∧
        ∀ γ ∈ Subgroup.normalizer (J : Set _), ∀ t,
          fundamentalGroupHom (Limits.pullback.snd (specMap k κ) f₂) xi₂
            (psi (primeToRootsCoefficientMap κ κ
              (arithmeticFundamentalGroupHom k κ f₂
                (xi₂ ≫ Limits.pullback.snd (specMap k κ) f₂) γ).toRingHom t)) =
            γ * fundamentalGroupHom (Limits.pullback.snd (specMap k κ) f₂) xi₂ (psi t) * γ⁻¹ := by
  obtain ⟨eΔ, heval, _hequiv⟩ :=
    exists_geometricEquiv_equivariant_of_arithmeticEquiv
      k κ X₁ X₂ (i ≫ c) f₂ ((Limits.pullback (specMap k κ) (i ≫ c)).genericExtensionMorphism Ω)
        xi₂ eP hP
  refine ⟨eΔ, heval, ?_⟩
  have hsurj : Function.Surjective (algebraMap (RatFunc κ) (Limits.pullback (specMap k κ) (i ≫
    c)).functionField) := by
    rw [hfield]
    exact (j.functionFieldRingEquivOfIsOpenImmersion).surjective.comp M.ffEquiv.surjective
  let xarith := Spec.map (CommRingCat.ofHom (algebraMap (RatFunc k) Ω)) ≫ jarith
  have hgeneric : ((Limits.pullback (specMap k κ) (i ≫ c)).genericExtensionMorphism Ω) ≫
    (Limits.pullback.snd (specMap k κ) (i ≫ c)) = xarith := by
    dsimp only [xarith]
    rw [← hpoint, ← hchartpoint, Category.comp_id]
  have hfull_chart := original_ratFuncPlace_normalizer_full_image
    V hV p.val hord (Q p) hsurj (i ≫ c) (Limits.pullback.snd (specMap k κ) (i ≫ c)) jgeom jarith
      hchartpoint hpoint hbasearith
  have hfull : ∀ τ : Gal(κ/k), ∃ γ : Aut (fiber (((Limits.pullback (specMap k κ) (i ≫
    c)).genericExtensionMorphism Ω) ≫ (Limits.pullback.snd (specMap k κ) (i ≫ c)))),
      γ ∈ Subgroup.normalizer ((genericPlaceInertia (Limits.pullback (specMap k κ) (i ≫ c)) p.val
        (Q p)).map
        (fundamentalGroupHom (Limits.pullback.snd (specMap k κ) (i ≫ c)) ((Limits.pullback
          (specMap k κ) (i ≫ c)).genericExtensionMorphism Ω)).toMonoidHom : Set _) ∧
      arithmeticFundamentalGroupHom k κ (i ≫ c) (((Limits.pullback (specMap k κ) (i ≫
        c)).genericExtensionMorphism Ω) ≫ (Limits.pullback.snd (specMap k κ) (i ≫ c))) γ = τ :=
    normalizer_full_image_at_canonical_point k κ (i ≫ c) (Limits.pullback.snd (specMap k κ) (i ≫
      c)) ((Limits.pullback (specMap k κ) (i ≫ c)).genericExtensionMorphism Ω) xarith hgeneric
      (genericPlaceInertia (Limits.pullback (specMap k κ) (i ≫ c)) p.val (Q p)) hfull_chart
  have hcycl₁ := rational_boundaryPlaceInertiaLift_conjugate
    k κ c i M eC heC j hj hproj hbase hfield Q hπ e0 hchart V hV p hord
  exact transported_originalRoots_arithmetic_data eP eΔ
    (fundamentalGroupHom (Limits.pullback.snd (specMap k κ) (i ≫ c)) ((Limits.pullback (specMap k
      κ) (i ≫ c)).genericExtensionMorphism Ω))
    (fundamentalGroupHom (Limits.pullback.snd (specMap k κ) f₂) xi₂)
    (arithmeticFundamentalGroupHom k κ (i ≫ c) (((Limits.pullback (specMap k κ) (i ≫
      c)).genericExtensionMorphism Ω) ≫ (Limits.pullback.snd (specMap k κ) (i ≫ c)))).toMonoidHom
    (arithmeticFundamentalGroupHom k κ f₂
      (xi₂ ≫ Limits.pullback.snd (specMap k κ) f₂)).toMonoidHom
    heval hP (genericPlaceInertia (Limits.pullback (specMap k κ) (i ≫ c)) p.val (Q p))
    (boundaryPlaceInertiaLift M j hj hfield Q p)
    (boundaryPlaceInertiaLift_range M j hj hfield Q p)
    (fun τ t => primeToRootsCoefficientMap κ κ τ.toRingHom t)
    hfull hcycl₁

end ActualRationalSource

end AnabelianGeometry.WeightFiltration
