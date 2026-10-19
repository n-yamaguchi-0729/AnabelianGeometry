/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.BareRationalConfigurationBidirectionalCusps
import Nyll.AnabelianGeometry.WeightFiltration.BoundaryInertiaConjugacySeparation

/-! # An actual bijection of the original rational puncture labels

The two recognition directions use one fixed geometric equivalence and its
inverse. Separation of the original inertia conjugacy classes makes the two
chosen boundary maps mutually inverse. The existing boundary-place equivalences
then return a bijection of the original finite configurations.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve AlgebraicGeometry.FiniteEtale
open AlgebraicGeometry.ProjSpace SchemeTheory EtaleFundamentalGroups.Inertia
open scoped RatFunc

namespace AnabelianGeometry.WeightFiltration

private theorem subgroup_map_equiv_symm
    {G H : Type*} [Group G] [Group H] (e : G ≃* H) (A : Subgroup G) :
    (A.map e.toMonoidHom).map e.symm.toMonoidHom = A := by
  rw [Subgroup.map_map]
  have hid : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by
    apply MonoidHom.ext
    intro x
    exact e.symm_apply_apply x
  rw [hid, Subgroup.map_id]

private theorem subgroup_map_conj_equiv
    {G H : Type*} [Group G] [Group H] (e : G ≃* H) (A : Subgroup G) (a : G) :
    (A.map (MulAut.conj a).toMonoidHom).map e.toMonoidHom =
      (A.map e.toMonoidHom).map (MulAut.conj (e a)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  apply MonoidHom.ext
  intro x
  change e (a * x * a⁻¹) = e a * e x * (e a)⁻¹
  simp only [map_mul, map_inv]

private theorem subgroup_map_conj_comp
    {G : Type*} [Group G] (A : Subgroup G) (a b : G) :
    (A.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      A.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  apply MonoidHom.ext
  intro x
  change b * (a * x * a⁻¹) * b⁻¹ = (b * a) * x * (b * a)⁻¹
  simp only [mul_inv_rev, mul_assoc]

private theorem subgroup_conjugacy_roundTrip
    {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (A B : Subgroup G) (C : Subgroup H) (a : H) (b : G)
    (hforward : A.map e.toMonoidHom = C.map (MulAut.conj a).toMonoidHom)
    (hbackward : C.map e.symm.toMonoidHom = B.map (MulAut.conj b).toMonoidHom) :
    A = B.map (MulAut.conj (e.symm a * b)).toMonoidHom := by
  have h := congrArg (fun D : Subgroup H => D.map e.symm.toMonoidHom) hforward
  rw [subgroup_map_equiv_symm, subgroup_map_conj_equiv, hbackward,
    subgroup_map_conj_comp] at h
  exact h

private theorem exists_indexEquiv_of_bidirectional_conjugacy
    {P Q G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (I : P → Subgroup G) (J : Q → Subgroup H)
    (hI : ∀ p p' a, I p = (I p').map (MulAut.conj a).toMonoidHom → p = p')
    (hJ : ∀ q q' a, J q = (J q').map (MulAut.conj a).toMonoidHom → q = q')
    (hforward : ∀ p, ∃ q a, (I p).map e.toMonoidHom =
      (J q).map (MulAut.conj a).toMonoidHom)
    (hbackward : ∀ q, ∃ p b, (J q).map e.symm.toMonoidHom =
      (I p).map (MulAut.conj b).toMonoidHom) :
    ∃ E : P ≃ Q, ∀ p, ∃ a, (I p).map e.toMonoidHom =
      (J (E p)).map (MulAut.conj a).toMonoidHom := by
  classical
  choose f a hf using hforward
  choose g b hg using hbackward
  have hleft : Function.LeftInverse g f := by
    intro p
    exact (hI p (g (f p)) _
      (subgroup_conjugacy_roundTrip e (I p) (I (g (f p))) (J (f p))
        (a p) (b (f p)) (hf p) (hg (f p)))).symm
  have hright : Function.RightInverse g f := by
    intro q
    exact (hJ q (f (g q)) _
      (subgroup_conjugacy_roundTrip e.symm (J q) (J (f (g q))) (I (g q))
        (b q) (a (g q)) (hg q) (hf (g q)))).symm
  exact ⟨⟨f, g, hleft, hright⟩, fun p => ⟨a p, hf p⟩⟩

attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra
  rationalConfigurationGeometricFieldAlgebra rationalConfigurationGeometricConstantAlgebra
  rationalConfigurationGeometricField_scalarTower
  placeBaseAmbientAlgebra placeBaseAmbientTower placeConstantAmbientTower

local instance (priority := 2000) punctureEquivSMulRatFunc
    {A E : Type*} [CommSemiring A] [Field E] [Algebra A (RatFunc E)] :
    SMul A (RatFunc E) := (inferInstance : Algebra A (RatFunc E)).toSMul

/-- The originally chosen inertia subgroups distinguish all original boundary labels. -/
theorem rationalConfigurationChosenInertia_eq_conjugate_imp_eq
    (k κ : Type) [Field k] [Field κ] [CharZero κ] [IsAlgClosed κ]
    [Algebra k κ] [Infinite k]
    (s : Finset (Projectivization k (k × k))) (hs : 3 ≤ s.card)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    [Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ω]
    [IsAlgClosure (rationalConfigurationGeometricScheme k κ s).functionField Ω]
    (p q : (projectiveLineRatFuncModel κ).openBoundaryPlaces
      (rationalConfigurationBaseChangeChart k κ s))
    (a : rationalConfigurationGeometricGroup k κ s Ω)
    (h : rationalConfigurationChosenInertia k κ s Ω p =
      (rationalConfigurationChosenInertia k κ s Ω q).map (MulAut.conj a).toMonoidHom) :
    p = q := by
  let U := rationalConfigurationGeometricScheme k κ s
  let M := projectiveLineRatFuncModel κ
  let j : U ⟶ M.C := rationalConfigurationBaseChangeChart k κ s
  let : IsOpenImmersion j := inferInstanceAs
    (IsOpenImmersion (rationalConfigurationBaseChangeChart k κ s))
  let : CharZero U.functionField := Algebra.charZero_of_charZero (R := κ) (A := U.functionField)
  let : IsSepClosure U.functionField Ω := inferInstance
  let : Algebra (RatFunc κ) Ω := rationalConfigurationGeometricAmbientAlgebra k κ s Ω
  let : Algebra κ Ω := rationalConfigurationConstantAmbientAlgebra k κ s Ω
  let : IsScalarTower (RatFunc κ) U.functionField Ω := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower κ (RatFunc κ) Ω := IsScalarTower.of_algebraMap_eq' rfl
  let : IsAlgClosure (RatFunc κ) Ω :=
    rationalConfigurationAmbient_isAlgClosure_geometric k κ s Ω
  let : IsSepClosure (RatFunc κ) Ω := inferInstance
  let : IsCurveOver κ (RatFunc κ) := AlgebraicCurve.instIsCurveOverRatFunc κ
  let : Finite (M.openBoundaryPlaces j) := rationalConfigurationBoundaryPlaces_finite k κ s
  let Q := M.boundaryNormalizationPrimes (Ω := Ω) j
  let : ∀ p : M.openBoundaryPlaces j, (Q p).IsMaximal := fun p => inferInstance
  have hj : DenseRange j := rationalConfigurationBaseChangeChart_denseRange k κ s
  have hfield : algebraMap (RatFunc κ) U.functionField =
      (j.functionFieldMap hj).comp M.ffEquiv.toRingHom :=
    rationalConfigurationGeometricFunctionFieldEquiv_hfield k κ s
  change genericPlaceInertia U p.val (Q p) =
    (genericPlaceInertia U q.val (Q q)).map (MulAut.conj a).toMonoidHom at h
  exact boundaryPlace_eq_of_inertia_eq_conjugate M j hj hfield Q
    (rationalConfigurationBoundaryPlaces_card_ge_three k κ s hs) p q a h

/-- The bare arithmetic isomorphism supplies a bijection of the original punctures,
with inertia conjugacy measured by the same geometric equivalence for every label. -/
theorem bare_rationalConfiguration_punctureEquiv
    (k κ : Type) [Field k] [NumberField k]
    [Field κ] [CharZero κ] [IsAlgClosed κ] [Algebra k κ] [IsAlgClosure k κ]
    (s t : Finset (Projectivization k (k × k))) (hs : 3 ≤ s.card) (ht : 3 ≤ t.card)
    (Ω₁ Ω₂ : Type) [Field Ω₁] [Field Ω₂] [IsAlgClosed Ω₁] [IsAlgClosed Ω₂]
    [Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ω₁]
    [Algebra (rationalConfigurationGeometricScheme k κ t).functionField Ω₂]
    [IsAlgClosure (rationalConfigurationGeometricScheme k κ s).functionField Ω₁]
    [IsAlgClosure (rationalConfigurationGeometricScheme k κ t).functionField Ω₂]
    (eP : rationalConfigurationArithmeticGroup k κ s Ω₁ ≃ₜ*
      rationalConfigurationArithmeticGroup k κ t Ω₂)
    (hP : ∀ γ,
      arithmeticFundamentalGroupHom k κ ((rationalConfigurationOpen t).ι ≫ π k 1)
        (rationalConfigurationArithmeticBasePoint k κ t Ω₂) (eP γ) =
      arithmeticFundamentalGroupHom k κ ((rationalConfigurationOpen s).ι ≫ π k 1)
        (rationalConfigurationArithmeticBasePoint k κ s Ω₁) γ) :
    ∃ eΔ : rationalConfigurationGeometricGroup k κ s Ω₁ ≃ₜ*
        rationalConfigurationGeometricGroup k κ t Ω₂,
      (∀ v, rationalConfigurationGeometricInclusion k κ t Ω₂ (eΔ v) =
        eP (rationalConfigurationGeometricInclusion k κ s Ω₁ v)) ∧
      ∃ σ : s ≃ t, ∀ p : s,
        ∃ a : rationalConfigurationGeometricGroup k κ t Ω₂,
          (rationalConfigurationChosenInertia k κ s Ω₁
            (rationalConfigurationBoundaryPlace k κ s p)).map eΔ.toMonoidHom =
          (rationalConfigurationChosenInertia k κ t Ω₂
            (rationalConfigurationBoundaryPlace k κ t (σ p))).map
              (MulAut.conj a).toMonoidHom := by
  obtain ⟨eΔ, heΔ, hforward, hbackward⟩ :=
    bare_rationalConfiguration_bidirectionalCusps_recognition k κ s t hs ht Ω₁ Ω₂ eP hP
  obtain ⟨E, hE⟩ := exists_indexEquiv_of_bidirectional_conjugacy eΔ.toMulEquiv
    (rationalConfigurationChosenInertia k κ s Ω₁)
    (rationalConfigurationChosenInertia k κ t Ω₂)
    (rationalConfigurationChosenInertia_eq_conjugate_imp_eq k κ s hs Ω₁)
    (rationalConfigurationChosenInertia_eq_conjugate_imp_eq k κ t ht Ω₂)
    hforward hbackward
  let es := rationalConfigurationBoundaryPlaceEquiv k κ s
  let et := rationalConfigurationBoundaryPlaceEquiv k κ t
  let σ : s ≃ t := es.trans (E.trans et.symm)
  refine ⟨eΔ, heΔ, σ, ?_⟩
  intro p
  obtain ⟨a, ha⟩ := hE (es p)
  refine ⟨a, ?_⟩
  change (rationalConfigurationChosenInertia k κ s Ω₁ (es p)).map eΔ.toMonoidHom =
    (rationalConfigurationChosenInertia k κ t Ω₂
      (et (et.symm (E (es p))))).map (MulAut.conj a).toMonoidHom
  rw [et.apply_symm_apply]
  exact ha

/-- Canonical ambient closures leave only the bare configurations and arithmetic
isomorphism as inputs to the actual puncture bijection. -/
theorem bare_rationalConfiguration_punctureEquiv_canonical
    (k : Type) [Field k] [NumberField k]
    (s t : Finset (Projectivization k (k × k))) (hs : 3 ≤ s.card) (ht : 3 ≤ t.card)
    (eP : rationalConfigurationArithmeticGroup k (AlgebraicClosure k) s
        (rationalConfigurationCanonicalAmbient k s) ≃ₜ*
      rationalConfigurationArithmeticGroup k (AlgebraicClosure k) t
        (rationalConfigurationCanonicalAmbient k t))
    (hP : ∀ γ,
      arithmeticFundamentalGroupHom k (AlgebraicClosure k)
        ((rationalConfigurationOpen t).ι ≫ π k 1)
        (rationalConfigurationArithmeticBasePoint k (AlgebraicClosure k) t
          (rationalConfigurationCanonicalAmbient k t)) (eP γ) =
      arithmeticFundamentalGroupHom k (AlgebraicClosure k)
        ((rationalConfigurationOpen s).ι ≫ π k 1)
        (rationalConfigurationArithmeticBasePoint k (AlgebraicClosure k) s
          (rationalConfigurationCanonicalAmbient k s)) γ) :
    ∃ eΔ : rationalConfigurationGeometricGroup k (AlgebraicClosure k) s
          (rationalConfigurationCanonicalAmbient k s) ≃ₜ*
        rationalConfigurationGeometricGroup k (AlgebraicClosure k) t
          (rationalConfigurationCanonicalAmbient k t),
      (∀ v, rationalConfigurationGeometricInclusion k (AlgebraicClosure k) t
          (rationalConfigurationCanonicalAmbient k t) (eΔ v) =
        eP (rationalConfigurationGeometricInclusion k (AlgebraicClosure k) s
          (rationalConfigurationCanonicalAmbient k s) v)) ∧
      ∃ σ : s ≃ t, ∀ p : s,
        ∃ a : rationalConfigurationGeometricGroup k (AlgebraicClosure k) t
          (rationalConfigurationCanonicalAmbient k t),
          (rationalConfigurationChosenInertia k (AlgebraicClosure k) s
            (rationalConfigurationCanonicalAmbient k s)
            (rationalConfigurationBoundaryPlace k (AlgebraicClosure k) s p)).map
              eΔ.toMonoidHom =
          (rationalConfigurationChosenInertia k (AlgebraicClosure k) t
            (rationalConfigurationCanonicalAmbient k t)
            (rationalConfigurationBoundaryPlace k (AlgebraicClosure k) t (σ p))).map
              (MulAut.conj a).toMonoidHom :=
  bare_rationalConfiguration_punctureEquiv k (AlgebraicClosure k) s t hs ht
    (rationalConfigurationCanonicalAmbient k s)
    (rationalConfigurationCanonicalAmbient k t) eP hP

end AnabelianGeometry.WeightFiltration
