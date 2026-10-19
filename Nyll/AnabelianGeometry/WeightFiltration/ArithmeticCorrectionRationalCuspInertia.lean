/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.BareRationalCuspDecompositionProjection
import Nyll.AnabelianGeometry.WeightFiltration.BareRationalCuspDecomposition
import Nyll.EtaleFundamentalGroups.GeometricFiber.ArithmeticExactSequence

/-! # Geometric inertia conjugators from arithmetic corrections -/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.FiniteEtale AlgebraicGeometry.ProjSpace
open EtaleFundamentalGroups SchemeTheory

namespace AnabelianGeometry.WeightFiltration

private theorem correction_normalizer_map
    {P : Type*} [Group P] (H : Subgroup P) (d : P)
    (hd : d ∈ Subgroup.normalizer (H : Set P)) :
    H.map (MulAut.conj d).toMonoidHom = H := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.mem_set_normalizer_iff.mp hd x).mp hx
  · intro x hx
    refine ⟨d⁻¹ * x * d, ?_, ?_⟩
    · have hd' := (Subgroup.normalizer (H : Set P)).inv_mem hd
      simpa only [inv_inv] using (Subgroup.mem_set_normalizer_iff.mp hd' x).mp hx
    · change d * (d⁻¹ * x * d) * d⁻¹ = x
      simp only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left]

theorem arithmeticCorrection_exists_geometric_inertia_conjugator
    {G P Γ : Type*} [Group G] [Group P] [Group Γ]
    (i : G →* P) (q : P →* Γ) (hexact : i.range = q.ker)
    (I : Subgroup G) (D : Subgroup P)
    (hDN : D ≤ Subgroup.normalizer (I.map i : Set P))
    (hfull : Function.Surjective (fun d : D => q d.val)) (c : P) :
    ∃ (g : G) (d : D), q d.val = q c ∧ i g = c * d.val⁻¹ ∧
      (I.map i).map (MulAut.conj c).toMonoidHom =
        (I.map i).map (MulAut.conj (i g)).toMonoidHom := by
  obtain ⟨d, hd⟩ := hfull (q c)
  change q d.val = q c at hd
  have hker : c * d.val⁻¹ ∈ q.ker := by
    change q (c * d.val⁻¹) = 1
    rw [map_mul, map_inv, hd, mul_inv_cancel]
  have hrange : c * d.val⁻¹ ∈ i.range := hexact.symm ▸ hker
  obtain ⟨g, hg⟩ := hrange
  have hprod : i g * d.val = c := by
    rw [hg]
    simp only [mul_assoc, inv_mul_cancel, mul_one]
  refine ⟨g, d, hd, hg, ?_⟩
  calc
    (I.map i).map (MulAut.conj c).toMonoidHom =
        (I.map i).map ((MulAut.conj (i g)).toMonoidHom.comp
          (MulAut.conj d.val).toMonoidHom) := by
      congr 1
      ext x
      change c * x * c⁻¹ = i g * (d.val * x * d.val⁻¹) * (i g)⁻¹
      rw [← hprod]
      simp only [mul_inv_rev, mul_assoc]
    _ = ((I.map i).map (MulAut.conj d.val).toMonoidHom).map
        (MulAut.conj (i g)).toMonoidHom := (Subgroup.map_map _ _ _).symm
    _ = (I.map i).map (MulAut.conj (i g)).toMonoidHom := by
      rw [correction_normalizer_map (I.map i) d.val (hDN d.property)]

attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra
  rationalConfigurationGeometricFieldAlgebra rationalConfigurationGeometricConstantAlgebra
  rationalConfigurationGeometricField_scalarTower

theorem rationalConfiguration_arithmeticCorrection_chosenInertia
    (k κ : Type) [Field k] [NumberField k]
    [Field κ] [CharZero κ] [IsAlgClosed κ] [Algebra k κ] [IsAlgClosure k κ]
    (s : Finset (Projectivization k (k × k))) (hs : 3 ≤ s.card)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    [Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ω]
    [IsAlgClosure (rationalConfigurationGeometricScheme k κ s).functionField Ω]
    (p : (projectiveLineRatFuncModel κ).openBoundaryPlaces
      (rationalConfigurationBaseChangeChart k κ s))
    (c : rationalConfigurationArithmeticGroup k κ s Ω) :
    ∃ g : rationalConfigurationGeometricGroup k κ s Ω,
      ((rationalConfigurationChosenInertia k κ s Ω p).map
        (rationalConfigurationGeometricInclusion k κ s Ω).toMonoidHom).map
          (MulAut.conj c).toMonoidHom =
      ((rationalConfigurationChosenInertia k κ s Ω p).map
        (rationalConfigurationGeometricInclusion k κ s Ω).toMonoidHom).map
          (MulAut.conj (rationalConfigurationGeometricInclusion k κ s Ω g)).toMonoidHom := by
  let i := (rationalConfigurationGeometricInclusion k κ s Ω).toMonoidHom
  let q := (arithmeticFundamentalGroupHom k κ
    ((rationalConfigurationOpen s).ι ≫ π k 1)
    (rationalConfigurationArithmeticBasePoint k κ s Ω)).toMonoidHom
  let I := rationalConfigurationChosenInertia k κ s Ω p
  let D := rationalConfigurationChosenDecomposition k κ s Ω p
  have hex := arithmetic_exactSequence_of_isSepClosure k κ
    (rationalConfigurationOpen s : Scheme) ((rationalConfigurationOpen s).ι ≫ π k 1)
    ((rationalConfigurationGeometricScheme k κ s).genericExtensionMorphism Ω)
  have hDN : D ≤ Subgroup.normalizer (I.map i : Set _) := by
    exact le_of_eq
      (rationalConfigurationChosenDecomposition_eq_normalizer k κ s Ω p hs)
  have hfull : Function.Surjective (fun d : D => q d.val) :=
    rationalConfigurationChosenDecomposition_arithmetic_surjective k κ s Ω p
  obtain ⟨g, _, _, _, hconj⟩ :=
    arithmeticCorrection_exists_geometric_inertia_conjugator i q hex.2.2.symm I D hDN hfull c
  exact ⟨g, hconj⟩

private theorem correction_map_cancel
    {G P : Type*} [Group G] [Group P] (i : G →* P)
    (hi : Function.Injective i) (H K : Subgroup G) (h : H.map i = K.map i) : H = K := by
  apply le_antisymm
  · intro x hx
    have hm : i x ∈ K.map i := h ▸ (show i x ∈ H.map i from ⟨x, hx, rfl⟩)
    obtain ⟨y, hy, hyx⟩ := hm
    exact hi hyx ▸ hy
  · intro x hx
    have hm : i x ∈ H.map i := h.symm ▸ (show i x ∈ K.map i from ⟨x, hx, rfl⟩)
    obtain ⟨y, hy, hyx⟩ := hm
    exact hi hyx ▸ hy

theorem rationalConfiguration_arithmeticCorrection_geometricInertia
    (k κ : Type) [Field k] [NumberField k]
    [Field κ] [CharZero κ] [IsAlgClosed κ] [Algebra k κ] [IsAlgClosure k κ]
    (s : Finset (Projectivization k (k × k))) (hs : 3 ≤ s.card)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    [Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ω]
    [IsAlgClosure (rationalConfigurationGeometricScheme k κ s).functionField Ω]
    (p : (projectiveLineRatFuncModel κ).openBoundaryPlaces
      (rationalConfigurationBaseChangeChart k κ s))
    (c : rationalConfigurationArithmeticGroup k κ s Ω)
    (θ : rationalConfigurationGeometricGroup k κ s Ω →*
      rationalConfigurationGeometricGroup k κ s Ω)
    (hθ : ∀ x, rationalConfigurationGeometricInclusion k κ s Ω (θ x) =
      c * rationalConfigurationGeometricInclusion k κ s Ω x * c⁻¹) :
    ∃ g : rationalConfigurationGeometricGroup k κ s Ω,
      (rationalConfigurationChosenInertia k κ s Ω p).map θ =
        (rationalConfigurationChosenInertia k κ s Ω p).map (MulAut.conj g).toMonoidHom := by
  let i := (rationalConfigurationGeometricInclusion k κ s Ω).toMonoidHom
  let I := rationalConfigurationChosenInertia k κ s Ω p
  obtain ⟨g, hg⟩ := rationalConfiguration_arithmeticCorrection_chosenInertia
    k κ s hs Ω p c
  have hex := arithmetic_exactSequence_of_isSepClosure k κ
    (rationalConfigurationOpen s : Scheme) ((rationalConfigurationOpen s).ι ≫ π k 1)
    ((rationalConfigurationGeometricScheme k κ s).genericExtensionMorphism Ω)
  refine ⟨g, correction_map_cancel i hex.1 (I.map θ)
    (I.map (MulAut.conj g).toMonoidHom) ?_⟩
  have hleft : i.comp θ = (MulAut.conj c).toMonoidHom.comp i := by
    apply MonoidHom.ext
    intro x
    exact hθ x
  have hright : i.comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj (i g)).toMonoidHom.comp i := by
    apply MonoidHom.ext
    intro x
    change i (g * x * g⁻¹) = i g * i x * (i g)⁻¹
    rw [map_mul, map_mul, map_inv]
  calc
    (I.map θ).map i = I.map (i.comp θ) := Subgroup.map_map _ _ _
    _ = I.map ((MulAut.conj c).toMonoidHom.comp i) := congrArg (I.map) hleft
    _ = (I.map i).map (MulAut.conj c).toMonoidHom := (Subgroup.map_map _ _ _).symm
    _ = (I.map i).map (MulAut.conj (i g)).toMonoidHom := hg
    _ = I.map ((MulAut.conj (i g)).toMonoidHom.comp i) := Subgroup.map_map _ _ _
    _ = I.map (i.comp (MulAut.conj g).toMonoidHom) := congrArg (I.map) hright.symm
    _ = (I.map (MulAut.conj g).toMonoidHom).map i := (Subgroup.map_map _ _ _).symm

end AnabelianGeometry.WeightFiltration
