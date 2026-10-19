/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GeometricFiber.ArithmeticNaturality
import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldFunctoriality

/-!
# Arithmetic maps over an actual extension of the base field

The two arithmetic maps use independently chosen comparisons of fiber functors.
For a commuting scheme square over a tower of fields, their discrepancy is one
explicit, uniform inner conjugation. The actual scheme morphism and geometric
point are retained throughout.

-/

noncomputable section

universe u u₁ u₂ v₁ v₂ w

open CategoryTheory CategoryTheory.PreGaloisCategory

private theorem autHomOfCompIso_trans_target
    {C : Type u₁} [Category.{u₂} C]
    {D : Type v₁} [Category.{v₂} D]
    (H : C ⥤ D)
    {F G : C ⥤ FintypeCat.{w}} {F' : D ⥤ FintypeCat.{w}}
    (t : H ⋙ F' ≅ F) (r : F ≅ G) (σ : Aut F') :
    autHomOfCompIso H (t ≪≫ r) σ =
      r.conjAut (autHomOfCompIso H t σ) := by
  simp only [autHomOfCompIso_apply, Iso.trans_conjAut]

private theorem autHomOfCompIso_whiskerLeft_trans
    {C : Type u₁} [Category.{u₂} C]
    {D : Type v₁} [Category.{v₂} D]
    (H : C ⥤ D)
    {F : C ⥤ FintypeCat.{w}} {F' G' : D ⥤ FintypeCat.{w}}
    (t : F' ≅ G') (r : H ⋙ G' ≅ F) (σ : Aut F') :
    autHomOfCompIso H (Functor.isoWhiskerLeft H t ≪≫ r) σ =
      autHomOfCompIso H r (t.conjAut σ) := by
  simp only [autHomOfCompIso_apply, Iso.trans_conjAut]
  exact congrArg r.conjAut
    (Functor.map_conjAut
      ((Functor.whiskeringLeft C D FintypeCat.{w}).obj H) t σ).symm

namespace AlgebraicGeometry.FiniteEtale

/-- Evaluate the arithmetic map in the canonical automorphism group. This
helper unfolds only the arithmetic map and its chosen field identification. -/
private theorem absoluteGaloisToFiberAut_arithmeticFundamentalGroupHom
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    [IsSepClosure k K] [IsSepClosed K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶ X) (γ : π₁ᵉᵗ(xi)) :
    absoluteGaloisToFiberAutMulEquiv k K ‹IsSepClosed K›
        (arithmeticFundamentalGroupHom k K f xi γ) =
      ((nonempty_fiber_iso (xi ≫ f) (ξ k K)).some).conjAut
        (fundamentalGroupHom f xi γ) := by
  let t : fiber (xi ≫ f) ≅ fib k K :=
    (nonempty_fiber_iso (xi ≫ f) (ξ k K)).some
  change (toAutHomeo (fib k K) (K ≃ₐ[k] K))
      ((toAutHomeo (fib k K) (K ≃ₐ[k] K)).symm
        ((continuousConjAut t) (fundamentalGroupHom f xi γ))) = _
  exact (toAutHomeo (fib k K) (K ≃ₐ[k] K)).apply_symm_apply _

/-- For an actual scheme square over `k → E`, restriction of the arithmetic
map over `E` agrees, up to one uniform inner conjugation, with the arithmetic
map over `k` composed with the actual pointed fundamental-group map.

The conjugator is obtained from the two fiber-functor comparisons; no
comparison equation or arithmetic-preservation hypothesis is supplied. -/
theorem arithmeticFundamentalGroupHom_fieldExtension_conjugate
    (k E κ : Type u) [Field k] [Field E] [Field κ]
    [Algebra k E] [Algebra E κ] [Algebra k κ]
    [IsScalarTower k E κ]
    [IsSepClosure k κ] [IsSepClosure E κ]
    {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (c : Y ⟶ Spec (.of E))
    (a : Y ⟶ X)
    (ha : a ≫ f = c ≫ Spec.map (CommRingCat.ofHom (algebraMap k E)))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (xiY : Spec (.of Ω) ⟶ Y) :
    ∃ α : Gal(κ/k), ∀ γ : π₁ᵉᵗ(xiY),
      (arithmeticFundamentalGroupHom E κ c xiY γ).restrictScalars k =
        α * arithmeticFundamentalGroupHom k κ f (xiY ≫ a)
          (fundamentalGroupHom a xiY γ) * α⁻¹ := by
  let : IsSepClosed κ := IsSepClosure.sep_closed k
  let b : Spec (.of E) ⟶ Spec (.of k) := ξ k E
  let z : Spec (.of Ω) ⟶ Spec (.of E) := xiY ≫ c
  let H := pullback b
  let eE : Gal(κ/E) ≃* Aut (fib E κ) :=
    absoluteGaloisToFiberAutMulEquiv E κ (IsSepClosure.sep_closed k)
  let eK : Gal(κ/k) ≃* Aut (fib k κ) :=
    absoluteGaloisToFiberAutMulEquiv k κ (IsSepClosure.sep_closed k)
  let tE : fiber z ≅ fib E κ :=
    (nonempty_fiber_iso z (ξ E κ)).some
  let tK : fiber (z ≫ b) ≅ fib k κ :=
    (nonempty_fiber_iso (z ≫ b) (ξ k κ)).some
  let r : H ⋙ fib E κ ≅ fib k κ := fieldPullbackFiberIso k E κ
  let T₁ : H ⋙ fiber z ≅ fib k κ := pullbackFiberIso b z ≪≫ tK
  let T₂ : H ⋙ fiber z ≅ fib k κ := Functor.isoWhiskerLeft H tE ≪≫ r
  let β : Aut (fib k κ) := T₁.symm ≪≫ T₂
  let α : Gal(κ/k) := eK.symm β
  have hE (γ : π₁ᵉᵗ(xiY)) :
      eE (arithmeticFundamentalGroupHom E κ c xiY γ) =
        tE.conjAut (fundamentalGroupHom c xiY γ) :=
    absoluteGaloisToFiberAut_arithmeticFundamentalGroupHom E κ c xiY γ
  have hK (δ : π₁ᵉᵗ(z)) :
      eK (arithmeticFundamentalGroupHom k κ b z δ) =
        tK.conjAut (fundamentalGroupHom b z δ) :=
    absoluteGaloisToFiberAut_arithmeticFundamentalGroupHom k κ b z δ
  have hT₁ (δ : π₁ᵉᵗ(z)) :
      autHomOfCompIso H T₁ δ =
        eK (arithmeticFundamentalGroupHom k κ b z δ) := by
    exact (autHomOfCompIso_trans_target H (pullbackFiberIso b z) tK δ).trans
      (hK δ).symm
  have hcore (γ : π₁ᵉᵗ(xiY)) :
      eK ((arithmeticFundamentalGroupHom E κ c xiY γ).restrictScalars k) =
        MulAut.conj β
          (eK (arithmeticFundamentalGroupHom k κ b z
            (fundamentalGroupHom c xiY γ))) := by
    calc
      eK ((arithmeticFundamentalGroupHom E κ c xiY γ).restrictScalars k) =
          autHomOfCompIso H r
            (eE (arithmeticFundamentalGroupHom E κ c xiY γ)) :=
        (fieldFundamentalGroupHom_toAutMulEquiv k E κ
          (arithmeticFundamentalGroupHom E κ c xiY γ)).symm
      _ = autHomOfCompIso H T₂ (fundamentalGroupHom c xiY γ) := by
        rw [hE]
        exact (autHomOfCompIso_whiskerLeft_trans H tE r
          (fundamentalGroupHom c xiY γ)).symm
      _ = MulAut.conj β (autHomOfCompIso H T₁
          (fundamentalGroupHom c xiY γ)) :=
        autHomOfCompIso_eq_conj H T₁ T₂ (fundamentalGroupHom c xiY γ)
      _ = MulAut.conj β
          (eK (arithmeticFundamentalGroupHom k κ b z
            (fundamentalGroupHom c xiY γ))) := by rw [hT₁]
  have ha' : a ≫ f = c ≫ b := ha
  have harithmetic (γ : π₁ᵉᵗ(xiY)) :
      arithmeticFundamentalGroupHom k κ f (xiY ≫ a)
          (fundamentalGroupHom a xiY γ) =
        arithmeticFundamentalGroupHom k κ b z
          (fundamentalGroupHom c xiY γ) := by
    calc
      arithmeticFundamentalGroupHom k κ f (xiY ≫ a)
          (fundamentalGroupHom a xiY γ) =
          arithmeticFundamentalGroupHom k κ (a ≫ f) xiY γ :=
        arithmeticFundamentalGroupHom_comp k κ a f xiY γ
      _ = arithmeticFundamentalGroupHom k κ (c ≫ b) xiY γ := by rw [ha']
      _ = arithmeticFundamentalGroupHom k κ b z
          (fundamentalGroupHom c xiY γ) :=
        (arithmeticFundamentalGroupHom_comp k κ c b xiY γ).symm
  refine ⟨α, fun γ => ?_⟩
  rw [harithmetic]
  have h := congrArg eK.symm (hcore γ)
  simpa only [MulAut.conj_apply, map_mul, map_inv,
    MulEquiv.symm_apply_apply, α] using h

/-- The actual field-extension square preserves exactly the geometric kernel. -/
theorem arithmeticFundamentalGroupHom_fieldExtension_ker_comap
    (k E κ : Type u) [Field k] [Field E] [Field κ]
    [Algebra k E] [Algebra E κ] [Algebra k κ]
    [IsScalarTower k E κ]
    [IsSepClosure k κ] [IsSepClosure E κ]
    {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (c : Y ⟶ Spec (.of E))
    (a : Y ⟶ X)
    (ha : a ≫ f = c ≫ Spec.map (CommRingCat.ofHom (algebraMap k E)))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (xiY : Spec (.of Ω) ⟶ Y) :
    (arithmeticFundamentalGroupHom k κ f (xiY ≫ a)).ker.comap
        (fundamentalGroupHom a xiY).toMonoidHom =
      (arithmeticFundamentalGroupHom E κ c xiY).ker := by
  obtain ⟨α, hα⟩ :=
    arithmeticFundamentalGroupHom_fieldExtension_conjugate k E κ f c a ha xiY
  ext γ
  change arithmeticFundamentalGroupHom k κ f (xiY ≫ a)
      (fundamentalGroupHom a xiY γ) = 1 ↔
    arithmeticFundamentalGroupHom E κ c xiY γ = 1
  constructor
  · intro hγ
    have hr : (arithmeticFundamentalGroupHom E κ c xiY γ).restrictScalars k = 1 := by
      rw [hα γ, hγ]
      simpa only [mul_one] using mul_inv_cancel α
    apply AlgEquiv.ext
    intro x
    exact congrArg (fun z : Gal(κ/k) => z x) hr
  · intro hγ
    have hc : α * arithmeticFundamentalGroupHom k κ f (xiY ≫ a)
        (fundamentalGroupHom a xiY γ) * α⁻¹ = 1 := by
      rw [← hα γ, hγ]
      rfl
    have h := congrArg (fun z : Gal(κ/k) => α⁻¹ * z * α) hc
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one,
      mul_inv_cancel_left, one_mul] using h

end AlgebraicGeometry.FiniteEtale
