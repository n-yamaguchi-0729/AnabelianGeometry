/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GeometricFiber.ArithmeticNaturality
import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldFunctoriality

/-!
# The explicit finite-base fibre comparison and its conjugator

Retain the exact comparison behind the uniform arithmetic conjugation. This
makes its action on the original constant-cover point available for proving
that the conjugator fixes the same finite field, rather than postulating it.

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

/-- The two original comparisons between the same constant-fibre functors. -/
def fieldExtensionFiberComparison
    (k E κ : Type u) [Field k] [Field E] [Field κ]
    [Algebra k E] [Algebra E κ] [Algebra k κ] [IsScalarTower k E κ]
    [IsSepClosed κ]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (z : Spec (.of Ω) ⟶ Spec (.of E)) : Aut (fib k κ) :=
  ((pullbackFiberIso (ξ k E) z) ≪≫
    (nonempty_fiber_iso (z ≫ ξ k E) (ξ k κ)).some).symm ≪≫
      (Functor.isoWhiskerLeft (pullback (ξ k E))
        (nonempty_fiber_iso z (ξ E κ)).some ≪≫ fieldPullbackFiberIso k E κ)

/-- The corresponding actual automorphism of the fixed common closure. -/
def fieldExtensionComparisonConjugator
    (k E κ : Type u) [Field k] [Field E] [Field κ]
    [Algebra k E] [Algebra E κ] [Algebra k κ] [IsScalarTower k E κ]
    [IsSepClosure k κ] [IsSepClosed κ]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (z : Spec (.of Ω) ⟶ Spec (.of E)) : Gal(κ/k) :=
  (absoluteGaloisToFiberAutMulEquiv k κ ‹IsSepClosed κ›).symm
    (fieldExtensionFiberComparison k E κ z)

/-- Its action on every constant-cover point is the retained comparison. -/
theorem fieldExtensionComparisonConjugator_toAut
    (k E κ : Type u) [Field k] [Field E] [Field κ]
    [Algebra k E] [Algebra E κ] [Algebra k κ] [IsScalarTower k E κ]
    [IsSepClosure k κ] [IsSepClosed κ]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (z : Spec (.of Ω) ⟶ Spec (.of E)) :
    absoluteGaloisToFiberAutMulEquiv k κ ‹IsSepClosed κ›
      (fieldExtensionComparisonConjugator k E κ z) =
        fieldExtensionFiberComparison k E κ z :=
  (absoluteGaloisToFiberAutMulEquiv k κ ‹IsSepClosed κ›).apply_symm_apply _


/-- The conjugator sends the first comparison's original point to the second
comparison's point, uniformly for every actual constant cover. -/
theorem fieldExtensionComparisonConjugator_smul
    (k E κ : Type u) [Field k] [Field E] [Field κ]
    [Algebra k E] [Algebra E κ] [Algebra k κ] [IsScalarTower k E κ]
    [IsSepClosure k κ] [IsSepClosed κ]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (z : Spec (.of Ω) ⟶ Spec (.of E))
    (A : FiniteEtale (Spec (.of k)))
    (x : (fiber z).obj ((pullback (ξ k E)).obj A)) :
    fieldExtensionComparisonConjugator k E κ z •
      (((pullbackFiberIso (ξ k E) z) ≪≫
        (nonempty_fiber_iso (z ≫ ξ k E) (ξ k κ)).some).hom.app A x) =
      ((Functor.isoWhiskerLeft (pullback (ξ k E))
        (nonempty_fiber_iso z (ξ E κ)).some ≪≫
          fieldPullbackFiberIso k E κ).hom.app A x) := by
  let T₁ := (pullbackFiberIso (ξ k E) z) ≪≫
    (nonempty_fiber_iso (z ≫ ξ k E) (ξ k κ)).some
  let T₂ := Functor.isoWhiskerLeft (pullback (ξ k E))
    (nonempty_fiber_iso z (ξ E κ)).some ≪≫ fieldPullbackFiberIso k E κ
  change (absoluteGaloisToFiberAutMulEquiv k κ ‹IsSepClosed κ›
    (fieldExtensionComparisonConjugator k E κ z)).hom.app A (T₁.hom.app A x) =
      T₂.hom.app A x
  rw [fieldExtensionComparisonConjugator_toAut]
  change T₂.hom.app A (T₁.inv.app A (T₁.hom.app A x)) = T₂.hom.app A x
  exact congrArg (T₂.hom.app A) (FintypeCat.hom_inv_id_apply (T₁.app A) x)

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
theorem fieldExtensionComparisonConjugator_arithmetic
    (k E κ : Type u) [Field k] [Field E] [Field κ]
    [Algebra k E] [Algebra E κ] [Algebra k κ]
    [IsScalarTower k E κ]
    [IsSepClosure k κ] [IsSepClosure E κ] [IsSepClosed κ]
    {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (c : Y ⟶ Spec (.of E))
    (a : Y ⟶ X)
    (ha : a ≫ f = c ≫ Spec.map (CommRingCat.ofHom (algebraMap k E)))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (xiY : Spec (.of Ω) ⟶ Y) :
    ∀ γ : π₁ᵉᵗ(xiY),
      (arithmeticFundamentalGroupHom E κ c xiY γ).restrictScalars k =
        fieldExtensionComparisonConjugator k E κ (xiY ≫ c) *
          arithmeticFundamentalGroupHom k κ f (xiY ≫ a)
            (fundamentalGroupHom a xiY γ) *
          (fieldExtensionComparisonConjugator k E κ (xiY ≫ c))⁻¹ := by
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
  intro γ
  change (arithmeticFundamentalGroupHom E κ c xiY γ).restrictScalars k =
    α * arithmeticFundamentalGroupHom k κ f (xiY ≫ a)
      (fundamentalGroupHom a xiY γ) * α⁻¹
  rw [harithmetic]
  have h := congrArg eK.symm (hcore γ)
  simpa only [MulAut.conj_apply, map_mul, map_inv,
    MulEquiv.symm_apply_apply, α] using h

end AlgebraicGeometry.FiniteEtale
