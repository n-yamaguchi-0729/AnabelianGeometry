/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.CyclotomicCommonLiftFiniteBase
import Nyll.AnabelianGeometry.WeightFiltration.RecoveredArithmeticBoundaryWeight
import Nyll.EtaleFundamentalGroups.GeometricFiber.RecoveredCoverActionComparison
import Nyll.EtaleFundamentalGroups.GeometricFiber.ArithmeticFieldExtensionPointedConjugacy

/-! # A transported candidate in the actual recovered cover

The arithmetic quotient, finite-cover image and action are constructed from
actual scheme morphisms. The only candidate-specific inputs are normalizer
openness and its literal roots conjugation, supplied by the source cusp and
the arithmetic isomorphism. No relative test or kernel membership is assumed.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale
open CategoryTheory.PreGaloisCategory EtaleFundamentalGroups
open EtaleFundamentalGroups.Inertia ProCGroups.Abelian
open AlgebraicGeometry.SmoothProperCurve NeronModelInfra SchemeTheory

namespace AnabelianGeometry.WeightFiltration

/-- Openness of the actual pointed finite-cover image. -/
private theorem pointedFiniteEtale_range_isOpen
    {X Y : Scheme} [ConnectedSpace X]
    (a : Y ⟶ X) [IsFiniteEtale a]
    {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ Y) (xi : Spec (.of Ω) ⟶ X)
    (hx : x ≫ a = xi) :
    IsOpen (((pointedFundamentalGroupHom a x xi hx).toMonoidHom.range :
      Subgroup π₁ᵉᵗ(xi)) : Set π₁ᵉᵗ(xi)) := by
  let A : FiniteEtale X := FiniteEtale.mk a
  have hrange := pointedFundamentalGroupHom_range_eq_stabilizer A x xi hx
  change IsOpen (((pointedFundamentalGroupHom A.hom x xi hx).toMonoidHom.range :
    Subgroup π₁ᵉᵗ(xi)) : Set π₁ᵉᵗ(xi))
  rw [hrange]
  exact stabilizer_isOpen π₁ᵉᵗ(xi)
    ((fiberObjEquivHom xi A).symm (Over.homMk x hx))

/-- Every value of the same roots map lies in the intrinsic span on the
specified recovered cover. The actual finite coefficient-field label is
obtained from the scheme square, including its uniform conjugator. -/
theorem recoveredCandidate_image_mem_openCyclotomicSpan
    (k E κ : Type) [Field k] [Field E] [Field κ]
    [Algebra k E] [Algebra E κ] [Algebra k κ] [IsScalarTower k E κ]
    [IsAlgClosed κ] [IsSepClosure k κ] [IsSepClosure E κ]
    (X : Scheme) [CompactSpace X] [QuasiSeparatedSpace X]
    (f : X ⟶ Spec (.of k))
    [ConnectedSpace (show Scheme from Limits.pullback (specMap k κ) f)]
    (N : Scheme) [CompactSpace N] [QuasiSeparatedSpace N]
    (c : N ⟶ Spec (.of E))
    [ConnectedSpace (show Scheme from Limits.pullback (specMap E κ) c)]
    (a : N ⟶ X) [IsFiniteEtale a]
    (ha : a ≫ f = c ≫ specMap k E)
    {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶ Limits.pullback (specMap k κ) f)
    (W : FiniteEtale (Limits.pullback (specMap k κ) f)) [IsConnected W]
    (w : (fiber xi).obj W)
    (u : Limits.pullback (specMap E κ) c ⟶ Limits.pullback (specMap k κ) f)
    (hscheme : u ≫ Limits.pullback.snd (specMap k κ) f =
      Limits.pullback.snd (specMap E κ) c ≫ a)
    (R : Limits.pullback (specMap E κ) c ≅ W.left)
    (hR : R.hom ≫ W.hom = u)
    (x : Spec (.of Ω) ⟶ Limits.pullback (specMap E κ) c)
    (hxR : x ≫ R.hom = (fiberObjEquivHom xi W w).left)
    (J : ClosedSubgroup π₁ᵉᵗ(xi ≫ Limits.pullback.snd (specMap k κ) f))
    (hN : IsOpen (((Subgroup.normalizer (J : Set _)).map
      (arithmeticFundamentalGroupHom k κ f
        (xi ≫ Limits.pullback.snd (specMap k κ) f)).toMonoidHom :
          Subgroup Gal(κ/k)) : Set Gal(κ/k)))
    (psiV : (primeToRootsSystem κ κ).inverseLimit →*
      MulAction.stabilizer π₁ᵉᵗ(xi) w)
    (hcycl : ∀ γ ∈ Subgroup.normalizer (J : Set _), ∀ t,
      fundamentalGroupHom (Limits.pullback.snd (specMap k κ) f) xi
        (psiV (primeToRootsCoefficientMap κ κ
          (arithmeticFundamentalGroupHom k κ f
            (xi ≫ Limits.pullback.snd (specMap k κ) f) γ).toRingHom t) : π₁ᵉᵗ(xi)) =
        γ * fundamentalGroupHom (Limits.pullback.snd (specMap k κ) f) xi
          (psiV t : π₁ᵉᵗ(xi)) * γ⁻¹) :
    ∃ (hgeo : x ≫ u = xi)
      (e : π₁ᵉᵗ(x) ≃ₜ* MulAction.stabilizer π₁ᵉᵗ(xi) w),
      (∀ v, (e v : π₁ᵉᵗ(xi)) = pointedFundamentalGroupHom u x xi hgeo v) ∧
      ∀ t, TopologicalAbelianization.mk _ (e.symm (psiV t)) ∈
        openCyclotomicSpan
          (fun σ : Gal(κ/E) => primeToRootsCoefficientMap κ κ σ.toRingHom)
          (fun σ => geometricAbelianGaloisAction E κ N c x σ) := by
  let : ConnectedSpace X := connectedSpace_of_connected_constantField k κ f
  let pX := Limits.pullback.snd (specMap k κ) f
  let pY := Limits.pullback.snd (specMap E κ) c
  let iX := fundamentalGroupHom pX xi
  obtain ⟨hgeo, hpoint, e, he, _heval, haction⟩ :=
    recoveredPoint_stabilizerEquiv_arithmeticAction E κ N c pX xi W w
      u a hscheme R hR x hxR
  let p := arithmeticFundamentalGroupHom k κ f (xi ≫ pX)
  let q := arithmeticFundamentalGroupHom E κ c (x ≫ pY)
  let coverMap := pointedFundamentalGroupHom a (x ≫ pY) (xi ≫ pX) hpoint
  let H : OpenSubgroup π₁ᵉᵗ(xi ≫ pX) :=
    ⟨coverMap.toMonoidHom.range, pointedFiniteEtale_range_isOpen a (x ≫ pY)
      (xi ≫ pX) hpoint⟩
  have hq : Function.Surjective q :=
    (arithmetic_exactSequence_of_isSepClosure E κ N c x).2.1
  obtain ⟨α, hlabel⟩ := arithmeticFundamentalGroupHom_fieldExtension_pointed_conjugate
    k E κ f c a ha (x ≫ pY) (xi ≫ pX) hpoint
  let i : π₁ᵉᵗ(x) →* π₁ᵉᵗ(xi ≫ pX) :=
    iX.toMonoidHom.comp
      ((MulAction.stabilizer π₁ᵉᵗ(xi) w).subtype.comp e.toMonoidHom)
  have hi : Function.Injective i := by
    intro v v' hv
    apply e.injective
    apply Subtype.ext
    exact (arithmetic_exactSequence_of_isSepClosure k κ X f xi).1 hv
  let psi : (primeToRootsSystem κ κ).inverseLimit →* π₁ᵉᵗ(x) :=
    e.symm.toMonoidHom.comp psiV
  have hipsi (t : (primeToRootsSystem κ κ).inverseLimit) :
      i (psi t) = iX (psiV t : π₁ᵉᵗ(xi)) := by
    change iX (e (e.symm (psiV t)) : π₁ᵉᵗ(xi)) = _
    rw [e.apply_symm_apply]
  have hcycl' : ∀ γ ∈ Subgroup.normalizer (J : Set _), ∀ t,
      i (psi (primeToRootsCoefficientMap κ κ (p γ).toRingHom t)) =
        γ * i (psi t) * γ⁻¹ := by
    intro γ hγ t
    rw [hipsi, hipsi]
    exact hcycl γ hγ t
  have haction' : ∀ γ : π₁ᵉᵗ(x ≫ pY), ∀ v : π₁ᵉᵗ(x), ∃ v',
      geometricAbelianGaloisAction E κ N c x (q γ)
        (TopologicalAbelianization.mk _ v) = TopologicalAbelianization.mk _ v' ∧
      i v' = coverMap γ * i v * (coverMap γ)⁻¹ := by
    intro γ v
    obtain ⟨v', hv', hiv'⟩ := haction γ v
    refine ⟨v', ?_, hiv'⟩
    apply (TopologicalAbelianization.congr e).injective
    rw [TopologicalAbelianization.congr_apply_mk]
    exact hv'
  refine ⟨hgeo, e, he, ?_⟩
  intro t
  exact candidate_image_mem_openCyclotomicSpan_over_finite_base k E κ p q hq
    coverMap H rfl α hlabel J hN i hi psi
    (fun σ => geometricAbelianGaloisAction E κ N c x σ) hcycl' haction' t

/-- At the same recovered generic point, actual weight separation turns the
span membership into the actual compactification kernel. A section is actual
geometric data, supplied after finite refinement by the existing section owner. -/
theorem recoveredCandidate_image_mem_compactificationKernel
    (k E κ : Type) [Field k] [Field E] [NumberField E]
    [Field κ] [CharZero κ] [IsAlgClosed κ]
    [Algebra k E] [Algebra E κ] [Algebra k κ] [IsScalarTower k E κ]
    [IsSepClosure k κ] [IsSepClosure E κ]
    (X : Scheme) [CompactSpace X] [QuasiSeparatedSpace X]
    (f : X ⟶ Spec (.of k))
    [ConnectedSpace (show Scheme from Limits.pullback (specMap k κ) f)]
    {C N : Scheme} [CompactSpace N] [QuasiSeparatedSpace N]
    (c : C ⟶ Spec (.of E)) (j : N ⟶ C) [IsOpenImmersion j]
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (a : N ⟶ X) [IsFiniteEtale a]
    (ha : a ≫ f = (j ≫ c) ≫ specMap k E)
    {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶ Limits.pullback (specMap k κ) f)
    (W : FiniteEtale (Limits.pullback (specMap k κ) f)) [IsConnected W]
    [IsIntegral W.left] [Algebra W.left.functionField Ω]
    [IsSepClosure W.left.functionField Ω]
    (w : (fiber xi).obj W)
    (hw : W.left.genericExtensionMorphism Ω = (fiberObjEquivHom xi W w).left)
    (R : Limits.pullback (specMap E κ) (j ≫ c) ≅ W.left)
    (hscheme : (R.hom ≫ W.hom) ≫ Limits.pullback.snd (specMap k κ) f =
      Limits.pullback.snd (specMap E κ) (j ≫ c) ≫ a)
    (epsilon : SchemeHomOver (𝟙 (Spec (.of E))) c)
    (J : ClosedSubgroup π₁ᵉᵗ(xi ≫ Limits.pullback.snd (specMap k κ) f))
    (hN : IsOpen (((Subgroup.normalizer (J : Set _)).map
      (arithmeticFundamentalGroupHom k κ f
        (xi ≫ Limits.pullback.snd (specMap k κ) f)).toMonoidHom :
          Subgroup Gal(κ/k)) : Set Gal(κ/k)))
    (psiV : (primeToRootsSystem κ κ).inverseLimit →*
      MulAction.stabilizer π₁ᵉᵗ(xi) w)
    (hcycl : ∀ γ ∈ Subgroup.normalizer (J : Set _), ∀ t,
      fundamentalGroupHom (Limits.pullback.snd (specMap k κ) f) xi
        (psiV (primeToRootsCoefficientMap κ κ
          (arithmeticFundamentalGroupHom k κ f
            (xi ≫ Limits.pullback.snd (specMap k κ) f) γ).toRingHom t) : π₁ᵉᵗ(xi)) =
        γ * fundamentalGroupHom (Limits.pullback.snd (specMap k κ) f) xi
          (psiV t : π₁ᵉᵗ(xi)) * γ⁻¹) :
    letI : IsIntegral (show Scheme from Limits.pullback (specMap E κ) (j ≫ c)) :=
      IsIntegral.of_isIso R.inv
    let x := W.left.genericExtensionMorphism Ω ≫ R.inv
    ∃ (hgeo : x ≫ (R.hom ≫ W.hom) = xi)
      (e : π₁ᵉᵗ(x) ≃ₜ* MulAction.stabilizer π₁ᵉᵗ(xi) w),
      (∀ v, (e v : π₁ᵉᵗ(xi)) =
        pointedFundamentalGroupHom (R.hom ≫ W.hom) x xi hgeo v) ∧
      ∀ t, TopologicalAbelianization.mk _ (e.symm (psiV t)) ∈
        (compactificationAbelianizationMap
          (coefficientModelMap (specMap E κ) c j) x).toMonoidHom.ker := by
  let : IsIntegral (show Scheme from Limits.pullback (specMap E κ) (j ≫ c)) :=
    IsIntegral.of_isIso R.inv
  let x := W.left.genericExtensionMorphism Ω ≫ R.inv
  have hxR : x ≫ R.hom = (fiberObjEquivHom xi W w).left := by
    simpa only [x, Category.assoc, Iso.inv_hom_id, Category.comp_id] using hw
  obtain ⟨hgeo, e, he, hspan⟩ := recoveredCandidate_image_mem_openCyclotomicSpan
    k E κ X f N (j ≫ c) a ha xi W w (R.hom ≫ W.hom) hscheme R rfl x hxR
    J hN psiV hcycl
  have hweight := recoveredArithmetic_compactification_kernel_eq_openCyclotomicSpan
    E κ c j R (Omega := Ω) epsilon
  refine ⟨hgeo, e, he, ?_⟩
  intro t
  rw [hweight]
  exact hspan t

end AnabelianGeometry.WeightFiltration
