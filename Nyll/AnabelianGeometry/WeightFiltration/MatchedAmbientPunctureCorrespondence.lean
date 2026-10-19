/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.ChosenCuspAmbientComparison

/-!
# Puncture correspondence under a change of matched ambient points
-/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.FiniteEtale AlgebraicGeometry.ProjSpace
namespace AnabelianGeometry.WeightFiltration
attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra

private theorem ambient_map_conjugate
    {G H : Type*} [Group G] [Group H] (I : Subgroup G) (f : G →* H) (a : G) :
    (I.map (MulAut.conj a).toMonoidHom).map f =
      (I.map f).map (MulAut.conj (f a)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  change f (a * x * a⁻¹) = f a * f x * (f a)⁻¹
  rw [map_mul, map_mul, map_inv]

private theorem ambient_map_conjugate_comp
    {G : Type*} [Group G] (I : Subgroup G) (a b : G) :
    (I.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      I.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  change b * (a * x * a⁻¹) * b⁻¹ = (b * a) * x * (b * a)⁻¹
  simp only [mul_inv_rev, mul_assoc]

private theorem ambient_cancel_conjugate
    {G : Type*} [Group G] (I J : Subgroup G) (a b : G)
    (h : I.map (MulAut.conj a).toMonoidHom = J.map (MulAut.conj b).toMonoidHom) :
    I = J.map (MulAut.conj (a⁻¹ * b)).toMonoidHom := by
  have h' := congrArg (fun K : Subgroup G => K.map (MulAut.conj a⁻¹).toMonoidHom) h
  rw [ambient_map_conjugate_comp, ambient_map_conjugate_comp, inv_mul_cancel] at h'
  have hid : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
    ext x
    change 1 * x * (1 : G)⁻¹ = x
    simp only [inv_one, one_mul, mul_one]
  rw [hid, Subgroup.map_id] at h'
  exact h'

private theorem ambient_correspondence_comp
    {G₀ G₁ H₀ H₁ : Type*} [Group G₀] [Group G₁] [Group H₀] [Group H₁]
    (eS : G₀ →* G₁) (eT : H₀ →* H₁) (α₀ : G₀ →* H₀) (α₁ : G₁ →* H₁)
    (hcomm : α₁.comp eS = eT.comp α₀)
    (I₀ : Subgroup G₀) (I₁ : Subgroup G₁) (J₀ : Subgroup H₀) (J₁ : Subgroup H₁)
    (aS : G₁) (aT : H₁) (a : H₀)
    (hS : I₀.map eS = I₁.map (MulAut.conj aS).toMonoidHom)
    (hT : J₀.map eT = J₁.map (MulAut.conj aT).toMonoidHom)
    (hI : I₀.map α₀ = J₀.map (MulAut.conj a).toMonoidHom) :
    I₁.map α₁ = J₁.map (MulAut.conj ((α₁ aS)⁻¹ * (eT a * aT))).toMonoidHom := by
  apply ambient_cancel_conjugate (I₁.map α₁) J₁ (α₁ aS) (eT a * aT)
  calc
    (I₁.map α₁).map (MulAut.conj (α₁ aS)).toMonoidHom =
        (I₁.map (MulAut.conj aS).toMonoidHom).map α₁ :=
      (ambient_map_conjugate I₁ α₁ aS).symm
    _ = (I₀.map eS).map α₁ := congrArg (fun K => K.map α₁) hS.symm
    _ = (I₀.map α₀).map eT := by rw [Subgroup.map_map, hcomm, Subgroup.map_map]
    _ = (J₀.map (MulAut.conj a).toMonoidHom).map eT :=
      congrArg (fun K => K.map eT) hI
    _ = (J₀.map eT).map (MulAut.conj (eT a)).toMonoidHom :=
      ambient_map_conjugate J₀ eT a
    _ = (J₁.map (MulAut.conj aT).toMonoidHom).map
        (MulAut.conj (eT a)).toMonoidHom := congrArg
      (fun K => K.map (MulAut.conj (eT a)).toMonoidHom) hT
    _ = J₁.map (MulAut.conj (eT a * aT)).toMonoidHom :=
      ambient_map_conjugate_comp J₁ aT (eT a)

private abbrev retainedAmbientPoint
    (k κ : Type) [Field k] [Field κ] [Algebra k κ] [Infinite k]
    (s : Finset (Projectivization k (k × k))) (Ω : Type) [Field Ω]
    (A : Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ω) :
    Spec (.of Ω) ⟶ rationalConfigurationGeometricScheme k κ s := by
  let : Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ω := A
  exact (rationalConfigurationGeometricScheme k κ s).genericExtensionMorphism Ω

private abbrev retainedAmbientInertia
    (k κ : Type) [Field k] [NumberField k] [Field κ] [CharZero κ]
    [IsAlgClosed κ] [Algebra k κ] [IsAlgClosure k κ]
    (s : Finset (Projectivization k (k × k))) (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    (A : Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ω)
    (H : let : Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ω := A
      IsAlgClosure (rationalConfigurationGeometricScheme k κ s).functionField Ω)
    (p : s) : Subgroup (Aut (fiber (retainedAmbientPoint k κ s Ω A))) := by
  let : Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ω := A
  let : IsAlgClosure (rationalConfigurationGeometricScheme k κ s).functionField Ω := H
  exact rationalConfigurationChosenInertia k κ s Ω (rationalConfigurationBoundaryPlace k κ s p)

theorem rationalConfiguration_matchedAmbient_same_puncture_equiv
    (k κ : Type) [Field k] [NumberField k] [Field κ] [CharZero κ]
    [IsAlgClosed κ] [Algebra k κ] [IsAlgClosure k κ]
    (s t : Finset (Projectivization k (k × k)))
    (Ωs Ωt : Type) [Field Ωs] [Field Ωt] [IsAlgClosed Ωs] [IsAlgClosed Ωt]
    [Algebra (RatFunc k) Ωs] [IsSepClosure (RatFunc k) Ωs]
    [Algebra k Ωs] [IsScalarTower k (RatFunc k) Ωs]
    [Algebra (RatFunc k) Ωt] [IsSepClosure (RatFunc k) Ωt]
    [Algebra k Ωt] [IsScalarTower k (RatFunc k) Ωt]
    (AS₀ AS₁ : Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ωs)
    (AT₀ AT₁ : Algebra (rationalConfigurationGeometricScheme k κ t).functionField Ωt)
    (HS₀ : let : Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ωs := AS₀
      IsAlgClosure (rationalConfigurationGeometricScheme k κ s).functionField Ωs)
    (HS₁ : let : Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ωs := AS₁
      IsAlgClosure (rationalConfigurationGeometricScheme k κ s).functionField Ωs)
    (HT₀ : let : Algebra (rationalConfigurationGeometricScheme k κ t).functionField Ωt := AT₀
      IsAlgClosure (rationalConfigurationGeometricScheme k κ t).functionField Ωt)
    (HT₁ : let : Algebra (rationalConfigurationGeometricScheme k κ t).functionField Ωt := AT₁
      IsAlgClosure (rationalConfigurationGeometricScheme k κ t).functionField Ωt) :
    let xs₀ := retainedAmbientPoint k κ s Ωs AS₀
    let xs₁ := retainedAmbientPoint k κ s Ωs AS₁
    let xt₀ := retainedAmbientPoint k κ t Ωt AT₀
    let xt₁ := retainedAmbientPoint k κ t Ωt AT₁
    let fs := (rationalConfigurationOpen s).ι ≫ π k 1
    let ft := (rationalConfigurationOpen t).ι ≫ π k 1
    let us := Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k κ))) fs
    let ut := Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k κ))) ft
    let zs := Spec.map (CommRingCat.ofHom (algebraMap (RatFunc k) Ωs)) ≫
      rationalConfigurationArithmeticGenericPoint k s
    let zt := Spec.map (CommRingCat.ofHom (algebraMap (RatFunc k) Ωt)) ≫
      rationalConfigurationArithmeticGenericPoint k t
    ∀ (hs₀ : xs₀ ≫ us = zs) (hs₁ : xs₁ ≫ us = zs)
      (ht₀ : xt₀ ≫ ut = zt) (ht₁ : xt₁ ≫ ut = zt),
    let eS := commonArithmeticPointGeometricEquiv k κ
      (rationalConfigurationOpen s : Scheme) fs xs₀ xs₁ zs hs₀ hs₁
    let eT := commonArithmeticPointGeometricEquiv k κ
      (rationalConfigurationOpen t : Scheme) ft xt₀ xt₁ zt ht₀ ht₁
    ∀ (α : Aut (fiber xs₀) ≃ₜ* Aut (fiber xt₀)) (σ : s ≃ t),
      (∀ p : s, ∃ a : Aut (fiber xt₀),
        (retainedAmbientInertia k κ s Ωs AS₀ HS₀ p).map α.toMonoidHom =
          (retainedAmbientInertia k κ t Ωt AT₀ HT₀ (σ p)).map
            (MulAut.conj a).toMonoidHom) →
      ∀ p : s, ∃ a : Aut (fiber xt₁),
        (retainedAmbientInertia k κ s Ωs AS₁ HS₁ p).map
            (eS.symm.trans (α.trans eT)).toMonoidHom =
          (retainedAmbientInertia k κ t Ωt AT₁ HT₁ (σ p)).map
            (MulAut.conj a).toMonoidHom := by
  intro xs₀ xs₁ xt₀ xt₁ fs ft us ut zs zt hs₀ hs₁ ht₀ ht₁ eS eT α σ hI p
  obtain ⟨aS, haS⟩ := rationalConfigurationChosenInertia_commonPoint_conjugate
    k κ s Ωs AS₀ AS₁ HS₀ HS₁ hs₀ hs₁ (rationalConfigurationBoundaryPlace k κ s p)
  obtain ⟨aT, haT⟩ := rationalConfigurationChosenInertia_commonPoint_conjugate
    k κ t Ωt AT₀ AT₁ HT₀ HT₁ ht₀ ht₁ (rationalConfigurationBoundaryPlace k κ t (σ p))
  obtain ⟨a, ha⟩ := hI p
  let aS' : Aut (fiber xs₁) := aS
  let aT' : Aut (fiber xt₁) := aT
  let α₁ : Aut (fiber xs₁) ≃ₜ* Aut (fiber xt₁) := eS.symm.trans (α.trans eT)
  have hcomm : α₁.toMonoidHom.comp eS.toMonoidHom = eT.toMonoidHom.comp α.toMonoidHom := by
    apply MonoidHom.ext
    intro x
    change eT (α (eS.symm (eS x))) = eT (α x)
    rw [eS.symm_apply_apply]
  exact ⟨(α₁ aS')⁻¹ * (eT a * aT'), ambient_correspondence_comp
    eS.toMonoidHom eT.toMonoidHom α.toMonoidHom α₁.toMonoidHom hcomm
    (retainedAmbientInertia k κ s Ωs AS₀ HS₀ p)
    (retainedAmbientInertia k κ s Ωs AS₁ HS₁ p)
    (retainedAmbientInertia k κ t Ωt AT₀ HT₀ (σ p))
    (retainedAmbientInertia k κ t Ωt AT₁ HT₁ (σ p)) aS' aT' a haS haT ha⟩

end AnabelianGeometry.WeightFiltration
