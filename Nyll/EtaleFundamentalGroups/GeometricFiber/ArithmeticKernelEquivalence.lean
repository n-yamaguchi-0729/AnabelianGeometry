/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GeometricFiber.GeometricAbelianGaloisAction

/-! # Equivariance induced by an arbitrary arithmetic isomorphism over a fixed base -/

noncomputable section

namespace ProCGroups

/-- Restrict an isomorphism over a fixed quotient to its literal kernels. -/
def kernelContinuousMulEquiv
    {P₁ P₂ Γ : Type*}
    [Group P₁] [TopologicalSpace P₁] [Group P₂] [TopologicalSpace P₂] [Group Γ]
    (eP : P₁ ≃ₜ* P₂) (p₁ : P₁ →* Γ) (p₂ : P₂ →* Γ)
    (h : ∀ g : P₁, p₂ (eP g) = p₁ g) : p₁.ker ≃ₜ* p₂.ker := by
  have hf (n : p₁.ker) : eP n.val ∈ p₂.ker := by
    change p₂ (eP n.val) = 1
    exact (h n.val).trans n.property
  have hg (n : p₂.ker) : eP.symm n.val ∈ p₁.ker := by
    change p₁ (eP.symm n.val) = 1
    calc
      p₁ (eP.symm n.val) = p₂ (eP (eP.symm n.val)) := (h (eP.symm n.val)).symm
      _ = p₂ n.val := congrArg p₂ (eP.apply_symm_apply n.val)
      _ = 1 := n.property
  refine
    { toMulEquiv :=
        { toFun := fun n => ⟨eP n.val, hf n⟩
          invFun := fun n => ⟨eP.symm n.val, hg n⟩
          left_inv := ?_
          right_inv := ?_
          map_mul' := ?_ }
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · intro n
    exact Subtype.ext (eP.symm_apply_apply n.val)
  · intro n
    exact Subtype.ext (eP.apply_symm_apply n.val)
  · intro m n
    apply Subtype.ext
    exact map_mul eP (m : P₁) (n : P₁)
  · exact (eP.continuous_toFun.comp continuous_subtype_val).subtype_mk hf
  · exact (eP.symm.continuous_toFun.comp continuous_subtype_val).subtype_mk hg

@[simp] theorem kernelContinuousMulEquiv_coe_apply
    {P₁ P₂ Γ : Type*}
    [Group P₁] [TopologicalSpace P₁] [Group P₂] [TopologicalSpace P₂] [Group Γ]
    (eP : P₁ ≃ₜ* P₂) (p₁ : P₁ →* Γ) (p₂ : P₂ →* Γ)
    (h : ∀ g : P₁, p₂ (eP g) = p₁ g) (n : p₁.ker) :
    (kernelContinuousMulEquiv eP p₁ p₂ h n : P₂) = eP (n : P₁) := rfl

end ProCGroups

open CategoryTheory ProCGroups.Abelian

namespace AlgebraicGeometry.FiniteEtale

universe u

/-- An arithmetic isomorphism over the fixed Galois group induces an actual
geometric isomorphism with equivariant abelianization. -/
theorem exists_geometricEquiv_equivariant_of_arithmeticEquiv
    (k L : Type u) [Field k] [Field L] [Algebra k L] [IsSepClosure k L]
    (X₁ X₂ : Scheme.{u})
    [CompactSpace X₁] [QuasiSeparatedSpace X₁]
    [CompactSpace X₂] [QuasiSeparatedSpace X₂]
    (f₁ : X₁ ⟶ Spec (.of k)) (f₂ : X₂ ⟶ Spec (.of k))
    [ConnectedSpace ↑(Limits.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k L))) f₁)]
    [ConnectedSpace ↑(Limits.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k L))) f₂)]
    {Ω₁ Ω₂ : Type u} [Field Ω₁] [Field Ω₂] [IsSepClosed Ω₁] [IsSepClosed Ω₂]
    (xi₁ : Spec (.of Ω₁) ⟶ Limits.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k L))) f₁)
    (xi₂ : Spec (.of Ω₂) ⟶ Limits.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k L))) f₂)
    (eP : Aut (fiber (xi₁ ≫ Limits.pullback.snd _ f₁)) ≃ₜ*
      Aut (fiber (xi₂ ≫ Limits.pullback.snd _ f₂)))
    (hP : ∀ g, arithmeticFundamentalGroupHom k L f₂
      (xi₂ ≫ Limits.pullback.snd _ f₂) (eP g) =
        arithmeticFundamentalGroupHom k L f₁ (xi₁ ≫ Limits.pullback.snd _ f₁) g) :
    ∃ eΔ : Aut (fiber xi₁) ≃ₜ* Aut (fiber xi₂),
      (∀ v, fundamentalGroupHom (Limits.pullback.snd _ f₂) xi₂ (eΔ v) =
        eP (fundamentalGroupHom (Limits.pullback.snd _ f₁) xi₁ v)) ∧
      ∀ (σ : L ≃ₐ[k] L) (x : TopologicalAbelianization (Aut (fiber xi₁))),
        TopologicalAbelianization.congr eΔ
          (geometricAbelianGaloisAction k L X₁ f₁ xi₁ σ x) =
        geometricAbelianGaloisAction k L X₂ f₂ xi₂ σ
          (TopologicalAbelianization.congr eΔ x) := by
  let P₁ := Aut (fiber (xi₁ ≫ Limits.pullback.snd _ f₁))
  let P₂ := Aut (fiber (xi₂ ≫ Limits.pullback.snd _ f₂))
  let i₁ := fundamentalGroupHom (Limits.pullback.snd _ f₁) xi₁
  let i₂ := fundamentalGroupHom (Limits.pullback.snd _ f₂) xi₂
  let p₁ := arithmeticFundamentalGroupHom k L f₁ (xi₁ ≫ Limits.pullback.snd _ f₁)
  let p₂ := arithmeticFundamentalGroupHom k L f₂ (xi₂ ≫ Limits.pullback.snd _ f₂)
  let E₁ := geometricFundamentalGroupKernelEquiv k L X₁ f₁ xi₁
  let E₂ := geometricFundamentalGroupKernelEquiv k L X₂ f₂ xi₂
  let EK := ProCGroups.kernelContinuousMulEquiv eP p₁.toMonoidHom p₂.toMonoidHom hP
  let E := E₁.trans (EK.trans E₂.symm)
  have hE₁ (v : Aut (fiber xi₁)) : (E₁ v : P₁) = i₁ v :=
    geometricFundamentalGroupKernelEquiv_apply k L X₁ f₁ xi₁ v
  have hE₂ (v : Aut (fiber xi₂)) : (E₂ v : P₂) = i₂ v :=
    geometricFundamentalGroupKernelEquiv_apply k L X₂ f₂ xi₂ v
  have hE (v : Aut (fiber xi₁)) : i₂ (E v) = eP (i₁ v) := by
    calc
      i₂ (E v) = (E₂ (E v) : P₂) := (hE₂ (E v)).symm
      _ = (EK (E₁ v) : P₂) := congrArg Subtype.val (E₂.apply_symm_apply (EK (E₁ v)))
      _ = eP (E₁ v : P₁) := rfl
      _ = eP (i₁ v) := congrArg eP (hE₁ v)
  refine ⟨E, hE, ?_⟩
  intro σ x
  obtain ⟨g, hg⟩ := (arithmetic_exactSequence_of_isSepClosure k L X₁ f₁ xi₁).2.1 σ
  obtain ⟨v, rfl⟩ := TopologicalAbelianization.surjective_mk _ x
  let n : p₁.toMonoidHom.ker := MulAut.conjNormal g (E₁ v)
  let w := E₁.symm n
  have hw : i₁ w = g * i₁ v * g⁻¹ := by
    calc
      i₁ w = (E₁ w : P₁) := (hE₁ w).symm
      _ = (n : P₁) := congrArg Subtype.val (E₁.apply_symm_apply n)
      _ = g * (E₁ v : P₁) * g⁻¹ := rfl
      _ = g * i₁ v * g⁻¹ := congrArg (fun b : P₁ => g * b * g⁻¹) (hE₁ v)
  have hw' : i₂ (E w) = eP g * i₂ (E v) * (eP g)⁻¹ := by
    calc
      i₂ (E w) = eP (i₁ w) := hE w
      _ = eP (g * i₁ v * g⁻¹) := congrArg eP hw
      _ = eP g * eP (i₁ v) * (eP g)⁻¹ := by rw [map_mul, map_mul, map_inv]
      _ = eP g * i₂ (E v) * (eP g)⁻¹ := by rw [hE v]
  have hs := geometricAbelianGaloisAction_mk_of_conjugate k L X₁ f₁ xi₁ g v w hw
  have ht := geometricAbelianGaloisAction_mk_of_conjugate k L X₂ f₂ xi₂ (eP g) (E v) (E w) hw'
  rw [hg] at hs
  rw [hP g, hg] at ht
  rw [hs, TopologicalAbelianization.congr_apply_mk,
    TopologicalAbelianization.congr_apply_mk]
  exact ht.symm

end AlgebraicGeometry.FiniteEtale
