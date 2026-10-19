/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.GroupTheory.Subgroup.Centralizer

/-! # Pure-group bridges for arithmetic inertia normalizers

These arguments keep the geometric and arithmetic groups as opaque parameters.
The arithmetic application supplies its actual inclusions, quotient maps, and
self-normalizing geometric inertia; no arithmetic decomposition equality is
assumed in the kernel-lifting theorem.
-/

namespace AnabelianGeometry.WeightFiltration

private theorem arithmeticBridge_mem_map_iff
    {G P : Type*} [Group G] [Group P]
    (i : G →* P) (hi : Function.Injective i)
    (I : Subgroup G) (x : G) :
    i x ∈ I.map i ↔ x ∈ I := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    exact hi hyx ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

private theorem arithmeticBridge_normalizer_reflect
    {G P : Type*} [Group G] [Group P]
    (i : G →* P) (hi : Function.Injective i)
    (I : Subgroup G) (g : G)
    (hg : i g ∈ Subgroup.normalizer (I.map i : Set P)) :
    g ∈ Subgroup.normalizer (I : Set G) := by
  apply Subgroup.mem_set_normalizer_iff.mpr
  intro x
  have hx := Subgroup.mem_set_normalizer_iff.mp hg (i x)
  have hconj : i (g * x * g⁻¹) = i g * i x * (i g)⁻¹ := by
    simp only [map_mul, map_inv]
  change (i x ∈ I.map i ↔ i g * i x * (i g)⁻¹ ∈ I.map i) at hx
  rw [← hconj] at hx
  exact (arithmeticBridge_mem_map_iff i hi I x).symm.trans
    (hx.trans (arithmeticBridge_mem_map_iff i hi I (g * x * g⁻¹)))

/-- A subgroup containing the geometric inertia image, normalizing it, and
surjecting to the arithmetic quotient is the full arithmetic normalizer.

For `g` in the normalizer, choose `d` in `D` with the same quotient image.
Exactness lifts `d⁻¹ * g` to the geometric group, and geometric
self-normalization puts this lift in `I`. -/
theorem arithmeticImage_normalizer_eq_of_full_image
    {G P Γ : Type*} [Group G] [Group P] [Group Γ]
    (i : G →* P) (p : P →* Γ)
    (hi : Function.Injective i) (hexact : i.range = p.ker)
    (I : Subgroup G)
    (hself : Subgroup.normalizer (I : Set G) = I)
    (D : Subgroup P)
    (hID : I.map i ≤ D)
    (hDN : D ≤ Subgroup.normalizer (I.map i : Set P))
    (hfull : ∀ σ : Γ, ∃ d : P, d ∈ D ∧ p d = σ) :
    D = Subgroup.normalizer (I.map i : Set P) := by
  apply le_antisymm hDN
  intro g hg
  obtain ⟨d, hd, hpd⟩ := hfull (p g)
  have hker : d⁻¹ * g ∈ p.ker := by
    change p (d⁻¹ * g) = 1
    rw [map_mul, map_inv, hpd, inv_mul_cancel]
  have hrange : d⁻¹ * g ∈ i.range := by
    rw [hexact]
    exact hker
  obtain ⟨x, hx⟩ := hrange
  have hxnorm : i x ∈ Subgroup.normalizer (I.map i : Set P) := by
    rw [hx]
    exact (Subgroup.normalizer (I.map i : Set P)).mul_mem
      ((Subgroup.normalizer (I.map i : Set P)).inv_mem (hDN hd)) hg
  have hxI : x ∈ I := by
    rw [← hself]
    exact arithmeticBridge_normalizer_reflect i hi I x hxnorm
  have hixD : i x ∈ D := hID ⟨x, hxI, rfl⟩
  have hproduct := D.mul_mem hd hixD
  rw [hx] at hproduct
  simpa only [← mul_assoc, mul_inv_cancel, one_mul] using hproduct

/-- The same bridge stated using surjectivity of the actual restricted
arithmetic homomorphism. -/
theorem arithmeticImage_normalizer_eq_of_surjective_restriction
    {G P Γ : Type*} [Group G] [Group P] [Group Γ]
    (i : G →* P) (p : P →* Γ)
    (hi : Function.Injective i) (hexact : i.range = p.ker)
    (I : Subgroup G)
    (hself : Subgroup.normalizer (I : Set G) = I)
    (D : Subgroup P)
    (hID : I.map i ≤ D)
    (hDN : D ≤ Subgroup.normalizer (I.map i : Set P))
    (hfull : Function.Surjective (p.comp D.subtype)) :
    D = Subgroup.normalizer (I.map i : Set P) := by
  apply arithmeticImage_normalizer_eq_of_full_image i p hi hexact I hself D hID hDN
  intro σ
  obtain ⟨d, hd⟩ := hfull σ
  exact ⟨d, d.property, hd⟩

private theorem arithmeticBridge_normalizer_map_iff
    {P₁ P₂ : Type*} [Group P₁] [Group P₂]
    (e : P₁ ≃* P₂) (H : Subgroup P₁) (g : P₁) :
    e g ∈ Subgroup.normalizer (H.map e.toMonoidHom : Set P₂) ↔
      g ∈ Subgroup.normalizer (H : Set P₁) := by
  constructor
  · intro hg
    exact arithmeticBridge_normalizer_reflect e.toMonoidHom e.injective H g hg
  · intro hg
    apply Subgroup.mem_set_normalizer_iff.mpr
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    have hx := Subgroup.mem_set_normalizer_iff.mp hg x
    have hconj : e (g * x * g⁻¹) = e g * e x * (e g)⁻¹ := by
      simp only [map_mul, map_inv]
    change (e x ∈ H.map e.toMonoidHom ↔
      e g * e x * (e g)⁻¹ ∈ H.map e.toMonoidHom)
    rw [← hconj]
    exact (arithmeticBridge_mem_map_iff e.toMonoidHom e.injective H x).trans
      (hx.trans
        (arithmeticBridge_mem_map_iff e.toMonoidHom e.injective H
          (g * x * g⁻¹)).symm)

private theorem arithmeticBridge_normalizer_map
    {P₁ P₂ : Type*} [Group P₁] [Group P₂]
    (e : P₁ ≃* P₂) (H : Subgroup P₁) :
    (Subgroup.normalizer (H : Set P₁)).map e.toMonoidHom =
      Subgroup.normalizer (H.map e.toMonoidHom : Set P₂) := by
  apply Subgroup.ext
  intro y
  obtain ⟨x, rfl⟩ := e.surjective y
  exact (arithmeticBridge_mem_map_iff e.toMonoidHom e.injective
    (Subgroup.normalizer (H : Set P₁)) x).trans
      (arithmeticBridge_normalizer_map_iff e H x).symm

/-- A geometric inertia conjugacy transports to the literal arithmetic
images through a commuting square of actual inclusions. The conjugating
element is the actual arithmetic image `i₂ a`. -/
theorem arithmeticImage_map_eq_conjugate
    {G₁ G₂ P₁ P₂ : Type*}
    [Group G₁] [Group G₂] [Group P₁] [Group P₂]
    (eP : P₁ ≃* P₂) (eΔ : G₁ ≃* G₂)
    (i₁ : G₁ →* P₁) (i₂ : G₂ →* P₂)
    (heval : ∀ x : G₁, i₂ (eΔ x) = eP (i₁ x))
    (I₁ : Subgroup G₁) (I₂ : Subgroup G₂) (a : G₂)
    (hI : I₁.map eΔ.toMonoidHom = I₂.map (MulAut.conj a).toMonoidHom) :
    (I₁.map i₁).map eP.toMonoidHom =
      (I₂.map i₂).map (MulAut.conj (i₂ a)).toMonoidHom := by
  calc
    (I₁.map i₁).map eP.toMonoidHom = (I₁.map eΔ.toMonoidHom).map i₂ := by
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext x
      change eP (i₁ x) = i₂ (eΔ x)
      exact (heval x).symm
    _ = (I₂.map (MulAut.conj a).toMonoidHom).map i₂ := by rw [hI]
    _ = (I₂.map i₂).map (MulAut.conj (i₂ a)).toMonoidHom := by
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext x
      change i₂ (a * x * a⁻¹) = i₂ a * i₂ x * (i₂ a)⁻¹
      simp only [map_mul, map_inv]

/-- The same geometric conjugacy transports full arithmetic normalizers.
The actual decomposition caller may replace each normalizer by its proved
arithmetic decomposition subgroup using the kernel-lifting theorem above. -/
theorem arithmeticImage_normalizer_map_eq_conjugate
    {G₁ G₂ P₁ P₂ : Type*}
    [Group G₁] [Group G₂] [Group P₁] [Group P₂]
    (eP : P₁ ≃* P₂) (eΔ : G₁ ≃* G₂)
    (i₁ : G₁ →* P₁) (i₂ : G₂ →* P₂)
    (heval : ∀ x : G₁, i₂ (eΔ x) = eP (i₁ x))
    (I₁ : Subgroup G₁) (I₂ : Subgroup G₂) (a : G₂)
    (hI : I₁.map eΔ.toMonoidHom = I₂.map (MulAut.conj a).toMonoidHom) :
    (Subgroup.normalizer (I₁.map i₁ : Set P₁)).map eP.toMonoidHom =
      (Subgroup.normalizer (I₂.map i₂ : Set P₂)).map
        (MulAut.conj (i₂ a)).toMonoidHom := by
  have hmap := arithmeticImage_map_eq_conjugate eP eΔ i₁ i₂ heval I₁ I₂ a hI
  calc
    (Subgroup.normalizer (I₁.map i₁ : Set P₁)).map eP.toMonoidHom =
        Subgroup.normalizer ((I₁.map i₁).map eP.toMonoidHom : Set P₂) :=
      arithmeticBridge_normalizer_map eP (I₁.map i₁)
    _ = Subgroup.normalizer
        ((I₂.map i₂).map (MulAut.conj (i₂ a)).toMonoidHom : Set P₂) := by
      rw [hmap]
    _ = (Subgroup.normalizer (I₂.map i₂ : Set P₂)).map
        (MulAut.conj (i₂ a)).toMonoidHom :=
      (arithmeticBridge_normalizer_map (MulAut.conj (i₂ a)) (I₂.map i₂)).symm

end AnabelianGeometry.WeightFiltration
