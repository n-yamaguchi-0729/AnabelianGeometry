/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GaloisCovers.FiniteQuotientRealization
public import Nyll.ProCGroups.Abelian.CharacterDetection

/-!
# Actual abelian Galois covers detect geometric abelianization

A finite character separating an original fundamental-group element is
realized by an actual pointed finite étale Galois cover. Its deck group is
proved abelian from the original finite character image. Thus a nontrivial
abelianization class supplies an actual cover on which it acts nontrivially.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicGeometry
open ProCGroups.Abelian

namespace EtaleFundamentalGroups

universe u

/-- A nonidentity class in the topological abelianization is detected by
the native quotient of an actual abelian finite étale Galois cover. -/
theorem exists_abelian_galoisCover_quotient_ne_one
    {X : Scheme.{u}} [ConnectedSpace X]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ X) (g : π₁ᵉᵗ(ξ))
    (hg : TopologicalAbelianization.mk π₁ᵉᵗ(ξ) g ≠ 1) :
    ∃ (Y : FiniteEtale X) (hY : IsGalois Y)
      (_ : IsMulCommutative (Aut Y)) (y : (FiniteEtale.fiber ξ).obj Y),
      finiteEtaleGaloisCoverQuotientMonoidHom ξ Y hY y g ≠ 1 := by
  have hgne : TopologicalAbelianization.mk π₁ᵉᵗ(ξ) g ≠
      TopologicalAbelianization.mk π₁ᵉᵗ(ξ) 1 := by
    rw [map_one]
    exact hg
  obtain ⟨A, hAgroup, hAtopology, hAfinite, hAdiscrete, χ, hχ⟩ :=
    TopologicalAbelianization.exists_finite_character_of_mk_ne hgne
  let B : Subgroup A := χ.toMonoidHom.range
  let χB : π₁ᵉᵗ(ξ) →ₜ* B :=
    { toMonoidHom := χ.toMonoidHom.rangeRestrict
      continuous_toFun := χ.continuous.subtype_mk (fun g => ⟨g, rfl⟩) }
  obtain ⟨Y, hY, y, e, he⟩ := FiniteEtale.exists_galoisCover_quotient_mulEquiv
    ξ B χB χ.toMonoidHom.rangeRestrict_surjective
  have hGalois : IsGalois Y := hY
  have hcommOp : IsMulCommutative ((Aut Y)ᵐᵒᵖ) := .of_comm fun σ τ => by
    apply e.injective
    rw [map_mul, map_mul, mul_comm]
  have hcomm : IsMulCommutative (Aut Y) := .of_comm fun σ τ => by
    apply MulOpposite.op_injective
    change MulOpposite.op τ * MulOpposite.op σ = MulOpposite.op σ * MulOpposite.op τ
    exact mul_comm' _ _
  refine ⟨Y, hY, hcomm, y, ?_⟩
  intro hzero
  have hpoint := DFunLike.congr_fun he g
  change e (finiteEtaleGaloisCoverQuotientMonoidHom ξ Y hY y g) = χB g at hpoint
  rw [hzero, map_one] at hpoint
  apply hχ
  have hvalue : χ g = 1 := (congrArg Subtype.val hpoint).symm
  exact hvalue.trans (map_one χ).symm

end EtaleFundamentalGroups
