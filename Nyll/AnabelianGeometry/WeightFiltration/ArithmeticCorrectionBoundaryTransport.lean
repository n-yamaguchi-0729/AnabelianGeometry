/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GeometricFiber.GeometricAbelianGaloisAction
import Nyll.ProCGroups.Topologies.Conjugation

/-! # Removing an arithmetic correction while retaining boundary ranges

Conjugation by an arithmetic element acts on the geometric abelianization
through its actual Galois quotient. Removing that conjugation therefore
preserves every boundary range fixed by that quotient action. The element
need not lie in the geometric subgroup. For rational punctures the required
stability is supplied by `rational_boundaryPlaceInertiaHom_range_galois_fixed`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale
open ProCGroups.Abelian

namespace AnabelianGeometry.WeightFiltration

universe u v

/-- Undo the specified arithmetic conjugation on an actual geometric group.
The uncorrected geometric map and its unchanged stable subgroup images are
constructed together, using the arithmetic exact sequence. -/
theorem exists_geometricEquiv_remove_arithmetic_correction
    (k κ : Type u) [Field k] [Field κ] [Algebra k κ] [IsSepClosure k κ]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (f : X ⟶ Spec (.of k))
    [ConnectedSpace ↑(Limits.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k κ))) f)]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶ Limits.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k κ))) f)
    {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (b : G →* Aut (fiber (xi ≫ Limits.pullback.snd _ f)))
    (e : G ≃ₜ* Aut (fiber xi))
    (c : Aut (fiber (xi ≫ Limits.pullback.snd _ f)))
    (he : ∀ v, fundamentalGroupHom (Limits.pullback.snd _ f) xi (e v) =
      c * b v * c⁻¹) :
    ∃ e₀ : G ≃ₜ* Aut (fiber xi),
      (∀ v, fundamentalGroupHom (Limits.pullback.snd _ f) xi (e₀ v) = b v) ∧
      ∀ (R : Subgroup (TopologicalAbelianization G))
        (S : Subgroup (TopologicalAbelianization (Aut (fiber xi)))),
        R.map (TopologicalAbelianization.congr e).toMonoidHom = S →
        S.map (geometricAbelianGaloisAction k κ X f xi
          (arithmeticFundamentalGroupHom k κ f (xi ≫ Limits.pullback.snd _ f) c)).toMonoidHom = S →
        R.map (TopologicalAbelianization.congr e₀).toMonoidHom = S := by
  let p := arithmeticFundamentalGroupHom k κ f (xi ≫ Limits.pullback.snd _ f)
  let i := fundamentalGroupHom (Limits.pullback.snd _ f) xi
  let K := geometricFundamentalGroupKernelEquiv k κ X f xi
  let C := K.trans
    ((ProCGroups.Subgroup.conjNormalContinuousMulEquiv p.toMonoidHom.ker c⁻¹).trans K.symm)
  let e₀ := e.trans C
  have hC (w : Aut (fiber xi)) : i (C w) = c⁻¹ * i w * c := by
    calc
      i (C w) = (K (C w) : Aut (fiber (xi ≫ Limits.pullback.snd _ f))) := rfl
      _ = (ProCGroups.Subgroup.conjNormalContinuousMulEquiv p.toMonoidHom.ker c⁻¹
          (K w) : Aut (fiber (xi ≫ Limits.pullback.snd _ f))) :=
        congrArg Subtype.val (K.apply_symm_apply _)
      _ = c⁻¹ * i w * c := by
        change c⁻¹ * i w * (c⁻¹)⁻¹ = _
        rw [inv_inv]
  have hraw (v : G) : i (e₀ v) = b v := by
    change i (C (e v)) = _
    rw [hC, he v]
    simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
  refine ⟨e₀, hraw, ?_⟩
  intro R S hR hS
  let a := geometricAbelianGaloisAction k κ X f xi (p c)
  let E := TopologicalAbelianization.congr e
  let E₀ := TopologicalAbelianization.congr e₀
  have hvalue (z : TopologicalAbelianization G) : a (E₀ z) = E z := by
    obtain ⟨v, rfl⟩ := TopologicalAbelianization.surjective_mk G z
    rw [TopologicalAbelianization.congr_apply_mk,
      TopologicalAbelianization.congr_apply_mk]
    exact geometricAbelianGaloisAction_mk_of_conjugate k κ X f xi c (e₀ v) (e v)
      ((he v).trans (congrArg (fun y => c * y * c⁻¹) (hraw v).symm))
  have hmap : (R.map E₀.toMonoidHom).map a.toMonoidHom = R.map E.toMonoidHom := by
    rw [Subgroup.map_map]
    apply congrArg (fun h : TopologicalAbelianization G →*
      TopologicalAbelianization (Aut (fiber xi)) => R.map h)
    exact MonoidHom.ext hvalue
  apply Subgroup.map_injective (f := a.toMonoidHom) a.injective
  exact hmap.trans (hR.trans hS.symm)

end AnabelianGeometry.WeightFiltration
