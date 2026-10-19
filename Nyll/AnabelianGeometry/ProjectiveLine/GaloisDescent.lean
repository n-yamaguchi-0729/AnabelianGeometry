/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.ProjectiveLine.LinearFieldMap
import Nyll.SchemeTheory.ProjectiveSpace.RationalPuncturePointInjective
import Mathlib.FieldTheory.Galois.Basic

/-! # Galois descent of projective transformations

Fixed projective points descend by their affine coordinate. The images of
zero, infinity and one then descend a Galois-equivariant projective action.
No fixed linear representative is assumed.
-/

noncomputable section

namespace AnabelianGeometry.ProjectiveLine

universe u v
variable {K : Type u} {L : Type v} [Field K] [Field L]

theorem affinePoint_ne_infinityPoint (t : K) :
    affinePoint t ≠ infinityPoint := by
  intro h
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' K _ _ _ _).mp h
  have hz := congrArg Prod.snd ha
  change a * 0 = (1 : K) at hz
  rw [mul_zero] at hz
  exact zero_ne_one hz

/-- Every projective point is in the affine chart or is its single point at infinity. -/
theorem eq_infinityPoint_or_exists_affinePoint (p : Projectivization K (K × K)) :
    p = infinityPoint ∨ ∃ t : K, p = affinePoint t := by
  by_cases hp : p.rep.2 = 0
  · left
    rw [← p.mk_rep]
    apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
    refine ⟨p.rep.1, ?_⟩
    apply Prod.ext
    · exact mul_one _
    · change p.rep.1 * 0 = p.rep.2
      rw [mul_zero, hp]
  · right
    refine ⟨p.rep.1 / p.rep.2, ?_⟩
    calc
      p = Projectivization.mk K p.rep p.rep_nonzero := p.mk_rep.symm
      _ = affinePoint (p.rep.1 / p.rep.2) := by
        apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
        refine ⟨p.rep.2, ?_⟩
        apply Prod.ext
        · exact mul_div_cancel₀ p.rep.1 hp
        · exact mul_one _

variable [Algebra K L]

/-- A Galois automorphism fixes every projective point defined over the base field. -/
theorem projectiveFieldMap_algEquiv_algebraMap (σ : L ≃ₐ[K] L)
    (p : Projectivization K (K × K)) :
    projectiveFieldMap σ.toRingHom (projectiveFieldMap (algebraMap K L) p) =
      projectiveFieldMap (algebraMap K L) p := by
  rw [← projectiveFieldMap_comp]
  have hσ : σ.toRingHom.comp (algebraMap K L) = algebraMap K L := by
    ext x
    exact σ.commutes x
  rw [hσ]

/-- Galois-fixed projective points over a finite Galois extension descend to the base field. -/
theorem exists_projectiveFieldMap_eq_of_fixed
    [FiniteDimensional K L] [IsGalois K L]
    (p : Projectivization L (L × L))
    (hp : ∀ σ : L ≃ₐ[K] L, projectiveFieldMap σ.toRingHom p = p) :
    ∃ q : Projectivization K (K × K), projectiveFieldMap (algebraMap K L) q = p := by
  rcases eq_infinityPoint_or_exists_affinePoint p with h | ⟨t, h⟩
  · exact ⟨infinityPoint, (projectiveFieldMap_infinityPoint (algebraMap K L)).trans h.symm⟩
  · have ht : ∀ σ : L ≃ₐ[K] L, σ t = t := by
      intro σ
      apply affinePoint_injective
      exact (projectiveFieldMap_affinePoint σ.toRingHom t).symm.trans
        ((congrArg (projectiveFieldMap σ.toRingHom) h.symm).trans ((hp σ).trans h))
    obtain ⟨a, ha⟩ := (IsGalois.mem_range_algebraMap_iff_fixed t).mpr ht
    refine ⟨affinePoint a, ?_⟩
    rw [projectiveFieldMap_affinePoint, ha, ← h]

/-- An equivariant projective linear action descends; its matrix need not be Galois-fixed. -/
theorem exists_projectiveLinearEquiv_descent
    [FiniteDimensional K L] [IsGalois K L]
    (F : (L × L) ≃ₗ[L] (L × L))
    (hF : ∀ (σ : L ≃ₐ[K] L) (p : Projectivization L (L × L)),
      projectiveFieldMap σ.toRingHom (projectiveLinearEquiv F p) =
        projectiveLinearEquiv F (projectiveFieldMap σ.toRingHom p)) :
    ∃ f : (K × K) ≃ₗ[K] (K × K),
      projectiveLinearEquiv (linearEquivFieldMap (algebraMap K L) f) =
        projectiveLinearEquiv F := by
  let a : Projectivization K (K × K) := affinePoint 0
  let b : Projectivization K (K × K) := infinityPoint
  let c : Projectivization K (K × K) := affinePoint 1
  have hab : a ≠ b := affinePoint_ne_infinityPoint 0
  have hcb : c ≠ b := affinePoint_ne_infinityPoint 1
  have hca : c ≠ a := fun h => one_ne_zero (affinePoint_injective h)
  let j := projectiveFieldMap (algebraMap K L)
  have hj : Function.Injective j := projectiveFieldMap_injective (algebraMap K L)
  have hfixed (p : Projectivization K (K × K)) (σ : L ≃ₐ[K] L) :
      projectiveFieldMap σ.toRingHom (projectiveLinearEquiv F (j p)) =
        projectiveLinearEquiv F (j p) := by
    rw [hF, projectiveFieldMap_algEquiv_algebraMap]
  obtain ⟨a', ha'⟩ := exists_projectiveFieldMap_eq_of_fixed
    (projectiveLinearEquiv F (j a)) (hfixed a)
  obtain ⟨b', hb'⟩ := exists_projectiveFieldMap_eq_of_fixed
    (projectiveLinearEquiv F (j b)) (hfixed b)
  obtain ⟨c', hc'⟩ := exists_projectiveFieldMap_eq_of_fixed
    (projectiveLinearEquiv F (j c)) (hfixed c)
  have hne {p q p' q' : Projectivization K (K × K)}
      (hpq : p ≠ q) (hp : j p' = projectiveLinearEquiv F (j p))
      (hq : j q' = projectiveLinearEquiv F (j q)) : p' ≠ q' := by
    intro heq
    apply hpq
    apply hj
    apply (projectiveLinearEquiv F).injective
    rw [← hp, ← hq, heq]
  have hab' : a' ≠ b' := hne hab ha' hb'
  have hcb' : c' ≠ b' := hne hcb hc' hb'
  have hca' : c' ≠ a' := hne hca hc' ha'
  let f := matchTriplesLinearEquiv a b c a' b' c' hab hcb hca hab' hcb' hca'
  refine ⟨f, ?_⟩
  apply projectiveLinearEquiv_eq_of_three _ F (j a) (j b) (j c)
    (hj.ne hab) (hj.ne hca) (hj.ne hcb)
  · rw [projectiveLinearEquiv_fieldMap,
      projectiveLinearEquiv_matchTriplesLinearEquiv, matchTriples_first]
    exact ha'
  · rw [projectiveLinearEquiv_fieldMap,
      projectiveLinearEquiv_matchTriplesLinearEquiv, matchTriples_second]
    exact hb'
  · rw [projectiveLinearEquiv_fieldMap,
      projectiveLinearEquiv_matchTriplesLinearEquiv, matchTriples_third]
    exact hc'

end AnabelianGeometry.ProjectiveLine
