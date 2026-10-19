/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.ProjectiveSpace.Normalization

/-! # Field maps on projective configurations

Coefficient extension acts on the actual projectivization quotient. It is
injective for every field embedding, and commutes with cross ratios, including
the total cross-ratio function at degenerate tuples.
-/

namespace AnabelianGeometry.ProjectiveLine

universe u v w

variable {K : Type u} {L : Type v} {M : Type w}
  [Field K] [Field L] [Field M]

/-- Apply a field homomorphism to both homogeneous coordinates. -/
def coordinateFieldMap (ι : K →+* L) : (K × K) →ₛₗ[ι] (L × L) where
  toFun a := (ι a.1, ι a.2)
  map_add' a b := Prod.ext (map_add ι a.1 b.1) (map_add ι a.2 b.2)
  map_smul' t a := Prod.ext (map_mul ι t a.1) (map_mul ι t a.2)

theorem coordinateFieldMap_injective (ι : K →+* L) :
    Function.Injective (coordinateFieldMap ι) := by
  intro a b h
  exact Prod.ext (ι.injective (congrArg Prod.fst h))
    (ι.injective (congrArg Prod.snd h))

/-- The coefficient map on projective points. -/
def projectiveFieldMap (ι : K →+* L) :
    Projectivization K (K × K) → Projectivization L (L × L) :=
  Projectivization.map (coordinateFieldMap ι) (coordinateFieldMap_injective ι)

theorem projectiveFieldMap_mk (ι : K →+* L) (a : K × K) (ha : a ≠ 0) :
    projectiveFieldMap ι (Projectivization.mk K a ha) =
      Projectivization.mk L (coordinateFieldMap ι a)
        (map_zero (coordinateFieldMap ι) ▸ (coordinateFieldMap_injective ι).ne ha) :=
  Projectivization.map_mk (coordinateFieldMap ι) (coordinateFieldMap_injective ι) a ha

theorem bracket_coordinateFieldMap (ι : K →+* L) (a b : K × K) :
    bracket (coordinateFieldMap ι a) (coordinateFieldMap ι b) = ι (bracket a b) := by
  change ι a.1 * ι b.2 - ι a.2 * ι b.1 = ι (a.1 * b.2 - a.2 * b.1)
  rw [map_sub, map_mul, map_mul]

theorem homogeneousCrossRatio_coordinateFieldMap (ι : K →+* L)
    (a b c d : K × K) :
    homogeneousCrossRatio (coordinateFieldMap ι a) (coordinateFieldMap ι b)
      (coordinateFieldMap ι c) (coordinateFieldMap ι d) =
        ι (homogeneousCrossRatio a b c d) := by
  simp only [homogeneousCrossRatio, bracket_coordinateFieldMap, map_div₀, map_mul]

/-- Cross ratios commute with arbitrary field embeddings. -/
theorem crossRatio_projectiveFieldMap (ι : K →+* L)
    (a b c d : Projectivization K (K × K)) :
    crossRatio (projectiveFieldMap ι a) (projectiveFieldMap ι b)
      (projectiveFieldMap ι c) (projectiveFieldMap ι d) = ι (crossRatio a b c d) := by
  rw [← a.mk_rep, ← b.mk_rep, ← c.mk_rep, ← d.mk_rep]
  simp only [projectiveFieldMap_mk, crossRatio_mk]
  exact homogeneousCrossRatio_coordinateFieldMap ι a.rep b.rep c.rep d.rep

/-- Extending the field does not identify distinct projective points. -/
theorem projectiveFieldMap_injective (ι : K →+* L) :
    Function.Injective (projectiveFieldMap ι) := by
  intro p q h
  have hm : Projectivization.mk L (coordinateFieldMap ι p.rep)
      (map_zero (coordinateFieldMap ι) ▸
        (coordinateFieldMap_injective ι).ne p.rep_nonzero) =
      Projectivization.mk L (coordinateFieldMap ι q.rep)
      (map_zero (coordinateFieldMap ι) ▸
        (coordinateFieldMap_injective ι).ne q.rep_nonzero) := by
    exact ((projectiveFieldMap_mk ι p.rep p.rep_nonzero).symm.trans
      (congrArg (projectiveFieldMap ι) p.mk_rep)).trans
      (h.trans ((congrArg (projectiveFieldMap ι) q.mk_rep).symm.trans
        (projectiveFieldMap_mk ι q.rep q.rep_nonzero)))
  obtain ⟨t, ht⟩ := (Projectivization.mk_eq_mk_iff' L _ _ _ _).mp hm
  have hz : bracket (coordinateFieldMap ι p.rep) (coordinateFieldMap ι q.rep) = 0 := by
    rw [← ht]
    change (t * ι q.rep.1) * ι q.rep.2 - (t * ι q.rep.2) * ι q.rep.1 = 0
    ring
  rw [bracket_coordinateFieldMap] at hz
  exact (bracket_rep_eq_zero_iff p q).mp (ι.injective (hz.trans (map_zero ι).symm))

theorem projectiveFieldMap_id (p : Projectivization K (K × K)) :
    projectiveFieldMap (RingHom.id K) p = p := by
  induction p using Projectivization.ind with
  | h a ha => rfl

theorem projectiveFieldMap_comp (ι : K →+* L) (τ : L →+* M)
    (p : Projectivization K (K × K)) :
    projectiveFieldMap (τ.comp ι) p = projectiveFieldMap τ (projectiveFieldMap ι p) := by
  induction p using Projectivization.ind with
  | h a ha => rfl

theorem projectiveFieldMap_affinePoint (ι : K →+* L) (t : K) :
    projectiveFieldMap ι (affinePoint t) = affinePoint (ι t) := by
  rw [affinePoint, projectiveFieldMap_mk]
  apply (Projectivization.mk_eq_mk_iff' L _ _ _ _).mpr
  refine ⟨1, ?_⟩
  change (1 : L) • (ι t, 1) = (ι t, ι 1)
  simp only [one_smul, map_one]

theorem projectiveFieldMap_infinityPoint (ι : K →+* L) :
    projectiveFieldMap ι (infinityPoint (K := K)) = infinityPoint := by
  rw [infinityPoint, projectiveFieldMap_mk]
  apply (Projectivization.mk_eq_mk_iff' L _ _ _ _).mpr
  refine ⟨1, ?_⟩
  change (1 : L) • (1, 0) = (ι 1, ι 0)
  simp only [one_smul, map_one, map_zero]

/-- A field automorphism acts by an actual equivalence of projective points. -/
def projectiveFieldEquiv (σ : K ≃+* L) :
    Projectivization K (K × K) ≃ Projectivization L (L × L) where
  toFun := projectiveFieldMap σ.toRingHom
  invFun := projectiveFieldMap σ.symm.toRingHom
  left_inv p := by
    rw [← projectiveFieldMap_comp]
    have hσ : σ.symm.toRingHom.comp σ.toRingHom = RingHom.id K := by
      ext x
      exact σ.symm_apply_apply x
    rw [hσ, projectiveFieldMap_id]
  right_inv p := by
    rw [← projectiveFieldMap_comp]
    have hσ : σ.toRingHom.comp σ.symm.toRingHom = RingHom.id L := by
      ext x
      exact σ.apply_symm_apply x
    rw [hσ, projectiveFieldMap_id]

end AnabelianGeometry.ProjectiveLine
