/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.ProjectiveSpace.MatchTriplesSchemeIso
import Mathlib.Data.Fintype.CardEmbedding

/-! # Three-point rigidity of projective transformations

The uniqueness statements concern the projective action, not its linear
representative. They also give independence of a reference triple and a finite
bound for the projective transformations preserving a finite configuration.
-/

namespace AnabelianGeometry.ProjectiveLine

universe u
variable {K : Type u} [Field K]

theorem linearEquiv_apply_coordinates (f : (K × K) ≃ₗ[K] (K × K)) (v : K × K) :
    f v = transform (f (1, 0)).1 (f (0, 1)).1 (f (1, 0)).2 (f (0, 1)).2 v := by
  have hv : v = v.1 • (1, 0) + v.2 • (0, 1) := by
    apply Prod.ext <;> simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add,
      Prod.snd_add, smul_eq_mul, mul_one, mul_zero, add_zero, zero_add]
  calc
    f v = f (v.1 • (1, 0) + v.2 • (0, 1)) := congrArg f hv
    _ = transform (f (1, 0)).1 (f (0, 1)).1 (f (1, 0)).2 (f (0, 1)).2 v := by
      rw [map_add, map_smul, map_smul]
      apply Prod.ext
      · change v.1 * (f (1, 0)).1 + v.2 * (f (0, 1)).1 =
          (f (1, 0)).1 * v.1 + (f (0, 1)).1 * v.2
        ring
      · change v.1 * (f (1, 0)).2 + v.2 * (f (0, 1)).2 =
          (f (1, 0)).2 * v.1 + (f (0, 1)).2 * v.2
        ring

theorem linearEquiv_coordinate_determinant_ne_zero
    (f : (K × K) ≃ₗ[K] (K × K)) :
    (f (1, 0)).1 * (f (0, 1)).2 - (f (0, 1)).1 * (f (1, 0)).2 ≠ 0 := by
  intro hdet
  have ha : f (1, 0) ≠ 0 := by
    intro ha
    have h := f.injective (ha.trans (map_zero f).symm)
    exact one_ne_zero (congrArg Prod.fst h)
  obtain ⟨c, hc⟩ := exists_bracket_ne_zero (f (1, 0)) ha
  have hab : bracket (f (1, 0)) (f (0, 1)) = 0 := by
    change (f (1, 0)).1 * (f (0, 1)).2 - (f (1, 0)).2 * (f (0, 1)).1 = 0
    rw [mul_comm (f (1, 0)).2 (f (0, 1)).1]
    exact hdet
  have h := eq_smul_of_bracket_eq_zero (f (1, 0)) (f (0, 1)) c hc hab
  rw [← map_smul] at h
  have hz := congrArg Prod.snd (f.injective h)
  change (1 : K) = (bracket (f (0, 1)) c / bracket (f (1, 0)) c) * 0 at hz
  rw [mul_zero] at hz
  exact one_ne_zero hz

/-- Every linear representative preserves the same cross-ratio convention. -/
theorem crossRatio_projectiveLinearEquiv (f : (K × K) ≃ₗ[K] (K × K))
    (a b c d : Projectivization K (K × K)) :
    crossRatio (projectiveLinearEquiv f a) (projectiveLinearEquiv f b)
      (projectiveLinearEquiv f c) (projectiveLinearEquiv f d) = crossRatio a b c d := by
  rw [← a.mk_rep, ← b.mk_rep, ← c.mk_rep, ← d.mk_rep]
  simp only [projectiveLinearEquiv_mk, crossRatio_mk]
  rw [linearEquiv_apply_coordinates f a.rep, linearEquiv_apply_coordinates f b.rep,
    linearEquiv_apply_coordinates f c.rep, linearEquiv_apply_coordinates f d.rep]
  exact homogeneousCrossRatio_transform _ _ _ _
    (linearEquiv_coordinate_determinant_ne_zero f) a.rep b.rep c.rep d.rep

/-- Cross-ratio preserving equivalences agreeing at three distinct points agree everywhere. -/
theorem equiv_eq_of_crossRatio_of_three
    (f g : Projectivization K (K × K) ≃ Projectivization K (K × K))
    (hf : ∀ a b c d, crossRatio (f a) (f b) (f c) (f d) = crossRatio a b c d)
    (hg : ∀ a b c d, crossRatio (g a) (g b) (g c) (g d) = crossRatio a b c d)
    (a b c : Projectivization K (K × K))
    (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (ha : f a = g a) (hb : f b = g b) (hc : f c = g c) : f = g := by
  apply Equiv.ext
  intro p
  by_cases hp : p = b
  · subst p
    exact hb
  · apply eq_of_crossRatio_eq_of_ne (f a) (f b) (f c) (f p) (g p)
      (f.injective.ne hab.symm) (f.injective.ne hca) (f.injective.ne hcb)
      (f.injective.ne hp)
    · rw [hb]
      exact g.injective.ne hp
    · rw [hf, ha, hb, hc, hg]

/-- Three points determine a projective transformation, with no choice of a scalar representative.
-/
theorem projectiveLinearEquiv_eq_of_three
    (f g : (K × K) ≃ₗ[K] (K × K))
    (a b c : Projectivization K (K × K))
    (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (ha : projectiveLinearEquiv f a = projectiveLinearEquiv g a)
    (hb : projectiveLinearEquiv f b = projectiveLinearEquiv g b)
    (hc : projectiveLinearEquiv f c = projectiveLinearEquiv g c) :
    projectiveLinearEquiv f = projectiveLinearEquiv g :=
  equiv_eq_of_crossRatio_of_three (projectiveLinearEquiv f) (projectiveLinearEquiv g)
    (crossRatio_projectiveLinearEquiv f) (crossRatio_projectiveLinearEquiv g)
    a b c hab hca hcb ha hb hc

/-- A transformation matching a labelled configuration is independent of its construction. -/
theorem projectiveLinearEquiv_eq_of_configuration
    {ι : Type*} (x : ι → Projectivization K (K × K)) (hx : Function.Injective x)
    (a b c : ι) (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (f g : (K × K) ≃ₗ[K] (K × K))
    (h : ∀ i, projectiveLinearEquiv f (x i) = projectiveLinearEquiv g (x i)) :
    projectiveLinearEquiv f = projectiveLinearEquiv g :=
  projectiveLinearEquiv_eq_of_three f g (x a) (x b) (x c)
    (hx.ne hab) (hx.ne hca) (hx.ne hcb) (h a) (h b) (h c)

theorem projectiveLinearEquiv_trans (f g : (K × K) ≃ₗ[K] (K × K)) :
    projectiveLinearEquiv (f.trans g) =
      (projectiveLinearEquiv f).trans (projectiveLinearEquiv g) := by
  apply Equiv.ext
  intro p
  induction p using Projectivization.ind with
  | h v hv => rfl

theorem normalizeTriple_first (a b c : Projectivization K (K × K))
    (hab : a ≠ b) (hcb : c ≠ b) (hca : c ≠ a) :
    normalizeTriple a b c hab hcb hca a = affinePoint 0 := by
  calc
    normalizeTriple a b c hab hcb hca a =
        normalizeTriple a b c hab hcb hca (Projectivization.mk K a.rep a.rep_nonzero) :=
      congrArg (normalizeTriple a b c hab hcb hca) a.mk_rep.symm
    _ = affinePoint 0 := normalizeCoordinates_first a.rep b.rep c.rep _ _ _ a.rep_nonzero

theorem normalizeTriple_third (a b c : Projectivization K (K × K))
    (hab : a ≠ b) (hcb : c ≠ b) (hca : c ≠ a) :
    normalizeTriple a b c hab hcb hca c = affinePoint 1 := by
  calc
    normalizeTriple a b c hab hcb hca c =
        normalizeTriple a b c hab hcb hca (Projectivization.mk K c.rep c.rep_nonzero) :=
      congrArg (normalizeTriple a b c hab hcb hca) c.mk_rep.symm
    _ = affinePoint 1 := normalizeCoordinates_third a.rep b.rep c.rep _ _ _ c.rep_nonzero

theorem matchTriples_first (a b c a' b' c' : Projectivization K (K × K))
    (hab : a ≠ b) (hcb : c ≠ b) (hca : c ≠ a)
    (hab' : a' ≠ b') (hcb' : c' ≠ b') (hca' : c' ≠ a') :
    matchTriples a b c a' b' c' hab hcb hca hab' hcb' hca' a = a' := by
  apply (normalizeTriple a' b' c' hab' hcb' hca').injective
  change (normalizeTriple a' b' c' hab' hcb' hca')
    ((normalizeTriple a' b' c' hab' hcb' hca').symm
      (normalizeTriple a b c hab hcb hca a)) = _
  rw [Equiv.apply_symm_apply, normalizeTriple_first, normalizeTriple_first]

theorem matchTriples_third (a b c a' b' c' : Projectivization K (K × K))
    (hab : a ≠ b) (hcb : c ≠ b) (hca : c ≠ a)
    (hab' : a' ≠ b') (hcb' : c' ≠ b') (hca' : c' ≠ a') :
    matchTriples a b c a' b' c' hab hcb hca hab' hcb' hca' c = c' := by
  apply (normalizeTriple a' b' c' hab' hcb' hca').injective
  change (normalizeTriple a' b' c' hab' hcb' hca')
    ((normalizeTriple a' b' c' hab' hcb' hca').symm
      (normalizeTriple a b c hab hcb hca c)) = _
  rw [Equiv.apply_symm_apply, normalizeTriple_third, normalizeTriple_third]

/-- Composition of configuration matching maps is the matching map for the composed labels. -/
theorem projectiveLinearEquiv_comp_of_configuration
    {ι : Type*} (x y z : ι → Projectivization K (K × K))
    (hx : Function.Injective x)
    (a b c : ι) (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (f g h : (K × K) ≃ₗ[K] (K × K))
    (hf : ∀ i, projectiveLinearEquiv f (x i) = y i)
    (hg : ∀ i, projectiveLinearEquiv g (y i) = z i)
    (hh : ∀ i, projectiveLinearEquiv h (x i) = z i) :
    (projectiveLinearEquiv f).trans (projectiveLinearEquiv g) =
      projectiveLinearEquiv h := by
  rw [← projectiveLinearEquiv_trans]
  apply projectiveLinearEquiv_eq_of_configuration x hx a b c hab hca hcb
  intro i
  rw [projectiveLinearEquiv_trans]
  change projectiveLinearEquiv g (projectiveLinearEquiv f (x i)) =
    projectiveLinearEquiv h (x i)
  rw [hf, hg, hh]

/-- Projective actions preserving a finite configuration, without counting scalar representatives.
-/
def ConfigurationTransformations (s : Finset (Projectivization K (K × K))) :=
  {f : Projectivization K (K × K) ≃ Projectivization K (K × K) //
    (∃ e : (K × K) ≃ₗ[K] (K × K), f = projectiveLinearEquiv e) ∧
      ∀ p ∈ s, f p ∈ s}

/-- Evaluation at an ordered triple injects the stabilizer into the distinct triples of the
boundary. -/
def configurationTripleEmbedding (s : Finset (Projectivization K (K × K)))
    (t : Fin 3 ↪ s) : ConfigurationTransformations s ↪ (Fin 3 ↪ s) where
  toFun f :=
    { toFun := fun i => ⟨f.val (t i).val, f.property.2 (t i).val (t i).property⟩
      inj' := by
        intro i j h
        apply t.injective
        apply Subtype.ext
        exact f.val.injective (congrArg Subtype.val h) }
  inj' := by
    intro f g h
    apply Subtype.ext
    obtain ⟨F, hF⟩ := f.property.1
    obtain ⟨G, hG⟩ := g.property.1
    rw [hF, hG]
    apply projectiveLinearEquiv_eq_of_three F G (t 0).val (t 1).val (t 2).val
    · intro hz
      exact (by decide : (0 : Fin 3) ≠ 1) (t.injective (Subtype.ext hz))
    · intro hz
      exact (by decide : (2 : Fin 3) ≠ 0) (t.injective (Subtype.ext hz))
    · intro hz
      exact (by decide : (2 : Fin 3) ≠ 1) (t.injective (Subtype.ext hz))
    · have hz := congrArg (fun q : Fin 3 ↪ s => (q 0).val) h
      change f.val (t 0).val = g.val (t 0).val at hz
      simpa only [hF, hG] using hz
    · have hz := congrArg (fun q : Fin 3 ↪ s => (q 1).val) h
      change f.val (t 1).val = g.val (t 1).val at hz
      simpa only [hF, hG] using hz
    · have hz := congrArg (fun q : Fin 3 ↪ s => (q 2).val) h
      change f.val (t 2).val = g.val (t 2).val at hz
      simpa only [hF, hG] using hz

/-- A finite configuration with at least three points has finitely many projective symmetries. -/
theorem finite_configurationTransformations
    (s : Finset (Projectivization K (K × K))) (hs : 3 ≤ s.card) :
    Finite (ConfigurationTransformations s) := by
  classical
  have hcard : Fintype.card (Fin 3) ≤ Fintype.card s := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using hs
  obtain ⟨t⟩ := Function.Embedding.nonempty_of_card_le hcard
  exact Finite.of_injective (configurationTripleEmbedding s t)
    (configurationTripleEmbedding s t).injective

/-- The upper bound counts ordered triples of distinct boundary points. -/
theorem card_configurationTransformations_le
    (s : Finset (Projectivization K (K × K))) (hs : 3 ≤ s.card)
    [Fintype (ConfigurationTransformations s)] :
    Fintype.card (ConfigurationTransformations s) ≤ s.card.descFactorial 3 := by
  classical
  have hcard : Fintype.card (Fin 3) ≤ Fintype.card s := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using hs
  obtain ⟨t⟩ := Function.Embedding.nonempty_of_card_le hcard
  have h := Fintype.card_le_of_injective (configurationTripleEmbedding s t)
    (configurationTripleEmbedding s t).injective
  simpa only [Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_coe] using h

end AnabelianGeometry.ProjectiveLine
