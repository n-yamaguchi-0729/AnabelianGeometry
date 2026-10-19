/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.ProjectiveSpace.PuncturedProjectiveLineBaseChange
import Nyll.SchemeTheory.ProjectiveSpace.RationalPuncturePointInjective

/-! # Every geometric boundary point of the actual rational configuration open

The boundary is indexed by the original finite labels, including infinity.
The point over each label is constructed by coefficient extension of its
homogeneous representative. Its fiber is proved to be a singleton directly
from the homogeneous puncture equation, rather than assumed.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial

namespace AlgebraicGeometry.ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k κ : Type) [Field k] [Field κ] [Algebra k κ]

/-- The original homogeneous representative with coefficients extended to κ. -/
def extendedPunctureCoordinates (p : Projectivization k (k × k)) : κ × κ :=
  (algebraMap k κ p.rep.1, algebraMap k κ p.rep.2)

theorem extendedPunctureCoordinates_ne_zero (p : Projectivization k (k × k)) :
    extendedPunctureCoordinates k κ p ≠ 0 := by
  intro h
  apply p.rep_nonzero
  apply Prod.ext
  · apply (algebraMap k κ).injective
    simpa only [extendedPunctureCoordinates, Prod.fst_zero, map_zero] using congrArg Prod.fst h
  · apply (algebraMap k κ).injective
    simpa only [extendedPunctureCoordinates, Prod.snd_zero, map_zero] using congrArg Prod.snd h

/-- The actual geometric point lying over a prescribed rational puncture. -/
def rationalConfigurationGeometricPoint (p : Projectivization k (k × k)) :
    projectiveLineScheme κ :=
  rationalPuncturePoint (extendedPunctureCoordinates k κ p)
    (extendedPunctureCoordinates_ne_zero k κ p)

theorem rationalConfigurationGeometricPoint_isClosed
    (p : Projectivization k (k × k)) :
    IsClosed ({rationalConfigurationGeometricPoint k κ p} : Set (projectiveLineScheme κ)) :=
  isClosed_singleton_rationalPuncturePoint _ _

private theorem punctureForm_mem_map_iff (v : k × k) (x : projectiveLineScheme κ) :
    punctureForm v ∈ (map k κ 1 x).asHomogeneousIdeal ↔
      punctureForm (algebraMap k κ v.1, algebraMap k κ v.2) ∈ x.asHomogeneousIdeal := by
  change MvPolynomial.map (algebraMap k κ) (punctureForm v) ∈ x.asHomogeneousIdeal ↔ _
  simp only [punctureForm, map_sub, map_mul, MvPolynomial.map_C, MvPolynomial.map_X]

/-- A rational puncture has precisely one geometric point above it. -/
theorem map_eq_projectiveRationalPoint_iff
    (p : Projectivization k (k × k)) (x : projectiveLineScheme κ) :
    map k κ 1 x = projectiveRationalPoint p ↔
      x = rationalConfigurationGeometricPoint k κ p := by
  constructor
  · intro hx
    have hm : punctureForm p.rep ∈ (map k κ 1 x).asHomogeneousIdeal := by
      rw [hx]
      exact punctureForm_mem_rationalPuncturePoint p.rep p.rep_nonzero
    have hm' := (punctureForm_mem_map_iff k κ p.rep x).mp hm
    exact eq_of_punctureForm_mem (extendedPunctureCoordinates k κ p)
      (extendedPunctureCoordinates_ne_zero k κ p) x
      (rationalConfigurationGeometricPoint k κ p) hm'
      (punctureForm_mem_rationalPuncturePoint _ _)
  · intro hx
    subst x
    apply eq_of_punctureForm_mem p.rep p.rep_nonzero
    · exact (punctureForm_mem_map_iff k κ p.rep _).mpr
        (punctureForm_mem_rationalPuncturePoint _ _)
    · exact punctureForm_mem_rationalPuncturePoint p.rep p.rep_nonzero

@[simp]
theorem map_rationalConfigurationGeometricPoint (p : Projectivization k (k × k)) :
    map k κ 1 (rationalConfigurationGeometricPoint k κ p) = projectiveRationalPoint p :=
  (map_eq_projectiveRationalPoint_iff k κ p _).mpr rfl

theorem rationalConfigurationGeometricPoint_injective :
    Function.Injective (rationalConfigurationGeometricPoint k κ) := by
  intro p q hpq
  apply projectiveRationalPoint_injective
  exact (map_rationalConfigurationGeometricPoint k κ p).symm.trans
    ((congrArg (map k κ 1) hpq).trans (map_rationalConfigurationGeometricPoint k κ q))

/-- The actual chart has the inverse-image open as its exact range. -/
theorem rationalConfigurationBaseChangeChart_range
    (s : Finset (Projectivization k (k × k))) :
    Set.range (rationalConfigurationBaseChangeChart k κ s) =
      (map k κ 1) ⁻¹' (rationalConfigurationOpen s : Set (projectiveLineScheme k)) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    have heq := congrArg
      (fun q : Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
        ((rationalConfigurationOpen s).ι ≫ π k 1) ⟶ projectiveLineScheme k => q y)
      (rationalConfigurationBaseChangeChart_comp_map k κ s)
    change map k κ 1 (rationalConfigurationBaseChangeChart k κ s y) =
      (Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
        ((rationalConfigurationOpen s).ι ≫ π k 1) y).val at heq
    change map k κ 1 (rationalConfigurationBaseChangeChart k κ s y) ∈
      rationalConfigurationOpen s
    rw [heq]
    exact (Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
      ((rationalConfigurationOpen s).ι ≫ π k 1) y).property
  · intro hx
    let y : (rationalConfigurationOpen s : Scheme) := ⟨map k κ 1 x, hx⟩
    obtain ⟨z, hz, _⟩ := Scheme.exists_preimage_of_isPullback
      (rationalConfigurationBaseChangeChart_isPullback k κ s) x y rfl
    exact ⟨z, hz⟩

/-- An actual geometric point is in the open exactly when no original label removes it. -/
theorem mem_range_rationalConfigurationBaseChangeChart_iff
    (s : Finset (Projectivization k (k × k))) (x : projectiveLineScheme κ) :
    x ∈ Set.range (rationalConfigurationBaseChangeChart k κ s) ↔
      ∀ p ∈ s, x ≠ rationalConfigurationGeometricPoint k κ p := by
  rw [rationalConfigurationBaseChangeChart_range]
  change map k κ 1 x ∈ rationalConfigurationOpen s ↔ _
  rw [mem_rationalConfigurationOpen_iff]
  exact forall_congr' fun p => forall_congr' fun _ =>
    not_congr (map_eq_projectiveRationalPoint_iff k κ p x)

/-- Every omitted point is the point of one of the original labels. -/
theorem not_mem_range_rationalConfigurationBaseChangeChart_iff
    (s : Finset (Projectivization k (k × k))) (x : projectiveLineScheme κ) :
    x ∉ Set.range (rationalConfigurationBaseChangeChart k κ s) ↔
      ∃ p ∈ s, x = rationalConfigurationGeometricPoint k κ p := by
  classical
  constructor
  · intro hx
    by_contra hn
    apply hx
    apply (mem_range_rationalConfigurationBaseChangeChart_iff k κ s x).mpr
    intro p hp heq
    exact hn ⟨p, hp, heq⟩
  · rintro ⟨p, hp, rfl⟩ hx
    exact (mem_range_rationalConfigurationBaseChangeChart_iff k κ s _).mp hx p hp rfl

/-- The exact label set of the actual geometric boundary. -/
def rationalConfigurationGeometricBoundaryEquiv
    (s : Finset (Projectivization k (k × k))) :
    s ≃ {x : projectiveLineScheme κ |
      x ∉ Set.range (rationalConfigurationBaseChangeChart k κ s)} :=
  Equiv.ofBijective
    (fun p => ⟨rationalConfigurationGeometricPoint k κ p.val,
      (not_mem_range_rationalConfigurationBaseChangeChart_iff k κ s _).mpr
        ⟨p.val, p.property, rfl⟩⟩)
    ⟨by
      intro p q hpq
      exact Subtype.ext (rationalConfigurationGeometricPoint_injective k κ
        (congrArg Subtype.val hpq)), by
      rintro ⟨x, hx⟩
      obtain ⟨p, hp, hxp⟩ :=
        (not_mem_range_rationalConfigurationBaseChangeChart_iff k κ s x).mp hx
      exact ⟨⟨p, hp⟩, Subtype.ext hxp.symm⟩⟩

theorem rationalConfigurationGeometricBoundary_card
    (s : Finset (Projectivization k (k × k))) :
    Nat.card {x : projectiveLineScheme κ |
      x ∉ Set.range (rationalConfigurationBaseChangeChart k κ s)} = s.card := by
  rw [← Nat.card_congr (rationalConfigurationGeometricBoundaryEquiv k κ s)]
  simp only [Nat.card_eq_fintype_card, Fintype.card_coe]

end AlgebraicGeometry.ProjSpace
