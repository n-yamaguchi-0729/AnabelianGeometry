/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps
import Mathlib.Tactic.FinCases

/-! # Linear coordinate changes on the projective-line scheme

The infinite-field hypothesis is used for polynomial identities by evaluation.
The identification with rational closed points is treated separately.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization

namespace AlgebraicGeometry.ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type u} [Field K]

local notation "V₂" => Fin 2 → K
local notation "P₂" => MvPolynomial (Fin 2) K
local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin 2) K

/-- The standard homogeneous-coordinate vectors. -/
def coordinateBasisVector (j : Fin 2) : V₂ := Pi.single j 1

/-- The coordinate linear forms of the given linear map. -/
def coordinateForm (f : V₂ →ₗ[K] V₂) (i : Fin 2) : P₂ :=
  C (f (coordinateBasisVector 0) i) * X 0 +
    C (f (coordinateBasisVector 1) i) * X 1

theorem coordinate_vector_decomposition (v : V₂) :
    v = v 0 • coordinateBasisVector 0 + v 1 • coordinateBasisVector 1 := by
  ext j
  fin_cases j <;> simp [coordinateBasisVector]

theorem coordinateForm_isHomogeneous (f : V₂ →ₗ[K] V₂) (i : Fin 2) :
    (coordinateForm f i).IsHomogeneous 1 := by
  exact (isHomogeneous_C_mul_X _ _).add (isHomogeneous_C_mul_X _ _)

@[simp]
theorem eval_coordinateForm (f : V₂ →ₗ[K] V₂) (i : Fin 2) (v : V₂) :
    MvPolynomial.eval v (coordinateForm f i) = f v i := by
  calc
    MvPolynomial.eval v (coordinateForm f i) =
        f (coordinateBasisVector 0) i * v 0 +
          f (coordinateBasisVector 1) i * v 1 := by simp [coordinateForm]
    _ = f (v 0 • coordinateBasisVector 0 + v 1 • coordinateBasisVector 1) i := by
      simp [map_add, map_smul, mul_comm]
    _ = f v i := by rw [← coordinate_vector_decomposition v]

/-- Graded pullback of polynomials by a linear coordinate map. -/
def linearSubstitution (f : V₂ →ₗ[K] V₂) : 𝒜 →+*ᵍ 𝒜 where
  toRingHom := (MvPolynomial.aeval (coordinateForm f)).toRingHom
  map_mem {i} {p} hp := by
    change (MvPolynomial.aeval (coordinateForm f) p) ∈ 𝒜 i
    apply (MvPolynomial.mem_homogeneousSubmodule i _).mpr
    have h := ((MvPolynomial.mem_homogeneousSubmodule i p).mp hp).aeval
      (coordinateForm f) (coordinateForm_isHomogeneous f)
    simpa only [one_mul] using h

@[simp]
theorem linearSubstitution_C (f : V₂ →ₗ[K] V₂) (a : K) :
    linearSubstitution f (C a) = C a := by simp [linearSubstitution]

@[simp]
theorem linearSubstitution_X (f : V₂ →ₗ[K] V₂) (i : Fin 2) :
    linearSubstitution f (X i) = coordinateForm f i := by simp [linearSubstitution]

/-- Substitution has the intended evaluation action. -/
@[simp]
theorem eval_linearSubstitution (f : V₂ →ₗ[K] V₂) (p : P₂) (v : V₂) :
    MvPolynomial.eval v (linearSubstitution f p) = MvPolynomial.eval (f v) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp only [linearSubstitution_C, MvPolynomial.eval_C]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
      simp only [map_mul, linearSubstitution_X, eval_coordinateForm, hp, MvPolynomial.eval_X]

private theorem projMap_eq_of_eq
    (f g : 𝒜 →+*ᵍ 𝒜)
    (hf : HomogeneousIdeal.irrelevant 𝒜 ≤
      HomogeneousIdeal.map f (HomogeneousIdeal.irrelevant 𝒜))
    (hg : HomogeneousIdeal.irrelevant 𝒜 ≤
      HomogeneousIdeal.map g (HomogeneousIdeal.irrelevant 𝒜))
    (h : f = g) : Proj.map f hf = Proj.map g hg := by
  cases h
  rfl

section Inverse

variable [Infinite K]

/-- The graded substitutions of inverse linear equivalences are inverse. -/
theorem linearSubstitution_comp_symm (e : V₂ ≃ₗ[K] V₂) :
    (linearSubstitution e.toLinearMap).comp (linearSubstitution e.symm.toLinearMap) =
      GradedRingHom.id 𝒜 := by
  apply GradedRingHom.ext
  intro p
  apply MvPolynomial.funext
  intro v
  change MvPolynomial.eval v
      (linearSubstitution e.toLinearMap (linearSubstitution e.symm.toLinearMap p)) =
    MvPolynomial.eval v p
  rw [eval_linearSubstitution, eval_linearSubstitution]
  change MvPolynomial.eval (e.symm (e v)) p = MvPolynomial.eval v p
  rw [LinearEquiv.symm_apply_apply]

theorem linearSubstitution_symm_comp (e : V₂ ≃ₗ[K] V₂) :
    (linearSubstitution e.symm.toLinearMap).comp (linearSubstitution e.toLinearMap) =
      GradedRingHom.id 𝒜 := by
  simpa using linearSubstitution_comp_symm e.symm

omit [Infinite K] in
/-- A graded right inverse gives the irrelevant-ideal condition for Proj. -/
theorem irrelevant_le_map_of_graded_rightInverse
    (f g : 𝒜 →+*ᵍ 𝒜) (hfg : f.comp g = GradedRingHom.id 𝒜) :
    HomogeneousIdeal.irrelevant 𝒜 ≤
      HomogeneousIdeal.map f (HomogeneousIdeal.irrelevant 𝒜) := by
  apply (HomogeneousIdeal.irrelevant_le 𝒜).mpr
  intro d hd p hp
  have hgp : g p ∈ HomogeneousIdeal.irrelevant 𝒜 :=
    HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hd (g.map_mem hp)
  have hmem : f (g p) ∈ (HomogeneousIdeal.map f (HomogeneousIdeal.irrelevant 𝒜)).toIdeal :=
    Ideal.mem_map_of_mem f.toRingHom hgp
  have hval : f (g p) = p := GradedRingHom.congr_fun hfg p
  rw [hval] at hmem
  exact hmem

theorem irrelevant_le_map_linearSubstitution (e : V₂ ≃ₗ[K] V₂) :
    HomogeneousIdeal.irrelevant 𝒜 ≤
      HomogeneousIdeal.map (linearSubstitution e.toLinearMap) (HomogeneousIdeal.irrelevant 𝒜) :=
  irrelevant_le_map_of_graded_rightInverse
    (linearSubstitution e.toLinearMap) (linearSubstitution e.symm.toLinearMap)
    (linearSubstitution_comp_symm e)

/-- The actual projective-line morphism. -/
def linearCoordinateMap (e : V₂ ≃ₗ[K] V₂) : Proj 𝒜 ⟶ Proj 𝒜 :=
  Proj.map (linearSubstitution e.toLinearMap) (irrelevant_le_map_linearSubstitution e)

/-- The actual projective-line scheme isomorphism. -/
def linearCoordinateIso (e : V₂ ≃ₗ[K] V₂) : Proj 𝒜 ≅ Proj 𝒜 where
  hom := linearCoordinateMap e
  inv := linearCoordinateMap e.symm
  hom_inv_id := by
    unfold linearCoordinateMap
    calc
      Proj.map (linearSubstitution e.toLinearMap)
          (irrelevant_le_map_linearSubstitution e) ≫
        Proj.map (linearSubstitution e.symm.toLinearMap)
          (irrelevant_le_map_linearSubstitution e.symm) =
        Proj.map
          ((linearSubstitution e.toLinearMap).comp (linearSubstitution e.symm.toLinearMap))
          (HomogeneousIdeal.irrelevant_le_map_comp
            (irrelevant_le_map_linearSubstitution e.symm)
            (irrelevant_le_map_linearSubstitution e)) :=
        (Proj.map_comp (linearSubstitution e.symm.toLinearMap)
          (linearSubstitution e.toLinearMap)
          (irrelevant_le_map_linearSubstitution e.symm)
          (irrelevant_le_map_linearSubstitution e)).symm
      _ = Proj.map (GradedRingHom.id 𝒜)
          (le_of_eq (HomogeneousIdeal.map_id (I := HomogeneousIdeal.irrelevant 𝒜)).symm) :=
        projMap_eq_of_eq _ _ _ _ (linearSubstitution_comp_symm e)
      _ = 𝟙 _ := Proj.map_id
  inv_hom_id := by
    unfold linearCoordinateMap
    calc
      Proj.map (linearSubstitution e.symm.toLinearMap)
          (irrelevant_le_map_linearSubstitution e.symm) ≫
        Proj.map (linearSubstitution e.toLinearMap)
          (irrelevant_le_map_linearSubstitution e) =
        Proj.map
          ((linearSubstitution e.symm.toLinearMap).comp (linearSubstitution e.toLinearMap))
          (HomogeneousIdeal.irrelevant_le_map_comp
            (irrelevant_le_map_linearSubstitution e)
            (irrelevant_le_map_linearSubstitution e.symm)) :=
        (Proj.map_comp (linearSubstitution e.toLinearMap)
          (linearSubstitution e.symm.toLinearMap)
          (irrelevant_le_map_linearSubstitution e)
          (irrelevant_le_map_linearSubstitution e.symm)).symm
      _ = Proj.map (GradedRingHom.id 𝒜)
          (le_of_eq (HomogeneousIdeal.map_id (I := HomogeneousIdeal.irrelevant 𝒜)).symm) :=
        projMap_eq_of_eq _ _ _ _ (linearSubstitution_symm_comp e)
      _ = 𝟙 _ := Proj.map_id

@[simp]
theorem linearCoordinateMap_preimage_basicOpen (e : V₂ ≃ₗ[K] V₂) (p : P₂) :
    linearCoordinateMap e ⁻¹ᵁ Proj.basicOpen 𝒜 p =
      Proj.basicOpen 𝒜 (linearSubstitution e.toLinearMap p) :=
  Proj.map_preimage_basicOpen (linearSubstitution e.toLinearMap)
    (irrelevant_le_map_linearSubstitution e) p

end Inverse

/-- Substitution fixes constants on every localization chart. -/
theorem linearSubstitution_awayMap_fromZero (f : V₂ →ₗ[K] V₂) (s : P₂) :
    (Away.map (linearSubstitution f) s).comp
        ((HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers s)).comp
          (grad0Equiv K 1).toRingHom) =
      (HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers (linearSubstitution f s))).comp
          (grad0Equiv K 1).toRingHom := by
  ext r : 1
  apply HomogeneousLocalization.val_injective (Submonoid.powers (linearSubstitution f s))
  change (Localization.mk _ _ : Localization.Away (linearSubstitution f s)) =
    Localization.mk _ _
  refine Localization.mk_eq_mk_iff.mpr (Localization.r_of_eq ?_)
  simp [grad0Equiv, linearSubstitution]

private theorem awayι_comp_π_of_pos
    {d : ℕ} (hd : 0 < d) (s : P₂) (hs : s ∈ 𝒜 d) :
    Proj.awayι 𝒜 s hs hd ≫ π K 1 =
      Spec.map (CommRingCat.ofHom
        ((HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers s)).comp
          (grad0Equiv K 1).toRingHom)) := by
  unfold π
  rw [← Category.assoc, Proj.awayι_toSpecZero,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]

section OverBase

variable [Infinite K]

theorem linearCoordinateMap_comp_π_chart
    (e : V₂ ≃ₗ[K] V₂) {d : ℕ} (hd : 0 < d) (s : P₂) (hs : s ∈ 𝒜 d) :
    Proj.awayι 𝒜 (linearSubstitution e.toLinearMap s)
        ((linearSubstitution e.toLinearMap).map_mem hs) hd
      ≫ linearCoordinateMap e ≫ π K 1 =
    Proj.awayι 𝒜 (linearSubstitution e.toLinearMap s)
        ((linearSubstitution e.toLinearMap).map_mem hs) hd ≫ π K 1 := by
  unfold linearCoordinateMap
  rw [← Category.assoc,
    Proj.awayι_comp_map (linearSubstitution e.toLinearMap)
      (irrelevant_le_map_linearSubstitution e) hd s hs,
    Category.assoc, awayι_comp_π_of_pos hd s hs,
    awayι_comp_π_of_pos hd (linearSubstitution e.toLinearMap s)
      ((linearSubstitution e.toLinearMap).map_mem hs)]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (Spec.map <| CommRingCat.ofHom ·)
    (linearSubstitution_awayMap_fromZero e.toLinearMap s)

/-- The projective-line coordinate morphism is over the original field. -/
theorem linearCoordinateMap_comp_π (e : V₂ ≃ₗ[K] V₂) :
    linearCoordinateMap e ≫ π K 1 = π K 1 := by
  refine (Proj.mapAffineOpenCover (linearSubstitution e.toLinearMap)
    (irrelevant_le_map_linearSubstitution e)).openCover.hom_ext _ _ fun i => ?_
  obtain ⟨⟨d, hd⟩, s, hs⟩ := i
  exact linearCoordinateMap_comp_π_chart e hd s hs

theorem linearCoordinateIso_hom_comp_π (e : V₂ ≃ₗ[K] V₂) :
    (linearCoordinateIso e).hom ≫ π K 1 = π K 1 := linearCoordinateMap_comp_π e

theorem linearCoordinateIso_inv_comp_π (e : V₂ ≃ₗ[K] V₂) :
    (linearCoordinateIso e).inv ≫ π K 1 = π K 1 := linearCoordinateMap_comp_π e.symm

end OverBase

end AlgebraicGeometry.ProjSpace
