/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Tactic.Ring

/-! # Intrinsic projective puncture opens from homogeneous linear forms -/

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial

namespace AlgebraicGeometry.ProjSpace

universe u
variable {K : Type u} [Field K]

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "P₂" => MvPolynomial (Fin 2) K
local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin 2) K

/-- The homogeneous equation of a rational puncture representative. -/
def punctureForm (v : K × K) : P₂ := C v.2 * X 0 - C v.1 * X 1

theorem punctureForm_smul (c : K) (v : K × K) :
    punctureForm (c • v) = C c * punctureForm v := by
  simp only [punctureForm, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, map_mul]
  ring

/-- Nonzero rescaling preserves the actual scheme open. -/
theorem basicOpen_punctureForm_smul (c : K) (hc : c ≠ 0) (v : K × K) :
    Proj.basicOpen 𝒜 (punctureForm (c • v)) = Proj.basicOpen 𝒜 (punctureForm v) := by
  rw [punctureForm_smul]
  ext p
  let I : Ideal P₂ := p.asHomogeneousIdeal.toIdeal
  have hprime : I.IsPrime := p.isPrime
  change C c * punctureForm v ∉ I ↔ punctureForm v ∉ I
  have hC : C c ∉ I := by
    intro h
    have hmul := I.mul_mem_left (C c⁻¹) h
    have hOne : (1 : P₂) ∈ I := by
      simpa only [← map_mul, inv_mul_cancel₀ hc, map_one] using hmul
    exact hprime.ne_top (I.eq_top_iff_one.mpr hOne)
  rw [hprime.mul_mem_iff_mem_or_mem]
  simp only [hC, false_or]

/-- Equal projective representatives define equal puncture opens. -/
theorem basicOpen_punctureForm_eq_of_mk_eq
    (v w : K × K) (hv : v ≠ 0) (hw : w ≠ 0)
    (h : Projectivization.mk K v hv = Projectivization.mk K w hw) :
    Proj.basicOpen 𝒜 (punctureForm v) = Proj.basicOpen 𝒜 (punctureForm w) := by
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' K v w hv hw).mp h
  have hc0 : c ≠ 0 := by
    intro hzero
    apply hv
    simpa only [hzero, zero_smul] using hc.symm
  rw [← hc]
  exact basicOpen_punctureForm_smul c hc0 w

/-- The actual scheme open depends only on the projective point. -/
def projectivePunctureOpen (p : Projectivization K (K × K)) : (Proj 𝒜).Opens :=
  Projectivization.lift
    (fun v : {v : K × K // v ≠ 0} => Proj.basicOpen 𝒜 (punctureForm v.val))
    (by
      intro a b c h
      have hc : c ≠ 0 := by
        intro hzero
        apply a.property
        simpa only [hzero, zero_smul] using h
      change Proj.basicOpen 𝒜 (punctureForm a.val) = Proj.basicOpen 𝒜 (punctureForm b.val)
      rw [h]
      exact basicOpen_punctureForm_smul c hc b.val)
    p

@[simp]
theorem projectivePunctureOpen_mk (v : K × K) (hv : v ≠ 0) :
    projectivePunctureOpen (Projectivization.mk K v hv) =
      Proj.basicOpen 𝒜 (punctureForm v) := rfl

end AlgebraicGeometry.ProjSpace
