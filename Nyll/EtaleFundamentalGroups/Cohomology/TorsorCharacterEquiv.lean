/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.EtaleFundamentalGroups.Cohomology.TorsorCharacter

/-! # Equivariant torsor equivalences from displacement characters -/

noncomputable section
namespace EtaleFundamentalGroups.Cohomology

variable {G A P Q : Type*} [Group G] [TopologicalSpace G]
  [CommGroup A] [TopologicalSpace A]
  [Torsor A P] [MulAction G P] [SMulCommClass G A P]
  [TopologicalSpace P] [DiscreteTopology P] [ContinuousSMul G P]
  [Torsor A Q] [MulAction G Q] [SMulCommClass G A Q]
  [TopologicalSpace Q] [DiscreteTopology Q] [ContinuousSMul G Q]

/-- Matching displacement characters construct an equivariant equivalence
of the original torsor actions, rather than merely matching their kernels. -/
theorem exists_equivariant_equiv_of_torsorCharacter_eq
    (p : P) (q : Q) (hχ : torsorCharacter (G := G) p = torsorCharacter q) :
    ∃ e : P ≃ Q,
      (∀ (a : A) (x : P), e (a • x) = a • e x) ∧
      ∀ (g : G) (x : P), e (g • x) = g • e x := by
  let e : P ≃ Q :=
    { toFun := fun x => (x /ₛ p : A) • q
      invFun := fun y => (y /ₛ q : A) • p
      left_inv := fun x => by simp only [smul_sdiv, sdiv_smul]
      right_inv := fun y => by simp only [smul_sdiv, sdiv_smul] }
  refine ⟨e, ?_, ?_⟩
  · intro a x
    change (((a • x) /ₛ p : A) • q) = a • ((x /ₛ p : A) • q)
    rw [smul_sdiv_assoc, mul_smul]
  · intro g x
    have hP : g • x = (x /ₛ p : A) • (g • p) := by
      conv_lhs => rw [← sdiv_smul x p]
      exact smul_comm g (x /ₛ p : A) p
    change ((g • x) /ₛ p : A) • q = g • ((x /ₛ p : A) • q)
    rw [hP, smul_sdiv_assoc, mul_smul]
    change (x /ₛ p : A) • ((torsorCharacter (G := G) p g) • q) = _
    rw [hχ]
    change (x /ₛ p : A) • (((g • q) /ₛ q : A) • q) = _
    rw [sdiv_smul]
    exact (smul_comm g (x /ₛ p : A) q).symm

end EtaleFundamentalGroups.Cohomology
