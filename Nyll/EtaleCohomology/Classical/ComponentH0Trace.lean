/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.AdicH0Naturality
public import Nyll.EtaleCohomology.Classical.ComponentCohomologyIsomorphism
public import Nyll.EtaleCohomology.Trace.FiniteFamily
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# The actual H0 trace counts fixed components

The original component decomposition and the original connected H0
coordinates identify the original rational H0 with functions on the
actual component index. An actual scheme automorphism acts by the
actual image permutation, since each original component pullback
preserves its connected H0 coordinate. Its original trace therefore
counts exactly the fixed components, including the empty case.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace
open EtaleCohomology.Classical

namespace EtaleCohomology

variable (X : Scheme.{u}) [IsNoetherian X]
  (hdom : ∀ x : X, IsDomain (X.presheaf.stalk x))
  (ℓ : ℕ) [Fact ℓ.Prime]

/-- The original rational H0 is the space of scalar functions on the
actual finite set of reduced irreducible components. -/
def rationalEllAdicH0ComponentsEquiv :
    rationalEllAdicCohomology ℓ X 0 ≃ₗ[ℚ_[ℓ]] (irreducibleComponents X → ℚ_[ℓ]) :=
  (rationalEllAdicComponentCohomologyEquiv X hdom ℓ 0).trans
    (LinearEquiv.piCongrRight fun Z : irreducibleComponents X =>
      rationalEllAdicH0LinearEquiv (X.reducedIrreducibleComponent Z.1 Z.2) ℓ)

/-- Each scalar coordinate retains the original connected H0 map
on the same actual component. -/
theorem rationalEllAdicH0ComponentsEquiv_apply (a : rationalEllAdicCohomology ℓ X 0)
    (Z : irreducibleComponents X) :
    rationalEllAdicH0ComponentsEquiv X hdom ℓ a Z =
      rationalEllAdicH0LinearEquiv (X.reducedIrreducibleComponent Z.1 Z.2) ℓ
        (rationalEllAdicComponentCohomologyEquiv X hdom ℓ 0 a Z) := rfl

/-- Original pullback by an actual automorphism is the actual
permutation of the original component H0 coordinates. -/
theorem rationalEllAdicH0ComponentsEquiv_isomorphism (e : X ≅ X)
    (a : rationalEllAdicCohomology ℓ X 0) (Z : irreducibleComponents X) :
    rationalEllAdicH0ComponentsEquiv X hdom ℓ
        (rationalEllAdicCohomologyPullback ℓ e.hom 0 a) Z =
      rationalEllAdicH0ComponentsEquiv X hdom ℓ a
        (Scheme.irreducibleComponentsIsoEquiv e Z) := by
  rw [rationalEllAdicH0ComponentsEquiv_apply, rationalEllAdicH0ComponentsEquiv_apply,
    rationalEllAdicComponentCohomologyEquiv_isomorphism]
  exact rationalEllAdicH0LinearEquiv_pullback ℓ
    (Scheme.reducedIrreducibleComponentIso e Z).hom _

/-- Conjugation by the actual scalar-coordinate comparison gives
the original component permutation operator. -/
theorem rationalEllAdicH0ComponentsEquiv_conj (e : X ≅ X) :
    (rationalEllAdicH0ComponentsEquiv X hdom ℓ).conj
        (rationalEllAdicCohomologyPullback ℓ e.hom 0) =
      LinearMap.pi (fun Z : irreducibleComponents X =>
        (LinearMap.proj (Scheme.irreducibleComponentsIsoEquiv e Z) :
          (irreducibleComponents X → ℚ_[ℓ]) →ₗ[ℚ_[ℓ]] ℚ_[ℓ])) := by
  apply LinearMap.ext
  intro a
  funext Z
  change rationalEllAdicH0ComponentsEquiv X hdom ℓ
    (rationalEllAdicCohomologyPullback ℓ e.hom 0
      ((rationalEllAdicH0ComponentsEquiv X hdom ℓ).symm a)) Z =
        a (Scheme.irreducibleComponentsIsoEquiv e Z)
  rw [rationalEllAdicH0ComponentsEquiv_isomorphism, LinearEquiv.apply_symm_apply]

include hdom in
/-- The original rational H0 trace counts the actual fixed components,
without assuming connectedness or a supplied cohomological action. -/
theorem rationalEllAdicH0_trace_eq_fixedComponentCard (e : X ≅ X) :
    LinearMap.trace ℚ_[ℓ] (rationalEllAdicCohomology ℓ X 0)
        (rationalEllAdicCohomologyPullback ℓ e.hom 0) =
      (Nat.card {Z : irreducibleComponents X // Scheme.irreducibleComponentsIsoEquiv e Z = Z} :
        ℚ_[ℓ]) := by
  classical
  let I := irreducibleComponents X
  let : Fintype I := X.irreducibleComponentsFintype
  let σ : I → I := Scheme.irreducibleComponentsIsoEquiv e
  let E := rationalEllAdicH0ComponentsEquiv X hdom ℓ
  let T := rationalEllAdicCohomologyPullback ℓ e.hom 0
  have hconj : E.conj T = LinearMap.pi (fun Z : I =>
      (LinearMap.proj (σ Z) : (I → ℚ_[ℓ]) →ₗ[ℚ_[ℓ]] ℚ_[ℓ])) :=
    rationalEllAdicH0ComponentsEquiv_conj X hdom ℓ e
  calc
    LinearMap.trace ℚ_[ℓ] (rationalEllAdicCohomology ℓ X 0) T =
        LinearMap.trace ℚ_[ℓ] (I → ℚ_[ℓ]) (E.conj T) :=
      (LinearMap.trace_conj' T E).symm
    _ = ∑ Z ∈ Finset.univ.filter (fun Z => σ Z = Z),
        LinearMap.trace ℚ_[ℓ] ℚ_[ℓ]
          ((LinearMap.proj (σ Z)).comp (LinearMap.single ℚ_[ℓ] (fun _ : I => ℚ_[ℓ]) Z)) := by
      rw [hconj]
      simpa only [LinearMap.id_comp] using
        trace_finiteFamily_eq_sum_fixed (fun _ : I => ℚ_[ℓ]) σ
          (fun _ => (LinearMap.id : ℚ_[ℓ] →ₗ[ℚ_[ℓ]] ℚ_[ℓ]))
    _ = ∑ Z ∈ Finset.univ.filter (fun Z => σ Z = Z), (1 : ℚ_[ℓ]) := by
      apply Finset.sum_congr rfl
      intro Z hZ
      have hfix : σ Z = Z := (Finset.mem_filter.mp hZ).2
      rw [hfix, LinearMap.proj_comp_single_same, LinearMap.trace_id,
        CommSemiring.finrank_self, Nat.cast_one]
    _ = ∑ Z : {Z : I // σ Z = Z}, (1 : ℚ_[ℓ]) :=
      Finset.sum_subtype _ (fun Z => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]) (fun _ => (1 : ℚ_[ℓ]))
    _ = (Nat.card {Z : I // σ Z = Z} : ℚ_[ℓ]) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
        Nat.card_eq_fintype_card]

end EtaleCohomology
