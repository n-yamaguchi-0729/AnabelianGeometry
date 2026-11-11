/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.ComponentCohomologyIsomorphism
public import Nyll.EtaleCohomology.Trace.FiniteFamily
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Trace

/-!
# Original cohomology traces on the actual components

An original scheme automorphism permutes the actual reduced components.
The original cohomology decomposition identifies its original pullback
with those component pullbacks. Consequently its trace is the sum of
the actual diagonal blocks on the fixed components. Neither a chosen
component action nor an equivariance hypothesis is an input.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace
open EtaleCohomology.Classical

namespace EtaleCohomology

variable {X : Scheme.{u}} (e : X ≅ X) (ℓ : ℕ) [Fact ℓ.Prime]

/-- The diagonal block of the actual component pullback. The projection
and single-coordinate inclusion supply the canonical identification
when the actual component index is fixed. -/
abbrev rationalEllAdicComponentDiagonal (i : ℕ) (Z : irreducibleComponents X) :
    Module.End ℚ_[ℓ]
      (rationalEllAdicCohomology ℓ (X.reducedIrreducibleComponent Z.1 Z.2) i) :=
  let _ : DecidableEq (irreducibleComponents X) := Classical.decEq _
  finiteFamilyDiagonal
    (fun W : irreducibleComponents X =>
      rationalEllAdicCohomology ℓ (X.reducedIrreducibleComponent W.1 W.2) i)
    (Scheme.irreducibleComponentsIsoEquiv e)
    (fun W => rationalEllAdicCohomologyPullback ℓ
      (Scheme.reducedIrreducibleComponentIso e W).hom i) Z

/-- An actual component not fixed by the original automorphism has
zero diagonal block in its original cohomology. -/
theorem rationalEllAdicComponentDiagonal_eq_zero (i : ℕ)
    (Z : irreducibleComponents X) (hZ : Scheme.irreducibleComponentsIsoEquiv e Z ≠ Z) :
    rationalEllAdicComponentDiagonal e ℓ i Z = 0 := by
  let _ : DecidableEq (irreducibleComponents X) := Classical.decEq _
  exact finiteFamilyDiagonal_eq_zero
    (fun W : irreducibleComponents X =>
      rationalEllAdicCohomology ℓ (X.reducedIrreducibleComponent W.1 W.2) i)
    (Scheme.irreducibleComponentsIsoEquiv e)
    (fun W => rationalEllAdicCohomologyPullback ℓ
      (Scheme.reducedIrreducibleComponentIso e W).hom i) Z hZ

private def fixedComponentTrace {J : Type u} [DecidableEq J]
    (S : J → Scheme.{u}) (σ : J → J) (f : ∀ j, S j ⟶ S (σ j))
    (p : ℕ) [Fact p.Prime] (i : ℕ) : ℚ_[p] :=
  let V : J → Type u := fun j => rationalEllAdicCohomology p (S j) i
  let a : ∀ j, V (σ j) →ₗ[ℚ_[p]] V j := fun j => rationalEllAdicCohomologyPullback p (f j) i
  ∑ᶠ z : {j : J // σ j = j}, LinearMap.trace ℚ_[p] (V z.val) (finiteFamilyDiagonal V σ a z.val)

private theorem trace_eq_fixedComponentTrace {J : Type u} [Finite J] [DecidableEq J]
    {Y : Scheme.{u}} (S : J → Scheme.{u}) (σ : J → J) (f : ∀ j, S j ⟶ S (σ j))
    (p : ℕ) [Fact p.Prime] (i : ℕ)
    [∀ j, FiniteDimensional ℚ_[p] (rationalEllAdicCohomology p (S j) i)]
    (E : rationalEllAdicCohomology p Y i ≃ₗ[ℚ_[p]] (∀ j, rationalEllAdicCohomology p (S j) i))
    (T : Module.End ℚ_[p] (rationalEllAdicCohomology p Y i))
    (hconj : E.conj T = LinearMap.pi
      (fun j => (rationalEllAdicCohomologyPullback p (f j) i).comp (LinearMap.proj (σ j)))) :
    LinearMap.trace ℚ_[p] (rationalEllAdicCohomology p Y i) T = fixedComponentTrace S σ f p i :=
  trace_finiteFamily_conj_eq_finsum_diagonal
    (fun j => rationalEllAdicCohomology p (S j) i) E T σ
    (fun j => rationalEllAdicCohomologyPullback p (f j) i) hconj

variable [IsNoetherian X] (hdom : ∀ x : X, IsDomain (X.presheaf.stalk x))

private theorem siteComponentSchemeData_eq :
    (⟨(fun Z => (reducedIrreducibleComponentEtale X hdom Z).left),
        (fun Z => (Scheme.reducedIrreducibleComponentIso e Z).hom)⟩ :
      Σ S : irreducibleComponents X → Scheme.{u},
        ∀ Z, S Z ⟶ S (Scheme.irreducibleComponentsIsoEquiv e Z)) =
      ⟨(fun Z => X.reducedIrreducibleComponent Z.1 Z.2),
        (fun Z => (Scheme.reducedIrreducibleComponentIso e Z).hom)⟩ := rfl

private def siteFixedComponentTrace (i : ℕ) : ℚ_[ℓ] :=
  let _ : DecidableEq (irreducibleComponents X) := Classical.decEq _
  fixedComponentTrace (fun Z => (reducedIrreducibleComponentEtale X hdom Z).left)
    (Scheme.irreducibleComponentsIsoEquiv e)
    (fun Z => (Scheme.reducedIrreducibleComponentIso e Z).hom) ℓ i

private theorem trace_eq_siteFixedComponentTrace (i : ℕ)
    [hV : ∀ Z : irreducibleComponents X, FiniteDimensional ℚ_[ℓ]
      (rationalEllAdicCohomology ℓ (X.reducedIrreducibleComponent Z.1 Z.2) i)] :
    LinearMap.trace ℚ_[ℓ] (rationalEllAdicCohomology ℓ X i)
        (rationalEllAdicCohomologyPullback ℓ e.hom i) =
      siteFixedComponentTrace e ℓ hdom i := by
  let I := irreducibleComponents X
  let _ : DecidableEq I := Classical.decEq _
  let _ : Fintype I := X.irreducibleComponentsFintype
  let σ : I → I := Scheme.irreducibleComponentsIsoEquiv e
  let S : I → Scheme.{u} := fun Z => (reducedIrreducibleComponentEtale X hdom Z).left
  let f : ∀ Z, S Z ⟶ S (σ Z) := fun Z => (Scheme.reducedIrreducibleComponentIso e Z).hom
  let _ : ∀ Z, FiniteDimensional ℚ_[ℓ] (rationalEllAdicCohomology ℓ (S Z) i) := fun Z => hV Z
  have hconj := rationalEllAdicComponentCohomologyEquiv_conj hdom ℓ e i
  have htrace := trace_eq_fixedComponentTrace S σ f ℓ i
    (rationalEllAdicComponentCohomologyEquiv X hdom ℓ i)
    (rationalEllAdicCohomologyPullback ℓ e.hom i) hconj
  exact htrace

private theorem siteFixedComponentTrace_eq_sum (i : ℕ) :
    siteFixedComponentTrace e ℓ hdom i =
      ∑ᶠ Z : {Z : irreducibleComponents X // Scheme.irreducibleComponentsIsoEquiv e Z = Z},
        LinearMap.trace ℚ_[ℓ]
          (rationalEllAdicCohomology ℓ (X.reducedIrreducibleComponent Z.val.1 Z.val.2) i)
          (rationalEllAdicComponentDiagonal e ℓ i Z.val) := by
  let I := irreducibleComponents X
  let _ : DecidableEq I := Classical.decEq _
  let σ : I → I := Scheme.irreducibleComponentsIsoEquiv e
  have hvalue := congrArg
    (fun data : Σ C : I → Scheme.{u}, ∀ Z, C Z ⟶ C (σ Z) =>
      fixedComponentTrace data.1 σ data.2 ℓ i) (siteComponentSchemeData_eq e hdom)
  exact hvalue

include hdom in
/-- The original rational cohomology trace is supported on the actual
fixed components. The component groups may have different dimensions;
the theorem uses their original pullbacks and no chosen bases. -/
theorem rationalEllAdicCohomology_trace_eq_sum_fixed_components (i : ℕ)
    [hV : ∀ Z : irreducibleComponents X, FiniteDimensional ℚ_[ℓ]
      (rationalEllAdicCohomology ℓ (X.reducedIrreducibleComponent Z.1 Z.2) i)] :
    LinearMap.trace ℚ_[ℓ] (rationalEllAdicCohomology ℓ X i)
        (rationalEllAdicCohomologyPullback ℓ e.hom i) =
      ∑ᶠ Z : {Z : irreducibleComponents X // Scheme.irreducibleComponentsIsoEquiv e Z = Z},
        LinearMap.trace ℚ_[ℓ]
          (rationalEllAdicCohomology ℓ (X.reducedIrreducibleComponent Z.val.1 Z.val.2) i)
          (rationalEllAdicComponentDiagonal e ℓ i Z.val) := by
  exact (trace_eq_siteFixedComponentTrace e ℓ hdom i (hV := hV)).trans
    (siteFixedComponentTrace_eq_sum e ℓ hdom i)

end EtaleCohomology
