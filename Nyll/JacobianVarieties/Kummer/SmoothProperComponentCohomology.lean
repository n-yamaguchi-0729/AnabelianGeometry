/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperComponents
public import Nyll.AlgebraicCurves.Models.Construction.CurveIsIntegral
public import Nyll.AlgebraicCurves.Models.Construction.OfSmoothProperCurve
public import Nyll.AlgebraicCurves.Models.Kummer.FiniteAdicH1
public import Nyll.EtaleCohomology.Classical.AdicH0Comparison
public import Nyll.EtaleCohomology.Classical.ComponentCohomologyPullback
public import Nyll.JacobianVarieties.Kummer.SmoothProperCurveH2
public import Nyll.SchemeTheory.FunctionFields.StructureMorphism
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Finiteness.Basic
public import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveOver

/-!
# Original cohomology of all components of a smooth proper curve

The actual finite component decomposition applies to the original
scheme with no connectedness assumption. Each actual component is a
smooth proper integral curve, so the already constructed native H0,
H1, and H2 comparisons supply finite-dimensional original cohomology.
The original coproduct comparison transports this finiteness back to
the original scheme. The empty curve is included.
-/

@[expose] public section

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open EtaleCohomology EtaleCohomology.Classical

namespace AlgebraicGeometry.SmoothProperCurve

variable (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}}
  (c : X ⟶ Spec (CommRingCat.of K)) [IsProper c] [SmoothOfRelativeDimension 1 c]
  (ℓ : ℕ) [Fact ℓ.Prime]

/-- The original rational cohomology decomposes over the actual
geometric components, with all geometric hypotheses supplied by
the original smooth proper curve. -/
def nativeRationalComponentCohomologyEquiv (i : ℕ) :
    rationalEllAdicCohomology ℓ X i ≃ₗ[ℚ_[ℓ]]
      ∀ Z : irreducibleComponents X,
        rationalEllAdicCohomology ℓ (X.reducedIrreducibleComponent Z.1 Z.2) i :=
  let _ : IsNoetherian X := smoothProperScheme_isNoetherian c
  rationalEllAdicComponentCohomologyEquiv X (smoothSchemeDomainStalks c) ℓ i

private theorem componentCoordinate_eq_pullback
    {Y : Scheme.{u}} [IsNoetherian Y] (hdom : ∀ y : Y, IsDomain (Y.presheaf.stalk y))
    (p : ℕ) [Fact p.Prime] (i : ℕ)
    (E : rationalEllAdicCohomology p Y i ≃ₗ[ℚ_[p]]
      ∀ Z : irreducibleComponents Y,
        rationalEllAdicCohomology p (Y.reducedIrreducibleComponent Z.1 Z.2) i)
    (hE : E = rationalEllAdicComponentCohomologyEquiv Y hdom p i)
    (a : rationalEllAdicCohomology p Y i) (Z : irreducibleComponents Y) :
    E a Z = rationalEllAdicCohomologyPullback p (Y.reducedIrreducibleComponentι Z.1 Z.2) i a := by
  have hι :
      (reducedIrreducibleComponentEtale Y hdom Z).hom =
        Y.reducedIrreducibleComponentι Z.1 Z.2 := rfl
  exact (congrArg (fun F => F a Z) hE).trans
    ((rationalEllAdicComponentCohomologyEquiv_eq_pullback Y hdom p i a Z).trans
      (congrArg (fun f : Y.reducedIrreducibleComponent Z.1 Z.2 ⟶ Y =>
        rationalEllAdicCohomologyPullback p f i a) hι))

omit [IsAlgClosed K] in
/-- The actual geometric coordinate is the original pullback by
the original component inclusion. -/
theorem nativeRationalComponentCohomologyEquiv_eq_pullback (i : ℕ)
    (a : rationalEllAdicCohomology ℓ X i) (Z : irreducibleComponents X) :
    nativeRationalComponentCohomologyEquiv K c ℓ i a Z =
      rationalEllAdicCohomologyPullback ℓ (X.reducedIrreducibleComponentι Z.1 Z.2) i a := by
  let _ : IsNoetherian X := smoothProperScheme_isNoetherian c
  exact componentCoordinate_eq_pullback (smoothSchemeDomainStalks c) ℓ i
    (nativeRationalComponentCohomologyEquiv K c ℓ i) rfl a Z

/-- Finite-dimensional components give a finite-dimensional source through a
linear decomposition. -/
private theorem finiteDimensional_of_component_decomposition
    {𝕜 V ι : Type*} {W : ι → Type*} [DivisionRing 𝕜] [Finite ι]
    [AddCommGroup V] [Module 𝕜 V] [∀ z, AddCommGroup (W z)] [∀ z, Module 𝕜 (W z)]
    (E : V ≃ₗ[𝕜] (∀ z, W z)) (hW : ∀ z, FiniteDimensional 𝕜 (W z)) :
    FiniteDimensional 𝕜 V := by
  have : ∀ z, FiniteDimensional 𝕜 (W z) := hW
  exact E.symm.finiteDimensional

include c in
omit [IsAlgClosed K] in
/-- Original H0 is finite-dimensional without a connectedness
assumption on the smooth proper curve. -/
theorem nativeRationalH0_finiteDimensional :
    FiniteDimensional ℚ_[ℓ] (rationalEllAdicCohomology ℓ X 0) := by
  let : Fintype (irreducibleComponents X) := smoothProperComponentsFintype c
  exact finiteDimensional_of_component_decomposition
    (W := fun Z : irreducibleComponents X =>
      rationalEllAdicCohomology ℓ (X.reducedIrreducibleComponent Z.1 Z.2) 0)
    (nativeRationalComponentCohomologyEquiv K c ℓ 0) (fun Z =>
      finiteDimensional_rationalEllAdicH0 (X.reducedIrreducibleComponent Z.1 Z.2) ℓ)

variable (hℓ : IsUnit (ℓ : K))

/-- The integral smooth proper curve model gives finite-dimensional H¹ in
the original cohomology carrier. -/
private theorem finiteDimensional_of_integral_smooth_proper
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}} [IsIntegral C]
    (d : C ⟶ Spec (CommRingCat.of k)) [IsProper d] [SmoothOfRelativeDimension 1 d]
    (p : ℕ) [Fact p.Prime] (hp : IsUnit (p : k)) :
    FiniteDimensional ℚ_[p] (rationalEllAdicCohomology p C 1) := by
  let : Algebra k C.functionField := (AlgebraicCurve.baseToFunctionField d).toAlgebra
  have : AlgebraicCurve.IsCurveOver k C.functionField :=
    AlgebraicCurve.isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one d
      (RingEquiv.refl C.functionField) (fun _ => rfl)
  exact (AlgebraicCurve.CurveModel.ofSmoothProperCurve d).finiteDimensional_rationalEllAdicH1 p hp

include c hℓ in
/-- The actual component's original H1 is finite-dimensional by
the model on that same component and its original function field. -/
theorem nativeRationalComponentH1_finiteDimensional (Z : irreducibleComponents X) :
    FiniteDimensional ℚ_[ℓ]
      (rationalEllAdicCohomology ℓ (X.reducedIrreducibleComponent Z.1 Z.2) 1) := by
  let d := X.reducedIrreducibleComponentι Z.1 Z.2 ≫ c
  have : IsProper d := reducedIrreducibleComponent_isProper c Z
  have : SmoothOfRelativeDimension 1 d := reducedIrreducibleComponent_smooth_one c Z
  exact finiteDimensional_of_integral_smooth_proper d ℓ hℓ

include c hℓ in
/-- Original H1 is finite-dimensional on the whole smooth proper
curve; every actual component supplies its own original finite basis. -/
theorem nativeRationalH1_finiteDimensional :
    FiniteDimensional ℚ_[ℓ] (rationalEllAdicCohomology ℓ X 1) := by
  let : Fintype (irreducibleComponents X) := smoothProperComponentsFintype c
  exact finiteDimensional_of_component_decomposition
    (W := fun Z : irreducibleComponents X =>
      rationalEllAdicCohomology ℓ (X.reducedIrreducibleComponent Z.1 Z.2) 1)
    (nativeRationalComponentCohomologyEquiv K c ℓ 1) (fun Z =>
      nativeRationalComponentH1_finiteDimensional K c ℓ hℓ Z)

include c hℓ in
/-- The actual component's original H2 has the already constructed
native degree comparison and is therefore finite-dimensional. -/
theorem nativeRationalComponentH2_finiteDimensional (Z : irreducibleComponents X) :
    FiniteDimensional ℚ_[ℓ]
      (rationalEllAdicCohomology ℓ (X.reducedIrreducibleComponent Z.1 Z.2) 2) := by
  let d := X.reducedIrreducibleComponentι Z.1 Z.2 ≫ c
  have : IsProper d := reducedIrreducibleComponent_isProper c Z
  have : SmoothOfRelativeDimension 1 d := reducedIrreducibleComponent_smooth_one c Z
  exact nativeRationalEllAdicH2_finiteDimensional K d ℓ hℓ

include c hℓ in
/-- Original H2 is finite-dimensional on the whole smooth proper
curve, through the actual finite decomposition and native degrees. -/
theorem nativeRationalH2_finiteDimensional :
    FiniteDimensional ℚ_[ℓ] (rationalEllAdicCohomology ℓ X 2) := by
  let : Fintype (irreducibleComponents X) := smoothProperComponentsFintype c
  exact finiteDimensional_of_component_decomposition
    (W := fun Z : irreducibleComponents X =>
      rationalEllAdicCohomology ℓ (X.reducedIrreducibleComponent Z.1 Z.2) 2)
    (nativeRationalComponentCohomologyEquiv K c ℓ 2) (fun Z =>
      nativeRationalComponentH2_finiteDimensional K c ℓ hℓ Z)

include c hℓ in
/-- All three original component groups in the curve trace formula
are finite-dimensional, with the hypotheses supplied by the same curve. -/
theorem nativeRationalComponent_finiteDimensional_of_le_two (i : ℕ) (hi : i ≤ 2)
    (Z : irreducibleComponents X) : FiniteDimensional ℚ_[ℓ]
      (rationalEllAdicCohomology ℓ (X.reducedIrreducibleComponent Z.1 Z.2) i) := by
  cases i with
  | zero =>
      exact finiteDimensional_rationalEllAdicH0 (X.reducedIrreducibleComponent Z.1 Z.2) ℓ
  | succ i =>
      cases i with
      | zero => exact nativeRationalComponentH1_finiteDimensional K c ℓ hℓ Z
      | succ i =>
          have hi' : i ≤ 0 := Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hi)
          have hzero : i = 0 := Nat.eq_zero_of_le_zero hi'
          subst i
          exact nativeRationalComponentH2_finiteDimensional K c ℓ hℓ Z

end AlgebraicGeometry.SmoothProperCurve
