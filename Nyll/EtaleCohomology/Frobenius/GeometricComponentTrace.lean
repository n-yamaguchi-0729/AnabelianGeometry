/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.ComponentCohomologyPullback
public import Nyll.EtaleCohomology.Classical.ComponentCohomologyIsomorphism
public import Nyll.EtaleCohomology.Classical.ComponentCohomologyTrace
public import Nyll.EtaleCohomology.Classical.ExternalCupPullbackComposition
public import Nyll.EtaleCohomology.Frobenius.ComponentTrace
public import Nyll.EtaleCohomology.Frobenius.RationalAdic
public import Nyll.SchemeTheory.Morphisms.FrobeniusComponents
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Trace

/-!
# The original geometric component contributions

On an actually fixed component, the original geometric Frobenius
power restricts to an endomorphism of that same reduced component.
The original inclusion square identifies its original cohomology
pullback with the actual diagonal block of the original global
Frobenius operator. Thus the component trace formula uses geometric
Frobenius itself, over the original extended constant field.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open EtaleCohomology.Classical

namespace EtaleCohomology

private theorem finiteFamilyDiagonal_eq_of_coordinate
    {K : Type*} [Semiring K] {I : Type*} [DecidableEq I]
    (V : I → Type*) [∀ j, AddCommMonoid (V j)] [∀ j, Module K (V j)]
    {W : Type*} [AddCommMonoid W] [Module K W]
    (E : W ≃ₗ[K] (∀ j, V j)) (T U : Module.End K W)
    (σ : I → I) (a : ∀ j, V (σ j) →ₗ[K] V j)
    (j : I) (f : Module.End K (V j)) (hT : U = T)
    (hcoord : ∀ x, E (T x) j = a j (E x (σ j)))
    (hfixed : ∀ x, E (U x) j = f (E x j)) :
    finiteFamilyDiagonal V σ a j = f := by
  apply LinearMap.ext
  intro b
  let s : ∀ k, V k := LinearMap.single K V j b
  obtain ⟨x, hx⟩ := E.surjective s
  have hchange : E (T x) j = E (U x) j :=
    (congrArg (fun A : Module.End K W => E (A x) j) hT).symm
  have h := (hcoord x).symm.trans (hchange.trans (hfixed x))
  rw [hx] at h
  change a j (s (σ j)) = f b
  exact h.trans (congrArg f (Pi.single_eq_same j b))

private theorem coordinate_eq_of_pullback_square {A B : Scheme.{u}}
    (j : A ⟶ B) (g : B ⟶ B) (f : A ⟶ A) (hsq : j ≫ g = f ≫ j)
    (ℓ : ℕ) [Fact ℓ.Prime] (i : ℕ)
    (coordinate : rationalEllAdicCohomology ℓ B i → rationalEllAdicCohomology ℓ A i)
    (T : Module.End ℚ_[ℓ] (rationalEllAdicCohomology ℓ B i))
    (hc : ∀ x, coordinate x = rationalEllAdicCohomologyPullback ℓ j i x)
    (hT : T = rationalEllAdicCohomologyPullback ℓ g i)
    (x : rationalEllAdicCohomology ℓ B i) :
    coordinate (T x) = rationalEllAdicCohomologyPullback ℓ f i (coordinate x) := by
  have h := (rationalEllAdicCohomologyPullback_comp j g ℓ i).symm.trans
    ((congrArg (fun q : A ⟶ B => rationalEllAdicCohomologyPullback ℓ q i) hsq).trans
      (rationalEllAdicCohomologyPullback_comp f j ℓ i))
  exact (hc (T x)).trans
    ((congrArg (rationalEllAdicCohomologyPullback ℓ j i) (LinearMap.congr_fun hT x)).trans
      ((LinearMap.congr_fun h x).trans
        (congrArg (rationalEllAdicCohomologyPullback ℓ f i) (hc x).symm)))

private theorem componentCoordinate_eq_of_commuting_square {S : Scheme.{u}} [IsNoetherian S]
    (hS : ∀ x : S, IsDomain (S.presheaf.stalk x)) (ℓ : ℕ) [Fact ℓ.Prime]
    (i : ℕ) (Z : irreducibleComponents S) (g : S ⟶ S)
    (f : S.reducedIrreducibleComponent Z.1 Z.2 ⟶ S.reducedIrreducibleComponent Z.1 Z.2)
    (hsq : S.reducedIrreducibleComponentι Z.1 Z.2 ≫ g =
      f ≫ S.reducedIrreducibleComponentι Z.1 Z.2)
    (T : Module.End ℚ_[ℓ] (rationalEllAdicCohomology ℓ S i))
    (hT : T = rationalEllAdicCohomologyPullback ℓ g i)
    (a : rationalEllAdicCohomology ℓ S i) :
    rationalEllAdicComponentCohomologyEquiv S hS ℓ i (T a) Z =
      rationalEllAdicCohomologyPullback ℓ f i
        (rationalEllAdicComponentCohomologyEquiv S hS ℓ i a Z) :=
  coordinate_eq_of_pullback_square (S.reducedIrreducibleComponentι Z.1 Z.2) g f hsq ℓ i
    (fun x => rationalEllAdicComponentCohomologyEquiv S hS ℓ i x Z) T
    (fun x => rationalEllAdicComponentCohomologyEquiv_eq_pullback S hS ℓ i x Z) hT a

private theorem componentDiagonal_eq_of_fixed_coordinate {S : Scheme.{u}} [IsNoetherian S]
    (hS : ∀ x : S, IsDomain (S.presheaf.stalk x)) (e : S ≅ S)
    (ℓ : ℕ) [Fact ℓ.Prime] (i : ℕ) (Z : irreducibleComponents S)
    (U : Module.End ℚ_[ℓ] (rationalEllAdicCohomology ℓ S i))
    (f : S.reducedIrreducibleComponent Z.1 Z.2 ⟶ S.reducedIrreducibleComponent Z.1 Z.2)
    (hpow : U = rationalEllAdicCohomologyPullback ℓ e.hom i)
    (hf : ∀ x, rationalEllAdicComponentCohomologyEquiv S hS ℓ i (U x) Z =
      rationalEllAdicCohomologyPullback ℓ f i
        (rationalEllAdicComponentCohomologyEquiv S hS ℓ i x Z)) :
    rationalEllAdicComponentDiagonal e ℓ i Z = rationalEllAdicCohomologyPullback ℓ f i := by
  let _ : DecidableEq (irreducibleComponents S) := Classical.decEq _
  let V : irreducibleComponents S → Type u := fun W =>
    rationalEllAdicCohomology ℓ (S.reducedIrreducibleComponent W.1 W.2) i
  let E : rationalEllAdicCohomology ℓ S i ≃ₗ[ℚ_[ℓ]] (∀ W, V W) :=
    rationalEllAdicComponentCohomologyEquiv S hS ℓ i
  have h := finiteFamilyDiagonal_eq_of_coordinate V E
    (rationalEllAdicCohomologyPullback ℓ e.hom i) U
    (Scheme.irreducibleComponentsIsoEquiv e)
    (fun W => rationalEllAdicCohomologyPullback ℓ (Scheme.reducedIrreducibleComponentIso e W).hom i)
    Z (rationalEllAdicCohomologyPullback ℓ f i) hpow
    (fun x => rationalEllAdicComponentCohomologyEquiv_isomorphism hS hS e ℓ i x Z) hf
  exact h

variable (k Ω : Type u) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
  [Algebra.IsAlgebraic k Ω] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
  (ℓ : ℕ) [Fact ℓ.Prime]

local notation "Y" => (pullback (X ↘ Spec (CommRingCat.of k))
  (Spec.algebraMap k Ω) : Scheme)

variable [IsNoetherian (pullback (X ↘ Spec (CommRingCat.of k))
    (Spec.algebraMap k Ω))]
  (hdom : ∀ x : (pullback (X ↘ Spec (CommRingCat.of k))
      (Spec.algebraMap k Ω) : Scheme.{u}),
    IsDomain ((pullback (X ↘ Spec (CommRingCat.of k))
      (Spec.algebraMap k Ω) : Scheme.{u}).presheaf.stalk x))

/-- On an actually fixed component, the coordinate of the original
global Frobenius power is the original pullback of its actual
geometric restriction to that same component. -/
theorem finiteFieldFrobeniusRationalEllAdicCohomology_fixedComponent (i m : ℕ)
    (a : rationalEllAdicCohomology ℓ Y i) (Z : irreducibleComponents Y)
    (hZ : Scheme.irreducibleComponentsIsoEquiv (inverseArithmeticFrobeniusPowerIso k Ω X m) Z = Z) :
    rationalEllAdicComponentCohomologyEquiv Y hdom ℓ i
        (((finiteFieldFrobeniusRationalEllAdicCohomology k Ω X ℓ i) ^ m) a) Z =
      rationalEllAdicCohomologyPullback ℓ
        (Scheme.constantBaseChangeFrobeniusFixedComponent k Ω X m Z hZ) i
          (rationalEllAdicComponentCohomologyEquiv Y hdom ℓ i a Z) := by
  let v := ((End.of (Scheme.constantBaseChangeFrobenius k Ω X)) ^ m).asHom
  let vZ := Scheme.constantBaseChangeFrobeniusFixedComponent k Ω X m Z hZ
  have h := componentCoordinate_eq_of_commuting_square (S := Y) hdom ℓ i Z v vZ
    (Scheme.constantBaseChangeFrobeniusFixedComponent_ι k Ω X m Z hZ).symm
    ((finiteFieldFrobeniusRationalEllAdicCohomology k Ω X ℓ i) ^ m)
    (finiteFieldFrobeniusRationalEllAdicCohomology_pow k Ω X ℓ i m) a
  exact h

include hdom in
/-- The actual diagonal block is the actual geometric component
endomorphism's original pullback, with no transported action left
as an unproved comparison. -/
theorem rationalEllAdicComponentDiagonal_eq_geometricFrobenius (i m : ℕ)
    (Z : irreducibleComponents Y)
    (hZ : Scheme.irreducibleComponentsIsoEquiv (inverseArithmeticFrobeniusPowerIso k Ω X m) Z = Z) :
    rationalEllAdicComponentDiagonal (inverseArithmeticFrobeniusPowerIso k Ω X m) ℓ i Z =
      rationalEllAdicCohomologyPullback ℓ
        (Scheme.constantBaseChangeFrobeniusFixedComponent k Ω X m Z hZ) i := by
  have h := componentDiagonal_eq_of_fixed_coordinate (S := Y) hdom
    (inverseArithmeticFrobeniusPowerIso k Ω X m) ℓ i Z
    ((finiteFieldFrobeniusRationalEllAdicCohomology k Ω X ℓ i) ^ m)
    (Scheme.constantBaseChangeFrobeniusFixedComponent k Ω X m Z hZ)
    (finiteFieldFrobeniusRationalEllAdicCohomology_pow_eq_iso k Ω X ℓ i m)
    (fun x => finiteFieldFrobeniusRationalEllAdicCohomology_fixedComponent
      k Ω X ℓ hdom i m x Z hZ)
  exact h

include hdom in
/-- Every original Frobenius power has trace equal to the sum of the
original traces of its actual geometric restrictions to fixed components. -/
theorem finiteFieldFrobeniusRationalEllAdicCohomology_trace_geometricComponents (i m : ℕ)
    [∀ Z : irreducibleComponents Y, FiniteDimensional ℚ_[ℓ]
      (rationalEllAdicCohomology ℓ ((Y).reducedIrreducibleComponent Z.1 Z.2) i)] :
    LinearMap.trace ℚ_[ℓ] (rationalEllAdicCohomology ℓ Y i)
        ((finiteFieldFrobeniusRationalEllAdicCohomology k Ω X ℓ i) ^ m) =
      ∑ᶠ Z : {Z : irreducibleComponents Y //
          Scheme.irreducibleComponentsIsoEquiv (inverseArithmeticFrobeniusPowerIso k Ω X m) Z = Z},
        LinearMap.trace ℚ_[ℓ]
          (rationalEllAdicCohomology ℓ ((Y).reducedIrreducibleComponent Z.val.1 Z.val.2) i)
          (rationalEllAdicCohomologyPullback ℓ
            (Scheme.constantBaseChangeFrobeniusFixedComponent k Ω X m Z.val Z.property) i) := by
  have h := finiteFieldFrobeniusRationalEllAdicCohomology_trace_components k Ω X ℓ hdom i m
  refine h.trans (finsum_congr fun Z => ?_)
  exact congrArg (LinearMap.trace ℚ_[ℓ] _) <|
    rationalEllAdicComponentDiagonal_eq_geometricFrobenius k Ω X ℓ hdom i m Z.val Z.property

end EtaleCohomology
