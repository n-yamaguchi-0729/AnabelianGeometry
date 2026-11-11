/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.ComponentCohomologyPullback
public import Nyll.EtaleCohomology.Classical.ExternalCupPullbackComposition
public import Nyll.SchemeTheory.Divisors.IrreducibleComponentIsomorphism
public import Mathlib.LinearAlgebra.Pi

/-!
# The actual component action of an original scheme isomorphism

The proved component coordinates are the original pullbacks. The
actual square of component inclusions and component isomorphisms,
together with original pullback composition, therefore computes the
action of a scheme isomorphism on each original cohomology group.
For an automorphism this gives the actual operator between components,
with the index permutation determined by its actual topological map.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace
open EtaleCohomology.Classical

namespace EtaleCohomology

variable {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
  (hX : ∀ x : X, IsDomain (X.presheaf.stalk x))
  (hY : ∀ y : Y, IsDomain (Y.presheaf.stalk y))
  (e : X ≅ Y) (ℓ : ℕ) [Fact ℓ.Prime]

/-- On the original finite groups, the component coordinate of an
original isomorphism is pullback by its actual component isomorphism. -/
theorem finiteLevelComponentCohomologyEquiv_isomorphism (n i : ℕ)
    (a : finiteLevelCohomology Y ℓ n i) (Z : irreducibleComponents X) :
    finiteLevelComponentCohomologyEquiv X hX ℓ n i
        (finiteLevelCohomologyPullback ℓ e.hom n i a) Z =
      finiteLevelCohomologyPullback ℓ (Scheme.reducedIrreducibleComponentIso e Z).hom n i
        (finiteLevelComponentCohomologyEquiv Y hY ℓ n i a
          (Scheme.irreducibleComponentsIsoEquiv e Z)) := by
  rw [finiteLevelComponentCohomologyEquiv_eq_pullback,
    finiteLevelComponentCohomologyEquiv_eq_pullback]
  let ιZ := X.reducedIrreducibleComponentι Z.1 Z.2
  let ιW := Y.reducedIrreducibleComponentι (Scheme.irreducibleComponentsIsoEquiv e Z).1
    (Scheme.irreducibleComponentsIsoEquiv e Z).2
  let c := Scheme.reducedIrreducibleComponentIso e Z
  calc
    _ = finiteLevelCohomologyPullback ℓ (ιZ ≫ e.hom) n i a :=
      (LinearMap.congr_fun (finiteLevelCohomologyPullback_comp ιZ e.hom ℓ n i) a).symm
    _ = finiteLevelCohomologyPullback ℓ (c.hom ≫ ιW) n i a :=
      congrArg (fun f => finiteLevelCohomologyPullback ℓ f n i a)
        (Scheme.reducedIrreducibleComponentIso_hom_ι e Z).symm
    _ = _ := LinearMap.congr_fun (finiteLevelCohomologyPullback_comp c.hom ιW ℓ n i) a

/-- The same original component action holds on the actual integral
inverse-limit families. -/
theorem ellAdicComponentCohomologyEquiv_isomorphism (i : ℕ)
    (a : ellAdicCohomology Y ℓ i) (Z : irreducibleComponents X) :
    ellAdicComponentCohomologyEquiv X hX ℓ i (ellAdicCohomologyPullback ℓ e.hom i a) Z =
      ellAdicCohomologyPullback ℓ (Scheme.reducedIrreducibleComponentIso e Z).hom i
        (ellAdicComponentCohomologyEquiv Y hY ℓ i a
          (Scheme.irreducibleComponentsIsoEquiv e Z)) := by
  rw [ellAdicComponentCohomologyEquiv_eq_pullback, ellAdicComponentCohomologyEquiv_eq_pullback]
  let ιZ := X.reducedIrreducibleComponentι Z.1 Z.2
  let ιW := Y.reducedIrreducibleComponentι (Scheme.irreducibleComponentsIsoEquiv e Z).1
    (Scheme.irreducibleComponentsIsoEquiv e Z).2
  let c := Scheme.reducedIrreducibleComponentIso e Z
  calc
    _ = ellAdicCohomologyPullback ℓ (ιZ ≫ e.hom) i a :=
      (LinearMap.congr_fun (ellAdicCohomologyPullback_comp ιZ e.hom ℓ i) a).symm
    _ = ellAdicCohomologyPullback ℓ (c.hom ≫ ιW) i a :=
      congrArg (fun f => ellAdicCohomologyPullback ℓ f i a)
        (Scheme.reducedIrreducibleComponentIso_hom_ι e Z).symm
    _ = _ := LinearMap.congr_fun (ellAdicCohomologyPullback_comp c.hom ιW ℓ i) a

/-- The original rational isomorphism action has the actual component
permutation and the actual component pullbacks. -/
theorem rationalEllAdicComponentCohomologyEquiv_isomorphism (i : ℕ)
    (a : rationalEllAdicCohomology ℓ Y i) (Z : irreducibleComponents X) :
    rationalEllAdicComponentCohomologyEquiv X hX ℓ i
        (rationalEllAdicCohomologyPullback ℓ e.hom i a) Z =
      rationalEllAdicCohomologyPullback ℓ (Scheme.reducedIrreducibleComponentIso e Z).hom i
        (rationalEllAdicComponentCohomologyEquiv Y hY ℓ i a
          (Scheme.irreducibleComponentsIsoEquiv e Z)) := by
  rw [rationalEllAdicComponentCohomologyEquiv_eq_pullback,
    rationalEllAdicComponentCohomologyEquiv_eq_pullback]
  let ιZ := X.reducedIrreducibleComponentι Z.1 Z.2
  let ιW := Y.reducedIrreducibleComponentι (Scheme.irreducibleComponentsIsoEquiv e Z).1
    (Scheme.irreducibleComponentsIsoEquiv e Z).2
  let c := Scheme.reducedIrreducibleComponentIso e Z
  calc
    _ = rationalEllAdicCohomologyPullback ℓ (ιZ ≫ e.hom) i a :=
      (LinearMap.congr_fun (rationalEllAdicCohomologyPullback_comp ιZ e.hom ℓ i) a).symm
    _ = rationalEllAdicCohomologyPullback ℓ (c.hom ≫ ιW) i a :=
      congrArg (fun f => rationalEllAdicCohomologyPullback ℓ f i a)
        (Scheme.reducedIrreducibleComponentIso_hom_ι e Z).symm
    _ = _ := LinearMap.congr_fun (rationalEllAdicCohomologyPullback_comp c.hom ιW ℓ i) a

/-- Conjugation by the actual decomposition gives exactly the
original operator between the actual component cohomology groups. -/
theorem rationalEllAdicComponentCohomologyEquiv_conj
    (e : X ≅ X) (i : ℕ) :
    (rationalEllAdicComponentCohomologyEquiv X hX ℓ i).conj
        (rationalEllAdicCohomologyPullback ℓ e.hom i) =
      LinearMap.pi (fun Z : irreducibleComponents X =>
        (rationalEllAdicCohomologyPullback ℓ
          (Scheme.reducedIrreducibleComponentIso e Z).hom i).comp
          (LinearMap.proj (Scheme.irreducibleComponentsIsoEquiv e Z))) := by
  apply LinearMap.ext
  intro a
  funext Z
  change rationalEllAdicComponentCohomologyEquiv X hX ℓ i
    (rationalEllAdicCohomologyPullback ℓ e.hom i
      ((rationalEllAdicComponentCohomologyEquiv X hX ℓ i).symm a)) Z =
    rationalEllAdicCohomologyPullback ℓ (Scheme.reducedIrreducibleComponentIso e Z).hom i
      (a (Scheme.irreducibleComponentsIsoEquiv e Z))
  rw [rationalEllAdicComponentCohomologyEquiv_isomorphism (hY := hX),
    LinearEquiv.apply_symm_apply]

end EtaleCohomology
