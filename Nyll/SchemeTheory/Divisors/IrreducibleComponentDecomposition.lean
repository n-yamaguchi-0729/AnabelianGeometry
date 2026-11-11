/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Divisors.EtaleIrreducibleComponents
public import Nyll.SchemeTheory.Divisors.ReducedIrreducibleComponentGeometry
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.Topology.NoetherianSpace

/-!
# Actual decomposition into reduced irreducible components

For a locally Noetherian scheme with domain stalks, the original
reduced irreducible components are disjoint open and closed subschemes.
Their original inclusions induce an actual coproduct isomorphism onto
the original scheme. If the scheme is Noetherian, the same actual
component index is finite. The construction also covers the empty scheme.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- The actual coproduct of the original reduced components maps to
the original scheme through their original closed immersions. -/
def reducedIrreducibleComponentsToScheme :
    (∐ fun Z : irreducibleComponents X => X.reducedIrreducibleComponent Z.1 Z.2) ⟶ X :=
  Sigma.desc fun Z => X.reducedIrreducibleComponentι Z.1 Z.2

/-- Each actual coproduct coordinate retains its original component immersion. -/
theorem ι_reducedIrreducibleComponentsToScheme (Z : irreducibleComponents X) :
    Sigma.ι (fun W : irreducibleComponents X =>
        X.reducedIrreducibleComponent W.1 W.2) Z ≫
      X.reducedIrreducibleComponentsToScheme =
        X.reducedIrreducibleComponentι Z.1 Z.2 :=
  Sigma.ι_comp_desc _ _

section DomainStalks

variable [IsLocallyNoetherian X]
  (hdom : ∀ x : X, IsDomain (X.presheaf.stalk x))

include hdom

/-- Domain stalks make each actual reduced component immersion open. -/
theorem reducedIrreducibleComponentι_isOpenImmersion
    (Z : Set X) (hZ : Z ∈ irreducibleComponents X) :
    IsOpenImmersion (X.reducedIrreducibleComponentι Z hZ) := by
  have (x : X) : _root_.IsReduced (X.presheaf.stalk x) := by
    have : IsDomain (X.presheaf.stalk x) := hdom x
    infer_instance
  have : IsReduced X := isReduced_of_isReduced_stalk X
  apply isOpenImmersion_of_isClosedImmersion_of_isOpen_range
  rw [range_reducedIrreducibleComponentι]
  exact isOpen_irreducibleComponent_of_isDomain_stalk X hdom Z hZ

/-- Two actual components meeting at a point are the same component. -/
theorem irreducibleComponents_eq_of_mem
    (Z W : irreducibleComponents X) (x : X) (hxZ : x ∈ Z.1) (hxW : x ∈ W.1) :
    Z = W := by
  have hZW : Z.1 ⊆ W.1 := by
    have hsubset : Z.1 ⊆ closure W.1 :=
      (subset_closure_inter_of_isPreirreducible_of_isOpen Z.2.1.2
        (isOpen_irreducibleComponent_of_isDomain_stalk X hdom W.1 W.2)
          ⟨x, hxZ, hxW⟩).trans (closure_mono Set.inter_subset_right)
    rwa [(isClosed_of_mem_irreducibleComponents W.1 W.2).closure_eq] at hsubset
  exact Subtype.ext (Set.Subset.antisymm hZW (Z.2.2 W.2.1 hZW))

/-- The ranges of distinct original component immersions are disjoint. -/
theorem pairwise_disjoint_reducedIrreducibleComponent_ranges :
    Pairwise (fun Z W : irreducibleComponents X =>
      Disjoint (Set.range (X.reducedIrreducibleComponentι Z.1 Z.2))
        (Set.range (X.reducedIrreducibleComponentι W.1 W.2))) := by
  intro Z W hZW
  rw [range_reducedIrreducibleComponentι, range_reducedIrreducibleComponentι]
  apply Set.disjoint_left.mpr
  intro x hxZ hxW
  exact hZW (irreducibleComponents_eq_of_mem X hdom Z W x hxZ hxW)

/-- The original component inclusions give an actual isomorphism
from their coproduct onto the original scheme. -/
theorem reducedIrreducibleComponentsToScheme_isIso :
    IsIso X.reducedIrreducibleComponentsToScheme := by
  have (Z : irreducibleComponents X) :
      IsOpenImmersion (X.reducedIrreducibleComponentι Z.1 Z.2) :=
    reducedIrreducibleComponentι_isOpenImmersion X hdom Z.1 Z.2
  have : IsOpenImmersion X.reducedIrreducibleComponentsToScheme :=
    isOpenImmersion_sigmaDesc _ _
      (pairwise_disjoint_reducedIrreducibleComponent_ranges X hdom)
  have : Epi X.reducedIrreducibleComponentsToScheme.base := by
    rw [TopCat.epi_iff_surjective]
    intro x
    let Z : irreducibleComponents X :=
      ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
    have hx : x ∈ Set.range (X.reducedIrreducibleComponentι Z.1 Z.2) := by
      rw [range_reducedIrreducibleComponentι]
      exact mem_irreducibleComponent
    obtain ⟨z, hz⟩ := hx
    refine ⟨Sigma.ι (fun W : irreducibleComponents X =>
      X.reducedIrreducibleComponent W.1 W.2) Z z, ?_⟩
    change (Sigma.ι _ Z ≫ X.reducedIrreducibleComponentsToScheme) z = x
    rw [ι_reducedIrreducibleComponentsToScheme]
    exact hz
  exact IsOpenImmersion.isIso X.reducedIrreducibleComponentsToScheme

/-- The original scheme is the actual disjoint union of its original
reduced integral components, without supplied decomposition data. -/
def reducedIrreducibleComponentsIso :
    (∐ fun Z : irreducibleComponents X => X.reducedIrreducibleComponent Z.1 Z.2) ≅ X := by
  have : IsIso X.reducedIrreducibleComponentsToScheme :=
    reducedIrreducibleComponentsToScheme_isIso X hdom
  exact asIso X.reducedIrreducibleComponentsToScheme

end DomainStalks

/-- On a Noetherian scheme the actual component index used by the
same coproduct decomposition is finite. -/
@[instance_reducible]
def irreducibleComponentsFintype [IsNoetherian X] : Fintype (irreducibleComponents X) :=
  (NoetherianSpace.finite_irreducibleComponents (α := X)).fintype

end AlgebraicGeometry.Scheme
