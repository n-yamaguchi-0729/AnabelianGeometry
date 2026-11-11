/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Divisors.IrreducibleComponentDecomposition
public import Nyll.SchemeTheory.Divisors.ReducedIrreducibleComponentGeometry
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Topology.Irreducible

/-!
# Original field-valued points on the actual reduced components

Every original field-valued point lies in a unique actual irreducible
component when the locally Noetherian scheme has domain stalks. The
original component inclusion is an open immersion, so the actual point
has a unique scheme-theoretic lift. This gives a bijection on original
scheme morphisms and on points preserving an original structure map.
The constructions include the empty target scheme.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme

variable (Ω : Type u) [Field Ω] (X : Scheme.{u})

/-- The actual component containing the original field-valued point. -/
def pointIrreducibleComponent (p : Spec (CommRingCat.of Ω) ⟶ X) : irreducibleComponents X :=
  ⟨irreducibleComponent (p default), irreducibleComponent_mem_irreducibleComponents (p default)⟩

/-- The whole actual image of the field-valued point lies in that
same original component. -/
theorem point_mem_irreducibleComponent (p : Spec (CommRingCat.of Ω) ⟶ X)
    (x : Spec (CommRingCat.of Ω)) : p x ∈ (pointIrreducibleComponent Ω X p).1 := by
  have hx : x = default := Subsingleton.elim _ _
  rw [hx]
  exact mem_irreducibleComponent

/-- The original component inclusion contains the image of the
original field-valued point. -/
theorem point_range_subset_component (p : Spec (CommRingCat.of Ω) ⟶ X) :
    Set.range p ⊆ Set.range (X.reducedIrreducibleComponentι
      (pointIrreducibleComponent Ω X p).1 (pointIrreducibleComponent Ω X p).2) := by
  rw [range_reducedIrreducibleComponentι]
  rintro _ ⟨x, rfl⟩
  exact point_mem_irreducibleComponent Ω X p x

variable [IsLocallyNoetherian X] (hdom : ∀ x : X, IsDomain (X.presheaf.stalk x))

/-- The actual open component immersion supplies the original
point's scheme-theoretic lift. -/
def pointComponentLift (p : Spec (CommRingCat.of Ω) ⟶ X) :
    Spec (CommRingCat.of Ω) ⟶ X.reducedIrreducibleComponent
      (pointIrreducibleComponent Ω X p).1 (pointIrreducibleComponent Ω X p).2 := by
  have : IsOpenImmersion (X.reducedIrreducibleComponentι
      (pointIrreducibleComponent Ω X p).1 (pointIrreducibleComponent Ω X p).2) :=
    reducedIrreducibleComponentι_isOpenImmersion X hdom _ _
  exact IsOpenImmersion.lift _ p (point_range_subset_component Ω X p)

/-- The original point is exactly the composition of its actual
component lift with the original inclusion. -/
theorem pointComponentLift_ι (p : Spec (CommRingCat.of Ω) ⟶ X) :
    pointComponentLift Ω X hdom p ≫ X.reducedIrreducibleComponentι
        (pointIrreducibleComponent Ω X p).1 (pointIrreducibleComponent Ω X p).2 = p := by
  have : IsOpenImmersion (X.reducedIrreducibleComponentι
      (pointIrreducibleComponent Ω X p).1 (pointIrreducibleComponent Ω X p).2) :=
    reducedIrreducibleComponentι_isOpenImmersion X hdom _ _
  exact IsOpenImmersion.lift_fac _ p (point_range_subset_component Ω X p)

/-- Original points on original components map to the original
scheme through the original component immersions. -/
def reducedComponentHomMap :
    (Σ Z : irreducibleComponents X,
      Spec (CommRingCat.of Ω) ⟶ X.reducedIrreducibleComponent Z.1 Z.2) →
        (Spec (CommRingCat.of Ω) ⟶ X) :=
  fun p => p.2 ≫ X.reducedIrreducibleComponentι p.1.1 p.1.2

include hdom in
/-- Disjointness of the actual components and their original mono
inclusions make the original point map injective. -/
theorem reducedComponentHomMap_injective : Function.Injective (reducedComponentHomMap Ω X) := by
  intro p q hpq
  rcases p with ⟨Z, p⟩
  rcases q with ⟨W, q⟩
  change p ≫ X.reducedIrreducibleComponentι Z.1 Z.2 =
    q ≫ X.reducedIrreducibleComponentι W.1 W.2 at hpq
  have hZ : (p ≫ X.reducedIrreducibleComponentι Z.1 Z.2) default ∈ Z.1 := by
    exact Eq.mp
      (congrArg (fun S : Set X =>
        (p ≫ X.reducedIrreducibleComponentι Z.1 Z.2) default ∈ S)
        (range_reducedIrreducibleComponentι X Z.1 Z.2)) ⟨p default, rfl⟩
  have hW : (p ≫ X.reducedIrreducibleComponentι Z.1 Z.2) default ∈ W.1 := by
    rw [hpq]
    exact Eq.mp
      (congrArg (fun S : Set X =>
        (q ≫ X.reducedIrreducibleComponentι W.1 W.2) default ∈ S)
        (range_reducedIrreducibleComponentι X W.1 W.2)) ⟨q default, rfl⟩
  have hZW : Z = W := irreducibleComponents_eq_of_mem X hdom Z W _ hZ hW
  cases hZW
  have hpq' : p = q := (cancel_mono (X.reducedIrreducibleComponentι Z.1 Z.2)).mp hpq
  cases hpq'
  rfl

include hdom in
/-- The actual component lift supplies every original field-valued point. -/
theorem reducedComponentHomMap_surjective : Function.Surjective (reducedComponentHomMap Ω X) :=
  fun p => ⟨⟨pointIrreducibleComponent Ω X p, pointComponentLift Ω X hdom p⟩,
    pointComponentLift_ι Ω X hdom p⟩

/-- Original field-valued points are the actual disjoint union of
the original field-valued points of the reduced components. -/
def reducedComponentHomEquiv :
    (Σ Z : irreducibleComponents X,
      Spec (CommRingCat.of Ω) ⟶ X.reducedIrreducibleComponent Z.1 Z.2) ≃
        (Spec (CommRingCat.of Ω) ⟶ X) :=
  Equiv.ofBijective (reducedComponentHomMap Ω X)
    ⟨reducedComponentHomMap_injective Ω X hdom, reducedComponentHomMap_surjective Ω X hdom⟩

variable (c : X ⟶ Spec (CommRingCat.of Ω))

/-- The same actual inclusions map original component points over
the field to original points of the given structure morphism. -/
def reducedComponentPointMap :
    (Σ Z : irreducibleComponents X,
      {s : Spec (CommRingCat.of Ω) ⟶ X.reducedIrreducibleComponent Z.1 Z.2 //
        s ≫ (X.reducedIrreducibleComponentι Z.1 Z.2 ≫ c) = 𝟙 _}) →
      {p : Spec (CommRingCat.of Ω) ⟶ X // p ≫ c = 𝟙 _} := fun p =>
  ⟨p.2.val ≫ X.reducedIrreducibleComponentι p.1.1 p.1.2,
    (Category.assoc _ _ _).trans p.2.property⟩

include hdom in
/-- The actual point map remains injective with the original
structure-map equation retained. -/
theorem reducedComponentPointMap_injective :
    Function.Injective (reducedComponentPointMap Ω X c) := by
  intro p q hpq
  rcases p with ⟨Z, p⟩
  rcases q with ⟨W, q⟩
  have hhom : reducedComponentHomMap Ω X ⟨Z, p.val⟩ =
      reducedComponentHomMap Ω X ⟨W, q.val⟩ := congrArg Subtype.val hpq
  have hZW : Z = W := congrArg Sigma.fst (reducedComponentHomMap_injective Ω X hdom hhom)
  cases hZW
  have hpq' : p.val = q.val :=
    (cancel_mono (X.reducedIrreducibleComponentι Z.1 Z.2)).mp hhom
  have hpq'' : p = q := Subtype.ext hpq'
  cases hpq''
  rfl

include hdom in
/-- Every original point over the field has an actual component
lift preserving the same structure-map equation. -/
theorem reducedComponentPointMap_surjective :
    Function.Surjective (reducedComponentPointMap Ω X c) := by
  intro p
  obtain ⟨⟨Z, s⟩, hs⟩ := reducedComponentHomMap_surjective Ω X hdom p.val
  change s ≫ X.reducedIrreducibleComponentι Z.1 Z.2 = p.val at hs
  have hsbase : s ≫ (X.reducedIrreducibleComponentι Z.1 Z.2 ≫ c) = 𝟙 _ := by
    rw [← Category.assoc, hs]
    exact p.property
  exact ⟨⟨Z, ⟨s, hsbase⟩⟩, Subtype.ext hs⟩

/-- The original field-valued points of a structure morphism are
the actual disjoint union of the original points of its components. -/
def reducedComponentPointEquiv :
    (Σ Z : irreducibleComponents X,
      {s : Spec (CommRingCat.of Ω) ⟶ X.reducedIrreducibleComponent Z.1 Z.2 //
        s ≫ (X.reducedIrreducibleComponentι Z.1 Z.2 ≫ c) = 𝟙 _}) ≃
      {p : Spec (CommRingCat.of Ω) ⟶ X // p ≫ c = 𝟙 _} :=
  Equiv.ofBijective (reducedComponentPointMap Ω X c)
    ⟨reducedComponentPointMap_injective Ω X hdom c,
      reducedComponentPointMap_surjective Ω X hdom c⟩

end AlgebraicGeometry.Scheme
