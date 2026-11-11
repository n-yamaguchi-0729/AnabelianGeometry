/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.BaseChangeFiniteSigmaCohomology
public import Nyll.EtaleCohomology.Classical.IrreducibleComponentCohomology
public import Nyll.EtaleCohomology.Constructible.SigmaRepresenter
public import Nyll.EtaleCohomology.Sites.EtaleRestriction
public import Nyll.SchemeTheory.Divisors.IrreducibleComponentDecomposition
public import Nyll.SchemeTheory.Divisors.ReducedIrreducibleComponentGeometry
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.MorphismProperty.Comma

/-!
# Components of an original étale object over its original base

The actual reduced components of an étale object give an actual
disjoint-union decomposition in the same small étale site. The
component maps are its original scheme immersions. After arbitrary
scheme base change, these same maps jointly detect original
cohomology classes whenever the component index is finite.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace

namespace EtaleCohomology

variable {X : Scheme.{u}} (W : X.Etale)
  (hdom : ∀ w : W.left, IsDomain (W.left.presheaf.stalk w))

section

variable [IsLocallyNoetherian W.left]

/-- An original reduced component, viewed over the unchanged base
of the original étale object. -/
def etaleObjectReducedComponent (Z : irreducibleComponents W.left) : X.Etale :=
  (etalePostcompose W.hom).obj (reducedIrreducibleComponentEtale W.left hdom Z)

/-- The original component immersion is the morphism of étale objects. -/
def etaleObjectReducedComponentMap (Z : irreducibleComponents W.left) :
    etaleObjectReducedComponent W hdom Z ⟶ W :=
  MorphismProperty.Over.homMk (W.left.reducedIrreducibleComponentι Z.1 Z.2) rfl

instance etaleObjectReducedComponent_integral (Z : irreducibleComponents W.left) :
    IsIntegral (etaleObjectReducedComponent W hdom Z).left := by
  change IsIntegral (W.left.reducedIrreducibleComponent Z.1 Z.2)
  infer_instance

instance etaleObjectReducedComponent_finite [IsFinite W.hom]
    (Z : irreducibleComponents W.left) :
    IsFinite (etaleObjectReducedComponent W hdom Z).hom := by
  change IsFinite (W.left.reducedIrreducibleComponentι Z.1 Z.2 ≫ W.hom)
  infer_instance

/-- The proved scheme decomposition is an isomorphism in the original
small étale site, with its unchanged original structure map. -/
def etaleObjectReducedComponentsIso :
    etaleSigma (etaleObjectReducedComponent W hdom) ≅ W := by
  let e := W.left.reducedIrreducibleComponentsIso hdom
  refine MorphismProperty.Over.isoMk e ?_
  apply Sigma.hom_ext
  intro Z
  change Sigma.ι (fun Z : irreducibleComponents W.left =>
    W.left.reducedIrreducibleComponent Z.1 Z.2) Z ≫
      (W.left.reducedIrreducibleComponentsToScheme ≫ W.hom) =
    Sigma.ι _ Z ≫ Sigma.desc
      (fun Z : irreducibleComponents W.left =>
        W.left.reducedIrreducibleComponentι Z.1 Z.2 ≫ W.hom)
  rw [← Category.assoc, Scheme.ι_reducedIrreducibleComponentsToScheme,
    Sigma.ι_comp_desc]

/-- Every summand inclusion is exactly its original component map. -/
theorem etaleObjectReducedComponentsIso_inclusion (Z : irreducibleComponents W.left) :
    etaleSigmaInj (etaleObjectReducedComponent W hdom) Z ≫
        (etaleObjectReducedComponentsIso W hdom).hom =
      etaleObjectReducedComponentMap W hdom Z := by
  apply MorphismProperty.Over.Hom.ext
  exact W.left.ι_reducedIrreducibleComponentsToScheme Z

end

variable [IsNoetherian W.left] {Y : Scheme.{u}} (p : Y ⟶ X)

/-- Original cohomology on a base-changed étale object is detected
on the base changes of its actual integral components. -/
theorem etaleBaseChangeReducedComponentsCohomology_ext
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ)
    (a b : Sheaf.H'.{u} F n ((etaleBaseChange p).obj W))
    (h : ∀ Z : irreducibleComponents W.left,
      (F.cohomologyPresheaf n).map
          ((etaleBaseChange p).map (etaleObjectReducedComponentMap W hdom Z)).op a =
        (F.cohomologyPresheaf n).map
          ((etaleBaseChange p).map (etaleObjectReducedComponentMap W hdom Z)).op b) : a = b := by
  let : Fintype (irreducibleComponents W.left) := W.left.irreducibleComponentsFintype
  apply etaleBaseChangeFiniteSigmaCohomology_ext_of_iso p
    (etaleObjectReducedComponent W hdom) F n (etaleObjectReducedComponentsIso W hdom) a b
  intro Z
  simpa only [etaleObjectReducedComponentsIso_inclusion] using h Z

end EtaleCohomology
