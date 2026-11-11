/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Sites.PointConstantFiber
public import Nyll.EtaleCohomology.Sites.PointSkyscraperExact
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Module.ULift
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Actual cohomology of small products of point skyscrapers

The exact family-of-fibers/skyscrapers adjunction computes classical `Sheaf.H`
as Ext in the coefficient-family category. The fiber of the constant integer
sheaf is the original integer object at each point, so this discrete diagram
is projective. Hence all positive cohomology vanishes, for arbitrary stalk
coefficients. No injectivity of those coefficients is required.
-/

@[expose] public section

noncomputable section

universe u v w

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian
open GrothendieckTopology.Point

namespace EtaleCohomology

private theorem projective_discreteDiagram {ι : Type u}
    {A : Type v} [Category.{w} A] [Abelian A]
    (P : Discrete ι ⥤ A) [∀ i : Discrete ι, Projective (P.obj i)] : Projective P := by
  constructor
  intro E M f e he
  have : ∀ i : Discrete ι, Epi (e.app i) := fun _ => inferInstance
  choose g hg using (fun i : Discrete ι => Projective.factors (f.app i) (e.app i))
  refine ⟨Discrete.natTrans g, ?_⟩
  apply NatTrans.ext
  funext i
  exact hg i

/-- Every positive classical cohomology group of the actual small product
of native point skyscrapers is zero, for arbitrary abelian coefficients. -/
theorem etalePointSkyscraperFamily_cohomology_subsingleton
    (X : Scheme.{u}) {ι : Type u} (Φ : ι → GrothendieckTopology.Point.{u} X.smallEtaleTopology)
    (M : Discrete ι ⥤ AddCommGrpCat.{u}) (n : ℕ) :
    Subsingleton (Sheaf.H.{u} ((familySkyscraperSheafFunctor Φ).obj M) (n + 1)) := by
  let L := familySheafFiber Φ (A := AddCommGrpCat.{u})
  let G := familySkyscraperSheafFunctor Φ (A := AddCommGrpCat.{u})
  let adj : L ⊣ G := familySkyscraperSheafAdjunction Φ
  have : L.IsLeftAdjoint := adj.isLeftAdjoint
  have : PreservesFiniteLimits L :=
    preservesFiniteLimits_of_evaluation L (fun i =>
      inferInstanceAs (PreservesFiniteLimits ((Φ i.as).sheafFiber (A := AddCommGrpCat.{u}))))
  have : PreservesBinaryBiproducts L :=
    preservesBinaryBiproducts_of_preservesBinaryProducts L
  have : L.Additive := Functor.additive_of_preservesBinaryBiproducts L
  have : PreservesBinaryBiproducts G :=
    preservesBinaryBiproducts_of_preservesBinaryProducts G
  have : G.Additive := Functor.additive_of_preservesBinaryBiproducts G
  have : PreservesFiniteColimits G := Functor.preservesFiniteColimits_of_preservesHomology G
  let : HasExt.{u + 1} (Discrete ι ⥤ AddCommGrpCat.{u}) := HasExt.standard _
  let Z := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))
  have hZ : Projective (AddCommGrpCat.of (ULift.{u} ℤ)) :=
    (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).projective_obj
      (ModuleCat.of ℤ (ULift.{u} ℤ))
  have (i : Discrete ι) : Projective ((L.obj Z).obj i) :=
    Projective.of_iso
      (((Φ i.as).constantSheafCompFiberIso AddCommGrpCat.{u}
        (terminalIsTerminal : IsTerminal (⊤_ X.Etale))).app
          (AddCommGrpCat.of (ULift.{u} ℤ))).symm hZ
  have : Projective (L.obj Z) := projective_discreteDiagram (L.obj Z)
  let e : Ext.{u + 1} (L.obj Z) M (n + 1) ≃+
      Sheaf.H.{u} (G.obj M) (n + 1) := adj.extEquiv
  refine subsingleton_of_forall_eq 0 (fun x => ?_)
  apply e.symm.injective
  rw [map_zero]
  exact Ext.eq_zero_of_projective (e.symm x)

end EtaleCohomology
