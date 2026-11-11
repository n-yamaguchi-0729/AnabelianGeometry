/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.AdicComponentCohomology
public import Nyll.EtaleCohomology.Classical.AdicPullback
public import Nyll.EtaleCohomology.Classical.EtaleRestrictionCohomologyComparison
public import Nyll.EtaleCohomology.Classical.FiniteComponentCohomology
public import Nyll.EtaleCohomology.Classical.IrreducibleComponentCohomology
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Actual component coordinates are the original geometric pullbacks

The original terminal and localized-site comparison agrees with the
original exact inverse-image construction in every degree. Applying
this to the actual component coproduct shows that every coordinate
of the proved decomposition is precisely pullback along the original
reduced component inclusion. The original finite, integral, and
rational maps are retained.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace
open EtaleCohomology.Classical
open scoped TensorProduct

namespace EtaleCohomology

variable (X : Scheme.{u}) [IsNoetherian X]
  (hdom : ∀ x : X, IsDomain (X.presheaf.stalk x))

local notation "U" => reducedIrreducibleComponentEtale X hdom

/-- The actual component coordinate on native sheaf cohomology is
the original geometric pullback, in its original restricted coefficients. -/
theorem reducedIrreducibleComponentsCohomologyEquiv_eq_pullback
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (i : ℕ)
    (a : Sheaf.H.{u} F i) (Z : irreducibleComponents X) :
    reducedIrreducibleComponentsCohomologyEquiv X hdom F i a Z =
      etaleAbelianRestrictionCohomologyPullback (U Z).hom F i a := by
  rw [reducedIrreducibleComponentsCohomologyEquiv_apply]
  exact etaleCohomologyPresheafRestrictionEquiv_terminal_restriction (U Z)
    (reducedIrreducibleComponentsEtaleIsTerminal X hdom)
    (etaleSigmaInj U Z) F i a

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- Each original finite coefficient component coordinate is the
original finite coefficient pullback along that actual inclusion. -/
theorem finiteLevelComponentCohomologyEquiv_eq_pullback (n i : ℕ)
    (a : finiteLevelCohomology X ℓ n i) (Z : irreducibleComponents X) :
    finiteLevelComponentCohomologyEquiv X hdom ℓ n i a Z =
      finiteLevelCohomologyPullback ℓ (U Z).hom n i a := by
  let f : (U Z).left ⟶ X := (U Z).hom
  let A : AddCommGrpCat.{u} := ellPowerCoefficients.{u} ℓ n
  let F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A
  let e : etaleAbelianPullback f ≅ etaleRestriction f AddCommGrpCat.{u} :=
    etaleAbelianPullbackRestrictionIso f
  let c := (etaleAbelianPullbackConstantIso f).app A
  have h := congrArg
    (Sheaf.H.map ((etaleAbelianRestrictionConstantIso f).app A).hom i)
      (reducedIrreducibleComponentsCohomologyEquiv_eq_pullback X hdom F i a Z)
  refine h.trans ?_
  change Sheaf.H.map (e.inv.app F ≫ c.hom) i
      (Sheaf.H.map (e.hom.app F) i
        (etaleAbelianCohomologyPullbackMap f F i a)) =
    Sheaf.H.map c.hom i (etaleAbelianCohomologyPullbackMap f F i a)
  have hc : e.hom.app F ≫ (e.inv.app F ≫ c.hom) = c.hom :=
    (Category.assoc (e.hom.app F) (e.inv.app F) c.hom).symm.trans
      ((congrArg (fun m => m ≫ c.hom) (e.hom_inv_id_app F)).trans (Category.id_comp _))
  exact (Sheaf.H.map_comp_apply (e.hom.app F) (e.inv.app F ≫ c.hom)
    (etaleAbelianCohomologyPullbackMap f F i a)).symm.trans
      (congrArg (fun m => Sheaf.H.map m i
        (etaleAbelianCohomologyPullbackMap f F i a)) hc)

/-- Each coordinate of the original integral comparison is the
original inverse-limit pullback along the same actual component. -/
theorem ellAdicComponentCohomologyEquiv_eq_pullback (i : ℕ)
    (a : ellAdicCohomology X ℓ i) (Z : irreducibleComponents X) :
    ellAdicComponentCohomologyEquiv X hdom ℓ i a Z =
      ellAdicCohomologyPullback ℓ (U Z).hom i a := by
  apply ellAdicCohomology_ext (U Z).left ℓ i
  intro n
  rw [ellAdicComponentCohomologyEquiv_projection, ellAdicProjection_pullback,
    finiteLevelComponentCohomologyEquiv_eq_pullback]
  rfl

/-- Every rational component coordinate is the original rational
geometric pullback, on arbitrary tensors in the original cohomology. -/
theorem rationalEllAdicComponentCohomologyEquiv_eq_pullback (i : ℕ)
    (a : rationalEllAdicCohomology ℓ X i) (Z : irreducibleComponents X) :
    rationalEllAdicComponentCohomologyEquiv X hdom ℓ i a Z =
      rationalEllAdicCohomologyPullback ℓ (U Z).hom i a := by
  induction a using TensorProduct.inductionOn with
  | tmul q a =>
      rw [rationalEllAdicComponentCohomologyEquiv_tmul,
        rationalEllAdicCohomologyPullback_tmul, ellAdicComponentCohomologyEquiv_eq_pullback]
  | add a b ha hb =>
      exact (congrFun ((rationalEllAdicComponentCohomologyEquiv X hdom ℓ i).map_add a b) Z).trans
        ((congrArg₂ (fun x y => x + y) ha hb).trans
          ((rationalEllAdicCohomologyPullback ℓ (U Z).hom i).map_add a b).symm)

end EtaleCohomology
