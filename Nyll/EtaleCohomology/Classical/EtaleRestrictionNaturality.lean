/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.EtaleRestriction
public import Nyll.EtaleCohomology.Classical.FreeAbelianYoneda
public import Nyll.EtaleCohomology.Sites.EtaleRestriction
public import Nyll.SchemeTheory.Sheaves.OverExtension
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Coefficient naturality of the original localization comparisons

The original terminal-object, localized-site, and small-etale-site
cohomology comparisons commute with the original coefficient maps.
The slice-equivalence comparison is explicitly the exact-functor map
on native Ext, with its original constant-source isomorphism. Its
adjunction unit and counit cancel by the actual triangle identity.
-/

@[expose] public section

noncomputable section

universe v u

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

namespace EtaleCohomology

section Site

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}] [HasExt.{v} (Sheaf J AddCommGrpCat.{v})]

/-- The original terminal-object comparison preserves every actual
coefficient morphism in all degrees. -/
theorem sheafCohomologyTerminalEquiv_naturality
    {T : C} (hT : IsTerminal T) {F G : Sheaf J AddCommGrpCat.{v}}
    (φ : F ⟶ G) (n : ℕ) (a : Sheaf.H.{v} F n) :
    sheafCohomologyTerminalEquiv J hT G n (Sheaf.H.map φ n a) =
      ((Sheaf.cohomologyPresheafFunctor J n).map φ).app (op T)
        (sheafCohomologyTerminalEquiv J hT F n a) := by
  change (Ext.mk₀ (freeAbelianSheafYonedaTerminalIso J hT).hom).comp
      (a.comp (Ext.mk₀ φ) (add_zero n)) (zero_add n) =
    ((Ext.mk₀ (freeAbelianSheafYonedaTerminalIso J hT).hom).comp a
      (zero_add n)).comp (Ext.mk₀ φ) (add_zero n)
  exact (Ext.comp_assoc_of_third_deg_zero _ _ _ (zero_add n)).symm

variable (U : C) [HasSheafify (J.over U) AddCommGrpCat.{v}]
  [HasExt.{v} (Sheaf (J.over U) AddCommGrpCat.{v})] [HasBinaryProducts C]

/-- The actual over-site comparison preserves the original
restriction of each coefficient morphism. -/
theorem sheafCohomologyOverEquiv_naturality
    {F G : Sheaf J AddCommGrpCat.{v}} (φ : F ⟶ G) (n : ℕ)
    (a : Sheaf.H'.{v} F n U) :
    sheafCohomologyOverEquiv J U G n
        (((Sheaf.cohomologyPresheafFunctor J n).map φ).app (op U) a) =
      Sheaf.H.map ((J.overPullback AddCommGrpCat.{v} U).map φ) n
        (sheafCohomologyOverEquiv J U F n a) := by
  change (overAbelianSheafExtensionAdjunction U J).extEquiv
      ((Ext.mk₀ (freeAbelianSheafYonedaOverExtensionIso J U).inv).comp
        (a.comp (Ext.mk₀ φ) (add_zero n)) (zero_add n)) =
    ((overAbelianSheafExtensionAdjunction U J).extEquiv
      ((Ext.mk₀ (freeAbelianSheafYonedaOverExtensionIso J U).inv).comp a
        (zero_add n))).comp
          (Ext.mk₀ ((J.overPullback AddCommGrpCat.{v} U).map φ)) (add_zero n)
  exact (congrArg (fun e => (overAbelianSheafExtensionAdjunction U J).extEquiv e)
    (Ext.comp_assoc_of_third_deg_zero
      (Ext.mk₀ (freeAbelianSheafYonedaOverExtensionIso J U).inv) a (Ext.mk₀ φ)
      (zero_add n)).symm).trans
        ((overAbelianSheafExtensionAdjunction U J).extEquiv_naturality_right₀
          ((Ext.mk₀ (freeAbelianSheafYonedaOverExtensionIso J U).inv).comp a
            (zero_add n)) φ)

end Site

section Etale

variable {X : Scheme.{u}} (V : X.Etale)

/-- The original slice-cohomology equivalence is the actual
exact-functor map, with its original constant-source comparison. -/
theorem etaleSliceAbelianCohomologyEquiv_apply
    (F : Sheaf (X.smallEtaleTopology.over V) AddCommGrpCat.{u}) (n : ℕ)
    (a : Sheaf.H.{u} F n) :
    etaleSliceAbelianCohomologyEquiv V F n a =
      (Ext.mk₀ ((etaleSliceAbelianConstantIso V).app
        (AddCommGrpCat.of (ULift.{u} ℤ))).inv).comp
          (a.mapExactFunctor (etaleSliceAbelianSheafEquivalence V).functor) (zero_add n) := by
  let E := etaleSliceAbelianSheafEquivalence V
  let e := (etaleSliceAbelianConstantIso V).app (AddCommGrpCat.of (ULift.{u} ℤ))
  change (Ext.mk₀ e.inv).comp
      (E.toAdjunction.extEquiv.symm
        (a.comp (Ext.mk₀ (E.toAdjunction.unit.app F)) (add_zero n))) (zero_add n) = _
  rw [Adjunction.extEquiv_symm_apply, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀, Ext.comp_assoc_of_second_deg_zero,
    Ext.mk₀_comp_mk₀, E.toAdjunction.left_triangle_components, Ext.comp_mk₀_id]

/-- The actual slice-equivalence comparison commutes with every
original coefficient map. -/
theorem etaleSliceAbelianCohomologyEquiv_naturality
    {F G : Sheaf (X.smallEtaleTopology.over V) AddCommGrpCat.{u}}
    (φ : F ⟶ G) (n : ℕ) (a : Sheaf.H.{u} F n) :
    etaleSliceAbelianCohomologyEquiv V G n (Sheaf.H.map φ n a) =
      Sheaf.H.map ((etaleSliceAbelianSheafEquivalence V).functor.map φ) n
        (etaleSliceAbelianCohomologyEquiv V F n a) := by
  rw [etaleSliceAbelianCohomologyEquiv_apply,
    etaleSliceAbelianCohomologyEquiv_apply, Sheaf.H.map_apply, Sheaf.H.map_apply,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
  exact (Ext.comp_assoc_of_third_deg_zero _ _ _ (zero_add n)).symm

/-- The original comparison from objectwise cohomology to cohomology
on the actual component scheme retains each original coefficient map. -/
theorem etaleCohomologyPresheafRestrictionEquiv_naturality
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}}
    (φ : F ⟶ G) (n : ℕ) (a : Sheaf.H'.{u} F n V) :
    etaleCohomologyPresheafRestrictionEquiv V G n
        (((Sheaf.cohomologyPresheafFunctor X.smallEtaleTopology n).map φ).app (op V) a) =
      Sheaf.H.map ((etaleRestriction V.hom AddCommGrpCat.{u}).map φ) n
        (etaleCohomologyPresheafRestrictionEquiv V F n a) := by
  change etaleSliceAbelianCohomologyEquiv V (G.over V) n
      (sheafCohomologyOverEquiv X.smallEtaleTopology V G n
        (((Sheaf.cohomologyPresheafFunctor X.smallEtaleTopology n).map φ).app (op V) a)) =
    Sheaf.H.map ((etaleSliceAbelianSheafEquivalence V).functor.map
      ((X.smallEtaleTopology.overPullback AddCommGrpCat.{u} V).map φ)) n
        (etaleSliceAbelianCohomologyEquiv V (F.over V) n
          (sheafCohomologyOverEquiv X.smallEtaleTopology V F n a))
  rw [sheafCohomologyOverEquiv_naturality, etaleSliceAbelianCohomologyEquiv_naturality]

end Etale

end EtaleCohomology
