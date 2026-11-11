/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.AbelianSheafFunctors
public import Nyll.EtaleCohomology.Classical.Etale
public import Nyll.EtaleCohomology.Classical.PullbackCoefficients
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Pullback on classical étale cohomology

The exact inverse image acts on the actual Ext groups defining `Sheaf.H`.
The existing comparison for the constant integer sheaf supplies the first
argument of Ext. No acyclicity or exactness of direct image is needed.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Abelian

namespace EtaleCohomology

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Pullback along an arbitrary scheme morphism on the existing classical
abelian étale cohomology groups. -/
def etaleAbelianCohomologyPullbackMap
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ) :
    Sheaf.H.{u} F n →+ Sheaf.H.{u} ((etaleAbelianPullback f).obj F) n :=
  ((Ext.mk₀ ((etaleAbelianPullbackConstantIso f).app
    (AddCommGrpCat.of (ULift ℤ))).inv).precomp _ (zero_add n)).comp
      ((etaleAbelianPullback f).mapExtAddHom _ F n)

/-- The pullback is obtained from the exact-functor map of extensions and
the actual constant-sheaf comparison. -/
lemma etaleAbelianCohomologyPullbackMap_apply
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ) (x : Sheaf.H.{u} F n) :
    etaleAbelianCohomologyPullbackMap f F n x =
      (Ext.mk₀ ((etaleAbelianPullbackConstantIso f).app
        (AddCommGrpCat.of (ULift ℤ))).inv).comp
          (x.mapExactFunctor (etaleAbelianPullback f)) (zero_add n) := rfl

/-- Pullback on cohomology is natural in the original coefficient sheaf. -/
theorem etaleAbelianCohomologyPullbackMap_naturality
    {F G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}} (φ : F ⟶ G) (n : ℕ)
    (x : Sheaf.H.{u} F n) :
    etaleAbelianCohomologyPullbackMap f G n (Sheaf.H.map φ n x) =
      Sheaf.H.map ((etaleAbelianPullback f).map φ) n
        (etaleAbelianCohomologyPullbackMap f F n x) := by
  rw [etaleAbelianCohomologyPullbackMap_apply, etaleAbelianCohomologyPullbackMap_apply,
    Sheaf.H.map_apply, Sheaf.H.map_apply, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀, Ext.comp_assoc_of_third_deg_zero]

/-- In degree zero, the pullback on extensions is the actual inverse-image
map on maps out of the constant integer sheaf. -/
theorem etaleAbelianCohomologyPullbackMap_zero
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) (x : Sheaf.H.{u} F 0) :
    Ext.addEquiv₀ (etaleAbelianCohomologyPullbackMap f F 0 x) =
      ((etaleAbelianPullbackConstantIso f).app
        (AddCommGrpCat.of (ULift ℤ))).inv ≫
          (etaleAbelianPullback f).map (Ext.addEquiv₀ x) := by
  apply Ext.addEquiv₀.symm.injective
  change Ext.mk₀ (Ext.addEquiv₀ (etaleAbelianCohomologyPullbackMap f F 0 x)) =
    Ext.mk₀ _
  rw [Ext.mk₀_addEquiv₀_apply, etaleAbelianCohomologyPullbackMap_apply]
  nth_rw 1 [← Ext.mk₀_addEquiv₀_apply x]
  rw [Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀]

private def moduleCoefficientAction (R : Type u) [CommRing R]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} R)) (r : R) : F ⟶ F :=
  ObjectProperty.homMk
    { app := fun U => ModuleCat.ofHom (r • LinearMap.id)
      naturality := fun U V g => by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact ((F.obj.map g).hom.map_smul r x).symm }

private theorem moduleCoefficientAction_pullback (R : Type u) [CommRing R]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} R)) (r : R) :
    (etalePullback f R).map (moduleCoefficientAction R F r) =
      moduleCoefficientAction R ((etalePullback f R).obj F) r := by
  let adj := etalePullbackPushforwardAdjunction f R
  apply (adj.homEquiv F ((etalePullback f R).obj F)).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  have hη : moduleCoefficientAction R F r ≫ adj.unit.app F =
      adj.unit.app F ≫ (etalePushforward f R).map
        ((etalePullback f R).map (moduleCoefficientAction R F r)) :=
    adj.unit.naturality (moduleCoefficientAction R F r)
  rw [← hη]
  ext U x
  exact ((adj.unit.app F).hom.app U).hom.map_smul r x

/-- The actual inverse-image comparison respects scalar multiplication on
the underlying abelian sheaves. -/
theorem etalePullbackForgetCoefficientsIso_coefficientAction
    (R : Type u) [CommRing R]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} R)) (r : R) :
    (etaleAbelianPullback f).map (Classical.coefficientAction.{u + 1, u, u, u} F r) ≫
        (etalePullbackForgetCoefficientsIso f R).inv.app F =
      (etalePullbackForgetCoefficientsIso f R).inv.app F ≫
        Classical.coefficientAction.{u + 1, u, u, u} ((etalePullback f R).obj F) r := by
  have h := (etalePullbackForgetCoefficientsIso f R).inv.naturality
    (moduleCoefficientAction R F r)
  change (etaleAbelianPullback f).map (Classical.coefficientAction.{u + 1, u, u, u} F r) ≫
      (etalePullbackForgetCoefficientsIso f R).inv.app F =
    (etalePullbackForgetCoefficientsIso f R).inv.app F ≫
      Classical.forgetCoefficients.{u + 1, u, u, u}.map
        ((etalePullback f R).map (moduleCoefficientAction R F r)) at h
  rw [moduleCoefficientAction_pullback] at h
  exact h

variable (R : Type u) [CommRing R]

/-- Pullback on classical étale cohomology with its original coefficient
module structure, along an arbitrary scheme morphism. -/
def etaleCohomologyPullbackMap
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} R)) (n : ℕ) :
    etaleCohomology Y R F n →ₗ[R]
      etaleCohomology X R ((etalePullback f R).obj F) n where
  toFun x := Sheaf.H.map ((etalePullbackForgetCoefficientsIso f R).inv.app F) n
    (etaleAbelianCohomologyPullbackMap f (Classical.forgetCoefficients.{u + 1, u, u, u}.obj F) n x)
  map_add' x y :=
    ((Sheaf.H.map ((etalePullbackForgetCoefficientsIso f R).inv.app F) n).comp
      (etaleAbelianCohomologyPullbackMap f
        (Classical.forgetCoefficients.{u + 1, u, u, u}.obj F) n)).map_add x y
  map_smul' r x := by
    change Sheaf.H.{u} (Classical.forgetCoefficients.{u + 1, u, u, u}.obj F) n at x
    change Sheaf.H.map ((etalePullbackForgetCoefficientsIso f R).inv.app F) n
        (etaleAbelianCohomologyPullbackMap f (Classical.forgetCoefficients.{u + 1, u, u, u}.obj F) n
          (Sheaf.H.map (Classical.coefficientAction.{u + 1, u, u, u} F r) n x)) =
      Sheaf.H.map (Classical.coefficientAction.{u + 1, u, u, u} ((etalePullback f R).obj F) r) n
        (Sheaf.H.map ((etalePullbackForgetCoefficientsIso f R).inv.app F) n
          (etaleAbelianCohomologyPullbackMap f
            (Classical.forgetCoefficients.{u + 1, u, u, u}.obj F) n x))
    rw [etaleAbelianCohomologyPullbackMap_naturality, ← Sheaf.H.map_comp_apply,
      etalePullbackForgetCoefficientsIso_coefficientAction, Sheaf.H.map_comp_apply]

/-- The coefficient-linear pullback is natural in the original module sheaf. -/
theorem etaleCohomologyPullbackMap_naturality
    {F G : Sheaf Y.smallEtaleTopology (ModuleCat.{u} R)} (φ : F ⟶ G) (n : ℕ)
    (x : etaleCohomology Y R F n) :
    etaleCohomologyPullbackMap f R G n (Classical.cohomologyMap.{u + 1, u, u, u, u} φ n x) =
      Classical.cohomologyMap.{u + 1, u, u, u, u} ((etalePullback f R).map φ) n
        (etaleCohomologyPullbackMap f R F n x) := by
  change Sheaf.H.{u} (Classical.forgetCoefficients.{u + 1, u, u, u}.obj F) n at x
  change Sheaf.H.map ((etalePullbackForgetCoefficientsIso f R).inv.app G) n
      (etaleAbelianCohomologyPullbackMap f (Classical.forgetCoefficients.{u + 1, u, u, u}.obj G) n
        (Sheaf.H.map (Classical.forgetCoefficients.{u + 1, u, u, u}.map φ) n x)) =
    Sheaf.H.map (Classical.forgetCoefficients.{u + 1, u, u, u}.map ((etalePullback f R).map φ)) n
      (Sheaf.H.map ((etalePullbackForgetCoefficientsIso f R).inv.app F) n
        (etaleAbelianCohomologyPullbackMap f
            (Classical.forgetCoefficients.{u + 1, u, u, u}.obj F) n x))
  rw [etaleAbelianCohomologyPullbackMap_naturality, ← Sheaf.H.map_comp_apply,
    ← Sheaf.H.map_comp_apply]
  exact congrArg (fun ψ => Sheaf.H.map ψ n
    (etaleAbelianCohomologyPullbackMap f
            (Classical.forgetCoefficients.{u + 1, u, u, u}.obj F) n x))
      ((etalePullbackForgetCoefficientsIso f R).inv.naturality φ)

end EtaleCohomology
