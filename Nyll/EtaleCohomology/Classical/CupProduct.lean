/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.ConstantCoefficientUnit
public import Nyll.EtaleCohomology.Classical.Etale
public import Nyll.EtaleCohomology.Classical.ModuleCohomology
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.LinearAlgebra.BilinearMap

/-!
# Yoneda cup products on actual étale cohomology

The actual constant regular module sheaf supplies the first coefficient.
Yoneda composition in the native module-sheaf category and the proved
constant-source Ext comparison give a bilinear product on the existing
classical étale cohomology groups, for every scheme and coefficient ring.
Its unit, associativity and naturality retain the original coefficient maps.

This constructs the constant-coefficient cohomology algebra and its action
on cohomology with arbitrary module coefficients. It does not assert curve
duality, graded commutativity or the cohomological Künneth theorem.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Abelian

namespace EtaleCohomology

variable (X : Scheme.{u}) (R : Type u) [CommRing R]

/-- The Yoneda cup action of actual constant-coefficient étale cohomology
on the cohomology of the given module sheaf. -/
def etaleCohomologyCup
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R))
    (a b c : ℕ) (h : a + b = c) :
    etaleCohomology X R
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)) a →ₗ[R]
      etaleCohomology X R F b →ₗ[R] etaleCohomology X R F c :=
  ((Ext.bilinearCompOfLinear R
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R))
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R))
      F a b c h).compl₁₂
    (etaleConstantModuleExtCohomologyEquiv X R
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R))
      a).symm.toLinearMap
    (etaleConstantModuleExtCohomologyEquiv X R F b).symm.toLinearMap).compr₂ₛₗ
      (etaleConstantModuleExtCohomologyEquiv X R F c).toLinearMap

theorem etaleCohomologyCup_apply
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R))
    (a b c : ℕ) (h : a + b = c)
    (x : etaleCohomology X R
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R))
      a) (y : etaleCohomology X R F b) :
    etaleCohomologyCup X R F a b c h x y =
      etaleConstantModuleExtCohomologyEquiv X R F c
        (((etaleConstantModuleExtCohomologyEquiv X R
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R))
          a).symm x).comp
          ((etaleConstantModuleExtCohomologyEquiv X R F b).symm y) h) := rfl

/-- The identity of the actual constant coefficient sheaf gives the
degree-zero cup unit. -/
def etaleCohomologyCupUnit : etaleCohomology X R
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)) 0 :=
  etaleConstantModuleExtCohomologyEquiv X R
    ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)) 0
    (Ext.mk₀ (𝟙
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R))))

/-- The degree-zero unit acts as the identity on every coefficient sheaf. -/
theorem etaleCohomologyCup_unit_left
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) (n : ℕ)
    (x : etaleCohomology X R F n) :
    etaleCohomologyCup X R F 0 n n (zero_add n)
      (etaleCohomologyCupUnit X R) x = x := by
  rw [etaleCohomologyCup_apply, etaleCohomologyCupUnit,
    LinearEquiv.symm_apply_apply, Ext.mk₀_id_comp, LinearEquiv.apply_symm_apply]

/-- Constant-coefficient cohomology has the same right unit. -/
theorem etaleCohomologyCup_unit_right (n : ℕ)
    (x : etaleCohomology X R
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)) n) :
    etaleCohomologyCup X R
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R))
      n 0 n (add_zero n)
      x (etaleCohomologyCupUnit X R) = x := by
  rw [etaleCohomologyCup_apply, etaleCohomologyCupUnit,
    LinearEquiv.symm_apply_apply, Ext.comp_mk₀_id, LinearEquiv.apply_symm_apply]

/-- Associativity of the actual cup action, with all degrees specified. -/
theorem etaleCohomologyCup_assoc
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R))
    (a b c ab bc abc : ℕ) (hab : a + b = ab) (hbc : b + c = bc)
    (habc : a + b + c = abc)
    (x : etaleCohomology X R
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R))
      a)
    (y : etaleCohomology X R
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)) b)
    (z : etaleCohomology X R F c) :
    etaleCohomologyCup X R F ab c abc (by omega)
        (etaleCohomologyCup X R
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R))
          a b ab hab x y) z =
      etaleCohomologyCup X R F a bc abc (by omega)
        x (etaleCohomologyCup X R F b c bc hbc y z) := by
  simp only [etaleCohomologyCup_apply, LinearEquiv.symm_apply_apply]
  congr 1
  exact Ext.comp_assoc _ _ _ hab hbc habc

private theorem constantExtCohomologyEquiv_symm_naturality
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)} (f : F ⟶ G)
    (n : ℕ) (x : etaleCohomology X R F n) :
    (etaleConstantModuleExtCohomologyEquiv X R G n).symm
        (Classical.cohomologyMap f n x) =
      ((etaleConstantModuleExtCohomologyEquiv X R F n).symm x).comp
        (Ext.mk₀ f) (add_zero n) := by
  let K₀ : Sheaf X.smallEtaleTopology (ModuleCat.{u} R) :=
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)
  let eF : Ext.{u} K₀ F n ≃ₗ[R] etaleCohomology X R F n :=
    etaleConstantModuleExtCohomologyEquiv X R F n
  let eG : Ext.{u} K₀ G n ≃ₗ[R] etaleCohomology X R G n :=
    etaleConstantModuleExtCohomologyEquiv X R G n
  let z : etaleCohomology X R G n := Classical.cohomologyMap f n x
  have hn : eG ((eF.symm x).comp (Ext.mk₀ f) (add_zero n)) =
      Classical.cohomologyMap f n (eF (eF.symm x)) :=
    etaleConstantModuleExtCohomologyEquiv_naturality X R f n (eF.symm x)
  have hx : Classical.cohomologyMap f n (eF (eF.symm x)) = z :=
    congrArg (fun w : etaleCohomology X R F n => Classical.cohomologyMap f n w)
      (eF.apply_symm_apply x)
  change eG.symm z = (eF.symm x).comp (Ext.mk₀ f) (add_zero n)
  apply eG.injective
  exact (eG.apply_symm_apply z).trans (hx.symm.trans hn.symm)

/-- The cup action commutes with the map on actual cohomology induced by
the original coefficient morphism. -/
theorem etaleCohomologyCup_naturality
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)} (f : F ⟶ G)
    (a b c : ℕ) (h : a + b = c)
    (x : etaleCohomology X R
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R))
      a) (y : etaleCohomology X R F b) :
    Classical.cohomologyMap f c (etaleCohomologyCup X R F a b c h x y) =
      etaleCohomologyCup X R G a b c h x (Classical.cohomologyMap f b y) := by
  let K₀ : Sheaf X.smallEtaleTopology (ModuleCat.{u} R) :=
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)
  let eK : Ext.{u} K₀ K₀ a ≃ₗ[R] etaleCohomology X R K₀ a :=
    etaleConstantModuleExtCohomologyEquiv X R K₀ a
  let eF : Ext.{u} K₀ F b ≃ₗ[R] etaleCohomology X R F b :=
    etaleConstantModuleExtCohomologyEquiv X R F b
  let eG : Ext.{u} K₀ G b ≃ₗ[R] etaleCohomology X R G b :=
    etaleConstantModuleExtCohomologyEquiv X R G b
  let eFc : Ext.{u} K₀ F c ≃ₗ[R] etaleCohomology X R F c :=
    etaleConstantModuleExtCohomologyEquiv X R F c
  let eGc : Ext.{u} K₀ G c ≃ₗ[R] etaleCohomology X R G c :=
    etaleConstantModuleExtCohomologyEquiv X R G c
  let α : Ext.{u} K₀ K₀ a := eK.symm x
  let β : Ext.{u} K₀ F b := eF.symm y
  let z : etaleCohomology X R G b := Classical.cohomologyMap f b y
  let mc : etaleCohomology X R F c →ₗ[R] etaleCohomology X R G c :=
    Classical.cohomologyMap f c
  have hF : etaleCohomologyCup X R F a b c h x y = eFc (α.comp β h) :=
    etaleCohomologyCup_apply X R F a b c h x y
  have hG : etaleCohomologyCup X R G a b c h x z =
      eGc (α.comp (eG.symm z) h) :=
    etaleCohomologyCup_apply X R G a b c h x z
  have hn : eGc ((α.comp β h).comp (Ext.mk₀ f) (add_zero c)) =
      mc (eFc (α.comp β h)) :=
    etaleConstantModuleExtCohomologyEquiv_naturality X R f c (α.comp β h)
  have hb : eG.symm z = β.comp (Ext.mk₀ f) (add_zero b) :=
    constantExtCohomologyEquiv_symm_naturality X R f b y
  change mc (etaleCohomologyCup X R F a b c h x y) =
    etaleCohomologyCup X R G a b c h x z
  calc
    mc (etaleCohomologyCup X R F a b c h x y) = mc (eFc (α.comp β h)) :=
      congrArg mc hF
    _ = eGc ((α.comp β h).comp (Ext.mk₀ f) (add_zero c)) := hn.symm
    _ = eGc (α.comp (β.comp (Ext.mk₀ f) (add_zero b)) h) :=
      congrArg eGc (Ext.comp_assoc_of_third_deg_zero α β (Ext.mk₀ f) h)
    _ = eGc (α.comp (eG.symm z) h) :=
      congrArg (fun w : Ext.{u} K₀ G b => eGc (α.comp w h)) hb.symm
    _ = etaleCohomologyCup X R G a b c h x z := hG.symm

/-- Multiples of the actual cup unit recover the original scalar action. -/
theorem etaleCohomologyCup_smul_unit
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) (n : ℕ)
    (r : R) (x : etaleCohomology X R F n) :
    etaleCohomologyCup X R F 0 n n (zero_add n)
      (r • etaleCohomologyCupUnit X R) x = r • x := by
  rw [map_smul, LinearMap.smul_apply, etaleCohomologyCup_unit_left]

end EtaleCohomology
