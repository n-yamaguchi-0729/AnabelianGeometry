/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.Etale
public import Nyll.EtaleCohomology.Classical.InjectiveModuleAcyclic
public import Nyll.SchemeTheory.HomologicalAlgebra.ExtAdjunctionAcyclic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Linear.FunctorCategory

/-!
# Module Ext and classical étale cohomology

The left adjoint to forgetting coefficients sends the constant integer sheaf
to a module sheaf corepresenting global sections. The actual adjunction unit
and exact coefficient-forgetting functor give a comparison of Ext groups.
The previously proved acyclicity of underlying native injective module sheaves
makes this comparison bijective in every degree.

Naturality uses the original coefficient morphism. Scalar compatibility then
identifies the module structure with the existing one on classical cohomology.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Abelian

namespace EtaleCohomology

variable (X : Scheme.{u}) (R : Type u) [CommRing R]

/-- The coefficient left adjoint on sheaves is obtained by composition and sheafification. -/
def coefficientExtension :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u} ⥤
      Sheaf X.smallEtaleTopology (ModuleCat.{u} R) :=
  Sheaf.composeAndSheafify X.smallEtaleTopology
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).leftAdjoint

/-- The actual coefficient extension is left adjoint to forgetting coefficients. -/
def coefficientExtensionAdjunction :
    coefficientExtension X R ⊣
      Classical.forgetCoefficients.{u + 1, u, u, u}
        (J := X.smallEtaleTopology) (R := R) :=
  Sheaf.adjunction X.smallEtaleTopology
    (Adjunction.ofIsRightAdjoint (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}))

/-- The image of the actual constant integer sheaf under the coefficient
left adjoint; its Hom functor is the underlying global-sections functor. -/
def etaleFreeIntegerModuleSheaf : Sheaf X.smallEtaleTopology (ModuleCat.{u} R) :=
  (coefficientExtension X R).obj
    ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)))

/-- The same actual adjunction gives the additive Hom comparison, for use
on the original module injective resolution. -/
def etaleModuleIntegerHomForgetEquiv
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    (etaleFreeIntegerModuleSheaf X R ⟶ F) ≃+
      (((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ))) ⟶
          (Classical.forgetCoefficients.{u + 1, u, u, u}
            (J := X.smallEtaleTopology) (R := R)).obj F) := by
  have : (coefficientExtension X R).Additive :=
    (coefficientExtensionAdjunction X R).left_adjoint_additive
  exact (coefficientExtensionAdjunction X R).homAddEquiv
    ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ))) F

theorem etaleModuleIntegerHomForgetEquiv_naturality
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)}
    (a : etaleFreeIntegerModuleSheaf X R ⟶ F) (f : F ⟶ G) :
    etaleModuleIntegerHomForgetEquiv X R G (a ≫ f) =
      etaleModuleIntegerHomForgetEquiv X R F a ≫
        (Classical.forgetCoefficients.{u + 1, u, u, u}
          (J := X.smallEtaleTopology) (R := R)).map f :=
  (coefficientExtensionAdjunction X R).homEquiv_naturality_right a f

/-- The original adjunction unit followed by the exact coefficient-forgetting
Ext map. -/
def etaleModuleExtCohomologyMap
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) (n : ℕ) :
    Ext.{u} (etaleFreeIntegerModuleSheaf X R) F n →+
      Sheaf.H.{u} ((Classical.forgetCoefficients.{u + 1, u, u, u}
        (J := X.smallEtaleTopology) (R := R)).obj F) n :=
  (coefficientExtensionAdjunction X R).extMapOfExactRight
    ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ))) F n

/-- The degree-zero comparison is the original coefficient adjunction on morphisms. -/
theorem etaleModuleExtCohomologyMap_mk₀
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)}
    (a : etaleFreeIntegerModuleSheaf X R ⟶ F) :
    etaleModuleExtCohomologyMap X R F 0 (Ext.mk₀ a) =
      Ext.mk₀ (etaleModuleIntegerHomForgetEquiv X R F a) :=
  (coefficientExtensionAdjunction X R).extMapOfExactRight_mk₀
    ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ))) a

theorem etaleModuleExtCohomologyMap_bijective
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) (n : ℕ) :
    Function.Bijective (etaleModuleExtCohomologyMap X R F n) :=
  (coefficientExtensionAdjunction X R).extMapOfExactRight_bijective_of_acyclic
    ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)))
    (fun I _ m => etaleInjectiveModule_cohomology_subsingleton X R I m) F n

/-- Naturality for the given coefficient morphism, expressed by ordinary
Yoneda postcomposition in the native module category. -/
theorem etaleModuleExtCohomologyMap_naturality
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)} (f : F ⟶ G)
    (n : ℕ) (e : Ext.{u} (etaleFreeIntegerModuleSheaf X R) F n) :
    etaleModuleExtCohomologyMap X R G n (e.comp (Ext.mk₀ f) (add_zero n)) =
      Sheaf.H.map ((Classical.forgetCoefficients.{u + 1, u, u, u}
        (J := X.smallEtaleTopology) (R := R)).map f) n (etaleModuleExtCohomologyMap X R F n e) := by
  have h : etaleModuleExtCohomologyMap X R G n (e.comp (Ext.mk₀ f) (add_zero n)) =
      (etaleModuleExtCohomologyMap X R F n e).comp
        ((Ext.mk₀ f).mapExactFunctor
          (Classical.forgetCoefficients.{u + 1, u, u, u}
            (J := X.smallEtaleTopology) (R := R))) (add_zero n) :=
    (coefficientExtensionAdjunction X R).extMapOfExactRight_comp
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ))) e (Ext.mk₀ f) (add_zero n)
  simpa only [Ext.mapExactFunctor_mk₀, Sheaf.H.map_apply] using h

private theorem forgetCoefficients_smul_id
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) (r : R) :
    (Classical.forgetCoefficients.{u + 1, u, u, u}
    (J := X.smallEtaleTopology) (R := R)).map (r • 𝟙 F) = Classical.coefficientAction F r := by
  ext V a
  rfl

/-- The original Ext comparison is linear for the existing scalar action
on classical étale cohomology. -/
def etaleModuleExtCohomologyEquiv
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) (n : ℕ) :
    Ext.{u} (etaleFreeIntegerModuleSheaf X R) F n ≃ₗ[R]
      etaleCohomology X R F n where
  toAddEquiv := AddEquiv.ofBijective (etaleModuleExtCohomologyMap X R F n)
    (etaleModuleExtCohomologyMap_bijective X R F n)
  map_smul' r e := by
    change etaleModuleExtCohomologyMap X R F n (r • e) =
      Sheaf.H.map (Classical.coefficientAction F r) n
        (etaleModuleExtCohomologyMap X R F n e)
    rw [Ext.smul_eq_comp_mk₀, etaleModuleExtCohomologyMap_naturality,
      forgetCoefficients_smul_id]

/-- The linear comparison retains naturality in the original coefficient map. -/
theorem etaleModuleExtCohomologyEquiv_naturality
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)} (f : F ⟶ G)
    (n : ℕ) (e : Ext.{u} (etaleFreeIntegerModuleSheaf X R) F n) :
    etaleModuleExtCohomologyEquiv X R G n (e.comp (Ext.mk₀ f) (add_zero n)) =
      Classical.cohomologyMap f n (etaleModuleExtCohomologyEquiv X R F n e) :=
  etaleModuleExtCohomologyMap_naturality X R f n e

end EtaleCohomology
