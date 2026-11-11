/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.Etale
public import Nyll.EtaleCohomology.Classical.ModuleExtCohomology
public import Nyll.EtaleCohomology.Classical.ModuleCohomology
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Yoneda

/-!
# The actual constant coefficient unit for étale cohomology

The module object used by the existing Ext comparison and the constant
regular module sheaf both corepresent the original global-sections functor.
Their resulting isomorphism identifies the Ext comparison with extensions
out of the actual constant coefficient sheaf. No chosen comparison is an
input.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Abelian Opposite

namespace EtaleCohomology

variable (X : Scheme.{u}) (R : Type u) [CommRing R]

/-- Morphisms out of the coefficient unit identify linearly with actual global sections. -/
def unitHomSectionsEquiv
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    (etaleFreeIntegerModuleSheaf X R ⟶ F) ≃ₗ[R]
      F.obj.obj (op (⊤_ X.Etale)) :=
  (Ext.linearEquiv₀ (R := R)).symm ≪≫ₗ
    etaleModuleExtCohomologyEquiv X R F 0 ≪≫ₗ etaleCohomologyZeroEquiv X R F

/-- The coefficient-unit sections equivalence respects the original coefficient morphisms. -/
theorem unitHomSectionsEquiv_naturality
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)}
    (a : etaleFreeIntegerModuleSheaf X R ⟶ F) (f : F ⟶ G) :
    unitHomSectionsEquiv X R G (a ≫ f) =
      f.hom.app (op (⊤_ X.Etale)) (unitHomSectionsEquiv X R F a) := by
  change etaleCohomologyZeroEquiv X R G
      (etaleModuleExtCohomologyEquiv X R G 0 (Ext.mk₀ (a ≫ f))) =
    f.hom.app (op (⊤_ X.Etale)) (etaleCohomologyZeroEquiv X R F
      (etaleModuleExtCohomologyEquiv X R F 0 (Ext.mk₀ a)))
  rw [← Ext.mk₀_comp_mk₀, etaleModuleExtCohomologyEquiv_naturality]
  exact Classical.cohomologyZeroEquiv_naturality f terminalIsTerminal _

/-- Morphisms out of the constant regular module sheaf identify with global sections. -/
def constantHomSectionsEquiv
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    (((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj
      (ModuleCat.of R R)) ⟶ F) ≃ F.obj.obj (op (⊤_ X.Etale)) :=
  ((constantSheafAdj X.smallEtaleTopology (ModuleCat.{u} R)
    terminalIsTerminal).homEquiv (ModuleCat.of R R) F).trans
      (ModuleCat.homEquiv.trans (LinearMap.ringLmapEquivSelf R R _).toEquiv)

/-- The constant-module sections equivalence respects the original coefficient morphisms. -/
theorem constantHomSectionsEquiv_naturality
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)}
    (a : ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj
      (ModuleCat.of R R)) ⟶ F) (f : F ⟶ G) :
    constantHomSectionsEquiv X R G (a ≫ f) =
      f.hom.app (op (⊤_ X.Etale)) (constantHomSectionsEquiv X R F a) := by
  change (((constantSheafAdj X.smallEtaleTopology (ModuleCat.{u} R)
      terminalIsTerminal).homEquiv (ModuleCat.of R R) G (a ≫ f)).hom) 1 =
    f.hom.app (op (⊤_ X.Etale))
      ((((constantSheafAdj X.smallEtaleTopology (ModuleCat.{u} R)
        terminalIsTerminal).homEquiv (ModuleCat.of R R) F a).hom) 1)
  rw [Adjunction.homEquiv_naturality_right]
  rfl

/-- The coefficient unit corepresents the original global-sections functor. -/
def unitCorepresentsSections :
    (((sheafSections X.smallEtaleTopology (ModuleCat.{u} R)).obj
      (op (⊤_ X.Etale))) ⋙ forget (ModuleCat.{u} R)).CorepresentableBy
        (etaleFreeIntegerModuleSheaf X R) where
  homEquiv := (unitHomSectionsEquiv X R _).toEquiv
  homEquiv_comp f a := unitHomSectionsEquiv_naturality X R a f

/-- The constant regular module sheaf corepresents the original global-sections functor. -/
def constantCorepresentsSections :
    (((sheafSections X.smallEtaleTopology (ModuleCat.{u} R)).obj
      (op (⊤_ X.Etale))) ⋙ forget (ModuleCat.{u} R)).CorepresentableBy
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)) where
  homEquiv := constantHomSectionsEquiv X R _
  homEquiv_comp f a := constantHomSectionsEquiv_naturality X R a f

/-- The coefficient unit already used by module Ext is the actual constant
regular module sheaf. Both sides corepresent the original sections. -/
def etaleFreeIntegerModuleSheafIsoConstant :
    etaleFreeIntegerModuleSheaf X R ≅
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)) :=
  (unitCorepresentsSections X R).uniqueUpToIso (constantCorepresentsSections X R)

/-- The corepresenting isomorphism preserves the actual constant section
represented by a morphism out of the constant regular module. -/
theorem etaleFreeIntegerModuleSheafIsoConstant_hom_sections
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R))
    (a : (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj
      (ModuleCat.of R R) ⟶ F) :
    etaleCohomologyZeroEquiv X R F
        (etaleModuleExtCohomologyEquiv X R F 0
          (Ext.mk₀ ((etaleFreeIntegerModuleSheafIsoConstant X R).hom ≫ a))) =
      ((constantSheafAdj X.smallEtaleTopology (ModuleCat.{u} R)
        terminalIsTerminal).homEquiv (ModuleCat.of R R) F a) 1 := by
  change unitHomSectionsEquiv X R F
      ((etaleFreeIntegerModuleSheafIsoConstant X R).hom ≫ a) =
    constantHomSectionsEquiv X R F a
  rw [unitHomSectionsEquiv_naturality]
  have he : unitHomSectionsEquiv X R
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R))
        (etaleFreeIntegerModuleSheafIsoConstant X R).hom =
      constantHomSectionsEquiv X R
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R))
          (𝟙 _) :=
    (unitHomSectionsEquiv X R _).apply_symm_apply _
  rw [he]
  exact (constantHomSectionsEquiv_naturality X R (𝟙 _) a).symm.trans
    (congrArg (constantHomSectionsEquiv X R F) (Category.id_comp a))

/-- The corepresenting isomorphism transports the source of the module Ext groups. -/
def constantSourceExtEquiv
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) (n : ℕ) :
    Ext.{u}
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R))
      F n ≃ₗ[R] Ext.{u} (etaleFreeIntegerModuleSheaf X R) F n := by
  let e := etaleFreeIntegerModuleSheafIsoConstant X R
  let p := (Ext.mk₀ e.hom).precompOfLinear R F (zero_add n)
  let q := (Ext.mk₀ e.inv).precompOfLinear R F (zero_add n)
  refine LinearEquiv.ofLinearMap p q ?_ ?_
  · ext a
    change (Ext.mk₀ e.hom).comp ((Ext.mk₀ e.inv).comp a (zero_add n))
      (zero_add n) = a
    rw [Ext.mk₀_comp_mk₀_assoc, Iso.hom_inv_id, Ext.mk₀_id_comp]
  · ext a
    change (Ext.mk₀ e.inv).comp ((Ext.mk₀ e.hom).comp a (zero_add n))
      (zero_add n) = a
    rw [Ext.mk₀_comp_mk₀_assoc, Iso.inv_hom_id, Ext.mk₀_id_comp]

/-- Actual classical étale cohomology is module Ext out of the constant
regular coefficient sheaf, with its original coefficient module structure. -/
def etaleConstantModuleExtCohomologyEquiv
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) (n : ℕ) :
    Ext.{u}
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R))
      F n ≃ₗ[R] etaleCohomology X R F n :=
  constantSourceExtEquiv X R F n ≪≫ₗ etaleModuleExtCohomologyEquiv X R F n

/-- The actual constant-source comparison commutes with the original
coefficient map. -/
theorem etaleConstantModuleExtCohomologyEquiv_naturality
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)} (f : F ⟶ G)
    (n : ℕ) (a : Ext.{u}
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)) F n) :
    etaleConstantModuleExtCohomologyEquiv X R G n
        (a.comp (Ext.mk₀ f) (add_zero n)) =
      Classical.cohomologyMap f n (etaleConstantModuleExtCohomologyEquiv X R F n a) := by
  change etaleModuleExtCohomologyEquiv X R G n
      ((Ext.mk₀ (etaleFreeIntegerModuleSheafIsoConstant X R).hom).comp
        (a.comp (Ext.mk₀ f) (add_zero n)) (zero_add n)) = _
  rw [← Ext.comp_assoc_of_third_deg_zero]
  exact etaleModuleExtCohomologyEquiv_naturality X R f n _

end EtaleCohomology
