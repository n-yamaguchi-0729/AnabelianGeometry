/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.CupAbelianCechResolution
public import Nyll.EtaleCohomology.Classical.CupAbelianExtensionCocycle
public import Nyll.EtaleCohomology.Classical.FreeAbelianCohomologySections
public import Nyll.EtaleCohomology.Classical.FreeAbelianYoneda
public import Nyll.EtaleFundamentalGroups.Cohomology.ExtensionFibers
public import Nyll.EtaleFundamentalGroups.Cohomology.H1FiniteCover
public import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-!
# The actual Cech lift supplied by an extension-fiber section

An original integer-one lift determines an actual free-abelian
Yoneda morphism. The terminal corepresenting comparison sends its
augmentation to the same original integer section, so the morphism
is a lift for the original Cech covering sequence. Its resulting
module cocycle represents the original abelian extension class.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite
open EtaleCohomology

namespace EtaleFundamentalGroups.Cohomology

variable {X : Scheme.{u}}

/-- The original abelian Cech augmentation evaluates to the actual
constant integer section one on its original covering object. -/
theorem abelianCechUnitAugmentation_section
    {T V : X.Etale} (hT : IsTerminal T) (f : V ⟶ T) :
    freeAbelianSheafYonedaHomEquiv X.smallEtaleTopology V
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)))
        (abelianCechUnitAugmentation X.smallEtaleTopology hT f) =
      (integerUnitSection X).app (op V) PUnit.unit := by
  let A := AddCommGrpCat.of (ULift.{u} ℤ)
  let η := (constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u} hT).unit.app A
  have hη : η =
      (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj A)).app (op T) := by
    simp only [η, constantSheafAdj, Adjunction.comp_unit_app,
      constantPresheafAdj_unit_app, Category.id_comp,
      sheafificationAdjunction_unit_app, evaluation_obj_map]
    rfl
  have htop := freeAbelianSheafYonedaTerminalIso_homEquiv
    X.smallEtaleTopology hT ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ))) (𝟙
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ))))
  simp only [Category.comp_id, Adjunction.homEquiv_unit] at htop
  change freeAbelianSheafYonedaHomEquiv X.smallEtaleTopology T
    ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)))
      (freeAbelianSheafYonedaTerminalIso X.smallEtaleTopology hT).hom =
    η (ULift.up (1 : ℤ)) at htop
  rw [hη] at htop
  change freeAbelianSheafYonedaHomEquiv X.smallEtaleTopology T
    ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)))
      (freeAbelianSheafYonedaTerminalIso X.smallEtaleTopology hT).hom =
    (integerUnitSection X).app (op T) PUnit.unit at htop
  rw [abelianCechUnitAugmentation, freeAbelianSheafYonedaHomEquiv_precomp, htop]
  exact (ConcreteCategory.congr_hom ((integerUnitSection X).naturality f.op)
    PUnit.unit).symm

variable (R : Type u) [CommRing R]

variable {F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)}
  {E : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}}
  (i : (Classical.forgetCoefficients.{u + 1, u, u, u}
    (J := X.smallEtaleTopology) (R := R)).obj F ⟶ E)
  (p : E ⟶ ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)))) (hip : i ≫ p = 0)
  {V : X.Etale}
  (s : (extensionFiber (ShortComplex.mk i p hip) (integerUnitSection X)).obj.obj (op V))

/-- The actual free-abelian Yoneda map determined by the original
integer-one lift on the specified original étale object. -/
def extensionFiberCechLift : (freeAbelianSheafYoneda X.smallEtaleTopology).obj V ⟶ E :=
  (freeAbelianSheafYonedaHomEquiv X.smallEtaleTopology V E).symm s.val

/-- The original lift commutes with the original Cech augmentation,
because both morphisms evaluate to the same original integer section. -/
theorem extensionFiberCechLift_projection
    {T : X.Etale} (hT : IsTerminal T) (f : V ⟶ T) :
    extensionFiberCechLift R i p hip s ≫ p =
      abelianCechUnitAugmentation X.smallEtaleTopology hT f := by
  apply (freeAbelianSheafYonedaHomEquiv X.smallEtaleTopology V
    ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)))).injective
  rw [freeAbelianSheafYonedaHomEquiv_postcomp,
    extensionFiberCechLift, Equiv.apply_symm_apply,
    abelianCechUnitAugmentation_section]
  exact s.property

/-- The module Cech cocycle supplied by an actual original lift
represents that original abelian extension, whenever its actual
étale object covers the terminal object. -/
theorem extensionFiberCechLift_class
    (hE : (ShortComplex.mk i p hip).ShortExact)
    {T : X.Etale} (hT : IsTerminal T) (f : V ⟶ T)
    (hf : Sieve.generate (Presieve.singleton f) ∈ X.smallEtaleTopology T) :
    etaleCechH1Class X R hT f hf
        (abelianExtensionModuleCechCocycle X R hT f i p hip hE
          (extensionFiberCechLift R i p hip s)
          (extensionFiberCechLift_projection R i p hip s hT f))
        (abelianExtensionModuleCechCocycle_cocycle X R hT f i p hip hE
          (extensionFiberCechLift R i p hip s)
          (extensionFiberCechLift_projection R i p hip s hT f)) = hE.extClass :=
  abelianExtensionModuleCechCocycle_class X R hT f i p hip hE
    (extensionFiberCechLift R i p hip s)
    (extensionFiberCechLift_projection R i p hip s hT f) hf

end EtaleFundamentalGroups.Cohomology
