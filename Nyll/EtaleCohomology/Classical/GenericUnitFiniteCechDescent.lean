/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.CupAbelianCechResolution
public import Nyll.EtaleCohomology.Classical.FreeAbelianCohomologySections
public import Nyll.EtaleCohomology.Classical.FreeAbelianYoneda
public import Nyll.EtaleCohomology.Classical.GenericUnitFiniteDeckSections
public import Nyll.EtaleCohomology.Classical.GenericUnitFiniteRestriction
public import Nyll.EtaleCohomology.Classical.SheafH0TerminalTransport
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Original finite-cover augmentation and native restriction

The original free representable augmentation evaluates to the original
global quotient section on that finite cover. Its finite-cover section
equivalence therefore gives precisely the native H⁰ pullback, including
the original terminal representative.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace Abelian
open CategoryTheory.PreGaloisCategory EtaleFundamentalGroups

namespace EtaleCohomology

variable {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
  (Y : FiniteEtale X) [IsConnected Y] [IsIntegral Y.left]
  {T : X.Etale} (hT : IsTerminal T) (f : (finiteEtaleInclusion X).obj Y ⟶ T)

/-- The original covering augmentation becomes the actual native
restriction of the same original H⁰ class. -/
theorem finiteEtaleGenericUnitQuotientSectionsEquiv_augmentation
    (a : (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ etaleGenericUnitQuotient X) :
    finiteEtaleGenericUnitQuotientSectionsEquiv Y
        (freeAbelianSheafYonedaHomEquiv X.smallEtaleTopology
          ((finiteEtaleInclusion X).obj Y) (etaleGenericUnitQuotient X)
          (abelianCechUnitAugmentation X.smallEtaleTopology hT f ≫ a)) =
      finiteGenericUnitH0Pullback Y (Ext.mk₀ a) := by
  let Q := etaleGenericUnitQuotient X
  let hX := MorphismProperty.Over.mkIdTerminal
    (show MorphismProperty Scheme.{u} from @Etale) X
  have ha : Ext.addEquiv₀ (Ext.mk₀ a) = a := Ext.addEquiv₀.apply_symm_apply a
  have hs : freeAbelianSheafYonedaHomEquiv X.smallEtaleTopology
      ((finiteEtaleInclusion X).obj Y) Q
      (abelianCechUnitAugmentation X.smallEtaleTopology hT f ≫ a) =
      Q.obj.map f.op (Sheaf.H.equiv₀ Q hT (Ext.mk₀ a)) := by
    rw [abelianCechUnitAugmentation, Category.assoc,
      freeAbelianSheafYonedaHomEquiv_precomp,
      freeAbelianSheafYonedaTerminalIso_homEquiv]
    change Q.obj.map f.op (AddCommGrpCat.uliftZMultiplesAddEquiv _
      ((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u} hT).homEquiv _ Q a)) =
      Q.obj.map f.op (AddCommGrpCat.uliftZMultiplesAddEquiv _
        ((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u} hT).homEquiv _ Q
          (Ext.addEquiv₀ (Ext.mk₀ a))))
    rw [ha]
  have hm : f ≫ hX.from T = hX.from ((finiteEtaleInclusion X).obj Y) := hX.hom_ext _ _
  have hcomp : Q.obj.map (hX.from T).op ≫ Q.obj.map f.op =
      Q.obj.map (hX.from ((finiteEtaleInclusion X).obj Y)).op :=
    (Q.obj.map_comp (hX.from T).op f.op).symm.trans
      (congrArg (fun z : (finiteEtaleInclusion X).obj Y ⟶ Scheme.Etale.mk (𝟙 X) =>
        Q.obj.map z.op) hm)
  have hsec : Q.obj.map f.op
      (Q.obj.map (hX.from T).op (Sheaf.H.equiv₀ Q hX (Ext.mk₀ a))) =
      Q.obj.map (hX.from ((finiteEtaleInclusion X).obj Y)).op
        (Sheaf.H.equiv₀ Q hX (Ext.mk₀ a)) :=
    ConcreteCategory.congr_hom hcomp (Sheaf.H.equiv₀ Q hX (Ext.mk₀ a))
  exact (congrArg (finiteEtaleGenericUnitQuotientSectionsEquiv Y)
    (hs.trans ((congrArg (Q.obj.map f.op)
      (sheafH0_restriction Q hT hX (hX.from T) (Ext.mk₀ a)).symm).trans hsec))).trans
        (finiteEtaleGenericUnitQuotientSectionsEquiv_global Y (Ext.mk₀ a))

end EtaleCohomology
