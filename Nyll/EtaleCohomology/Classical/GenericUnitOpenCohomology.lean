/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.AbelianRestrictionPullback
public import Nyll.EtaleCohomology.Classical.AbelianSheafFunctors
public import Nyll.EtaleCohomology.Classical.GenericUnitOpenRestriction
public import Nyll.EtaleCohomology.Classical.KummerPullback
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroup
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroupPushforward
public import Nyll.EtaleCohomology.Classical.PullbackCohomology
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.Algebra.Homology.ShortComplex.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences

/-!
# The original generic-unit boundary under an open immersion

The canonical generic-point square supplies the actual generic-unit and
quotient maps. The original inverse image, its restriction comparison, and
these maps give a morphism of the actual short exact sequences. Exact
pullback of their extension classes proves naturality of the original
H⁰ quotient to H¹(Gm) boundary.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian Limits TopologicalSpace

namespace EtaleCohomology

variable {X U : Scheme.{u}} [IsIntegral X] [IsIntegral U]
  (j : U ⟶ X) [IsOpenImmersion j]

/-- Original inverse image of generic units, normalized by the actual
generic-point square of the open immersion. -/
def etaleGenericUnitsPullback :
    (etaleAbelianPullback j).obj
      ((etaleAbelianPushforward (X.fromSpecStalk (genericPoint X))).obj
        (etaleMultiplicativeGroupSheaf (Spec X.functionField))) ⟶
      (etaleAbelianPushforward (U.fromSpecStalk (genericPoint U))).obj
        (etaleMultiplicativeGroupSheaf (Spec U.functionField)) :=
  (etaleAbelianPullbackRestrictionIso j).hom.app _ ≫
    (etaleRestrictionGenericUnitPushforwardIso j).hom

/-- Original inverse image of the actual generic-unit quotient,
normalized by its proved restriction isomorphism. -/
def etaleGenericUnitQuotientPullback :
    (etaleAbelianPullback j).obj (etaleGenericUnitQuotient X) ⟶
      etaleGenericUnitQuotient U :=
  (etaleAbelianPullbackRestrictionIso j).hom.app _ ≫
    (etaleRestrictionGenericUnitQuotientIso j).hom

/-- The actual generic-unit map retains the original regular units. -/
theorem etaleGenericUnitsPullback_unit :
    (etaleAbelianPullback j).map
      (etaleMultiplicativeGroupToPushforward (X.fromSpecStalk (genericPoint X))) ≫
        etaleGenericUnitsPullback j =
      etaleMultiplicativeGroupPullback j ≫
        etaleMultiplicativeGroupToPushforward (U.fromSpecStalk (genericPoint U)) := by
  dsimp only [etaleGenericUnitsPullback]
  rw [← Category.assoc, (etaleAbelianPullbackRestrictionIso j).hom.naturality,
    Category.assoc, etaleRestrictionGenericUnitPushforwardIso_unit,
    ← Category.assoc, etaleMultiplicativeGroupPullback_restriction]

/-- The actual quotient map retains the original cokernel projection. -/
theorem etaleGenericUnitQuotientPullback_π :
    (etaleAbelianPullback j).map (etaleGenericUnitShortComplex X).g ≫
        etaleGenericUnitQuotientPullback j =
      etaleGenericUnitsPullback j ≫ (etaleGenericUnitShortComplex U).g := by
  let SX : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
    etaleGenericUnitShortComplex X
  let SU : ShortComplex (Sheaf U.smallEtaleTopology AddCommGrpCat.{u}) :=
    etaleGenericUnitShortComplex U
  let L : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} ⥤
      Sheaf U.smallEtaleTopology AddCommGrpCat.{u} := etaleAbelianPullback j
  let R : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} ⥤
      Sheaf U.smallEtaleTopology AddCommGrpCat.{u} := etaleRestriction j AddCommGrpCat.{u}
  let η : L ⟶ R := (etaleAbelianPullbackRestrictionIso j).hom
  let p : R.obj SX.X₂ ⟶ SU.X₂ := (etaleRestrictionGenericUnitPushforwardIso j).hom
  let q : R.obj SX.X₃ ⟶ SU.X₃ := (etaleRestrictionGenericUnitQuotientIso j).hom
  have hn : L.map SX.g ≫ η.app SX.X₃ = η.app SX.X₂ ≫ R.map SX.g :=
    η.naturality SX.g
  have hq : R.map SX.g ≫ q = p ≫ SU.g :=
    etaleRestrictionGenericUnitQuotientIso_π j
  change L.map SX.g ≫ (η.app SX.X₃ ≫ q) = (η.app SX.X₂ ≫ p) ≫ SU.g
  exact (Category.assoc (L.map SX.g) (η.app SX.X₃) q).symm.trans
    ((congrArg (fun z : L.obj SX.X₂ ⟶ R.obj SX.X₃ => z ≫ q) hn).trans
      ((Category.assoc (η.app SX.X₂) (R.map SX.g) q).trans
        ((congrArg (fun z : R.obj SX.X₂ ⟶ SU.X₃ => η.app SX.X₂ ≫ z) hq).trans
          (Category.assoc (η.app SX.X₂) p SU.g).symm)))

/-- Original inverse image of the generic-unit sequence maps to the
original sequence on the open, with the original unit-sheaf pullback. -/
def etaleGenericUnitPullbackComplex :
    (etaleGenericUnitShortComplex X).map (etaleAbelianPullback j) ⟶
      etaleGenericUnitShortComplex U where
  τ₁ := etaleMultiplicativeGroupPullback j
  τ₂ := etaleGenericUnitsPullback j
  τ₃ := etaleGenericUnitQuotientPullback j
  comm₁₂ := (etaleGenericUnitsPullback_unit j).symm
  comm₂₃ := (etaleGenericUnitQuotientPullback_π j).symm

/-- Pullback on the original cohomology of the actual generic-unit
quotient, through the original exact inverse image. -/
def etaleGenericUnitQuotientCohomologyPullback (i : ℕ) :
    Sheaf.H.{u} (etaleGenericUnitQuotient X) i →+
      Sheaf.H.{u} (etaleGenericUnitQuotient U) i :=
  (Sheaf.H.map (etaleGenericUnitQuotientPullback j) i).comp
    (etaleAbelianCohomologyPullbackMap j (etaleGenericUnitQuotient X) i)

/-- This original cohomological pullback is actual restriction followed
by the actual quotient-sheaf isomorphism. -/
theorem etaleGenericUnitQuotientCohomologyPullback_restriction
    (i : ℕ) (a : Sheaf.H.{u} (etaleGenericUnitQuotient X) i) :
    etaleGenericUnitQuotientCohomologyPullback j i a =
      Sheaf.H.map (etaleRestrictionGenericUnitQuotientIso j).hom i
        (etaleAbelianRestrictionCohomologyPullback j
          (etaleGenericUnitQuotient X) i a) := by
  change Sheaf.H.map
      ((etaleAbelianPullbackRestrictionIso j).hom.app _ ≫
        (etaleRestrictionGenericUnitQuotientIso j).hom) i
      (etaleAbelianCohomologyPullbackMap j (etaleGenericUnitQuotient X) i a) =
    Sheaf.H.map (etaleRestrictionGenericUnitQuotientIso j).hom i
      (Sheaf.H.map ((etaleAbelianPullbackRestrictionIso j).hom.app
        (etaleGenericUnitQuotient X)) i
          (etaleAbelianCohomologyPullbackMap j (etaleGenericUnitQuotient X) i a))
  rw [Sheaf.H.map_comp_apply]

omit [IsIntegral U] [IsOpenImmersion j] in
/-- Exact inverse image preserves the original generic-unit boundary,
before applying a geometric comparison of coefficient sequences. -/
theorem genericUnitBoundary_zero_exactPullback
    (a : Sheaf.H.{u} (etaleGenericUnitQuotient X) 0) :
    etaleAbelianCohomologyPullbackMap j (etaleMultiplicativeGroupSheaf X) 1
        (Sheaf.H.δ (etaleGenericUnitShortComplex_shortExact X) 0 1 rfl a) =
      Sheaf.H.δ ((etaleGenericUnitShortComplex_shortExact X).map_of_exact
        (etaleAbelianPullback j)) 0 1 rfl
          (etaleAbelianCohomologyPullbackMap j (etaleGenericUnitQuotient X) 0 a) := by
  let S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
    etaleGenericUnitShortComplex X
  have hS : S.ShortExact := etaleGenericUnitShortComplex_shortExact X
  let L : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} ⥤
      Sheaf U.smallEtaleTopology AddCommGrpCat.{u} := etaleAbelianPullback j
  let ZX : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ))
  let ZU : Sheaf U.smallEtaleTopology AddCommGrpCat.{u} :=
    (constantSheaf U.smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ))
  let c : ZU ⟶ L.obj ZX := ((etaleAbelianPullbackConstantIso j).app
    (AddCommGrpCat.of (ULift.{u} ℤ))).inv
  let α : Ext.{u} ZX S.X₃ 0 := a
  let β : Ext.{u} S.X₃ S.X₁ 1 := hS.extClass
  let θ : Ext.{u} (L.obj S.X₃) (L.obj S.X₁) 1 := (hS.map_of_exact L).extClass
  have hcomp : (α.comp β rfl).mapExactFunctor L =
      (α.mapExactFunctor L).comp (β.mapExactFunctor L) rfl :=
    Ext.mapExactFunctor_comp L α β rfl
  have hclass : β.mapExactFunctor L = θ := Ext.mapExactFunctor_extClass L hS
  have hm : (α.comp β rfl).mapExactFunctor L =
      (α.mapExactFunctor L).comp θ rfl :=
    hcomp.trans (congrArg (fun z : Ext.{u} (L.obj S.X₃) (L.obj S.X₁) 1 =>
      (α.mapExactFunctor L).comp z rfl) hclass)
  change (Ext.mk₀ c).comp ((α.comp β rfl).mapExactFunctor L) (zero_add 1) =
    ((Ext.mk₀ c).comp (α.mapExactFunctor L) (zero_add 0)).comp θ rfl
  exact (congrArg (fun z : Ext.{u} (L.obj ZX) (L.obj S.X₁) 1 =>
    (Ext.mk₀ c).comp z (zero_add 1)) hm).trans
      (Ext.comp_assoc (Ext.mk₀ c) (α.mapExactFunctor L) θ (zero_add 0) rfl rfl).symm

/-- The original generic-unit connecting map commutes with the
original scheme pullback on H¹(Gm). -/
theorem etaleGenericUnitBoundary_zero_pullback
    (a : Sheaf.H.{u} (etaleGenericUnitQuotient X) 0) :
    etaleMultiplicativeGroupCohomologyPullback j 1
        (Sheaf.H.δ (etaleGenericUnitShortComplex_shortExact X) 0 1 rfl a) =
      Sheaf.H.δ (etaleGenericUnitShortComplex_shortExact U) 0 1 rfl
        (etaleGenericUnitQuotientCohomologyPullback j 0 a) := by
  let hX := etaleGenericUnitShortComplex_shortExact X
  let hU := etaleGenericUnitShortComplex_shortExact U
  let b := etaleAbelianCohomologyPullbackMap j (etaleGenericUnitQuotient X) 0 a
  have hδ := Sheaf.H.δ_naturality 0 1 rfl
    (hX.map_of_exact (etaleAbelianPullback j)) hU
    (etaleGenericUnitPullbackComplex j) b
  change Sheaf.H.δ hU 0 1 rfl
      (Sheaf.H.map (etaleGenericUnitQuotientPullback j) 0 b) =
    Sheaf.H.map (etaleMultiplicativeGroupPullback j) 1
      (Sheaf.H.δ (hX.map_of_exact (etaleAbelianPullback j)) 0 1 rfl b) at hδ
  exact (congrArg (Sheaf.H.map (etaleMultiplicativeGroupPullback j) 1)
    (genericUnitBoundary_zero_exactPullback j a)).trans hδ.symm

end EtaleCohomology
