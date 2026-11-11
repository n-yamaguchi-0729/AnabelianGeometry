/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.AbelianRestrictionPullback
public import Nyll.EtaleCohomology.Classical.AbelianSheafFunctors
public import Nyll.EtaleCohomology.Classical.EtaleRestriction
public import Nyll.EtaleCohomology.Classical.EtaleRestrictionCohomologySections
public import Nyll.EtaleCohomology.Classical.EtaleRestrictionNaturality
public import Nyll.EtaleCohomology.Classical.FreeAbelianYoneda
public import Nyll.EtaleCohomology.Classical.PullbackCohomology
public import Nyll.EtaleCohomology.Sites.EtaleRestriction
public import Nyll.EtaleCohomology.Sites.EtaleSlice
public import Nyll.SchemeTheory.Sheaves.OverExtension
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Original terminal restriction is the original pullback in every degree

Both constructions are the actual exact-functor map on Ext followed
by a degree-zero source morphism. The free-abelian Yoneda and slice
adjunction calculations identify these source morphisms on the
original constant integer sheaf. Their equality therefore proves
coherence in every degree, without a cohomological comparison
assumption or a change of the original pullback maps.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

namespace EtaleCohomology

variable {X : Scheme.{u}} (V : X.Etale)

/-- The actual source morphism of the terminal/over-site construction. -/
private def etaleRestrictionPresheafSource
    {T : X.Etale} (hT : IsTerminal T) (i : V ⟶ T) :
    (constantSheaf V.left.smallEtaleTopology AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶
      (etaleRestriction V.hom AddCommGrpCat.{u}).obj
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift.{u} ℤ))) :=
  ((etaleSliceAbelianConstantIso V).app (AddCommGrpCat.of (ULift.{u} ℤ))).inv ≫
    (etaleSliceAbelianSheafEquivalence V).functor.map
      ((overAbelianSheafExtensionAdjunction V X.smallEtaleTopology).homEquiv _ _
        (((freeAbelianSheafYonedaOverExtensionIso X.smallEtaleTopology V).inv ≫
          (freeAbelianSheafYoneda X.smallEtaleTopology).map i) ≫
            (freeAbelianSheafYonedaTerminalIso X.smallEtaleTopology hT).hom))

/-- The actual source morphism of the original inverse-image map,
transported by its original restriction comparison. -/
def etaleRestrictionPullbackSource :
    (constantSheaf V.left.smallEtaleTopology AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶
      (etaleRestriction V.hom AddCommGrpCat.{u}).obj
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift.{u} ℤ))) :=
  ((etaleAbelianPullbackConstantIso V.hom).app
    (AddCommGrpCat.of (ULift.{u} ℤ))).inv ≫
      (etaleAbelianPullbackRestrictionIso V.hom).hom.app
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift.{u} ℤ)))

private theorem etaleRestrictionPresheafSource_apply
    {T : X.Etale} (hT : IsTerminal T) (i : V ⟶ T)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ)
    (a : Sheaf.H.{u} F n) :
    etaleCohomologyPresheafRestrictionEquiv V F n
        ((F.cohomologyPresheaf n).map i.op
          (sheafCohomologyTerminalEquiv X.smallEtaleTopology hT F n a)) =
      (Ext.mk₀ (etaleRestrictionPresheafSource V hT i)).comp
        (a.mapExactFunctor (etaleRestriction V.hom AddCommGrpCat.{u})) (zero_add n) := by
  let A := AddCommGrpCat.of (ULift.{u} ℤ)
  let Z := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A
  let ZO := (constantSheaf (X.smallEtaleTopology.over V) AddCommGrpCat.{u}).obj A
  let YV := (freeAbelianSheafYoneda X.smallEtaleTopology).obj V
  let YT := (freeAbelianSheafYoneda X.smallEtaleTopology).obj T
  let D := X.smallEtaleTopology.overPullback AddCommGrpCat.{u} V
  let E := etaleSliceAbelianSheafEquivalence V
  let adj := overAbelianSheafExtensionAdjunction V X.smallEtaleTopology
  let j : (overAbelianSheafExtension V X.smallEtaleTopology).obj ZO ⟶ YV :=
    (freeAbelianSheafYonedaOverExtensionIso X.smallEtaleTopology V).inv
  let m : YV ⟶ YT := (freeAbelianSheafYoneda X.smallEtaleTopology).map i
  let t : YT ⟶ Z := (freeAbelianSheafYonedaTerminalIso X.smallEtaleTopology hT).hom
  let q : (overAbelianSheafExtension V X.smallEtaleTopology).obj ZO ⟶ Z := (j ≫ m) ≫ t
  let r : ZO ⟶ D.obj Z := adj.homEquiv ZO Z q
  let e : E.functor.obj ZO ≅
      (constantSheaf V.left.smallEtaleTopology AddCommGrpCat.{u}).obj A :=
    (etaleSliceAbelianConstantIso V).app A
  let b : Ext.{u} ZO (D.obj F) n := (Ext.mk₀ r).comp (a.mapExactFunctor D) (zero_add n)
  have hcombine :
      (Ext.mk₀ j).comp ((Ext.mk₀ m).comp
        ((Ext.mk₀ t).comp a (zero_add n)) (zero_add n)) (zero_add n) =
      (Ext.mk₀ q).comp a (zero_add n) :=
    (Ext.mk₀_comp_mk₀_assoc j m ((Ext.mk₀ t).comp a (zero_add n))).trans
      (Ext.mk₀_comp_mk₀_assoc (j ≫ m) t a)
  have hq : adj.extEquiv ((Ext.mk₀ q).comp a (zero_add n)) = b :=
    (adj.extEquiv_naturality_right (Ext.mk₀ q) a (zero_add n)).trans
      (congrArg (fun z : Ext.{u} ZO (D.obj Z) 0 =>
        z.comp (a.mapExactFunctor D) (zero_add n)) (adj.extEquiv_mk₀ q))
  have hbmap : b.mapExactFunctor E.functor =
      (Ext.mk₀ (E.functor.map r)).comp
        ((a.mapExactFunctor D).mapExactFunctor E.functor) (zero_add n) :=
    (Ext.mapExactFunctor_comp E.functor (Ext.mk₀ r)
      (a.mapExactFunctor D) (zero_add n)).trans
      (congrArg (fun z : Ext.{u} (E.functor.obj ZO) (E.functor.obj (D.obj Z)) 0 =>
        z.comp ((a.mapExactFunctor D).mapExactFunctor E.functor) (zero_add n))
          (Ext.mapExactFunctor_mk₀ E.functor r))
  have hmap : (a.mapExactFunctor D).mapExactFunctor E.functor =
      a.mapExactFunctor (etaleRestriction V.hom AddCommGrpCat.{u}) :=
    (Ext.comp_mapExactFunctor a D E.functor).symm
  have hterminal : sheafCohomologyTerminalEquiv X.smallEtaleTopology hT F n a =
      (Ext.mk₀ t).comp a (zero_add n) := rfl
  have hrestriction (z : Sheaf.H'.{u} F n T) :
      (F.cohomologyPresheaf n).map i.op z = (Ext.mk₀ m).comp z (zero_add n) := rfl
  have hover (z : Sheaf.H'.{u} F n V) :
      etaleCohomologyPresheafRestrictionEquiv V F n z =
        etaleSliceAbelianCohomologyEquiv V (D.obj F) n
          (adj.extEquiv ((Ext.mk₀ j).comp z (zero_add n))) := rfl
  refine ((congrArg (fun z : Sheaf.H'.{u} F n T =>
    etaleCohomologyPresheafRestrictionEquiv V F n ((F.cohomologyPresheaf n).map i.op z))
    hterminal).trans
      ((congrArg (etaleCohomologyPresheafRestrictionEquiv V F n)
        (hrestriction ((Ext.mk₀ t).comp a (zero_add n)))).trans
        (hover ((Ext.mk₀ m).comp ((Ext.mk₀ t).comp a (zero_add n)) (zero_add n))))).trans ?_
  exact
    (congrArg (fun z : Ext.{u}
        ((overAbelianSheafExtension V X.smallEtaleTopology).obj ZO) F n =>
      etaleSliceAbelianCohomologyEquiv V (D.obj F) n (adj.extEquiv z)) hcombine).trans
      ((congrArg (etaleSliceAbelianCohomologyEquiv V (D.obj F) n) hq).trans
        ((etaleSliceAbelianCohomologyEquiv_apply V (D.obj F) n b).trans
          ((congrArg (fun z : Ext.{u} (E.functor.obj ZO) (E.functor.obj (D.obj F)) n =>
            (Ext.mk₀ e.inv).comp z (zero_add n)) hbmap).trans
            ((Ext.mk₀_comp_mk₀_assoc e.inv (E.functor.map r)
              ((a.mapExactFunctor D).mapExactFunctor E.functor)).trans
              (congrArg (fun z : Ext.{u}
                  ((etaleRestriction V.hom AddCommGrpCat.{u}).obj Z)
                  ((etaleRestriction V.hom AddCommGrpCat.{u}).obj F) n =>
                (Ext.mk₀ (etaleRestrictionPresheafSource V hT i)).comp z (zero_add n)) hmap)))))

/-- The original pullback is the original exact-functor map preceded
by its actual constant-source morphism. -/
theorem etaleRestrictionPullbackSource_apply
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ)
    (a : Sheaf.H.{u} F n) :
    etaleAbelianRestrictionCohomologyPullback V.hom F n a =
      (Ext.mk₀ (etaleRestrictionPullbackSource V)).comp
        (a.mapExactFunctor (etaleRestriction V.hom AddCommGrpCat.{u})) (zero_add n) := by
  change ((Ext.mk₀ ((etaleAbelianPullbackConstantIso V.hom).app
      (AddCommGrpCat.of (ULift.{u} ℤ))).inv).comp
        (a.mapExactFunctor (etaleAbelianPullback V.hom)) (zero_add n)).comp
          (Ext.mk₀ ((etaleAbelianPullbackRestrictionIso V.hom).hom.app F)) (add_zero n) = _
  rw [Ext.comp_assoc_of_third_deg_zero, Ext.mapExactFunctor_comp_mk₀_natTransApp,
    Ext.mk₀_comp_mk₀_assoc]
  rfl

/-- Restriction of the original cohomology presheaf from any original
terminal representative, followed by the actual localized-site
comparison, is exactly the original cohomological pullback in every
degree. -/
theorem etaleCohomologyPresheafRestrictionEquiv_terminal_restriction
    {T : X.Etale} (hT : IsTerminal T) (i : V ⟶ T)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ)
    (a : Sheaf.H.{u} F n) :
    etaleCohomologyPresheafRestrictionEquiv V F n
        ((F.cohomologyPresheaf n).map i.op
          (sheafCohomologyTerminalEquiv X.smallEtaleTopology hT F n a)) =
      etaleAbelianRestrictionCohomologyPullback V.hom F n a := by
  let Z := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))
  let ZV := (constantSheaf V.left.smallEtaleTopology AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))
  let R := etaleRestriction V.hom AddCommGrpCat.{u}
  have hs : etaleRestrictionPresheafSource V hT i =
      etaleRestrictionPullbackSource V := by
    apply (Ext.mk₀_bijective ZV (R.obj Z)).injective
    let p : ZV ⟶ R.obj Z := etaleRestrictionPresheafSource V hT i
    let q : ZV ⟶ R.obj Z := etaleRestrictionPullbackSource V
    have hzero := etaleCohomologyPresheafRestrictionEquiv_terminal_restriction_zero
      V hT i Z (Ext.mk₀ (𝟙 Z))
    have hpre := etaleRestrictionPresheafSource_apply V hT i Z 0 (Ext.mk₀ (𝟙 Z))
    have hpb := etaleRestrictionPullbackSource_apply V Z 0 (Ext.mk₀ (𝟙 Z))
    have hmap : (Ext.mk₀ (𝟙 Z)).mapExactFunctor R = Ext.mk₀ (𝟙 (R.obj Z)) :=
      (Ext.mapExactFunctor_mk₀ R (𝟙 Z)).trans
        (congrArg (fun k : R.obj Z ⟶ R.obj Z => Ext.mk₀ k) (R.map_id Z))
    have hp : (Ext.mk₀ p).comp ((Ext.mk₀ (𝟙 Z)).mapExactFunctor R) (zero_add 0) =
        Ext.mk₀ p :=
      (congrArg (fun z : Ext.{u} (R.obj Z) (R.obj Z) 0 =>
        (Ext.mk₀ p).comp z (zero_add 0)) hmap).trans (Ext.comp_mk₀_id (Ext.mk₀ p))
    have hq : (Ext.mk₀ q).comp ((Ext.mk₀ (𝟙 Z)).mapExactFunctor R) (zero_add 0) =
        Ext.mk₀ q :=
      (congrArg (fun z : Ext.{u} (R.obj Z) (R.obj Z) 0 =>
        (Ext.mk₀ q).comp z (zero_add 0)) hmap).trans (Ext.comp_mk₀_id (Ext.mk₀ q))
    exact hp.symm.trans ((hpre.symm.trans (hzero.trans hpb)).trans hq)
  have hpre := etaleRestrictionPresheafSource_apply V hT i F n a
  have hpb := etaleRestrictionPullbackSource_apply V F n a
  exact hpre.trans
    ((congrArg (fun p : ZV ⟶ R.obj Z =>
      (Ext.mk₀ p).comp (a.mapExactFunctor R) (zero_add n)) hs).trans hpb.symm)

end EtaleCohomology
