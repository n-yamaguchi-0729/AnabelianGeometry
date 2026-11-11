/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.AbelianRestrictionPullback
public import Nyll.EtaleCohomology.Classical.EtaleRestriction
public import Nyll.EtaleCohomology.Classical.EtaleRestrictionNaturality
public import Nyll.EtaleCohomology.Classical.FreeAbelianCohomologySections
public import Nyll.EtaleCohomology.Classical.FreeAbelianYoneda
public import Nyll.EtaleCohomology.Sites.EtaleRestriction
public import Nyll.EtaleCohomology.Sites.EtaleSlice
public import Nyll.SchemeTheory.Sheaves.OverExtension
public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# The original localization comparisons retain actual sections

The constant-source isomorphism for the slice equivalence is its
original left-adjoint uniqueness isomorphism. Its adjunction unit
therefore gives the original section map. Combined with the original
free-abelian Yoneda comparisons, this identifies the degree-zero
terminal restriction with the original cohomological pullback.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

namespace EtaleCohomology

variable {X : Scheme.{u}} (V : X.Etale)

/-- The actual slice comparison on degree-zero cohomology is the
original unit of the actual equivalence of sheaf categories. -/
theorem etaleSliceAbelianCohomologyEquiv_zero_sections
    (F : Sheaf (X.smallEtaleTopology.over V) AddCommGrpCat.{u})
    (a : Sheaf.H.{u} F 0) :
    Sheaf.H.equiv₀ ((etaleSliceAbelianSheafEquivalence V).functor.obj F)
        ((Over.mkIdTerminal (X := V)).isTerminalObj
          (etaleSliceEquiv V).functor (Over.mk (𝟙 V)))
        (etaleSliceAbelianCohomologyEquiv V F 0 a) =
      ((etaleSliceAbelianSheafEquivalence V).unitIso.hom.app F).hom.app
        (op (Over.mk (𝟙 V)))
          (Sheaf.H.equiv₀ F (Over.mkIdTerminal (X := V)) a) := by
  let E := etaleSliceAbelianSheafEquivalence V
  let A := AddCommGrpCat.of (ULift.{u} ℤ)
  let Z := (constantSheaf (X.smallEtaleTopology.over V) AddCommGrpCat.{u}).obj A
  let hT := Over.mkIdTerminal (X := V)
  let hW := hT.isTerminalObj (etaleSliceEquiv V).functor (Over.mk (𝟙 V))
  let cOver := constantSheafAdj (X.smallEtaleTopology.over V) AddCommGrpCat.{u} hT
  let c₁ := cOver.comp E.toAdjunction
  let c₂ := constantSheafAdj V.left.smallEtaleTopology AddCommGrpCat.{u} hW
  let b : Z ⟶ F := Ext.addEquiv₀ a
  let e := (etaleSliceAbelianConstantIso V).app A
  have hz : Ext.addEquiv₀ (etaleSliceAbelianCohomologyEquiv V F 0 a) =
      e.inv ≫ E.functor.map (Ext.addEquiv₀ a) := by
    apply (Ext.mk₀_bijective _ (E.functor.obj F)).injective
    rw [Ext.mk₀_addEquiv₀_apply, etaleSliceAbelianCohomologyEquiv_apply,
      ← Ext.mk₀_comp_mk₀, ← Ext.mapExactFunctor_mk₀, Ext.mk₀_addEquiv₀_apply]
  have hc : c₂.homEquiv A (E.functor.obj F) (e.inv ≫ E.functor.map b) =
      c₁.homEquiv A (E.functor.obj F) (E.functor.map b) := by
    change c₂.homEquiv A (E.functor.obj F)
      ((c₂.leftAdjointUniq c₁).hom.app A ≫ E.functor.map b) = _
    let R₀ := (sheafSections V.left.smallEtaleTopology AddCommGrpCat.{u}).obj
      (op ((etaleSliceEquiv V).functor.obj (Over.mk (𝟙 V))))
    have hn := c₂.homEquiv_naturality_right
      ((c₂.leftAdjointUniq c₁).hom.app A) (E.functor.map b)
    have hu := Adjunction.homEquiv_leftAdjointUniq_hom_app c₂ c₁ A
    have hf := c₁.homEquiv_unit (X := A) (Y := E.functor.obj F) (f := E.functor.map b)
    exact hn.trans
      ((congrArg (fun q : A ⟶ R₀.obj (E.functor.obj Z) =>
        q ≫ R₀.map (E.functor.map b)) hu).trans hf.symm)
  have hb : c₁.homEquiv A (E.functor.obj F) (E.functor.map b) =
      cOver.homEquiv A (E.inverse.obj (E.functor.obj F))
        (b ≫ E.unitIso.hom.app F) := by
    rw [Adjunction.comp_homEquiv]
    change cOver.homEquiv A _
      (E.toAdjunction.homEquiv Z (E.functor.obj F) (E.functor.map b)) = _
    rw [E.toAdjunction.homEquiv_unit]
    exact congrArg (cOver.homEquiv A _)
      (E.unitIso.hom.naturality b).symm
  have heval : Sheaf.H.equiv₀ (E.functor.obj F) hW
      (etaleSliceAbelianCohomologyEquiv V F 0 a) =
      Sheaf.H.equiv₀ (E.inverse.obj (E.functor.obj F)) hT
        (Sheaf.H.map (E.unitIso.hom.app F) 0 a) := by
    change AddCommGrpCat.uliftZMultiplesAddEquiv _
        (c₂.homEquiv A _
          (Ext.addEquiv₀ (etaleSliceAbelianCohomologyEquiv V F 0 a))) =
      AddCommGrpCat.uliftZMultiplesAddEquiv _
        (cOver.homEquiv A _
          (Ext.addEquiv₀ (Sheaf.H.map (E.unitIso.hom.app F) 0 a)))
    rw [hz, Sheaf.H.addEquiv₀_map]
    exact congrArg (AddCommGrpCat.uliftZMultiplesAddEquiv _) (hc.trans hb)
  exact heval.trans
    (Sheaf.H.equiv₀_naturality hT (E.unitIso.hom.app F) a).symm

/-- The original localized-site comparison evaluates to the actual
source section, transported by the original slice-equivalence unit. -/
theorem etaleCohomologyPresheafRestrictionEquiv_zero_sections
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (a : Sheaf.H'.{u} F 0 V) :
    Sheaf.H.equiv₀ ((etaleRestriction V.hom AddCommGrpCat.{u}).obj F)
        ((Over.mkIdTerminal (X := V)).isTerminalObj
          (etaleSliceEquiv V).functor (Over.mk (𝟙 V)))
        (etaleCohomologyPresheafRestrictionEquiv V F 0 a) =
      F.obj.map ((etaleSliceEquiv V).unitIso.app (Over.mk (𝟙 V))).inv.left.op
        (freeAbelianSheafYonedaHomEquiv X.smallEtaleTopology V F (Ext.addEquiv₀ a)) := by
  have h := etaleSliceAbelianCohomologyEquiv_zero_sections V (F.over V)
    (sheafCohomologyOverEquiv X.smallEtaleTopology V F 0 a)
  rw [sheafCohomologyOverEquiv_zero_sections] at h
  exact h

/-- In degree zero the original terminal-object and localized-site
comparisons give exactly the original cohomological pullback. The
terminal representative and its actual source arrow are retained. -/
theorem etaleCohomologyPresheafRestrictionEquiv_terminal_restriction_zero
    {T : X.Etale} (hT : IsTerminal T) (i : V ⟶ T)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (a : Sheaf.H.{u} F 0) :
    etaleCohomologyPresheafRestrictionEquiv V F 0
        ((F.cohomologyPresheaf 0).map i.op
          (sheafCohomologyTerminalEquiv X.smallEtaleTopology hT F 0 a)) =
      etaleAbelianRestrictionCohomologyPullback V.hom F 0 a := by
  let W := (etaleSliceEquiv V).functor.obj (Over.mk (𝟙 V))
  let hW : IsTerminal W := (Over.mkIdTerminal (X := V)).isTerminalObj
    (etaleSliceEquiv V).functor (Over.mk (𝟙 V))
  let c := (etaleSliceEquiv V).unitIso.app (Over.mk (𝟙 V))
  let k : (etalePostcompose V.hom).obj W ⟶ T := c.inv.left ≫ i
  have hk : MorphismProperty.Over.homMk
      (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
      (A := (etalePostcompose V.hom).obj W) (B := T) k.left k.w = k := by
    apply MorphismProperty.Over.Hom.ext
    rfl
  have hp := etaleAbelianRestrictionCohomologyPullback_zero_sections
    V.hom F hT hW k.left k.w a
  rw [hk] at hp
  apply (Sheaf.H.equiv₀ ((etaleRestriction V.hom AddCommGrpCat.{u}).obj F) hW).injective
  rw [etaleCohomologyPresheafRestrictionEquiv_zero_sections,
    sheafCohomologyPresheaf_zero_sections_map,
    sheafCohomologyTerminalEquiv_zero_sections, hp]
  exact (ConcreteCategory.congr_hom
    (F.obj.map_comp i.op c.inv.left.op) (Sheaf.H.equiv₀ F hT a)).symm

end EtaleCohomology
