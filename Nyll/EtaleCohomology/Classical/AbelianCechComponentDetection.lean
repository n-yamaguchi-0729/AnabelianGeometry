/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.CupAbelianCechResolution
public import Nyll.EtaleCohomology.Classical.EtaleObjectComponentDecomposition
public import Nyll.EtaleCohomology.Classical.FreeAbelianCechOverlap
public import Nyll.EtaleCohomology.Classical.FreeAbelianYoneda
public import Nyll.EtaleCohomology.Sites.BaseChange
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Detecting the original covering relation on actual overlap components

The reduced components of the original parameter overlap remain jointly
detecting after scheme base change. The original free edge sheaf is the
free representable of that base-changed overlap. Hence equality on the
actual component edges proves equality on the original first relation.
The component edges use the two original projections, so they agree with
the edges used for the geometric transition and cup calculations.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Abelian Opposite TopologicalSpace

namespace EtaleCohomology

variable {X Y : Scheme.{u}} (p : X ⟶ Y)
  {T V : Y.Etale} (hT : IsTerminal T) (f : V ⟶ T)

/-- The base change of an actual overlap map is the pullback lift
of its same two projections. -/
theorem etaleBaseChange_overlapMap_eq_lift
    {W : Y.Etale} (j : W ⟶ pullback f f) :
    let B := etaleBaseChange p
    let hB := hT.isTerminalObj B T
    B.map j ≫ (PreservesPullback.iso B f f).hom =
      pullback.lift (B.map (j ≫ pullback.fst f f))
        (B.map (j ≫ pullback.snd f f))
        (hB.hom_ext
          (B.map (j ≫ pullback.fst f f) ≫ B.map f)
          (B.map (j ≫ pullback.snd f f) ≫ B.map f)) := by
  intro B hB
  apply pullback.hom_ext
  · rw [Category.assoc, PreservesPullback.iso_hom_fst,
      pullback.lift_fst, Functor.map_comp]
  · rw [Category.assoc, PreservesPullback.iso_hom_snd,
      pullback.lift_snd, Functor.map_comp]

/-- Equality on the actual base-changed integral component edges
detects equality after the original first covering relation, in every
cohomological degree and for every original coefficient sheaf. -/
theorem abelianCechFirstRelation_ext_of_baseChange_components
    [IsNoetherian (pullback f f).left]
    (hdom : ∀ z : (pullback f f).left,
      IsDomain ((pullback f f).left.presheaf.stalk z))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ) :
    let B := etaleBaseChange p
    let hB := hT.isTerminalObj B T
    let Q := freeAbelianSheafYoneda X.smallEtaleTopology
    let qB := abelianCechFirstRelationMap X.smallEtaleTopology hB (B.map f)
    ∀ a b : Ext (kernel (abelianCechUnitAugmentation
        X.smallEtaleTopology hB (B.map f))) F n,
      (∀ Z : irreducibleComponents (pullback f f).left,
        let j := etaleObjectReducedComponentMap (pullback f f) hdom Z
        let l := pullback.lift (B.map (j ≫ pullback.fst f f))
          (B.map (j ≫ pullback.snd f f))
          (hB.hom_ext
            (B.map (j ≫ pullback.fst f f) ≫ B.map f)
            (B.map (j ≫ pullback.snd f f) ≫ B.map f))
        let edge := Q.map l ≫
          (freeCechEdgeSheafIso X.smallEtaleTopology (B.map f)).inv ≫ qB
        (Ext.mk₀ edge).comp a (zero_add n) =
          (Ext.mk₀ edge).comp b (zero_add n)) →
      (Ext.mk₀ qB).comp a (zero_add n) =
        (Ext.mk₀ qB).comp b (zero_add n) := by
  intro B hB Q qB a b h
  let e := Q.mapIso (PreservesPullback.iso B f f) ≪≫
    (freeCechEdgeSheafIso X.smallEtaleTopology (B.map f)).symm
  have he : (Ext.mk₀ e.hom).comp ((Ext.mk₀ qB).comp a (zero_add n)) (zero_add n) =
      (Ext.mk₀ e.hom).comp ((Ext.mk₀ qB).comp b (zero_add n)) (zero_add n) := by
    apply etaleBaseChangeReducedComponentsCohomology_ext (pullback f f) hdom p F n
    intro Z
    let j := etaleObjectReducedComponentMap (pullback f f) hdom Z
    have hj : Q.map (B.map j) ≫ e.hom ≫ qB =
        Q.map (pullback.lift (B.map (j ≫ pullback.fst f f))
          (B.map (j ≫ pullback.snd f f))
          (hB.hom_ext
            (B.map (j ≫ pullback.fst f f) ≫ B.map f)
            (B.map (j ≫ pullback.snd f f) ≫ B.map f))) ≫
          (freeCechEdgeSheafIso X.smallEtaleTopology (B.map f)).inv ≫ qB := by
      have hj' : Q.map (B.map j) ≫ e.hom =
          Q.map (pullback.lift (B.map (j ≫ pullback.fst f f))
            (B.map (j ≫ pullback.snd f f))
            (hB.hom_ext
              (B.map (j ≫ pullback.fst f f) ≫ B.map f)
              (B.map (j ≫ pullback.snd f f) ≫ B.map f))) ≫
            (freeCechEdgeSheafIso X.smallEtaleTopology (B.map f)).inv := by
        change Q.map (B.map j) ≫
          (Q.map (PreservesPullback.iso B f f).hom ≫
            (freeCechEdgeSheafIso X.smallEtaleTopology (B.map f)).inv) = _
        rw [← Category.assoc, ← Functor.map_comp,
          etaleBaseChange_overlapMap_eq_lift p hT f j]
      simpa only [Category.assoc] using congrArg (fun z => z ≫ qB) hj'
    change (Ext.mk₀ (Q.map (B.map j))).comp
        ((Ext.mk₀ e.hom).comp ((Ext.mk₀ qB).comp a (zero_add n)) (zero_add n))
          (zero_add n) =
      (Ext.mk₀ (Q.map (B.map j))).comp
        ((Ext.mk₀ e.hom).comp ((Ext.mk₀ qB).comp b (zero_add n)) (zero_add n))
          (zero_add n)
    simpa only [Ext.mk₀_comp_mk₀_assoc, Category.assoc, hj] using h Z
  have he' := congrArg (fun z => (Ext.mk₀ e.inv).comp z (zero_add n)) he
  simpa only [Ext.mk₀_comp_mk₀_assoc, e.inv_hom_id_assoc] using he'

end EtaleCohomology
