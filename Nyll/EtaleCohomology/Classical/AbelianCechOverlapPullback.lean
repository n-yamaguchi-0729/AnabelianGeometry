/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.AbelianCechPullback
public import Nyll.EtaleCohomology.Classical.AbelianSheafFunctors
public import Nyll.EtaleCohomology.Classical.CupAbelianCechResolution
public import Nyll.EtaleCohomology.Classical.FreeAbelianCechOverlap
public import Nyll.EtaleCohomology.Classical.FreeAbelianYoneda
public import Nyll.EtaleCohomology.Classical.FreeAbelianYonedaPullback
public import Nyll.EtaleCohomology.Sites.BaseChange
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Actual overlap edges under scheme pullback

The map from an actual overlap to the first covering kernel commutes
with base change. This follows from its original second-minus-first
boundary and the naturality of the original free representables.
-/

@[expose] public section

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory Limits

namespace EtaleCohomology

private theorem overlapEdge_comp_kernel
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{v}] {T V W : C}
    (hT : IsTerminal T) (f : V ⟶ T) [HasPullback f f] (x y : W ⟶ V) :
    ((freeAbelianSheafYoneda J).map
        (pullback.lift x y (hT.hom_ext (x ≫ f) (y ≫ f))) ≫
      (freeCechEdgeSheafIso J f).inv ≫ abelianCechFirstRelationMap J hT f) ≫
        kernel.ι (abelianCechUnitAugmentation J hT f) =
      (freeAbelianSheafYoneda J).map y - (freeAbelianSheafYoneda J).map x := by
  rw [Category.assoc, Category.assoc, abelianCechFirstRelationMap_comp,
    freeCechEdgeSheafIso_boundary, Preadditive.comp_sub,
    ← Functor.map_comp, ← Functor.map_comp, pullback.lift_snd, pullback.lift_fst]

/-- The actual edge of two maps into the original cover is carried to
the edge of their actual base changes by the original first-kernel
comparison. -/
theorem abelianCechOverlapEdge_pullback
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    {T V W : Y.Etale} (hT : IsTerminal T) (f : V ⟶ T)
    (hf : Sieve.generate (Presieve.singleton f) ∈ Y.smallEtaleTopology T)
    (x y : W ⟶ V) :
    let B := etaleBaseChange p
    let hB := hT.isTerminalObj B T
    let l := pullback.lift x y (hT.hom_ext (x ≫ f) (y ≫ f))
    let lB := pullback.lift (B.map x) (B.map y)
      (hB.hom_ext (B.map x ≫ B.map f) (B.map y ≫ B.map f))
    let edge := (freeAbelianSheafYoneda Y.smallEtaleTopology).map l ≫
      (freeCechEdgeSheafIso Y.smallEtaleTopology f).inv ≫
        abelianCechFirstRelationMap Y.smallEtaleTopology hT f
    let edgeB := (freeAbelianSheafYoneda X.smallEtaleTopology).map lB ≫
      (freeCechEdgeSheafIso X.smallEtaleTopology (B.map f)).inv ≫
        abelianCechFirstRelationMap X.smallEtaleTopology hB (B.map f)
    edgeB ≫ abelianCechAugmentationKernelPullback p hT f hf =
      (freeAbelianSheafYonedaPullbackIso p W).inv ≫
        (etaleAbelianPullback p).map edge := by
  intro B hB l lB edge edgeB
  let L := etaleAbelianPullback p
  let k := kernel.ι (abelianCechUnitAugmentation Y.smallEtaleTopology hT f)
  have : Mono (L.map k) :=
    ((abelianCechAugmentationSequence_shortExact Y.smallEtaleTopology hT f hf).map_of_exact
      L).mono_f
  have hboundary : edge ≫ k =
      (freeAbelianSheafYoneda Y.smallEtaleTopology).map y -
        (freeAbelianSheafYoneda Y.smallEtaleTopology).map x :=
    overlapEdge_comp_kernel Y.smallEtaleTopology hT f x y
  have hboundaryB : edgeB ≫
      kernel.ι (abelianCechUnitAugmentation X.smallEtaleTopology hB (B.map f)) =
      (freeAbelianSheafYoneda X.smallEtaleTopology).map (B.map y) -
        (freeAbelianSheafYoneda X.smallEtaleTopology).map (B.map x) :=
    overlapEdge_comp_kernel X.smallEtaleTopology hB (B.map f) (B.map x) (B.map y)
  apply (cancel_mono (L.map k)).mp
  rw [Category.assoc, abelianCechAugmentationKernelPullback_comp,
    ← Category.assoc, hboundaryB, Category.assoc, ← Functor.map_comp,
    hboundary, Functor.map_sub, Preadditive.sub_comp, Preadditive.comp_sub,
    freeAbelianSheafYonedaPullbackIso_inv_naturality,
    freeAbelianSheafYonedaPullbackIso_inv_naturality]

end EtaleCohomology
