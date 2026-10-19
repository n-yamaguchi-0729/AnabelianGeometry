/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Models.Ramification.FiniteCurveBoundaryMap
import Nyll.AlgebraicCurves.Places.Ramification.GaloisPlaceFiber

/-! # Actual extending places as boundary coordinates of the same cover -/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve

namespace EtaleFundamentalGroups

/-- The exact boundary square embeds every place over a specified boundary
place into the actual boundary of the covering model. -/
def boundaryPlaceFiberEmbedding
    {κ F L : Type} [Field κ] [IsAlgClosed κ] [Field F] [Field L]
    [Algebra κ F] [Algebra κ L] [Algebra F L] [IsScalarTower κ F L]
    [FiniteDimensional F L] [IsGalois F L]
    (M : CurveModel κ F) (N : CurveModel κ L)
    (d : N.C ⟶ M.C) (hd : d ≫ M.toBase = N.toBase)
    [IsFinite d] (hsurj : Function.Surjective d)
    {X Y : Scheme} (j : X ⟶ M.C) (k : Y ⟶ N.C)
    (hboundary : ∀ y : N.C, y ∉ Set.range k ↔ d y ∉ Set.range j)
    (hfield : (M.finiteCurveFieldMap N d hd hsurj).toRingHom = algebraMap F L)
    (v : M.openBoundaryPlaces j) :
    Place.galoisPlaceFiber (L := L) v.val ↪ N.openBoundaryPlaces k := by
  let φ := M.finiteCurveFieldMap N d hd hsurj
  have hrestrict (w : Place κ L) :
      w.restrictAlong φ (M.finiteCurveFieldMap_integral N d hd hsurj) =
        w.restrict F := by
    apply Place.ext
    ext a
    change (M.finiteCurveFieldMap N d hd hsurj).toRingHom a ∈ w.toValuationSubring ↔
      algebraMap F L a ∈ w.toValuationSubring
    rw [DFunLike.congr_fun hfield a]
  have hb (z : Place.galoisPlaceFiber (L := L) v.val) :
      z.val ∈ N.openBoundaryPlaces k := by
    rw [M.openBoundaryPlaces_eq_restrict_preimage N d hd hsurj j k hboundary]
    change z.val.restrictAlong φ _ ∈ M.openBoundaryPlaces j
    rw [hrestrict z.val, z.property]
    exact v.property
  refine ⟨fun z => ⟨z.val, hb z⟩, ?_⟩
  intro a b h
  apply Subtype.ext
  exact congrArg (fun z : N.openBoundaryPlaces k => z.val) h

end EtaleFundamentalGroups
