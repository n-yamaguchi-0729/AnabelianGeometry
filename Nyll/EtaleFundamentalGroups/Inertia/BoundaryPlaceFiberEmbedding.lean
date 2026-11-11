/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Models.Ramification.FiniteCurveBoundaryMap
public import Nyll.AlgebraicCurves.Places.Ramification.GaloisPlaceFiber
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FundamentalGroup

/-! # Actual extending places as boundary coordinates of the same cover -/

@[expose] public section

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


/-- Every point of the actual finite étale fiber above one omitted place
is a distinct omitted place of the covering curve. This uses rational
points over the algebraically closed coefficient field and works in every
characteristic, without a Riemann--Hurwitz calculation. -/
def finiteEtaleBoundaryFiberEmbedding
    {κ F L : Type} [Field κ] [IsAlgClosed κ] [Field F] [Field L]
    [Algebra κ F] [Algebra κ L]
    (M : CurveModel κ F) (N : CurveModel κ L)
    (d : N.C ⟶ M.C) (hd : d ≫ M.toBase = N.toBase) [IsFiniteEtale d]
    {X Y : Scheme} (j : X ⟶ M.C) (k : Y ⟶ N.C)
    (hboundary : ∀ y : N.C, y ∉ Set.range k ↔ d y ∉ Set.range j)
    (v : M.openBoundaryPlaces j) :
    (FiniteEtale.fiber (M.pointEquivPlace.symm v.val).val).obj (FiniteEtale.mk d) ↪
      N.openBoundaryPlaces k := by
  let x := M.pointEquivPlace.symm v.val
  let W : FiniteEtale M.C := FiniteEtale.mk d
  let lift (z : (FiniteEtale.fiber x.val).obj W) :
      {p : Spec (.of κ) ⟶ N.C // p ≫ N.toBase = 𝟙 _} :=
    ⟨(FiniteEtale.fiberObjEquivHom x.val W z).left, by
      let p : Spec (.of κ) ⟶ N.C := (FiniteEtale.fiberObjEquivHom x.val W z).left
      have hp : p ≫ d = x.val := (FiniteEtale.fiberObjEquivHom x.val W z).w
      exact (congrArg (fun f : N.C ⟶ Spec (.of κ) => p ≫ f) hd.symm).trans
        ((Category.assoc p d M.toBase).symm.trans
          ((congrArg (fun f : Spec (.of κ) ⟶ M.C => f ≫ M.toBase) hp).trans
            x.property))⟩
  have hxpoint : x.val (IsLocalRing.closedPoint κ) = (M.placeEquiv.symm v.val).val := by
    change (pointEquivClosedPoint M.toBase x).val = _
    apply congrArg Subtype.val
    apply M.placeEquiv.injective
    exact (M.pointEquivPlace.apply_symm_apply v.val).trans
      (M.placeEquiv.apply_symm_apply v.val).symm
  have hpoint (z : (FiniteEtale.fiber x.val).obj W) :
      (N.placeEquiv.symm (N.pointEquivPlace (lift z))).val =
        (lift z).val (IsLocalRing.closedPoint κ) := by
    change (N.placeEquiv.symm (N.placeEquiv (pointEquivClosedPoint N.toBase (lift z)))).val = _
    exact congrArg Subtype.val (N.placeEquiv.symm_apply_apply _)
  have hb (z : (FiniteEtale.fiber x.val).obj W) :
      N.pointEquivPlace (lift z) ∈ N.openBoundaryPlaces k := by
    change (N.placeEquiv.symm (N.pointEquivPlace (lift z))).val ∉ Set.range k
    rw [hpoint]
    apply (hboundary _).mpr
    have hdx : d ((lift z).val (IsLocalRing.closedPoint κ)) =
        (M.placeEquiv.symm v.val).val :=
      (congrArg (fun f : Spec (.of κ) ⟶ M.C => f (IsLocalRing.closedPoint κ))
        (FiniteEtale.fiberObjEquivHom x.val W z).w).trans hxpoint
    rw [hdx]
    exact v.property
  refine ⟨fun z => ⟨N.pointEquivPlace (lift z), hb z⟩, ?_⟩
  intro a b hab
  apply (FiniteEtale.fiberObjEquivHom x.val W).injective
  apply Over.OverMorphism.ext
  exact congrArg Subtype.val
    (N.pointEquivPlace.injective (congrArg Subtype.val hab))

/-- The actual fiber degree above any omitted point is a lower bound for
the covering boundary. In particular a fiber of degree at least three
supplies the three punctures required by the mixed reconstruction. -/
theorem finiteEtale_fiber_card_le_boundary
    {κ F L : Type} [Field κ] [IsAlgClosed κ] [Field F] [Field L]
    [Algebra κ F] [Algebra κ L]
    (M : CurveModel κ F) (N : CurveModel κ L)
    (d : N.C ⟶ M.C) (hd : d ≫ M.toBase = N.toBase) [IsFiniteEtale d]
    {X Y : Scheme} [Nonempty Y] (j : X ⟶ M.C) (k : Y ⟶ N.C) [IsOpenImmersion k]
    (hboundary : ∀ y : N.C, y ∉ Set.range k ↔ d y ∉ Set.range j)
    (v : M.openBoundaryPlaces j) :
    Nat.card ((FiniteEtale.fiber (M.pointEquivPlace.symm v.val).val).obj (FiniteEtale.mk d)) ≤
      Nat.card (N.openBoundaryPlaces k) := by
  have : Finite (N.openBoundaryPlaces k) := (N.openBoundaryPlaces_finite k).to_subtype
  exact Nat.card_le_card_of_injective
    (finiteEtaleBoundaryFiberEmbedding M N d hd j k hboundary v)
    (finiteEtaleBoundaryFiberEmbedding M N d hd j k hboundary v).injective

end EtaleFundamentalGroups
