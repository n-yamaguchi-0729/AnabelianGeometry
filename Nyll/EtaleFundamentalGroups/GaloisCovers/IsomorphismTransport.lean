/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.FiniteEtale.Connected
public import Nyll.EtaleFundamentalGroups.GaloisCovers.Basic
public import Nyll.SchemeTheory.FiniteEtale.DensePullback
public import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.FintypeCat
public import Mathlib.CategoryTheory.Galois.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Galois covers under actual isomorphisms

An isomorphism of finite étale covers preserves the Galois property.
An isomorphism of base schemes also preserves it under the actual
pullback functor, together with the automorphism-group order.

The proofs retain the given isomorphisms: connectedness is transported by
their homeomorphisms, automorphisms by conjugation or faithful pullback,
and degree by the actual cartesian square. These comparisons let finite
coefficient models be flattened through a tower of intermediate fields.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

universe u

/-- The categorical Galois property is transported along an actual
isomorphism of finite étale covers. -/
theorem isGalois_of_iso {S : Scheme.{u}} [ConnectedSpace S]
    {Y Z : FiniteEtale S} (e : Y ≅ Z) [IsGalois Y] : IsGalois Z := by
  let G : FiniteEtale S ⥤ Scheme.{u} := forget S ⋙ Over.forget S
  have : ConnectedSpace Y.left := connectedSpace_left_of_isConnected Y
  have : ConnectedSpace Z.left := (G.mapIso e).hom.homeomorph.connectedSpace_iff.mp
    (inferInstance : ConnectedSpace Y.left)
  have : IsConnected Z := isConnected_of_connectedSpace_left Z
  let F := CategoryTheory.GaloisCategory.getFiberFunctor (FiniteEtale S)
  have hAut : Nat.card (Aut Z) = Nat.card (Aut Y) :=
    Nat.card_congr (Aut.autMulEquivOfIso e).symm.toEquiv
  have hFiber : Nat.card (F.obj Y) = Nat.card (F.obj Z) :=
    Nat.card_congr (FintypeCat.equivEquivIso.symm (F.mapIso e))
  exact (PreGaloisCategory.isGalois_iff_card_aut_eq_card_fiber F Z).mpr
    (hAut.trans (((PreGaloisCategory.isGalois_iff_card_aut_eq_card_fiber F Y).mp
      inferInstance).trans hFiber))

/-- Pullback along a base isomorphism preserves the Galois property and
the exact automorphism-group order. -/
theorem isGalois_pullback_and_card_aut_of_isIso
    {S T : Scheme.{u}} [ConnectedSpace S] [ConnectedSpace T]
    (j : S ⟶ T) [IsIso j] (Y : FiniteEtale T) [IsGalois Y] :
    let P := (pullback j).obj Y
    IsGalois P ∧ Nat.card (Aut P) = Nat.card (Aut Y) := by
  intro P
  let y : Y.left ⟶ T := Y.hom
  have : IsFiniteEtale y := Y.prop
  let p : P.left ⟶ Y.left := Limits.pullback.fst y j
  have : IsIso p := inferInstanceAs (IsIso (Limits.pullback.fst y j))
  have : ConnectedSpace Y.left := connectedSpace_left_of_isConnected Y
  have : ConnectedSpace P.left := p.homeomorph.connectedSpace_iff.mpr
    (inferInstance : ConnectedSpace Y.left)
  have : IsConnected P := isConnected_of_connectedSpace_left P
  let F := pullback j
  have : F.Faithful := pullback_faithful_of_isDominant j
  have hInjective : Function.Injective (F.mapAut Y) := by
    intro σ τ hστ
    apply Aut.ext
    apply Iso.ext
    apply F.map_injective
    exact congrArg (fun a => a.asIso.hom) hστ
  have hLower : Nat.card (Aut Y) ≤ Nat.card (Aut P) :=
    Nat.card_le_card_of_injective (F.mapAut Y) hInjective
  let s : S := Classical.choice (inferInstance : Nonempty S)
  let Ω := AlgebraicClosure (S.residueField s)
  let ξ : Spec (.of Ω) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) Ω)) ≫
      S.fromSpecResidueField s
  let ω := IsLocalRing.closedPoint Ω
  have hY : Nat.card (Aut Y) = Y.hom.finrank ((ξ ≫ j) ω) :=
    (isGalois_iff_card_aut_eq_finrank (ξ ≫ j) Y).mp inferInstance
  have hRank : P.hom.finrank (ξ ω) = Y.hom.finrank ((ξ ≫ j) ω) :=
    Scheme.Hom.finrank_of_isPullback (Limits.pullback.fst y j)
      (Limits.pullback.snd y j) y j (IsPullback.of_hasPullback y j) (ξ ω)
  have hUpper : Nat.card (Aut P) ≤ P.hom.finrank (ξ ω) := by
    have h := card_aut_le_card_fiber_of_connected (fiber ξ) P
    rwa [natCard_fiber_eq_finrank ξ P] at h
  have hCard : Nat.card (Aut P) = Nat.card (Aut Y) :=
    Nat.le_antisymm (hUpper.trans_eq (hRank.trans hY.symm)) hLower
  exact ⟨(isGalois_iff_card_aut_eq_finrank ξ P).mpr
    (hCard.trans (hY.trans hRank.symm)), hCard⟩

end AlgebraicGeometry.FiniteEtale
