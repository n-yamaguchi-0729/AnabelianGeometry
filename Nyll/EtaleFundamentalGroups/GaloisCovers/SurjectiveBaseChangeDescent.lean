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
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Galois.GaloisObjects
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Topology.Connected.Basic

/-!
# Detecting Galois descent by the actual deck-transformation map

Suppose a finite étale cover becomes Galois after surjective base change
between connected schemes. It is Galois before base change exactly when
every deck transformation after base change descends through the actual
pullback functor.

Surjectivity on source schemes descends connectedness of the cover.
Faithfulness of dominant pullback makes its map on automorphism groups
injective. The degree of a finite étale morphism is preserved by the
actual cartesian square. Comparing these degrees with the Galois
automorphism cardinality proves both directions of the criterion.

This is used after finite coefficient descent of the finitely many
automorphisms of a geometric Galois cover. It does not assume that those
automorphisms have descended or assert a finite-field model without
constructing one.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.PreGaloisCategory

namespace EtaleFundamentalGroups

universe u

/-- If a cover becomes Galois after surjective base change, being Galois
before base change is equivalent to surjectivity of the actual pullback
map on deck-transformation groups. Connectedness before base change is
proved from the original surjection. -/
theorem isGalois_iff_surjective_mapAut_of_surjective_baseChange
    {S T : Scheme.{u}} [ConnectedSpace S] [ConnectedSpace T]
    (j : T ⟶ S) [Surjective j] (Y : FiniteEtale S) :
    let F := FiniteEtale.pullback j
    let P := F.obj Y
    ∀ [IsGalois P], IsGalois Y ↔ Function.Surjective (F.mapAut Y) := by
  intro F P hGaloisP
  have : ConnectedSpace P.left := FiniteEtale.connectedSpace_left_of_isConnected P
  let y : Y.left ⟶ S := Y.hom
  have : IsFiniteEtale y := Y.prop
  let p : P.left ⟶ Y.left := pullback.fst y j
  have : Surjective p := inferInstanceAs (Surjective (pullback.fst y j))
  have : ConnectedSpace Y.left := p.surjective.connectedSpace p.continuous
  have : IsConnected Y := FiniteEtale.isConnected_of_connectedSpace_left Y
  have : F.Faithful := FiniteEtale.pullback_faithful_of_isDominant j
  have hInjective : Function.Injective (F.mapAut Y) := by
    intro σ τ hστ
    apply Aut.ext
    apply Iso.ext
    apply F.map_injective
    exact congrArg (fun a => a.asIso.hom) hστ
  let t : T := Classical.choice (inferInstance : Nonempty T)
  let Ω := AlgebraicClosure (T.residueField t)
  let ξ : Spec (.of Ω) ⟶ T :=
    Spec.map (CommRingCat.ofHom (algebraMap (T.residueField t) Ω)) ≫
      T.fromSpecResidueField t
  let ω := IsLocalRing.closedPoint Ω
  have hGaloisRank : Nat.card (Aut P) = P.hom.finrank (ξ ω) :=
    (FiniteEtale.isGalois_iff_card_aut_eq_finrank ξ P).mp hGaloisP
  have hRank : P.hom.finrank (ξ ω) = Y.hom.finrank ((ξ ≫ j) ω) := by
    change (pullback.snd y j).finrank (ξ ω) = y.finrank (j (ξ ω))
    exact Scheme.Hom.finrank_of_isPullback (pullback.fst y j) (pullback.snd y j)
      y j (IsPullback.of_hasPullback y j) (ξ ω)
  have hDegree : Nat.card (Aut P) = Y.hom.finrank ((ξ ≫ j) ω) :=
    hGaloisRank.trans hRank
  constructor
  · intro hY
    have hCard : Nat.card (Aut Y) = Nat.card (Aut P) :=
      ((FiniteEtale.isGalois_iff_card_aut_eq_finrank (ξ ≫ j) Y).mp hY).trans
        hDegree.symm
    exact ((Nat.bijective_iff_injective_and_card (F.mapAut Y)).mpr
      ⟨hInjective, hCard⟩).surjective
  · intro hSurjective
    let e : Aut Y ≃* Aut P := MulEquiv.ofBijective (F.mapAut Y) ⟨hInjective, hSurjective⟩
    apply (FiniteEtale.isGalois_iff_card_aut_eq_finrank (ξ ≫ j) Y).mpr
    exact (Nat.card_congr e.toEquiv).trans hDegree

end EtaleFundamentalGroups
