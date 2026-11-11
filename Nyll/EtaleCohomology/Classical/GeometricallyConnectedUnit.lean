/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.AbelianSheafFunctors
public import Nyll.EtaleCohomology.Sites.GeometricallyConnectedUnit
public import Nyll.EtaleCohomology.Sites.SheafFunctors
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.NatIso

/-!
# Actual abelian sheaf descent under geometrically connected pullback

The proved module unit makes the original module inverse image fully
faithful. The existing integer-sheaf equivalence transports this fact to
the original abelian inverse image, hence to its original adjunction unit.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory

namespace EtaleCohomology

/-- The original abelian inverse-image/direct-image unit is an isomorphism
for every coefficient sheaf along a flat quasi-compact geometrically
connected morphism. -/
theorem etaleAbelianPullbackUnit_isIso_of_geometricallyConnected
    {X Y : Scheme.{u}} (q : X ⟶ Y) [Flat q] [QuasiCompact q] [GeometricallyConnected q]
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    IsIso ((etaleAbelianPullbackPushforwardAdjunction q).unit.app F) := by
  have : ∀ G, IsIso ((etalePullbackPushforwardAdjunction q (ULift.{u} ℤ)).unit.app G) :=
    fun G => etaleGeometricallyConnected_unit_isIso q (ULift.{u} ℤ) G
  have : IsIso (etalePullbackPushforwardAdjunction q (ULift.{u} ℤ)).unit :=
    NatIso.isIso_of_isIso_app _
  let ff := (etalePullbackPushforwardAdjunction q (ULift.{u} ℤ)).fullyFaithfulLOfIsIsoUnit
  have : (etalePullback q (ULift.{u} ℤ)).Full := ff.full
  have : (etalePullback q (ULift.{u} ℤ)).Faithful := ff.faithful
  have : (etaleAbelianPullback q).Full := by
    dsimp only [etaleAbelianPullback]
    exact inferInstance
  have : (etaleAbelianPullback q).Faithful := by
    dsimp only [etaleAbelianPullback]
    exact inferInstance
  exact inferInstance

end EtaleCohomology
