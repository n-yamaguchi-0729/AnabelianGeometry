/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.CharacterAnnihilatorTransport
import Nyll.EtaleFundamentalGroups.Cohomology.FiniteH1Comparison
import Nyll.EtaleFundamentalGroups.FiniteEtale.Connected
import Nyll.EtaleFundamentalGroups.GaloisCategories.ConnectedActions
import Nyll.EtaleFundamentalGroups.GaloisCategories.CoverTransportFiber
import Nyll.EtaleFundamentalGroups.GeometricFiber.MatchedFiberCoverGroupTransport
import Nyll.EtaleFundamentalGroups.GaloisCovers.Basic
import Mathlib.CategoryTheory.Endomorphism

/-! # Finite covers and their cohomology under fundamental-group isomorphisms

An isomorphism of the original fundamental groups transports an actual
connected finite étale cover, its chosen point, degree, and all finite
constant-coefficient H¹ groups. The covering-group isomorphism retains the
original inclusion square; no matching of covers or cohomology is assumed.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale
open CategoryTheory.PreGaloisCategory EtaleFundamentalGroups.Cohomology
open scoped FintypeCatDiscrete

namespace AnabelianGeometry.GeometricFundamentalGroup

universe u

variable {X Y : Scheme.{u}} [ConnectedSpace X] [ConnectedSpace Y]
  {Ω₁ Ω₂ : Type u} [Field Ω₁] [Field Ω₂] [IsSepClosed Ω₁] [IsSepClosed Ω₂]
  (x : Spec (.of Ω₁) ⟶ X) (y : Spec (.of Ω₂) ⟶ Y)

/-- Actual finite-coefficient H¹ is recovered from the topological
fundamental group, with no assumptions of smoothness or properness. -/
def finiteH1EquivOfFundamentalGroupEquiv
    (e : π₁ᵉᵗ(x) ≃ₜ* π₁ᵉᵗ(y)) (C : AddCommGrpCat.{u}) [Finite C] :
    Sheaf.H.{u} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj C) 1 ≃+
      Sheaf.H.{u} ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj C) 1 := by
  let : TopologicalSpace (Multiplicative C) := ⊥
  have : DiscreteTopology (Multiplicative C) := ⟨rfl⟩
  exact (finiteH1CharacterEquiv C x).trans
    ((WeightFiltration.characterPullback e.symm).trans (finiteH1CharacterEquiv C y).symm)

/-- Transport an actual connected pointed cover, retaining its degree,
covering-group inclusion, and finite constant-coefficient cohomology. -/
theorem exists_connected_cover_preserving_degree_and_h1
    (e : π₁ᵉᵗ(x) ≃ₜ* π₁ᵉᵗ(y))
    (A : FiniteEtale X) [ConnectedSpace A.left]
    (a : Spec (.of Ω₁) ⟶ A.left) (ha : a ≫ A.hom = x) :
    ∃ (B : FiniteEtale Y) (_ : ConnectedSpace B.left)
      (b : Spec (.of Ω₂) ⟶ B.left) (hb : b ≫ B.hom = y)
      (eB : π₁ᵉᵗ(a) ≃ₜ* π₁ᵉᵗ(b)),
      (IsGalois A → IsGalois B) ∧
      (∀ g, pointedFundamentalGroupHom B.hom b y hb (eB g) =
        e (pointedFundamentalGroupHom A.hom a x ha g)) ∧
      Nat.card ((fiber y).obj B) = Nat.card ((fiber x).obj A) ∧
      ∀ (C : AddCommGrpCat.{u}) (_ : Finite C),
        Nat.card (Sheaf.H.{u}
          ((constantSheaf A.left.smallEtaleTopology AddCommGrpCat.{u}).obj C) 1) =
        Nat.card (Sheaf.H.{u}
          ((constantSheaf B.left.smallEtaleTopology AddCommGrpCat.{u}).obj C) 1) := by
  let B := (coverTransportOfAutEquiv (fiber x) (fiber y) e).functor.obj A
  let f : (fiber x).obj A ≃ (fiber y).obj B :=
    (coverTransportFiberEquiv (fiber x) (fiber y) e A).symm
  have hf (g : π₁ᵉᵗ(x)) (z : (fiber x).obj A) : f (g • z) = e g • f z := by
    simpa only [e.symm_apply_apply] using
      coverTransportFiberEquiv_symm_smul (fiber x) (fiber y) e A (e g) z
  let w : (fiber x).obj A := (fiberObjEquivHom x A).symm (Over.homMk a ha)
  have : IsConnected A := isConnected_of_connectedSpace_left A
  have : Nonempty ((fiber y).obj B) := ⟨f w⟩
  have : MulAction.IsPretransitive π₁ᵉᵗ(y) ((fiber y).obj B) := by
    constructor
    intro v w
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq π₁ᵉᵗ(x) (f.symm v) (f.symm w)
    refine ⟨e g, ?_⟩
    calc
      e g • v = e g • f (f.symm v) := by rw [f.apply_symm_apply]
      _ = f (g • f.symm v) := (hf g (f.symm v)).symm
      _ = f (f.symm w) := congrArg f hg
      _ = w := f.apply_symm_apply w
  have : IsConnected B := FiberFunctor.isConnected_of_isPretransitive (fiber y) B
  have hB : ConnectedSpace B.left := connectedSpace_left_of_isConnected B
  let b := actualFiberPointLift y B (f w)
  have hb : b ≫ B.hom = y := actualFiberPointLift_comp y B (f w)
  have hpoint : f ((fiberObjEquivHom x A).symm (Over.homMk a ha)) =
      (fiberObjEquivHom y B).symm (Over.homMk b hb) :=
    (actualFiberPointLift_fiberPoint y B (f w)).symm
  let eB := pointedCoverGroupTransport A B x y a b ha hb e f hf hpoint
  refine ⟨B, hB, b, hb, eB, ?_, ?_, Nat.card_congr f.symm, ?_⟩
  · intro hA
    have : IsGalois A := hA
    apply (isGalois_iff_card_aut_eq_card_fiber (fiber y) B).mpr
    let E := coverTransportOfAutEquiv (fiber x) (fiber y) e
    calc
      Nat.card (Aut B) = Nat.card (Aut A) :=
        (Nat.card_congr (E.fullyFaithfulFunctor.autMulEquivOfFullyFaithful A).toEquiv).symm
      _ = Nat.card ((fiber x).obj A) :=
        (isGalois_iff_card_aut_eq_card_fiber (fiber x) A).mp hA
      _ = Nat.card ((fiber y).obj B) := Nat.card_congr f
  · intro g
    exact pointedCoverGroupTransport_inclusion A B x y a b ha hb e f hf hpoint g
  · intro C hC
    exact Nat.card_congr (finiteH1EquivOfFundamentalGroupEquiv a b eB C).toEquiv

end AnabelianGeometry.GeometricFundamentalGroup
