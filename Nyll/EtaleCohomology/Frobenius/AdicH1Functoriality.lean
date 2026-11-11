/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Frobenius.Adic
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteH1PullbackIdentity

/-!
# Functoriality and invariant images of actual adic H¹

The finite-coefficient composition law passes to the original inverse limit
and its rational scalar extension. Commuting scheme squares therefore induce
commuting linear maps. In particular, the image of a pullback is invariant
under any pair of compatible original scheme endomorphisms.

These lemmas concern actual cohomology and actual morphisms; they do not
assume a character comparison or a weight decomposition as additional data.
-/

@[expose] public section

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory Limits EtaleFundamentalGroups.Cohomology

namespace EtaleCohomology.Classical

variable {X Y Z : Scheme.{u}} [ConnectedSpace X] [ConnectedSpace Y] [ConnectedSpace Z]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X)
  (ℓ : ℕ) [Fact ℓ.Prime]

include ξ

/-- Identity pullback on the original integral H¹ inverse limit. -/
@[simp] theorem ellAdicH1Pullback_id : ellAdicPullback (𝟙 X) ℓ 1 = LinearMap.id := by
  apply LinearMap.ext
  intro a
  apply ellAdicCohomology_ext X ℓ 1
  intro n
  exact constantFiniteH1Pullback_id ξ (ellPowerCoefficients ℓ n) (a.val n)

/-- Composition of original integral H¹ pullbacks, with no chosen comparison map. -/
theorem ellAdicH1Pullback_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    ellAdicPullback (f ≫ g) ℓ 1 =
      (ellAdicPullback f ℓ 1).comp (ellAdicPullback g ℓ 1) := by
  apply LinearMap.ext
  intro a
  apply ellAdicCohomology_ext X ℓ 1
  intro n
  exact constantFiniteH1Pullback_comp f g ξ (ellPowerCoefficients ℓ n) (a.val n)

/-- Identity pullback on actual rational H¹. -/
@[simp] theorem rationalEllAdicH1Pullback_id :
    rationalEllAdicPullback (𝟙 X) ℓ 1 = LinearMap.id := by
  change (ellAdicPullback (𝟙 X) ℓ 1).baseChange ℚ_[ℓ] = LinearMap.id
  rw [ellAdicH1Pullback_id ξ ℓ]
  exact LinearMap.baseChange_id

/-- Composition on actual rational H¹ is scalar extension of integral composition. -/
theorem rationalEllAdicH1Pullback_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    rationalEllAdicPullback (f ≫ g) ℓ 1 =
      (rationalEllAdicPullback f ℓ 1).comp (rationalEllAdicPullback g ℓ 1) := by
  change (ellAdicPullback (f ≫ g) ℓ 1).baseChange ℚ_[ℓ] =
    ((ellAdicPullback f ℓ 1).baseChange ℚ_[ℓ]).comp
      ((ellAdicPullback g ℓ 1).baseChange ℚ_[ℓ])
  rw [ellAdicH1Pullback_comp ξ ℓ f g]
  exact LinearMap.baseChange_comp _ _

/-- Any commuting square of original endomorphisms induces the expected H¹ square. -/
theorem rationalEllAdicH1Pullback_square
    (f : X ⟶ Y) (a : X ⟶ X) (b : Y ⟶ Y) (h : a ≫ f = f ≫ b) :
    (rationalEllAdicPullback a ℓ 1).comp (rationalEllAdicPullback f ℓ 1) =
      (rationalEllAdicPullback f ℓ 1).comp (rationalEllAdicPullback b ℓ 1) := by
  rw [← rationalEllAdicH1Pullback_comp ξ ℓ a f, h,
    rationalEllAdicH1Pullback_comp ξ ℓ f b]

/-- A commuting geometric square preserves the image of the original H¹ pullback. -/
theorem rationalEllAdicH1Pullback_range_invariant
    (f : X ⟶ Y) (a : X ⟶ X) (b : Y ⟶ Y) (h : a ≫ f = f ≫ b)
    {x : rationalEllAdicCohomology ℓ X 1}
    (hx : x ∈ LinearMap.range (rationalEllAdicPullback f ℓ 1)) :
    rationalEllAdicPullback a ℓ 1 x ∈ LinearMap.range (rationalEllAdicPullback f ℓ 1) := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨rationalEllAdicPullback b ℓ 1 y, ?_⟩
  exact (LinearMap.congr_fun (rationalEllAdicH1Pullback_square ξ ℓ f a b h) y).symm

end EtaleCohomology.Classical

namespace AlgebraicGeometry.Scheme

variable (k L : Type u) [Field k] [Fintype k] [Field L] [Algebra k L]
  [Algebra.IsAlgebraic k L] {X Y : Scheme.{u}}
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]

local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap k L))
local notation "fX" => (X ↘ Spec (CommRingCat.of k))
local notation "fY" => (Y ↘ Spec (CommRingCat.of k))

/-- Frobenius commutes with the actual morphism after constant base change.
The two original projection equations characterize that morphism, so the lemma
also applies to either conventional presentation of the scheme pullback. -/
theorem constantBaseChangeFrobenius_naturality
    (f : X ⟶ Y) (fL : pullback fX b ⟶ pullback fY b)
    (hfst : fL ≫ pullback.fst fY b = pullback.fst fX b ≫ f)
    (hsnd : fL ≫ pullback.snd fY b = pullback.snd fX b) :
    constantBaseChangeFrobenius k L X ≫ fL =
      fL ≫ constantBaseChangeFrobenius k L Y := by
  apply pullback.hom_ext
  · calc
      _ = pullback.fst fX b ≫ X.finiteFieldFrobenius k ≫ f := by
        rw [Category.assoc, hfst, ← Category.assoc,
          constantBaseChangeFrobenius_fst, Category.assoc]
      _ = pullback.fst fX b ≫ f ≫ Y.finiteFieldFrobenius k := by
        rw [finiteFieldFrobenius_naturality X k Y f]
      _ = _ := by
        rw [Category.assoc, constantBaseChangeFrobenius_fst,
          ← Category.assoc fL, hfst, Category.assoc]
  · rw [Category.assoc, hsnd, constantBaseChangeFrobenius_snd,
      Category.assoc, constantBaseChangeFrobenius_snd, hsnd]

end AlgebraicGeometry.Scheme

namespace EtaleCohomology.Classical

variable (k L : Type u) [Field k] [Fintype k] [Field L] [Algebra k L]
  [Algebra.IsAlgebraic k L] {X Y : Scheme.{u}}
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]

local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap k L))
local notation "fX" => (X ↘ Spec (CommRingCat.of k))
local notation "fY" => (Y ↘ Spec (CommRingCat.of k))

/-- The actual geometric Frobenius commutes with rational H¹ pullback after
constant base change. The original two projection equations supply naturality. -/
theorem rationalEllAdicFrobenius_pullback
    [ConnectedSpace ↥(pullback fX b)] [ConnectedSpace ↥(pullback fY b)]
    (f : X ⟶ Y) (fL : pullback fX b ⟶ pullback fY b)
    (hfst : fL ≫ pullback.fst fY b = pullback.fst fX b ≫ f)
    (hsnd : fL ≫ pullback.snd fY b = pullback.snd fX b)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ pullback fX b)
    (ℓ : ℕ) [Fact ℓ.Prime] :
    (rationalEllAdicFrobenius ℓ k L X 1).comp (rationalEllAdicPullback fL ℓ 1) =
      (rationalEllAdicPullback fL ℓ 1).comp (rationalEllAdicFrobenius ℓ k L Y 1) :=
  rationalEllAdicH1Pullback_square ξ ℓ fL
    (Scheme.constantBaseChangeFrobenius k L X) (Scheme.constantBaseChangeFrobenius k L Y)
    (Scheme.constantBaseChangeFrobenius_naturality k L f fL hfst hsnd)

end EtaleCohomology.Classical
