/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AnabelianGeometry.FiniteField.PointCount
public import Nyll.ProCGroups.InverseSystems.CompatibilityAndSurjectivity
public import Mathlib.CategoryTheory.Category.Preorder

/-!
# Compatible actual rational points in finite-type covering diagrams

The inverse system below consists of actual scheme morphisms from `Spec k`.
Its transition maps are the original diagram morphisms. Over a finite field,
quasi-compactness and finite type supply finiteness of each point set. Compactness constructs
a compatible family from mere stagewise nonemptiness; surjectivity of the
transition maps on rational points is neither assumed nor needed.
-/

@[expose] public section

universe uGeom uField₁ uField₂

noncomputable section

open AlgebraicGeometry CategoryTheory NeronModelInfra
open ProCGroups.InverseSystems

namespace AnabelianGeometry.FiniteField

universe u v

variable (k : Type u) [Field k] {I : Type v} [Preorder I]
  (D : I ⥤ Over (Spec (CommRingCat.of k)))

/-- The original scheme transition acts on actual rational points. -/
def rationalPointMap {i j : I} (h : i ≤ j) :
    SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (D.obj i).hom →
      SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (D.obj j).hom :=
  fun x => ⟨x.val ≫ (D.map (homOfLE h)).left, by
    rw [Category.assoc, Over.w]
    exact x.property⟩

/-- The point transition at an identity is the identity. -/
theorem rationalPointMap_id (i : I) : rationalPointMap k D (le_refl i) = id := by
  funext x
  apply Subtype.ext
  change x.val ≫ (D.map (𝟙 i)).left = x.val
  rw [D.map_id]
  exact Category.comp_id x.val

/-- Actual point transitions compose. -/
theorem rationalPointMap_comp {i j l : I} (h : i ≤ j) (h' : j ≤ l) :
    rationalPointMap k D h' ∘ rationalPointMap k D h =
      rationalPointMap k D (h.trans h') := by
  funext x
  apply Subtype.ext
  change (x.val ≫ (D.map (homOfLE h)).left) ≫ (D.map (homOfLE h')).left =
    x.val ≫ (D.map (homOfLE (h.trans h'))).left
  rw [Category.assoc, ← Over.comp_left, ← D.map_comp]
  rfl

/-- Actual rational points of a covering diagram, with reverse-inclusion indexing. -/
def rationalPointSystem : InverseSystem (I := Iᵒᵈ) where
  X i := SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (D.obj (OrderDual.ofDual i)).hom
  topologicalSpace _ := ⊥
  map {i j} h := rationalPointMap k D
    (show OrderDual.ofDual j ≤ OrderDual.ofDual i from h)
  continuous_map _ := continuous_bot
  map_id i := rationalPointMap_id k D (OrderDual.ofDual i)
  map_comp {i j l} h h' := rationalPointMap_comp k D
    (show OrderDual.ofDual l ≤ OrderDual.ofDual j from h')
    (show OrderDual.ofDual j ≤ OrderDual.ofDual i from h)

instance rationalPointSystem_discrete (i : Iᵒᵈ) :
    DiscreteTopology ((rationalPointSystem k D).X i) := ⟨rfl⟩

/-- The compatibility equation uses the original morphisms of the scheme diagram. -/
theorem rationalPointSystem_compatible_iff
    (x : ∀ i : I, SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (D.obj i).hom) :
    (rationalPointSystem k D).Compatible x ↔
      ∀ i j (h : i ≤ j), (x i).val ≫ (D.map (homOfLE h)).left = (x j).val := by
  constructor
  · intro hx i j h
    exact congrArg Subtype.val (hx j i h)
  · intro hx i j h
    exact Subtype.ext (hx j i h)

end AnabelianGeometry.FiniteField

namespace AnabelianGeometry.FiniteField

universe v

variable (k : Type uGeom) [Field k] [Finite k] {I : Type v} [Preorder I]
  (D : I ⥤ Over (Spec (CommRingCat.of k)))
  [∀ i, QuasiCompact (D.obj i).hom] [∀ i, LocallyOfFiniteType (D.obj i).hom]

/-- The stage sets are finite because they are the actual rational points of
quasi-compact finite-type schemes over a finite field. -/
instance rationalPointSystem_finite (i : Iᵒᵈ) :
    Finite ((rationalPointSystem k D).X i) := by
  have : CompactSpace (D.obj (OrderDual.ofDual i)).left :=
    QuasiCompact.compactSpace_of_compactSpace (D.obj (OrderDual.ofDual i)).hom
  exact finite_rationalPoints k (D.obj (OrderDual.ofDual i)).left
    (D.obj (OrderDual.ofDual i)).hom

/-- Stagewise rational points give an actual compatible point in the inverse
tower. Finiteness and compatibility are derived, rather than supplied as data. -/
theorem nonempty_finiteTypeRationalPointTower_iff
    (hdir : Directed (· ≤ ·) (id : Iᵒᵈ → Iᵒᵈ)) :
    Nonempty (rationalPointSystem k D).inverseLimit ↔
      ∀ i : I, Nonempty (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (D.obj i).hom) := by
  constructor
  · rintro ⟨x⟩ i
    exact ⟨x.val i⟩
  · intro h
    have : ∀ i : Iᵒᵈ, Nonempty ((rationalPointSystem k D).X i) := h
    exact (rationalPointSystem k D).nonempty_inverseLimit_of_finite hdir

omit [∀ i, QuasiCompact (D.obj i).hom] [∀ i, LocallyOfFiniteType (D.obj i).hom] in
/-- The existing proper-tower criterion, with the same public statement. -/
theorem nonempty_rationalPointTower_iff [∀ i, IsProper (D.obj i).hom]
    (hdir : Directed (· ≤ ·) (id : Iᵒᵈ → Iᵒᵈ)) :
    Nonempty (rationalPointSystem k D).inverseLimit ↔
      ∀ i : I, Nonempty (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (D.obj i).hom) :=
  nonempty_finiteTypeRationalPointTower_iff k D hdir

end AnabelianGeometry.FiniteField
