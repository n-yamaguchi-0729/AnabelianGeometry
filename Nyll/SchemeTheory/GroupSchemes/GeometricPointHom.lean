/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Geometric points detect actual morphisms and group homomorphisms

A reduced source and separated target let all algebraically closed
field-valued points detect equality over an arbitrary base. Applying this
to the identity and multiplication diagrams recovers an actual group
morphism from multiplication of its geometric points. The geometric
points retain their structure map to the original base.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.GroupSchemes

variable {S : Scheme.{u}} {X Y : Over S}

/-- Equality on all geometric points detects actual relative morphisms
from a reduced scheme to a separated scheme. -/
theorem hom_ext_geometricPoints [IsReduced X.left] [IsSeparated Y.hom]
    (f g : X ⟶ Y)
    (h : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (a : Spec (CommRingCat.of Ω) ⟶ S) (x : Over.mk a ⟶ X), x ≫ f = x ≫ g) :
    f = g := by
  apply Over.OverMorphism.ext
  apply ext_of_fromSpecResidueField_eq f.left g.left Y.hom Set.univ dense_univ
  · intro x _
    let Ω := AlgebraicClosure (X.left.residueField x)
    let j : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of (X.left.residueField x)) :=
      Spec.map (CommRingCat.ofHom (algebraMap (X.left.residueField x) Ω))
    have : Surjective j := by
      constructor
      intro y
      exact ⟨default, Subsingleton.elim _ _⟩
    let p := X.left.fromSpecResidueField x
    have hp : (p ≫ f.left) ≫ Y.hom = (p ≫ g.left) ≫ Y.hom := by
      rw [Category.assoc, Category.assoc, f.w, g.w]
    apply ext_of_isDominant_of_isSeparated Y.hom hp j
    have he := congrArg Over.Hom.left
      (h Ω (j ≫ p ≫ X.hom)
        (Over.homMk (j ≫ p) (Category.assoc j p X.hom)))
    exact (Category.assoc j p f.left).symm.trans
      (he.trans (Category.assoc j p g.left))
  · exact f.w.trans g.w.symm

variable {K : Type u} [Field K]
  (G H : CommGrp (Over (Spec (CommRingCat.of K))))

/-- A regular map is an actual group homomorphism if it preserves the
products of all geometric field-valued points. The source multiplication
scheme is required to be reduced, as it is for smooth groups over a field. -/
theorem isMonHom_of_geometricPoints [IsReduced (G.X ⊗ G.X).left] [IsSeparated H.X.hom]
    (f : G.X ⟶ H.X)
    (hmul : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (a : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of K))
      (x y : Over.mk a ⟶ G.X), (x * y) ≫ f = (x ≫ f) * (y ≫ f)) :
    IsMonHom f := by
  have hone (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (a : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of K)) :
      (1 : Over.mk a ⟶ G.X) ≫ f = 1 := by
    have h := hmul Ω a 1 1
    rw [one_mul] at h
    exact (mul_left_cancel (show
      ((1 : Over.mk a ⟶ G.X) ≫ f) * 1 =
        ((1 : Over.mk a ⟶ G.X) ≫ f) * ((1 : Over.mk a ⟶ G.X) ≫ f) from
          (mul_one _).trans h)).symm
  have : IsReduced (𝟙_ (Over (Spec (CommRingCat.of K)))).left :=
    inferInstanceAs (IsReduced (Spec (CommRingCat.of K)))
  constructor
  · apply hom_ext_geometricPoints
    intro Ω _ _ a x
    rw [show x = toUnit (Over.mk a) from toUnit_unique _ _]
    simpa only [Hom.one_def, Category.assoc] using hone Ω a
  · apply hom_ext_geometricPoints
    intro Ω _ _ a x
    have h := hmul Ω a (x ≫ fst G.X G.X) (x ≫ snd G.X G.X)
    simp only [Hom.mul_def] at h
    rw [← lift_map (x ≫ fst G.X G.X) (x ≫ snd G.X G.X) f f,
      lift_comp_fst_snd] at h
    simpa only [Category.assoc] using h

/-- The equivalent field-extension formulation retains the actual algebra
map for every algebraically closed extension of the original field. -/
theorem isMonHom_of_algebraicGeometricPoints
    [IsReduced (G.X ⊗ G.X).left] [IsSeparated H.X.hom] (f : G.X ⟶ H.X)
    (hmul : ∀ (Ω : Type u) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]
      (x y : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) ⟶ G.X),
      (x * y) ≫ f = (x ≫ f) * (y ≫ f)) : IsMonHom f := by
  apply isMonHom_of_geometricPoints G H f
  intro Ω _ _ a x y
  let : Algebra K Ω := (Spec.preimage a).hom.toAlgebra
  have ha : Spec.map (CommRingCat.ofHom (algebraMap K Ω)) = a := Spec.map_preimage a
  have h := hmul Ω
  rw [ha] at h
  exact h x y

/-- The same regular map, now bundled as a morphism of the given actual
commutative group schemes. -/
def homOfGeometricPoints [IsReduced (G.X ⊗ G.X).left] [IsSeparated H.X.hom]
    (f : G.X ⟶ H.X)
    (hmul : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (a : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of K))
      (x y : Over.mk a ⟶ G.X), (x * y) ≫ f = (x ≫ f) * (y ≫ f)) : G ⟶ H := by
  have := isMonHom_of_geometricPoints G H f hmul
  exact InducedCategory.homMk (Grp.homMk f)

/-- Bundling retains the original regular morphism exactly. -/
theorem homOfGeometricPoints_hom [IsReduced (G.X ⊗ G.X).left] [IsSeparated H.X.hom]
    (f : G.X ⟶ H.X)
    (hmul : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (a : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of K))
      (x y : Over.mk a ⟶ G.X), (x * y) ≫ f = (x ≫ f) * (y ≫ f)) :
    (homOfGeometricPoints G H f hmul).hom.hom.hom = f := rfl

end AlgebraicGeometry.GroupSchemes
