/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.CupCechRepresentative
public import Nyll.EtaleCohomology.Classical.FreeModuleCechCup
public import Nyll.EtaleCohomology.Classical.FreeModuleSheafAugmentation
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-!
# The actual native cup cocycle from two local lifts

Two actual local lifts of one into native self-extensions determine a
second lift in the original covering resolution. Its second difference
represents the original Yoneda cup. On an actual triangle `012` it is
the product of the first extension's difference on `12` and the second
extension's difference on `01`, with the original tensor-unit action.

The second lift and its cocycle equation are constructed here. They
are not extra inputs to the cup comparison.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory Abelian
open scoped EtaleCohomology.ModuleTensor

namespace EtaleCohomology

variable (X : Scheme.{u}) (R : Type u) [CommRing R]
  {T : X.Etale} (hT : IsTerminal T) {V : X.Etale} (f : V ⟶ T)

/-- The original triangle boundary is killed by the original map
to the augmentation kernel. -/
theorem moduleCechFirstRelationMap_triangle_zero :
    (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} R)).map
        (freeModuleCechTriangleBoundaryNat R (yoneda.map f)) ≫
      moduleCechFirstRelationMap X.smallEtaleTopology R hT f = 0 := by
  rw [← moduleCechSecondRelationMap_comp X.smallEtaleTopology R hT f,
    Category.assoc, kernel.condition, comp_zero]

/-- The edge difference of an actual local lift is the original
edge boundary of that lift. -/
theorem moduleCechFirstDifference_edge_comp
    {E : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)}
    (i : (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R) ⟶ E)
    (p : E ⟶ (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R))
    (hip : i ≫ p = 0)
    (hE : (ShortComplex.mk i p hip).ShortExact)
    (b : (freeModuleSheafYoneda X.smallEtaleTopology R).obj V ⟶ E)
    (hb : b ≫ p = moduleCechUnitAugmentation X.smallEtaleTopology R hT f) :
    (moduleCechFirstRelationMap X.smallEtaleTopology R hT f ≫
        moduleCechFirstDifference X.smallEtaleTopology R hT f i p hip hE b hb) ≫ i =
      (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} R)).map
        (freeModuleCechEdgeBoundaryNat R (yoneda.map f)) ≫ b := by
  rw [Category.assoc, moduleCechFirstDifference_comp, ← Category.assoc,
    moduleCechFirstRelationMap_comp]

/-- The actual relation lift, using the coefficient difference and
the lift of one at the first endpoint. -/
def moduleCechCupRelationLift
    {E : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)}
    (k : kernel (moduleCechUnitAugmentation X.smallEtaleTopology R hT f) ⟶
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R))
    (b : (freeModuleSheafYoneda X.smallEtaleTopology R).obj V ⟶ E) :
    (freeModuleSheafFunctor X R).obj (cechEdgeFunctor (yoneda.map f)) ⟶ E :=
  freeModuleSheafAction X R
    (moduleCechFirstRelationMap X.smallEtaleTopology R hT f ≫ k)
    ((freeModuleSheafFunctor X R).map (cechEdgeFirst (yoneda.map f)) ≫ b)

/-- The constructed relation lift has the required original
quotient; this follows from the actual counit law. -/
theorem moduleCechCupRelationLift_comp
    {E : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)}
    (q : E ⟶ (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R))
    (k : kernel (moduleCechUnitAugmentation X.smallEtaleTopology R hT f) ⟶
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R))
    (b : (freeModuleSheafYoneda X.smallEtaleTopology R).obj V ⟶ E)
    (hb : b ≫ q = moduleCechUnitAugmentation X.smallEtaleTopology R hT f) :
    moduleCechCupRelationLift X R hT f k b ≫ q =
      moduleCechFirstRelationMap X.smallEtaleTopology R hT f ≫ k := by
  let L := freeModuleSheafFunctor X R
  let a : L.obj (cechEdgeFunctor (yoneda.map f)) ⟶
      𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :=
    moduleCechFirstRelationMap X.smallEtaleTopology R hT f ≫ k
  let b₀ : L.obj (yoneda.obj V) ⟶ E := b
  let q₀ : E ⟶ 𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) := q
  have hb₀ : b₀ ≫ q₀ = freeModuleSheafCounit X R (yoneda.obj V) :=
    hb.trans (freeModuleSheafCounit_eq_moduleCechUnitAugmentation X R hT f).symm
  have he : L.map (cechEdgeFirst (yoneda.map f)) ≫ (b₀ ≫ q₀) =
      freeModuleSheafCounit X R (cechEdgeFunctor (yoneda.map f)) :=
    (congrArg
      (fun z : L.obj (yoneda.obj V) ⟶
          𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) =>
        L.map (cechEdgeFirst (yoneda.map f)) ≫ z) hb₀).trans
      (freeModuleSheafCounit_naturality X R (cechEdgeFirst (yoneda.map f)))
  change freeModuleSheafAction X R a
    (L.map (cechEdgeFirst (yoneda.map f)) ≫ b₀) ≫ q₀ = a
  exact (freeModuleSheafAction_postcomp X R a
    (L.map (cechEdgeFirst (yoneda.map f)) ≫ b₀) q₀).trans
      ((congrArg (freeModuleSheafAction X R a)
        ((Category.assoc _ _ _).trans he)).trans
          (freeModuleSheafAction_counit_right X R a))

section SecondDifference

variable
  {E : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)}
  (j : (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R) ⟶ E)
  (q : E ⟶ (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R))
  (hjq : j ≫ q = 0)
  (hE : (ShortComplex.mk j q hjq).ShortExact)
  (k : kernel (moduleCechUnitAugmentation X.smallEtaleTopology R hT f) ⟶
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R))
  (b : (freeModuleSheafYoneda X.smallEtaleTopology R).obj V ⟶ E)
  (hb : b ≫ q = moduleCechUnitAugmentation X.smallEtaleTopology R hT f)

/-- The second difference of the constructed relation lift in the
original cover resolution. -/
def moduleCechCupSecondDifference :
    kernel (moduleCechFirstRelationMap X.smallEtaleTopology R hT f) ⟶
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)) :=
  moduleCechSecondDifference X.smallEtaleTopology R hT f j q hjq hE k
    (moduleCechCupRelationLift X R hT f k b)
    (moduleCechCupRelationLift_comp X R hT f q k b hb)

/-- On the original triangle object the actual cup cocycle is
`a₁₂ b₀₁`, with the original order and coefficient multiplication. -/
theorem moduleCechCupSecondDifference_triangles :
    moduleCechSecondRelationMap X.smallEtaleTopology R hT f ≫
        moduleCechCupSecondDifference X R hT f j q hjq hE k b hb =
      freeModuleSheafAction X R
        ((freeModuleSheafFunctor X R).map (cechTriangleEdge12 (yoneda.map f)) ≫
          moduleCechFirstRelationMap X.smallEtaleTopology R hT f ≫ k)
        ((freeModuleSheafFunctor X R).map (cechTriangleEdge01 (yoneda.map f)) ≫
          moduleCechFirstRelationMap X.smallEtaleTopology R hT f ≫
            moduleCechFirstDifference X.smallEtaleTopology R hT f j q hjq hE b hb) := by
  have : Mono j := hE.mono_f
  let L := freeModuleSheafFunctor X R
  let r := moduleCechFirstRelationMap X.smallEtaleTopology R hT f
  let kβ := moduleCechFirstDifference X.smallEtaleTopology R hT f j q hjq hE b hb
  let a := r ≫ k
  let a₁₂ := L.map (cechTriangleEdge12 (yoneda.map f)) ≫ a
  have ha : (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} R)).map
      (freeModuleCechTriangleBoundaryNat R (yoneda.map f)) ≫ a = 0 := by
    change _ ≫ (r ≫ k) = 0
    rw [← Category.assoc, moduleCechFirstRelationMap_triangle_zero, zero_comp]
  have hβ : (r ≫ kβ) ≫ j =
      (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} R)).map
        (freeModuleCechEdgeBoundaryNat R (yoneda.map f)) ≫ b :=
    moduleCechFirstDifference_edge_comp X R hT f j q hjq hE b hb
  apply (cancel_mono j).mp
  calc
    _ = (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} R)).map
        (freeModuleCechTriangleBoundaryNat R (yoneda.map f)) ≫
          moduleCechCupRelationLift X R hT f k b :=
      moduleCechSecondDifference_triangles X.smallEtaleTopology R hT f j q hjq hE k
        (moduleCechCupRelationLift X R hT f k b)
        (moduleCechCupRelationLift_comp X R hT f q k b hb)
    _ = freeModuleSheafAction X R a₁₂
        (L.map (cechTriangleEdge01 (yoneda.map f)) ≫
          (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} R)).map
            (freeModuleCechEdgeBoundaryNat R (yoneda.map f)) ≫ b) :=
      freeModuleCechAction_triangle X R (yoneda.map f) a ha b
    _ = freeModuleSheafAction X R a₁₂
        (L.map (cechTriangleEdge01 (yoneda.map f)) ≫ ((r ≫ kβ) ≫ j)) :=
      congrArg (freeModuleSheafAction X R a₁₂)
        (congrArg (fun z => L.map (cechTriangleEdge01 (yoneda.map f)) ≫ z) hβ.symm)
    _ = _ :=
      (congrArg (freeModuleSheafAction X R a₁₂)
        (Category.assoc (L.map (cechTriangleEdge01 (yoneda.map f)))
          (r ≫ kβ) j).symm).trans
        (freeModuleSheafAction_postcomp X R a₁₂
          (L.map (cechTriangleEdge01 (yoneda.map f)) ≫ (r ≫ kβ)) j).symm

end SecondDifference

/-- Two actual local lifts give the original native Yoneda product,
through the explicitly constructed cup cocycle. -/
theorem moduleCechCupSecondDifference_extClass
    (hf : Sieve.generate (Presieve.singleton f) ∈ X.smallEtaleTopology T)
    {E₀ E₁ : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)}
    (i : (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R) ⟶ E₀)
    (p : E₀ ⟶ (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R))
    (hip : i ≫ p = 0)
    (hE₀ : (ShortComplex.mk i p hip).ShortExact)
    (j : (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R) ⟶ E₁)
    (q : E₁ ⟶ (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R))
    (hjq : j ≫ q = 0)
    (hE₁ : (ShortComplex.mk j q hjq).ShortExact)
    (b₀ : (freeModuleSheafYoneda X.smallEtaleTopology R).obj V ⟶ E₀)
    (hb₀ : b₀ ≫ p = moduleCechUnitAugmentation X.smallEtaleTopology R hT f)
    (b₁ : (freeModuleSheafYoneda X.smallEtaleTopology R).obj V ⟶ E₁)
    (hb₁ : b₁ ≫ q = moduleCechUnitAugmentation X.smallEtaleTopology R hT f) :
    hE₀.extClass.comp hE₁.extClass (show 1 + 1 = 2 from rfl) =
      ((moduleCechAugmentationSequence_shortExact X.smallEtaleTopology R hT f hf).extClass.comp
        (moduleCechFirstRelationSequence_shortExact X.smallEtaleTopology R hT f).extClass
          (show 1 + 1 = 2 from rfl)).comp
        (Ext.mk₀ (moduleCechCupSecondDifference X R hT f j q hjq hE₁
          (moduleCechFirstDifference X.smallEtaleTopology R hT f i p hip hE₀ b₀ hb₀)
          b₁ hb₁)) (add_zero 2) :=
  moduleCech_extClass_comp X.smallEtaleTopology R hT f hf i p hip hE₀ j q hjq hE₁ b₀ hb₀
    (moduleCechCupRelationLift X R hT f
      (moduleCechFirstDifference X.smallEtaleTopology R hT f i p hip hE₀ b₀ hb₀) b₁)
    (moduleCechCupRelationLift_comp X R hT f q
      (moduleCechFirstDifference X.smallEtaleTopology R hT f i p hip hE₀ b₀ hb₀) b₁ hb₁)

end EtaleCohomology
