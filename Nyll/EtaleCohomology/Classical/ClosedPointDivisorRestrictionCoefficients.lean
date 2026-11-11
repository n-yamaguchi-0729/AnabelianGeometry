/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorSheaf
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorOpenRestriction
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorIsoRestriction
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorIsoCoefficients
public import Nyll.EtaleCohomology.Classical.EtaleRestriction
public import Nyll.EtaleCohomology.Sites.EtaleRestriction
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.JacobsonSpace

/-!
# Coefficients of the whole divisor sheaf under chart restriction

The existing chart isomorphisms preserve the original coproduct injections.
Their inverses reduce the component-projection identities to the existing
injection-projection identities. Combining these identities with summand
coefficients retains every original coefficient of a divisor-sheaf section.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace EtaleCohomology

private theorem componentProjection_of_injections
    {ι κ : Type u} (X Y : Scheme.{u})
    (F : ι → Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (G : κ → Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})
    [HasColimitsOfShape (Discrete ι) (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
    [HasColimitsOfShape (Discrete κ) (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
    (R : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} ⥤
      Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) [R.Additive]
    (i : κ → ι) (hi : Function.Injective i)
    (E : R.obj (colimit (Discrete.functor F)) ≅ colimit (Discrete.functor G))
    (e : ∀ j, R.obj (F (i j)) ≅ G j)
    (hι : ∀ j, R.map (colimit.ι (Discrete.functor F) ⟨i j⟩) ≫ E.hom =
      (e j).hom ≫ colimit.ι (Discrete.functor G) ⟨j⟩) (j : κ) :
    R.map (sheafCoproductComponentProjection X F (i j)) ≫ (e j).hom =
      E.hom ≫ sheafCoproductComponentProjection Y G j := by
  classical
  apply (cancel_epi E.inv).mp
  apply colimit.hom_ext
  intro k
  obtain ⟨k⟩ := k
  have hk : colimit.ι (Discrete.functor G) ⟨k⟩ ≫ E.inv =
      (e k).inv ≫ R.map (colimit.ι (Discrete.functor F) ⟨i k⟩) := by
    apply (cancel_mono E.hom).mp
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Category.assoc, hι k, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  calc
    _ = (e k).inv ≫
        R.map (colimit.ι (Discrete.functor F) ⟨i k⟩ ≫
          sheafCoproductComponentProjection X F (i j)) ≫ (e j).hom := by
      rw [← Category.assoc, hk]
      simp only [R.map_comp, Category.assoc]
    _ = colimit.ι (Discrete.functor G) ⟨k⟩ ≫
        sheafCoproductComponentProjection Y G j := by
      by_cases h : k = j
      · subst k
        rw [sheafCoproductInjection_comp_componentProjection,
          sheafCoproductInjection_comp_componentProjection,
          R.map_id, Category.id_comp, Iso.inv_hom_id]
      · have hij : i k ≠ i j := fun h' => h (hi h')
        rw [sheafCoproductInjection_comp_componentProjection_of_ne X F hij,
          sheafCoproductInjection_comp_componentProjection_of_ne Y G h,
          R.map_zero, zero_comp, comp_zero]
    _ = _ := by
      rw [Iso.inv_hom_id_assoc]

/-- The original closed-point component projection commutes with the actual
divisor-sheaf transport along a chart isomorphism. -/
theorem closedPointDivisorIsoRestrictionIso_componentProjection
    {U X : Scheme.{u}} (e : U ≅ X) (y : closedPoints U) :
    (etaleRestriction e.hom AddCommGrpCat.{u}).map
        (closedPointDivisorSheafComponentProjection X
          ((e.hom.homeomorph.sets
            e.hom.isClosedEmbedding.preimage_closedPoints.symm).toEquiv y)) ≫
      (closedPointDivisorSummandIsoRestrictionIso e y).hom =
    (closedPointDivisorIsoRestrictionIso e).hom ≫
      closedPointDivisorSheafComponentProjection U y := by
  let : HasColimitsOfShape (Discrete (closedPoints X))
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
    closedPointDivisorSheafHasColimitsOfShape X
  let : HasColimitsOfShape (Discrete (closedPoints U))
      (Sheaf U.smallEtaleTopology AddCommGrpCat.{u}) :=
    closedPointDivisorSheafHasColimitsOfShape U
  let t := (e.hom.homeomorph.sets
    e.hom.isClosedEmbedding.preimage_closedPoints.symm).toEquiv
  exact componentProjection_of_injections X U
    (closedPointDivisorSummand X) (closedPointDivisorSummand U)
    (etaleRestriction e.hom AddCommGrpCat.{u}) t t.injective
    (closedPointDivisorIsoRestrictionIso e)
    (closedPointDivisorSummandIsoRestrictionIso e)
    (closedPointDivisorIsoRestrictionIso_injection e) y

/-- The original component projection at a point of an open commutes with
the actual open-restriction isomorphism of divisor sheaves. -/
theorem closedPointDivisorOpenRestrictionIso_componentProjection
    {X : Scheme.{u}} [JacobsonSpace X] (U : X.Opens) (y : closedPoints (U : Scheme)) :
    (etaleRestriction U.ι AddCommGrpCat.{u}).map
        (closedPointDivisorSheafComponentProjection X ((closedPointsOpenEquiv U) y).1) ≫
      (closedPointDivisorSummandOpenRestrictionIso U
        ((closedPointsOpenEquiv U) y).1 ((closedPointsOpenEquiv U) y).2).hom =
    (closedPointDivisorOpenRestrictionIso U).hom ≫
      closedPointDivisorSheafComponentProjection (U : Scheme) y := by
  let : HasColimitsOfShape (Discrete (closedPoints X))
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
    closedPointDivisorSheafHasColimitsOfShape X
  let : HasColimitsOfShape (Discrete (closedPoints (U : Scheme)))
      (Sheaf (U : Scheme).smallEtaleTopology AddCommGrpCat.{u}) :=
    closedPointDivisorSheafHasColimitsOfShape (U : Scheme)
  let t := closedPointsOpenEquiv U
  have ht : Function.Injective (fun y => (t y).1) := by
    intro a b h
    exact t.injective (Subtype.ext h)
  exact componentProjection_of_injections X (U : Scheme)
    (closedPointDivisorSummand X) (closedPointDivisorSummand (U : Scheme))
    (etaleRestriction U.ι AddCommGrpCat.{u}) (fun y => (t y).1) ht
    (closedPointDivisorOpenRestrictionIso U)
    (fun y => closedPointDivisorSummandOpenRestrictionIso U (t y).1 (t y).2)
    (closedPointDivisorOpenRestrictionIso_injection U) y

/-- The whole-divisor chart isomorphism preserves the coefficient obtained
from the original projection to a closed-point summand. -/
theorem closedPointDivisorIsoRestrictionIso_coefficient
    {U X : Scheme.{u}} (e : U ≅ X) (y : closedPoints U) (V : U.Etale) :
    let x : closedPoints X := (e.hom.homeomorph.sets
      e.hom.isClosedEmbedding.preimage_closedPoints.symm).toEquiv y
    ∀ (s : (closedPointDivisorSheaf X).obj.obj (op ((etalePostcompose e.hom).obj V)))
      (z : closedPointResidueFiber U y V),
      closedPointDivisorSummandSectionsAddEquiv U y V
        ((closedPointDivisorSheafComponentProjection U y).hom.app (op V)
          ((closedPointDivisorIsoRestrictionIso e).hom.hom.app (op V) s)) z =
      closedPointDivisorSummandSectionsAddEquiv X x ((etalePostcompose e.hom).obj V)
        ((closedPointDivisorSheafComponentProjection X x).hom.app
          (op ((etalePostcompose e.hom).obj V)) s)
        ⟨z.1, by
          change e.hom (V.hom z.1) = e.hom y.1
          exact congrArg e.hom z.2⟩ := by
  intro x s z
  have h := ConcreteCategory.congr_hom
    (congrArg (fun p => p.hom.app (op V))
      (closedPointDivisorIsoRestrictionIso_componentProjection e y)) s
  change (closedPointDivisorSummandIsoRestrictionIso e y).hom.hom.app (op V)
      ((closedPointDivisorSheafComponentProjection X x).hom.app
        (op ((etalePostcompose e.hom).obj V)) s) =
    (closedPointDivisorSheafComponentProjection U y).hom.app (op V)
      ((closedPointDivisorIsoRestrictionIso e).hom.hom.app (op V) s) at h
  exact (congrArg (fun t => closedPointDivisorSummandSectionsAddEquiv U y V t z) h.symm).trans
    (closedPointDivisorSummandIsoRestrictionIso_coefficient e y V _ z)

/-- The whole-divisor open restriction preserves every original integer
coefficient, with the actual open inclusion on its residue-fiber point. -/
theorem closedPointDivisorOpenRestrictionIso_coefficient
    {X : Scheme.{u}} [JacobsonSpace X] (U : X.Opens)
    (y : closedPoints (U : Scheme)) (V : (U : Scheme).Etale)
    (s : (closedPointDivisorSheaf X).obj.obj (op ((etalePostcompose U.ι).obj V)))
    (z : closedPointResidueFiber (U : Scheme) y V) :
    closedPointDivisorSummandSectionsAddEquiv (U : Scheme) y V
      ((closedPointDivisorSheafComponentProjection (U : Scheme) y).hom.app (op V)
        ((closedPointDivisorOpenRestrictionIso U).hom.hom.app (op V) s)) z =
    closedPointDivisorSummandSectionsAddEquiv X ((closedPointsOpenEquiv U) y).1
      ((etalePostcompose U.ι).obj V)
      ((closedPointDivisorSheafComponentProjection X ((closedPointsOpenEquiv U) y).1).hom.app
        (op ((etalePostcompose U.ι).obj V)) s)
      ⟨z.1, congrArg Subtype.val z.2⟩ := by
  let t := closedPointsOpenEquiv U
  have h := ConcreteCategory.congr_hom
    (congrArg (fun p => p.hom.app (op V))
      (closedPointDivisorOpenRestrictionIso_componentProjection U y)) s
  change (closedPointDivisorSummandOpenRestrictionIso U (t y).1 (t y).2).hom.hom.app (op V)
      ((closedPointDivisorSheafComponentProjection X (t y).1).hom.app
        (op ((etalePostcompose U.ι).obj V)) s) =
    (closedPointDivisorSheafComponentProjection (U : Scheme) y).hom.app (op V)
      ((closedPointDivisorOpenRestrictionIso U).hom.hom.app (op V) s) at h
  exact (congrArg (fun t => closedPointDivisorSummandSectionsAddEquiv
    (U : Scheme) y V t z) h.symm).trans
      (closedPointDivisorSummandOpenRestrictionIso_coefficient U (t y).1 (t y).2 V _ z)

end EtaleCohomology
