/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorGlobalSections
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorIsoRestriction
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorRestrictionCoefficients
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorSheaf
public import Nyll.EtaleCohomology.Sites.EtaleRestriction
public import Mathlib.AlgebraicGeometry.Sites.Small
public import Mathlib.CategoryTheory.Limits.MorphismProperty

/-!
# Original global divisor coefficients under a scheme isomorphism

The actual restriction and residue-field comparison permute the original
closed-point coefficients. No function-field coordinate or cohomological
comparison is assumed.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace

namespace EtaleCohomology

variable {Y X : Scheme.{u}} (e : Y ≅ X)

/-- The original divisor section map induced by restriction along the
scheme isomorphism and its native residue-field comparison. -/
def closedPointDivisorIsoGlobalSectionsMap :
    (closedPointDivisorSheaf X).obj.obj (op (Scheme.Etale.mk (𝟙 X))) →+
      (closedPointDivisorSheaf Y).obj.obj (op (Scheme.Etale.mk (𝟙 Y))) :=
  ((closedPointDivisorIsoRestrictionIso e).hom.hom.app
    (op (Scheme.Etale.mk (𝟙 Y)))).hom.comp
    ((closedPointDivisorSheaf X).obj.map
      ((MorphismProperty.Over.mkIdTerminal
        (show MorphismProperty Scheme.{u} from @Etale) X).from
        ((etalePostcompose e.hom).obj (Scheme.Etale.mk (𝟙 Y)))).op).hom

/-- Every original coefficient is transported to the corresponding
original closed point, with its integer unchanged. -/
theorem closedPointDivisorIsoGlobalSectionsMap_coefficient
    (s : (closedPointDivisorSheaf X).obj.obj (op (Scheme.Etale.mk (𝟙 X))))
    (y : closedPoints Y) :
    closedPointDivisorGlobalCoefficient Y y (closedPointDivisorIsoGlobalSectionsMap e s) =
      closedPointDivisorGlobalCoefficient X
        ((e.hom.homeomorph.sets
          e.hom.isClosedEmbedding.preimage_closedPoints.symm).toEquiv y) s := by
  let TY : Y.Etale := Scheme.Etale.mk (𝟙 Y)
  let TX : X.Etale := Scheme.Etale.mk (𝟙 X)
  let V := (etalePostcompose e.hom).obj TY
  let m := (MorphismProperty.Over.mkIdTerminal
    (show MorphismProperty Scheme.{u} from @Etale) X).from V
  let x : closedPoints X := (e.hom.homeomorph.sets
    e.hom.isClosedEmbedding.preimage_closedPoints.symm).toEquiv y
  let zY : closedPointResidueFiber Y y TY := ⟨y.1, rfl⟩
  let zX : closedPointResidueFiber X x V := ⟨y.1, rfl⟩
  let p := closedPointDivisorSheafComponentProjection X x
  let zT : closedPointResidueFiber X x TX := ⟨m.left y.1, by
    have hm := congrArg (fun f => f y.1)
      (MorphismProperty.Over.w
        (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) m)
    exact hm.trans zX.2⟩
  have hz : zT = ⟨x.1, rfl⟩ := Subtype.ext zT.2
  have hc := closedPointDivisorIsoRestrictionIso_coefficient e y TY
    ((closedPointDivisorSheaf X).obj.map m.op s) zY
  have hp := ConcreteCategory.congr_hom (p.hom.naturality m.op) s
  change p.hom.app (op V) ((closedPointDivisorSheaf X).obj.map m.op s) =
    (closedPointDivisorSummand X x).obj.map m.op (p.hom.app (op TX) s) at hp
  have hn := closedPointDivisorSummandSectionsAddEquiv_naturality
    X x V TX m (p.hom.app (op TX) s) zX
  change closedPointDivisorSummandSectionsAddEquiv X x V
      ((closedPointDivisorSummand X x).obj.map m.op (p.hom.app (op TX) s)) zX =
    closedPointDivisorSummandSectionsAddEquiv X x TX (p.hom.app (op TX) s) zT at hn
  change (closedPointDivisorSummandSectionsAddEquiv Y y TY
      ((closedPointDivisorSheafComponentProjection Y y).hom.app (op TY)
        ((closedPointDivisorIsoRestrictionIso e).hom.hom.app (op TY)
          ((closedPointDivisorSheaf X).obj.map m.op s))) zY).down =
    (closedPointDivisorSummandSectionsAddEquiv X x TX
      (p.hom.app (op TX) s) ⟨x.1, rfl⟩).down
  rw [hc, hp, hn, hz]

end EtaleCohomology
