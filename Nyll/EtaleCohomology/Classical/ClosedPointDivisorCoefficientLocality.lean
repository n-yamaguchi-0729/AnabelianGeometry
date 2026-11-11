/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorGlobalSections
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorSheaf
public import Mathlib.AlgebraicGeometry.Sites.Small
public import Mathlib.CategoryTheory.Limits.MorphismProperty

/-!
# Local detection of an original global divisor coefficient

The coefficient of an original divisor section at a closed point can be
read after restriction to any original étale object containing a point of
that residue fiber. This follows directly from the actual coproduct
projection and its residue-fiber naturality.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

/-- Restricting to a point of the actual residue fiber retains the
coefficient of the original global divisor section. -/
theorem closedPointDivisorGlobalCoefficient_restriction
    (X : Scheme.{u}) (x : closedPoints X) (V : X.Etale)
    (y : closedPointResidueFiber X x V)
    (s : (closedPointDivisorSheaf X).obj.obj (op (Scheme.Etale.mk (𝟙 X)))) :
    let hT := MorphismProperty.Over.mkIdTerminal
      (show MorphismProperty Scheme.{u} from @Etale) X
    (closedPointDivisorSummandSectionsAddEquiv X x V
      ((closedPointDivisorSheafComponentProjection X x).hom.app (op V)
        ((closedPointDivisorSheaf X).obj.map (hT.from V).op s)) y).down =
      closedPointDivisorGlobalCoefficient X x s := by
  intro hT
  let T : X.Etale := Scheme.Etale.mk (𝟙 X)
  let m := hT.from V
  let p := closedPointDivisorSheafComponentProjection X x
  let z : closedPointResidueFiber X x T :=
    ⟨m.left y.1, by
      have hm := congrArg (fun f => f y.1)
        (MorphismProperty.Over.w
          (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) m)
      exact hm.trans y.2⟩
  have hz : z = ⟨x.1, rfl⟩ := Subtype.ext z.2
  have hp := ConcreteCategory.congr_hom (p.hom.naturality m.op) s
  change p.hom.app (op V) ((closedPointDivisorSheaf X).obj.map m.op s) =
    (closedPointDivisorSummand X x).obj.map m.op (p.hom.app (op T) s) at hp
  have hn := closedPointDivisorSummandSectionsAddEquiv_naturality
    X x V T m (p.hom.app (op T) s) y
  change closedPointDivisorSummandSectionsAddEquiv X x V
      ((closedPointDivisorSummand X x).obj.map m.op (p.hom.app (op T) s)) y =
    closedPointDivisorSummandSectionsAddEquiv X x T (p.hom.app (op T) s) z at hn
  change (closedPointDivisorSummandSectionsAddEquiv X x V
    (p.hom.app (op V) ((closedPointDivisorSheaf X).obj.map m.op s)) y).down =
      (closedPointDivisorSummandSectionsAddEquiv X x T
        (p.hom.app (op T) s) ⟨x.1, rfl⟩).down
  rw [hp, hn, hz]

/-- Local equality of original divisor sections implies equality of the
original global coefficient at every point of the residue fiber. -/
theorem closedPointDivisorGlobalCoefficient_eq_of_restriction_eq
    (X : Scheme.{u}) (x : closedPoints X) (V : X.Etale)
    (y : closedPointResidueFiber X x V)
    (s t : (closedPointDivisorSheaf X).obj.obj (op (Scheme.Etale.mk (𝟙 X)))) :
    let hT := MorphismProperty.Over.mkIdTerminal
      (show MorphismProperty Scheme.{u} from @Etale) X
    (closedPointDivisorSheaf X).obj.map (hT.from V).op s =
      (closedPointDivisorSheaf X).obj.map (hT.from V).op t →
        closedPointDivisorGlobalCoefficient X x s =
          closedPointDivisorGlobalCoefficient X x t := by
  intro hT h
  rw [← closedPointDivisorGlobalCoefficient_restriction X x V y s,
    ← closedPointDivisorGlobalCoefficient_restriction X x V y t, h]

end EtaleCohomology
