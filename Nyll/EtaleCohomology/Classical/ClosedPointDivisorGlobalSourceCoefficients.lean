/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorGenericUnitCharts
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorGlobalSections
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorSheaf
public import Nyll.EtaleFundamentalGroups.Cohomology.AffineEtaleClosedPointDivisorSections
public import Mathlib.AlgebraicGeometry.Sites.Small
public import Mathlib.CategoryTheory.Limits.MorphismProperty

/-!
# Original global coefficients in an affine chart source

The finite divisor read on a common affine source evaluates the original
global divisor section at the original closed point. The assertion follows
from the original coproduct projection and residue-fiber naturality.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open IsDedekindDomain

namespace EtaleCohomology.DivisorGenericUnitGlobal

variable (R : Type u) [CommRing R] [IsDedekindDomain R]
  {X : Scheme.{u}} [JacobsonSpace X]
  (U : X.Opens) (e : Spec (CommRingCat.of R) ≅ (U : Scheme))
  (hR : ¬ IsField R)
  (S : Type u) [CommRing S] [IsDedekindDomain S]
  [Algebra R S] [Algebra.Etale R S]
  (q : Spec (CommRingCat.of S) ⟶ X) [Etale q]
  (hq : Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ (e.hom ≫ U.ι) = q)

/-- A source height-one coefficient of the restriction of an original
global divisor section is its coefficient at the original image point. -/
theorem affineChartDivisorSourceSection_global_coefficient :
    let _ : HasColimitsOfShape (Discrete (closedPoints (Spec (CommRingCat.of R))))
        (Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u}) :=
      closedPointDivisorSheafHasColimitsOfShape (Spec (CommRingCat.of R))
    let hT := MorphismProperty.Over.mkIdTerminal
      (show MorphismProperty Scheme.{u} from @Etale) X
    ∀ (w : HeightOneSpectrum S) (x : closedPoints X)
      (_ : q (⟨w.asIdeal, w.isPrime⟩ : PrimeSpectrum S) = x.1)
      (s : (closedPointDivisorSheaf X).obj.obj (op (Scheme.Etale.mk (𝟙 X)))),
      affineEtaleClosedPointDivisorSectionFinsupp (R := R) (S := S) hR
        (affineChartDivisorSourceSection R U e S q hq
          ((closedPointDivisorSheaf X).obj.map (hT.from (Scheme.Etale.mk q)).op s)) w =
        closedPointDivisorGlobalCoefficient X x s := by
  intro hShape hT w x hx s
  let a := affineChartDivisorSourceFiberPoint R U e hR S q hq w
  have hax : a.1 = x := by
    apply Subtype.ext
    exact a.2.2.symm.trans
      ((congrArg q
        (affineChartDivisorSourceFiberPoint_point R U e hR S q hq w)).trans hx)
  let V : X.Etale := Scheme.Etale.mk q
  let T : X.Etale := Scheme.Etale.mk (𝟙 X)
  let m := hT.from V
  let p := closedPointDivisorSheafComponentProjection X a.1
  let z : closedPointResidueFiber X a.1 T :=
    ⟨m.left a.2.1, by
      have hm := congrArg (fun f => f a.2.1)
        (MorphismProperty.Over.w
          (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) m)
      exact hm.trans a.2.2⟩
  have hz : z = ⟨a.1.1, rfl⟩ := Subtype.ext z.2
  have hp := ConcreteCategory.congr_hom (p.hom.naturality m.op) s
  change p.hom.app (op V) ((closedPointDivisorSheaf X).obj.map m.op s) =
    (closedPointDivisorSummand X a.1).obj.map m.op (p.hom.app (op T) s) at hp
  have hn := closedPointDivisorSummandSectionsAddEquiv_naturality
    X a.1 V T m (p.hom.app (op T) s) a.2
  change closedPointDivisorSummandSectionsAddEquiv X a.1 V
      ((closedPointDivisorSummand X a.1).obj.map m.op (p.hom.app (op T) s)) a.2 =
    closedPointDivisorSummandSectionsAddEquiv X a.1 T (p.hom.app (op T) s) z at hn
  change affineEtaleClosedPointDivisorCoefficient (R := R) (S := S) hR w
      (affineChartDivisorSourceSection R U e S q hq
        ((closedPointDivisorSheaf X).obj.map m.op s)) = _
  have hc : affineEtaleClosedPointDivisorCoefficient (R := R) (S := S) hR w
      (affineChartDivisorSourceSection R U e S q hq
        ((closedPointDivisorSheaf X).obj.map m.op s)) =
      (closedPointDivisorSummandSectionsAddEquiv X a.1 V
        (p.hom.app (op V) ((closedPointDivisorSheaf X).obj.map m.op s)) a.2).down :=
    affineChartDivisorSourceSection_coefficient R U e hR S q hq w
      ((closedPointDivisorSheaf X).obj.map m.op s)
  have hp' := congrArg
    (fun t : (closedPointDivisorSummand X a.1).obj.obj (op V) =>
      (closedPointDivisorSummandSectionsAddEquiv X a.1 V t a.2).down) hp
  have hn' := congrArg ULift.down hn
  have hz' := congrArg
    (fun y : closedPointResidueFiber X a.1 T =>
      (closedPointDivisorSummandSectionsAddEquiv X a.1 T
        (p.hom.app (op T) s) y).down) hz
  have ht : (closedPointDivisorSummandSectionsAddEquiv X a.1 T
      (p.hom.app (op T) s) ⟨a.1.1, rfl⟩).down =
      closedPointDivisorGlobalCoefficient X a.1 s := rfl
  exact hc.trans (hp'.trans (hn'.trans (hz'.trans (ht.trans
    (congrArg (fun y => closedPointDivisorGlobalCoefficient X y s) hax)))))

end EtaleCohomology.DivisorGenericUnitGlobal
