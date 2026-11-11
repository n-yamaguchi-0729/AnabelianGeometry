/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.Kernel
public import Nyll.AlgebraicCurves.Geometry.Picard.DivisionPullback
public import Nyll.AlgebraicCurves.Geometry.Picard.Functor.Functor
public import Nyll.AlgebraicCurves.Geometry.Picard.Representability.RepresentsRelSubPicGroup
public import Mathlib.Algebra.Group.Commute.Defs
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# The torsion cocycle of the actual Picard division cover

Two lifts to the original division pullback give two actual Picard points.
Their quotient is killed by the original multiplication map whenever the
lifts lie above the same parameter. These differences are natural in the
test scheme and satisfy the cocycle identity on triples of lifts.

In particular the two projections of the actual double overlap give a
torsion point without any choice of roots or of a trivialization. This is
the point-valued transition used by the original Poincaré root family.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits
open NeronModelInfra GoodReductionJacobian

namespace AlgebraicGeometry.RelPicard.RepresentsRelSubPic

variable {R : Type u} [CommRing R] {C : Scheme.{u}}
  {c : C ⟶ Spec (.of R)} {ε : SchemeHomOver (𝟙 (Spec (.of R))) c}
  {P : SubPicGroupCondition c ε} {D : RelativePic0Designation R c}
  (h : RepresentsRelSubPic c ε P.toSubPicCondition D)
  {T : Scheme.{u}} {t : T ⟶ Spec (.of R)}
  (a : SchemeHomOver t D.toBase) (n : ℕ)

local notation "s" => h.divisionStructure a n
local notation "b" => h.divisionPoint a n

/-- Pulling back the actual division point preserves its original
power equation over every test scheme. -/
theorem divisionPoint_pullback_pow {W : Scheme.{u}} {w : W ⟶ Spec (.of R)}
    (x : SchemeHomOver w s) :
    let _ := h.relativeGroupLaw.pointGroup w
    (postComp b x) ^ n = postComp a (postComp (h.divisionBaseMap a n) x) := by
  intro pointGroup
  let : Group (SchemeHomOver s D.toBase) := h.relativeGroupLaw.pointGroup s
  let q : SchemeHomOver s D.toBase →* SchemeHomOver w D.toBase :=
    { toFun := fun z => postComp z x
      map_one' := h.relativeGroupLaw.one_natural s w x.1 x.2
      map_mul' := h.relativeGroupLaw.mul_natural s w x.1 x.2 }
  calc
    (postComp b x) ^ n = q (b ^ n) := (map_pow q b n).symm
    _ = q (postComp a (h.divisionBaseMap a n)) :=
      congrArg q (h.divisionPoint_pow a n)
    _ = postComp a (postComp (h.divisionBaseMap a n) x) := by
      apply Subtype.ext
      exact (Category.assoc x.1 (h.divisionProjection a n) a.1).symm

/-- The actual difference of the Picard division points carried by
two lifts, ordered as the second lift divided by the first. -/
def divisionDifference {W : Scheme.{u}} {w : W ⟶ Spec (.of R)}
    (x y : SchemeHomOver w s) : SchemeHomOver w D.toBase :=
  h.relativeGroupLaw.mul w (postComp b y) (h.relativeGroupLaw.inv w (postComp b x))

/-- Two lifts above the same original parameter have a difference
whose nth power is the identity in the original point group. -/
theorem divisionDifference_pow {W : Scheme.{u}} {w : W ⟶ Spec (.of R)}
    (x y : SchemeHomOver w s)
    (hxy : postComp (h.divisionBaseMap a n) x =
      postComp (h.divisionBaseMap a n) y) :
    let _ := h.relativeGroupLaw.pointGroup w
    (h.divisionDifference a n x y) ^ n = 1 := by
  intro pointGroup
  have hcomm : Commute (postComp b y) (postComp b x)⁻¹ :=
    h.relativeGroupLaw_isCommutative w _ _
  change (postComp b y * (postComp b x)⁻¹) ^ n = 1
  rw [hcomm.mul_pow, inv_pow, divisionPoint_pullback_pow,
    divisionPoint_pullback_pow, hxy, mul_inv_cancel]

/-- The same difference is a torsion point for the original
scheme multiplication, with no auxiliary torsion structure. -/
theorem divisionDifference_isTorsion {W : Scheme.{u}} {w : W ⟶ Spec (.of R)}
    (x y : SchemeHomOver w s)
    (hxy : postComp (h.divisionBaseMap a n) x =
      postComp (h.divisionBaseMap a n) y) :
    h.relativeGroupLaw.IsTorsionPoint w n (h.divisionDifference a n x y) := by
  let : Group (SchemeHomOver w D.toBase) := h.relativeGroupLaw.pointGroup w
  let d := h.divisionDifference a n x y
  have hp (j : ℕ) : d ^ j = h.relativeGroupLaw.nsmul w j d := by
    induction j with
    | zero => rfl
    | succ j ih => rw [pow_succ, h.relativeGroupLaw.nsmul_succ, ih]; rfl
  exact (hp n).symm.trans (h.divisionDifference_pow a n x y hxy)

/-- Differences of the actual division points satisfy the original
cocycle identity, in the order appropriate to successive lifts. -/
theorem divisionDifference_cocycle {W : Scheme.{u}} {w : W ⟶ Spec (.of R)}
    (x y z : SchemeHomOver w s) :
    h.relativeGroupLaw.mul w (h.divisionDifference a n y z) (h.divisionDifference a n x y) =
      h.divisionDifference a n x z := by
  let : Group (SchemeHomOver w D.toBase) := h.relativeGroupLaw.pointGroup w
  change (postComp b z * (postComp b y)⁻¹) *
      (postComp b y * (postComp b x)⁻¹) = postComp b z * (postComp b x)⁻¹
  rw [mul_assoc, ← mul_assoc ((postComp b y)⁻¹), inv_mul_cancel, one_mul]

/-- The difference vanishes on the actual diagonal of the cover. -/
theorem divisionDifference_self {W : Scheme.{u}} {w : W ⟶ Spec (.of R)}
    (x : SchemeHomOver w s) :
    h.divisionDifference a n x x = h.relativeGroupLaw.one w :=
  h.relativeGroupLaw.mul_inv_cancel w (postComp b x)

/-- The original point difference commutes with restriction to
any further test scheme. -/
theorem divisionDifference_pullback {W W' : Scheme.{u}}
    {w : W ⟶ Spec (.of R)} {w' : W' ⟶ Spec (.of R)}
    (x y : SchemeHomOver w s) (v : SchemeHomOver w' w) :
    postComp (h.divisionDifference a n x y) v =
      h.divisionDifference a n (postComp x v) (postComp y v) := by
  let : Group (SchemeHomOver w D.toBase) := h.relativeGroupLaw.pointGroup w
  let : Group (SchemeHomOver w' D.toBase) := h.relativeGroupLaw.pointGroup w'
  let q : SchemeHomOver w D.toBase →* SchemeHomOver w' D.toBase :=
    { toFun := fun z => postComp z v
      map_one' := h.relativeGroupLaw.one_natural w w' v.1 v.2
      map_mul' := h.relativeGroupLaw.mul_natural w w' v.1 v.2 }
  have hcomp (z : SchemeHomOver w s) : q (postComp b z) = postComp b (postComp z v) := by
    apply Subtype.ext
    exact (Category.assoc v.1 z.1 b.1).symm
  change q (postComp b y * (postComp b x)⁻¹) =
    postComp b (postComp y v) * (postComp b (postComp x v))⁻¹
  rw [map_mul, map_inv, hcomp, hcomp]

/-- The actual double overlap of the original division cover. -/
abbrev divisionOverlap : Scheme.{u} :=
  pullback (h.divisionProjection a n) (h.divisionProjection a n)

/-- The common structure morphism of the actual double overlap. -/
def divisionOverlapStructure : h.divisionOverlap a n ⟶ Spec (.of R) :=
  pullback.fst (h.divisionProjection a n) (h.divisionProjection a n) ≫ s

/-- The first actual lift on the double overlap. -/
def divisionOverlapFirst : SchemeHomOver (h.divisionOverlapStructure a n) s :=
  ⟨pullback.fst (h.divisionProjection a n) (h.divisionProjection a n), rfl⟩

/-- The second actual lift on the double overlap. -/
def divisionOverlapSecond : SchemeHomOver (h.divisionOverlapStructure a n) s :=
  ⟨pullback.snd (h.divisionProjection a n) (h.divisionProjection a n), by
    change pullback.snd (h.divisionProjection a n) (h.divisionProjection a n) ≫
      (h.divisionProjection a n ≫ t) =
        pullback.fst (h.divisionProjection a n) (h.divisionProjection a n) ≫
          (h.divisionProjection a n ≫ t)
    rw [← Category.assoc, ← pullback.condition, Category.assoc]⟩

/-- The two original overlap lifts lie above the same parameter. -/
theorem divisionOverlap_projection_eq :
    postComp (h.divisionBaseMap a n) (h.divisionOverlapFirst a n) =
      postComp (h.divisionBaseMap a n) (h.divisionOverlapSecond a n) := by
  apply Subtype.ext
  exact pullback.condition

/-- The original overlap determines an actual point of the original
n-torsion subgroup, directly from the two universal division points. -/
theorem divisionOverlapDifference_isTorsion :
    h.relativeGroupLaw.IsTorsionPoint (h.divisionOverlapStructure a n) n
      (h.divisionDifference a n (h.divisionOverlapFirst a n) (h.divisionOverlapSecond a n)) :=
  h.divisionDifference_isTorsion a n _ _ (h.divisionOverlap_projection_eq a n)

end AlgebraicGeometry.RelPicard.RepresentsRelSubPic
