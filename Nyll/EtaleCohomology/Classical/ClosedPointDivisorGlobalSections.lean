/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorSheaf
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Data.Finsupp.Ext
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Global sections of the actual closed-point divisor coproduct

On a quasi-compact scheme, the existing finite-support theorem for sections
of a sheaf coproduct identifies the actual closed-point divisor sections
with finitely supported integer coefficients. At the identity étale object,
each residue fiber is a singleton. No affine, regular, dimension, properness,
or characteristic hypothesis is needed.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace EtaleCohomology

variable (X : Scheme.{u})

local notation "U" => Scheme.Etale.mk (𝟙 X)
local notation "D" => closedPointDivisorSheaf X

/-- A global section of one actual residue-field summand is an integer. -/
def closedPointDivisorSummandGlobalSectionsAddEquiv (x : closedPoints X) :
    (closedPointDivisorSummand X x).obj.obj (op U) ≃+ ℤ := by
  let y : closedPointResidueFiber X x U := ⟨x.1, rfl⟩
  let e : (closedPointResidueFiber X x U → ULift.{u} ℤ) ≃+ ℤ :=
    { toFun := fun f => (f y).down
      invFun := fun n _ => ULift.up n
      left_inv := by
        intro f
        funext z
        have hz : z = y := by
          apply Subtype.ext
          exact z.2
        subst z
        rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  exact (closedPointDivisorSummandSectionsAddEquiv X x U).trans e

/-- The coefficient at a closed point is the actual coproduct projection. -/
def closedPointDivisorGlobalCoefficient (x : closedPoints X) :
    (D).obj.obj (op U) →+ ℤ :=
  (closedPointDivisorSummandGlobalSectionsAddEquiv X x).toAddMonoidHom.comp
    ((closedPointDivisorSheafComponentProjection X x).hom.app (op U)).hom

/-- Insert an integer into the global sections of its actual closed-point summand. -/
def closedPointDivisorGlobalInjection (x : closedPoints X) :
    ℤ →+ (D).obj.obj (op U) :=
  ((closedPointDivisorSheafInjection X x).hom.app (op U)).hom.comp
    (closedPointDivisorSummandGlobalSectionsAddEquiv X x).symm.toAddMonoidHom

private theorem closedPointDivisorGlobalCoefficient_injection
    [DecidableEq (closedPoints X)]
    (x y : closedPoints X) (n : ℤ) :
    closedPointDivisorGlobalCoefficient X y
      (closedPointDivisorGlobalInjection X x n) = if x = y then n else 0 := by
  classical
  by_cases h : x = y
  · subst y
    change closedPointDivisorSummandGlobalSectionsAddEquiv X x
      (((closedPointDivisorSheafComponentProjection X x).hom.app (op U)).hom
        (((closedPointDivisorSheafInjection X x).hom.app (op U)).hom
          ((closedPointDivisorSummandGlobalSectionsAddEquiv X x).symm n))) = _
    rw [closedPointDivisorSheafComponentProjection_app_injection,
      AddEquiv.apply_symm_apply, ite_eq_left rfl]
  · change closedPointDivisorSummandGlobalSectionsAddEquiv X y
      (((closedPointDivisorSheafComponentProjection X y).hom.app (op U)).hom
        (((closedPointDivisorSheafInjection X x).hom.app (op U)).hom
          ((closedPointDivisorSummandGlobalSectionsAddEquiv X x).symm n))) = _
    rw [closedPointDivisorSheafComponentProjection_app_injection_of_ne h,
      map_zero, ite_eq_right h]

/-- A finite closed-point divisor gives a section by summing the original
coproduct injections, with the prescribed integer in each residue summand. -/
def closedPointDivisorSectionOfFinsupp :
    (closedPoints X →₀ ℤ) →+ (D).obj.obj (op U) :=
  Finsupp.liftAddHom (closedPointDivisorGlobalInjection X)

/-- A single-point divisor is the corresponding actual summand injection. -/
theorem closedPointDivisorSectionOfFinsupp_single (x : closedPoints X) (n : ℤ) :
    closedPointDivisorSectionOfFinsupp X (Finsupp.single x n) =
      ((closedPointDivisorSheafInjection X x).hom.app (op U)).hom
        ((closedPointDivisorSummandGlobalSectionsAddEquiv X x).symm n) :=
  Finsupp.liftAddHom_apply_single (closedPointDivisorGlobalInjection X) x n

/-- Component projection recovers the original finitely supported coefficient. -/
theorem closedPointDivisorSectionOfFinsupp_coefficient
    (d : closedPoints X →₀ ℤ) (x : closedPoints X) :
    closedPointDivisorGlobalCoefficient X x
      (closedPointDivisorSectionOfFinsupp X d) = d x := by
  classical
  have h : (closedPointDivisorGlobalCoefficient X x).comp
      (closedPointDivisorSectionOfFinsupp X) = Finsupp.applyAddHom x := by
    apply Finsupp.addHom_ext
    intro y n
    change closedPointDivisorGlobalCoefficient X x
      (closedPointDivisorSectionOfFinsupp X (Finsupp.single y n)) = _
    rw [closedPointDivisorSectionOfFinsupp_single]
    change closedPointDivisorGlobalCoefficient X x
      (closedPointDivisorGlobalInjection X y n) = (Finsupp.single y n) x
    rw [closedPointDivisorGlobalCoefficient_injection, Finsupp.single_apply]
  exact DFunLike.congr_fun h d

/-- On a quasi-compact scheme, finite closed-point divisors give exactly all global sections. -/
theorem closedPointDivisorSectionOfFinsupp_bijective [CompactSpace X] :
    Function.Bijective (closedPointDivisorSectionOfFinsupp X) := by
  classical
  constructor
  · intro d e h
    apply Finsupp.ext
    intro x
    have hc := congrArg (closedPointDivisorGlobalCoefficient X x) h
    simpa only [closedPointDivisorSectionOfFinsupp_coefficient] using hc
  · intro s
    let hShape : HasColimitsOfShape (Discrete (closedPoints X))
        (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
      closedPointDivisorSheafHasColimitsOfShape X
    have : QuasiCompact (terminal.from (U).left) :=
      (AlgebraicGeometry.compactSpace_iff_quasiCompact X).mp inferInstance
    obtain ⟨T, hT⟩ := closedPointDivisorSheaf_finiteSupport_of_quasiCompact X U s
    refine ⟨∑ x ∈ T, Finsupp.single x (closedPointDivisorGlobalCoefficient X x s), ?_⟩
    rw [map_sum]
    calc
      ∑ x ∈ T, closedPointDivisorSectionOfFinsupp X
          (Finsupp.single x (closedPointDivisorGlobalCoefficient X x s)) =
        ∑ x ∈ T,
          ((closedPointDivisorSheafInjection X x).hom.app (op U)).hom
            (((closedPointDivisorSheafComponentProjection X x).hom.app (op U)).hom s) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [closedPointDivisorSectionOfFinsupp_single]
        change ((closedPointDivisorSheafInjection X x).hom.app (op U)).hom
          ((closedPointDivisorSummandGlobalSectionsAddEquiv X x).symm
            (closedPointDivisorSummandGlobalSectionsAddEquiv X x
              (((closedPointDivisorSheafComponentProjection X x).hom.app (op U)).hom s))) = _
        rw [AddEquiv.symm_apply_apply]
      _ = s := hT.symm

/-- Sections over the identity étale object are exactly the finite
closed-point divisors on a quasi-compact scheme. -/
def closedPointDivisorSectionsFinsuppAddEquiv [CompactSpace X] :
    (D).obj.obj (op U) ≃+ (closedPoints X →₀ ℤ) :=
  (AddEquiv.ofBijective (closedPointDivisorSectionOfFinsupp X)
    (closedPointDivisorSectionOfFinsupp_bijective X)).symm

/-- The finite-support identification is evaluated by the actual component
projection, not by a separately supplied coordinate map. -/
theorem closedPointDivisorSectionsFinsuppAddEquiv_apply [CompactSpace X]
    (s : (D).obj.obj (op U)) (x : closedPoints X) :
    closedPointDivisorSectionsFinsuppAddEquiv X s x =
      closedPointDivisorGlobalCoefficient X x s := by
  let e := AddEquiv.ofBijective (closedPointDivisorSectionOfFinsupp X)
    (closedPointDivisorSectionOfFinsupp_bijective X)
  have h := congrArg (closedPointDivisorGlobalCoefficient X x) (e.apply_symm_apply s)
  change closedPointDivisorGlobalCoefficient X x
    (closedPointDivisorSectionOfFinsupp X (e.symm s)) = _ at h
  rw [closedPointDivisorSectionOfFinsupp_coefficient] at h
  exact h

/-- Actual global sections, evaluated at the site's chosen terminal object,
are finitely supported integer coefficients at the original closed points. -/
def closedPointDivisorGlobalSectionsFinsuppAddEquiv [CompactSpace X] :
    (D).obj.obj (op (⊤_ X.Etale)) ≃+ (closedPoints X →₀ ℤ) := by
  let hU : IsTerminal U := MorphismProperty.Over.mkIdTerminal
    (show MorphismProperty Scheme.{u} from @Etale) X
  exact ((D).obj.mapIso (hU.uniqueUpToIso terminalIsTerminal).op).addCommGroupIsoToAddEquiv.trans
    (closedPointDivisorSectionsFinsuppAddEquiv X)

/-- The same finite divisors compute the original derived degree-zero
cohomology of the categorical closed-point divisor coproduct. -/
def closedPointDivisorH0FinsuppAddEquiv [CompactSpace X] :
    Sheaf.H.{u} D 0 ≃+ (closedPoints X →₀ ℤ) :=
  (Sheaf.H.equiv₀ D (MorphismProperty.Over.mkIdTerminal
    (show MorphismProperty Scheme.{u} from @Etale) X)).trans
      (closedPointDivisorSectionsFinsuppAddEquiv X)

end EtaleCohomology
