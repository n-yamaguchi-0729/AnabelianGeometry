/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GeometricFiber.AbelianUnitMonodromy
public import Nyll.EtaleFundamentalGroups.GeometricFiber.PointedCoverImage
public import Nyll.EtaleFundamentalGroups.GeometricFiber.ProperGroupScheme

public import Nyll.EtaleFundamentalGroups.GeometricFiber.AbelianUnitTorsionFiber
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.AlgebraicPoints
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Nyll.ProCGroups.Abelian.FullTateModule

/-!
# The kernel of actual multiplication monodromy

The stabilizer of the actual unit point is the image of the fundamental group
of the multiplication cover. The actual pointed map of multiplication induces
the corresponding power map on the fundamental group.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale

namespace GoodReductionJacobian.RelativeGroupLaw.UnitMultiplication

variable {K : Type u} [Field K] [IsSepClosed K]
  {A : Scheme.{u}} {f : A ⟶ Spec (.of K)} [IsProper f] [Smooth f]
  (G : RelativeGroupLaw K f) (hc : G.IsCommutative)

/-- The distinguished torsion-fibre unit is the actual lift of the unit section. -/
theorem unit_eq_liftedPoint (n : unitIndices K) :
    unit G hc n =
      (fiberObjEquivHom (G.one (𝟙 (Spec (.of K)))).1 (cover G hc n)).symm
        (Over.homMk (G.one (𝟙 (Spec (.of K)))).1 (G.unit_comp_schemeNsmul (n.1 : ℕ))) := by
  apply (fiberObjEquivHom (G.one (𝟙 (Spec (.of K)))).1 (cover G hc n)).injective
  rw [Equiv.apply_symm_apply]
  apply Over.OverMorphism.ext
  have hz : fiberEquivTorsion G hc n (unit G hc n) = 0 :=
    (fiberEquivTorsion G hc n).apply_symm_apply 0
  have hp :
      (AlgPoints.toPoint (fiberEquivTorsion G hc n (unit G hc n)).1).1 =
        (AlgPoints.toPoint (0 : G.AlgPoints hc K)).1 :=
    congrArg (fun t : ProCGroups.torsionLevel (G.AlgPoints hc K) n.1 =>
      (AlgPoints.toPoint t.1).1) hz
  have hzero : (AlgPoints.toPoint (0 : G.AlgPoints hc K)).1 =
      (G.one (𝟙 (Spec (.of K)))).1 := by
    rw [AlgPoints.toPoint_zero]
    have hs : Spec.map (CommRingCat.ofHom (algebraMap K K)) = 𝟙 (Spec (.of K)) := by
      change Spec.map (CommRingCat.ofHom (RingHom.id K)) = _
      rw [CommRingCat.ofHom_id]
      exact Spec.map_id (CommRingCat.of K)
    rw [hs]
  exact (fiberEquivTorsion_toPoint G hc n (unit G hc n)).symm.trans (hp.trans hzero)

/-- Vanishing at the actual torsion level means being an actual n-th power
in the original fundamental group. -/
theorem monodromy_eq_zero_iff_exists_pow [GeometricallyConnected f]
    (n : unitIndices K) (g : π₁ᵉᵗ((G.one (𝟙 (Spec (.of K)))).1)) :
    monodromy G hc n g = 0 ↔
      ∃ a : π₁ᵉᵗ((G.one (𝟙 (Spec (.of K)))).1), a ^ (n.1 : ℕ) = g := by
  have _ : ConnectedSpace A := GeometricallyConnected.connectedSpace f f.isOpenMap
  let e : Spec (.of K) ⟶ A := (G.one (𝟙 (Spec (.of K)))).1
  have hunit : fiberEquivTorsion G hc n (unit G hc n) = 0 :=
    (fiberEquivTorsion G hc n).apply_symm_apply 0
  have hfix : monodromy G hc n g = 0 ↔ g • unit G hc n = unit G hc n := by
    change fiberEquivTorsion G hc n (g • unit G hc n) = 0 ↔ _
    rw [← hunit]
    exact (fiberEquivTorsion G hc n).injective.eq_iff
  rw [hfix, unit_eq_liftedPoint G hc n]
  change g ∈ MulAction.stabilizer π₁ᵉᵗ(e)
    ((fiberObjEquivHom e (cover G hc n)).symm
      (Over.homMk e (G.unit_comp_schemeNsmul (n.1 : ℕ)))) ↔ _
  rw [← pointedFundamentalGroupHom_range_eq_stabilizer (cover G hc n) e e
    (G.unit_comp_schemeNsmul (n.1 : ℕ))]
  change (∃ a : π₁ᵉᵗ(e), pointedFundamentalGroupHom (G.schemeNsmul (n.1 : ℕ)) e e
    (G.unit_comp_schemeNsmul (n.1 : ℕ)) a = g) ↔ _
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, (G.pointedFundamentalGroupHom_schemeNsmul (n.1 : ℕ) a).symm.trans ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, (G.pointedFundamentalGroupHom_schemeNsmul (n.1 : ℕ) a).trans ha⟩

/-- A character annihilated by an invertible index factors through the
actual multiplication monodromy at that same index, in arbitrary characteristic. -/
theorem character_factors_monodromy [GeometricallyConnected f]
    {H : Type v} [AddCommGroup H] (n : unitIndices K)
    (χ : π₁ᵉᵗ((G.one (𝟙 (Spec (.of K)))).val) →* Multiplicative H)
    (hH : ∀ a : H, (n.val : ℕ) • a = 0) :
    ∃ ψ : ProCGroups.torsionLevel (G.AlgPoints hc K) n.val →+ H,
      ∀ g, ψ (monodromy G hc n g) = (χ g).toAdd := by
  let m : π₁ᵉᵗ((G.one (𝟙 (Spec (.of K)))).val) →*
      Multiplicative (ProCGroups.torsionLevel (G.AlgPoints hc K) n.val) :=
    { toFun := fun g => Multiplicative.ofAdd (monodromy G hc n g)
      map_one' := congrArg Multiplicative.ofAdd (monodromy_one G hc n)
      map_mul' := fun g h =>
        congrArg Multiplicative.ofAdd (monodromy_mul G hc n g h) }
  have hm : Function.Surjective m := by
    intro x
    obtain ⟨g, hg⟩ := monodromy_surjective G hc n x.toAdd
    exact ⟨g, congrArg Multiplicative.ofAdd hg⟩
  have hker : m.ker ≤ χ.ker := by
    intro g hg
    have hz : monodromy G hc n g = 0 :=
      congrArg Multiplicative.toAdd (show m g = 1 from hg)
    obtain ⟨a, rfl⟩ := (monodromy_eq_zero_iff_exists_pow G hc n g).mp hz
    change χ (a ^ (n.val : ℕ)) = 1
    rw [map_pow]
    exact congrArg Multiplicative.ofAdd (hH (χ a).toAdd)
  let ψm := m.liftOfSurjective hm ⟨χ, hker⟩
  let ψ : ProCGroups.torsionLevel (G.AlgPoints hc K) n.val →+ H :=
    { toFun := fun x => (ψm (Multiplicative.ofAdd x)).toAdd
      map_zero' := congrArg Multiplicative.toAdd ψm.map_one
      map_add' := fun x y => congrArg Multiplicative.toAdd
        (ψm.map_mul (Multiplicative.ofAdd x) (Multiplicative.ofAdd y)) }
  refine ⟨ψ, ?_⟩
  intro g
  exact congrArg Multiplicative.toAdd
    (m.liftOfRightInverse_comp_apply (Function.surjInv hm)
      (Function.rightInverse_surjInv hm) ⟨χ, hker⟩ g)

end GoodReductionJacobian.RelativeGroupLaw.UnitMultiplication
