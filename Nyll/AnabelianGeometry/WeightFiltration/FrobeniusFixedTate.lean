/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.FrobeniusFixedSchemePoints
import Nyll.AnabelianGeometry.WeightFiltration.TateFiniteSubgroups
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.AlgebraicPoints
import Nyll.ProCGroups.Abelian.FullTateModuleMap
import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Actual Frobenius-fixed point groups and Tate vectors

The fixed coordinates lie in one finite subgroup of actual geometric points.
The existing finite-subgroup Tate theorem then kills the compatible family.
-/

open AlgebraicGeometry CategoryTheory GoodReductionJacobian
open GoodReductionJacobian.RelativeGroupLaw ProCGroups

namespace AnabelianGeometry.WeightFiltration

section General

variable (k Ω : Type) [CommRing k] [CommRing Ω] [IsLocalRing Ω] [Algebra k Ω]
  (X : Scheme) [CompactSpace X] (c : X ⟶ Spec (.of k)) [LocallyOfFiniteType c]
  (G : RelativeGroupLaw k c) (hc : G.IsCommutative)

/-- A coefficient automorphism with finitely many fixed values has a finite
fixed subgroup on the actual algebra-valued points of a finite-type group. -/
theorem finite_fixed_algebraicPoints (σ : Ω ≃ₐ[k] Ω) [Finite {x : Ω // σ x = x}] :
    Finite ((AlgPoints.map (L := G) (hc := hc)
      σ.toAlgHom).eqLocus
        (AddMonoidHom.id (G.AlgPoints hc Ω))) := by
  let F := AlgPoints.map (L := G) (hc := hc) σ.toAlgHom
  let S := F.eqLocus (AddMonoidHom.id (G.AlgPoints hc Ω))
  have := finite_fixed_scheme_points k Ω σ X c
  let send (x : S) :
      {p : NeronModelInfra.SchemeHomOver (Spec.algebraMap k Ω) c //
        Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ p.val = p.val} :=
    ⟨AlgPoints.toPoint x.val, by
      have hx : F x.val = x.val := x.property
      have h := congrArg (fun y : G.AlgPoints hc Ω => (AlgPoints.toPoint y).val) hx
      have hσ : σ.toAlgHom.toRingHom = σ.toRingHom := rfl
      simp only [F, AlgPoints.toPoint_map_coe, hσ] at h
      exact h⟩
  apply Finite.of_injective send
  intro x y h
  apply Subtype.ext
  change AlgPoints.toPoint x.val = AlgPoints.toPoint y.val
  exact congrArg (fun z => z.val) h

/-- A compatible restricted Tate family fixed by such a coefficient action vanishes. -/
theorem restrictedTate_eq_zero_of_fixed
    (σ : Ω ≃ₐ[k] Ω) [Finite {x : Ω // σ x = x}]
    (I : Submonoid ℕ+) (x : RestrictedTateModule (G.AlgPoints hc Ω) I)
    (hx : ∀ n : I, AlgPoints.map (L := G) (hc := hc) σ.toAlgHom
      (RestrictedTateModule.evaluation (G.AlgPoints hc Ω) I n x) =
      RestrictedTateModule.evaluation (G.AlgPoints hc Ω) I n x) : x = 0 := by
  let F := AlgPoints.map (L := G) (hc := hc) σ.toAlgHom
  let S := F.eqLocus (AddMonoidHom.id (G.AlgPoints hc Ω))
  have : Finite S := finite_fixed_algebraicPoints k Ω X c G hc σ
  exact restrictedTate_eq_zero_of_evaluation_mem_finite_subgroup S x hx

end General

variable (k Ω : Type) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
  [Algebra.IsAlgebraic k Ω] (X : Scheme) [CompactSpace X]
  (c : X ⟶ Spec (.of k)) [LocallyOfFiniteType c]
  (G : RelativeGroupLaw k c) (hc : G.IsCommutative)

/-- The actual coefficient Frobenius has a finite fixed point subgroup. -/
theorem finite_frobenius_fixed_algebraicPoints :
    Finite ((AlgPoints.map (L := G) (hc := hc)
      (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω).toAlgHom).eqLocus
        (AddMonoidHom.id (G.AlgPoints hc Ω))) := by
  have := finite_frobenius_fixed_values k Ω
  exact finite_fixed_algebraicPoints k Ω X c G hc
    (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω)

/-- A full Tate vector fixed by actual coefficient Frobenius vanishes. -/
theorem fullTate_eq_zero_of_frobenius_fixed
    (x : FullTateModule (G.AlgPoints hc Ω))
    (hx : FullTateModule.map (AlgPoints.map (L := G) (hc := hc)
      (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω).toAlgHom) x = x) : x = 0 := by
  let F := AlgPoints.map (L := G) (hc := hc)
    (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω).toAlgHom
  let S := F.eqLocus (AddMonoidHom.id (G.AlgPoints hc Ω))
  have : Finite S := finite_frobenius_fixed_algebraicPoints k Ω X c G hc
  apply fullTate_eq_zero_of_evaluation_mem_finite_subgroup S x
  intro n
  change F (FullTateModule.evaluation (G.AlgPoints hc Ω) n x) =
    FullTateModule.evaluation (G.AlgPoints hc Ω) n x
  have h := congrArg (FullTateModule.evaluation (G.AlgPoints hc Ω) n) hx
  rw [FullTateModule.evaluation_map] at h
  exact h

/-- Frobenius-fixed compatible torsion coordinates vanish on any multiplicative
set of indices, including the prime-to-characteristic indices. -/
theorem restrictedTate_eq_zero_of_frobenius_fixed
    (I : Submonoid ℕ+) (x : RestrictedTateModule (G.AlgPoints hc Ω) I)
    (hx : ∀ n : I, AlgPoints.map (L := G) (hc := hc)
      (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω).toAlgHom
        (RestrictedTateModule.evaluation (G.AlgPoints hc Ω) I n x) =
      RestrictedTateModule.evaluation (G.AlgPoints hc Ω) I n x) : x = 0 := by
  let F := AlgPoints.map (L := G) (hc := hc)
    (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω).toAlgHom
  let S := F.eqLocus (AddMonoidHom.id (G.AlgPoints hc Ω))
  have : Finite S := finite_frobenius_fixed_algebraicPoints k Ω X c G hc
  exact restrictedTate_eq_zero_of_evaluation_mem_finite_subgroup S x hx

end AnabelianGeometry.WeightFiltration
