/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.AlgebraicPointsBaseChange
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.CanonicalModelFactorization

/-!
# Actual points over further coefficients of a group-model pullback

A multiplication-compatible pullback identifies points over every further
coefficient algebra. The forward map is the given projection, and it commutes
with the original coefficient automorphisms.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
open RelativeGroupLaw_exists_isPullback_comp_eq_mul_eq_of_isPullback_of_comp_eq.DescB

namespace GoodReductionJacobian.RelativeGroupLaw

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
  {X Y : Scheme} {f : X ⟶ Spec (.of R)} {g : Y ⟶ Spec (.of S)}
  (G : RelativeGroupLaw R f) (hc : G.IsCommutative)
  (J : RelativeGroupLaw S g) (hJ : J.IsCommutative)
  (π : Y ⟶ X)
  (hπ : IsPullback π g f (Spec.map (CommRingCat.ofHom (algebraMap R S))))
  (hmul : ∀ (T : Scheme) (t : T ⟶ Spec (.of S)) (P Q : SchemeHomOver t g),
    (J.mul t P Q).val ≫ π =
      (G.mul (t ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)))
        ⟨P.val ≫ π, by rw [Category.assoc, hπ.w, ← Category.assoc, P.property]⟩
        ⟨Q.val ≫ π, by rw [Category.assoc, hπ.w, ← Category.assoc, Q.property]⟩).val)
  (L : Type) [CommRing L] [Algebra S L] [Algebra R L] [IsScalarTower R S L]

private theorem coefficient_square :
    Spec.algebraMap S L ≫ Spec.algebraMap R S = Spec.algebraMap R L := by
  change Spec.map (CommRingCat.ofHom (algebraMap S L)) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R S)) = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq R S L]

private def pullbackPointEquiv :
    SchemeHomOver (Spec.algebraMap S L) g ≃ SchemeHomOver (Spec.algebraMap R L) f where
  toFun P := ⟨P.val ≫ π, by
    rw [Category.assoc, hπ.w, ← Category.assoc, P.property, coefficient_square L]⟩
  invFun P := ⟨hπ.lift P.val (Spec.algebraMap S L)
    (P.property.trans (coefficient_square L).symm), hπ.lift_snd _ _ _⟩
  left_inv P := by
    apply Subtype.ext
    apply hπ.hom_ext
    · exact hπ.lift_fst _ _ _
    · exact (hπ.lift_snd _ _ _).trans P.property.symm
  right_inv P := Subtype.ext (hπ.lift_fst _ _ _)

/-- The original model projection is an additive equivalence on points over
any further coefficient algebra. -/
def algPointsPullbackEquiv : J.AlgPoints hJ L ≃+ G.AlgPoints hc L :=
  { (AlgPoints.equivPoint (L := J) (hc := hJ) (T := L)).trans
      ((pullbackPointEquiv π hπ L).trans
        (AlgPoints.equivPoint (L := G) (hc := hc) (T := L)).symm) with
    map_add' := by
      intro x y
      apply AlgPoints.toPoint_injective
      apply Subtype.ext
      change (J.mul (Spec.algebraMap S L) (AlgPoints.toPoint x) (AlgPoints.toPoint y)).val ≫ π = _
      rw [hmul]
      exact mul_val_congr G (coefficient_square L) _ _ _ _ rfl rfl }

/-- The comparison retains the literal scheme projection. -/
theorem algPointsPullbackEquiv_toPoint (x : J.AlgPoints hJ L) :
    (AlgPoints.toPoint (algPointsPullbackEquiv G hc J hJ π hπ hmul L x)).val =
      (AlgPoints.toPoint x).val ≫ π := rfl

/-- The actual coefficient action commutes with the actual model comparison. -/
theorem algPointsPullbackEquiv_equivariant
    (σ : L ≃ₐ[S] L) (x : J.AlgPoints hJ L) :
    algPointsPullbackEquiv G hc J hJ π hπ hmul L (AlgPoints.map σ.toAlgHom x) =
      AlgPoints.map (σ.restrictScalars R).toAlgHom
        (algPointsPullbackEquiv G hc J hJ π hπ hmul L x) := by
  apply AlgPoints.toPoint_injective
  apply Subtype.ext
  rw [algPointsPullbackEquiv_toPoint, AlgPoints.toPoint_map_coe,
    AlgPoints.toPoint_map_coe, algPointsPullbackEquiv_toPoint]
  exact Category.assoc _ _ _

/-- Passing from the original group to the actual pullback also retains
the coefficient action, rather than choosing an unrelated inverse. -/
theorem algPointsPullbackEquiv_symm_equivariant
    (σ : L ≃ₐ[S] L) (x : G.AlgPoints hc L) :
    (algPointsPullbackEquiv G hc J hJ π hπ hmul L).symm
        (AlgPoints.map (σ.restrictScalars R).toAlgHom x) =
      AlgPoints.map σ.toAlgHom
        ((algPointsPullbackEquiv G hc J hJ π hπ hmul L).symm x) := by
  apply (algPointsPullbackEquiv G hc J hJ π hπ hmul L).injective
  rw [AddEquiv.apply_symm_apply,
    algPointsPullbackEquiv_equivariant G hc J hJ π hπ hmul L σ,
    AddEquiv.apply_symm_apply]

end GoodReductionJacobian.RelativeGroupLaw
