/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.AlgebraicPointsPullback

/-!
# Abelian-variety model points over common coefficients

The original group and its integral model are compared through the same
generic fibre. Only points over the same further coefficient algebra are
identified. This does not identify all points over different fields.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
open RelativeGroupLaw_exists_isPullback_comp_eq_mul_eq_of_isPullback_of_comp_eq.DescB

namespace GoodReductionJacobian.RelativeGroupLaw

variable {R H S : Type} [CommRing R] [CommRing H] [CommRing S]
  [Algebra R S] [Algebra H S]
  {X Y : Scheme} {f : X ⟶ Spec (.of R)} {g : Y ⟶ Spec (.of H)}
  (G : RelativeGroupLaw R f) (hc : G.IsCommutative)
  (G₀ : RelativeGroupLaw H g) (hc₀ : G₀.IsCommutative)

local notation "c" => Spec.map (CommRingCat.ofHom (algebraMap R S))
local notation "Gc" => G.baseChange c
local notation "hGc" => RelativeGroupLaw.IsCommutative.baseChange c hc

variable (a : pullback f c ⟶ Y)
  (ha : IsPullback a (pullback.snd f c) g
    (Spec.map (CommRingCat.ofHom (algebraMap H S))))
  (hmul : ∀ (T : Scheme) (t : T ⟶ Spec (.of S))
    (P Q : SchemeHomOver t (pullback.snd f c)),
    ((Gc).mul t P Q).val ≫ a =
      (G₀.mul (t ≫ Spec.map (CommRingCat.ofHom (algebraMap H S)))
        ⟨P.val ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, P.property]⟩
        ⟨Q.val ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, Q.property]⟩).val)
  (L : Type) [CommRing L] [Algebra S L]
  [Algebra R L] [IsScalarTower R S L]
  [Algebra H L] [IsScalarTower H S L]

/-- Compare original and model points by the two actual generic-fibre projections. -/
def goodModelPointsEquiv
  (a : pullback f c ⟶ Y)
  (ha : IsPullback a (pullback.snd f c) g
    (Spec.map (CommRingCat.ofHom (algebraMap H S))))
  (hmul : ∀ (T : Scheme) (t : T ⟶ Spec (.of S))
    (P Q : SchemeHomOver t (pullback.snd f c)),
    ((Gc).mul t P Q).val ≫ a =
      (G₀.mul (t ≫ Spec.map (CommRingCat.ofHom (algebraMap H S)))
        ⟨P.val ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, P.property]⟩
        ⟨Q.val ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, Q.property]⟩).val)
  (L : Type) [CommRing L] [Algebra S L]
  [Algebra R L] [IsScalarTower R S L]
  [Algebra H L] [IsScalarTower H S L] :
    G.AlgPoints hc L ≃+ G₀.AlgPoints hc₀ L :=
  (algPointsPullbackEquiv G hc Gc hGc (pullback.fst f c)
    (IsPullback.of_hasPullback f c)
    (fun _ t P Q => baseChange_mul_fst c G t P Q) L).symm.trans
      (algPointsPullbackEquiv G₀ hc₀ Gc hGc a ha hmul L)

/-- Both directions of the common generic-fibre comparison preserve the
original coefficient automorphism, restricted to the appropriate base. -/
theorem goodModelPointsEquiv_equivariant
    (G₀ : RelativeGroupLaw H g) (hc₀ : G₀.IsCommutative)
  (a : pullback f c ⟶ Y)
  (ha : IsPullback a (pullback.snd f c) g
    (Spec.map (CommRingCat.ofHom (algebraMap H S))))
  (hmul : ∀ (T : Scheme) (t : T ⟶ Spec (.of S))
    (P Q : SchemeHomOver t (pullback.snd f c)),
    ((Gc).mul t P Q).val ≫ a =
      (G₀.mul (t ≫ Spec.map (CommRingCat.ofHom (algebraMap H S)))
        ⟨P.val ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, P.property]⟩
        ⟨Q.val ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, Q.property]⟩).val)
  (L : Type) [CommRing L] [Algebra S L]
  [Algebra R L] [IsScalarTower R S L]
  [Algebra H L] [IsScalarTower H S L]
    (σ : L ≃ₐ[S] L) (x : G.AlgPoints hc L) :
    goodModelPointsEquiv G hc G₀ hc₀ a ha hmul L
        (AlgPoints.map (σ.restrictScalars R).toAlgHom x) =
      AlgPoints.map (σ.restrictScalars H).toAlgHom
        (goodModelPointsEquiv G hc G₀ hc₀ a ha hmul L x) := by
  change algPointsPullbackEquiv G₀ hc₀ Gc hGc a ha hmul L
      ((algPointsPullbackEquiv G hc Gc hGc (pullback.fst f c)
        (IsPullback.of_hasPullback f c)
        (fun _ t P Q => baseChange_mul_fst c G t P Q) L).symm
          (AlgPoints.map (σ.restrictScalars R).toAlgHom x)) = _
  rw [algPointsPullbackEquiv_symm_equivariant]
  exact algPointsPullbackEquiv_equivariant G₀ hc₀ Gc hGc a ha hmul L σ _

end GoodReductionJacobian.RelativeGroupLaw
