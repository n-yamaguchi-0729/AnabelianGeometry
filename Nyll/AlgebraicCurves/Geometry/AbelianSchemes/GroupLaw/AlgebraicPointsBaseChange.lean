/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.BaseChange
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.AlgebraicPoints

/-!
# Algebraic points of a base-changed group

The existing pullback point equivalence is additive whenever the given group
law agrees with the base-changed law. Its forward map is the original pullback
projection, rather than a newly chosen point comparison.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

namespace GoodReductionJacobian.RelativeGroupLaw

private theorem mul_val_congr_base
    {R : Type} [CommRing R] {A T : Scheme}
    {f : A ⟶ Spec (.of R)} (G : RelativeGroupLaw R f)
    {t t' : T ⟶ Spec (.of R)} (h : t = t') (x y : SchemeHomOver t f) :
    (G.mul t x y).val =
      (G.mul t' ⟨x.val, x.property.trans h⟩ ⟨y.val, y.property.trans h⟩).val := by
  subst t'
  rfl

variable {R K : Type} [CommRing R] [CommRing K] [Algebra R K]
  {A : Scheme} {f : A ⟶ Spec (.of R)}
  (G : RelativeGroupLaw R f) (hc : G.IsCommutative)
  (H : RelativeGroupLaw K
    (baseChangeStr (Spec.map (CommRingCat.ofHom (algebraMap R K))) f))
  (hH : H.IsCommutative)
  (hmul : ∀ {T : Scheme} (t : T ⟶ Spec (.of K)) (x y : SchemeHomOver t
      (baseChangeStr (Spec.map (CommRingCat.ofHom (algebraMap R K))) f)),
    H.mul t x y = (G.baseChange (Spec.map (CommRingCat.ofHom (algebraMap R K)))).mul t x y)

private def baseChangeAlgPointsEquiv : H.AlgPoints hH K ≃ G.AlgPoints hc K := by
  let ι := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let s := Spec.map (CommRingCat.ofHom (algebraMap K K))
  have hs : s ≫ ι = ι := by
    simp only [s, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  let normalize : SchemeHomOver (s ≫ ι) f ≃ SchemeHomOver ι f :=
    Equiv.subtypeEquivRight fun x => by rw [hs]
  exact
    (AlgPoints.equivPoint (L := H) (hc := hH) (T := K)).trans
      ((baseChangePointEquiv ι s).trans
        (normalize.trans (AlgPoints.equivPoint (L := G) (hc := hc) (T := K)).symm))

private theorem baseChangeAlgPointsEquiv_point (x : H.AlgPoints hH K) :
    (AlgPoints.toPoint (L := G) (hc := hc) (T := K)
      (baseChangeAlgPointsEquiv G hc H hH x)).val =
    (AlgPoints.toPoint (L := H) (hc := hH) (T := K) x).val ≫
      pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))) := rfl

include hmul in
private theorem baseChangeAlgPointsEquiv_add (x y : H.AlgPoints hH K) :
    baseChangeAlgPointsEquiv G hc H hH (x + y) =
      baseChangeAlgPointsEquiv G hc H hH x + baseChangeAlgPointsEquiv G hc H hH y := by
  let ι := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let s := Spec.map (CommRingCat.ofHom (algebraMap K K))
  have hs : s ≫ ι = ι := by
    simp only [s, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  let normalize : SchemeHomOver (s ≫ ι) f ≃ SchemeHomOver ι f :=
    Equiv.subtypeEquivRight fun x => by rw [hs]
  let E := baseChangeAlgPointsEquiv G hc H hH
  let px := AlgPoints.toPoint (L := H) (hc := hH) (T := K) x
  let py := AlgPoints.toPoint (L := H) (hc := hH) (T := K) y
  have hx : normalize (baseChangePointToBase ι px) =
      AlgPoints.toPoint (L := G) (hc := hc) (T := K) (E x) :=
    Subtype.ext (baseChangeAlgPointsEquiv_point G hc H hH x).symm
  have hy : normalize (baseChangePointToBase ι py) =
      AlgPoints.toPoint (L := G) (hc := hc) (T := K) (E y) :=
    Subtype.ext (baseChangeAlgPointsEquiv_point G hc H hH y).symm
  have hm : (baseChangePointToBase ι (H.mul s px py)).val =
      (G.mul ι (normalize (baseChangePointToBase ι px))
        (normalize (baseChangePointToBase ι py))).val :=
    (congrArg (fun z => (baseChangePointToBase ι z).val) (hmul s px py)).trans
      ((congrArg Subtype.val (baseChangePointToBase_mul ι G s px py)).trans
        (mul_val_congr_base G hs _ _))
  apply AlgPoints.toPoint_injective (L := G) (hc := hc) (T := K)
  apply Subtype.ext
  calc
    (AlgPoints.toPoint (L := G) (hc := hc) (T := K) (E (x + y))).val =
        (AlgPoints.toPoint (L := H) (hc := hH) (T := K) (x + y)).val ≫
          pullback.fst f ι := baseChangeAlgPointsEquiv_point G hc H hH (x + y)
    _ = (baseChangePointToBase ι (H.mul s px py)).val := rfl
    _ = (G.mul ι (normalize (baseChangePointToBase ι px))
        (normalize (baseChangePointToBase ι py))).val := hm
    _ = (AlgPoints.toPoint (L := G) (hc := hc) (T := K) (E x + E y)).val := by
      rw [hx, hy]
      rfl

/-- The actual pullback projection identifies algebraic points additively,
using the supplied equality with the base-changed group law. -/
def algPointsBaseChangeEquiv : H.AlgPoints hH K ≃+ G.AlgPoints hc K :=
  { baseChangeAlgPointsEquiv G hc H hH with
    map_add' := baseChangeAlgPointsEquiv_add G hc H hH hmul }

/-- The comparison uses the literal projection to the original group scheme. -/
theorem algPointsBaseChangeEquiv_toPoint (x : H.AlgPoints hH K) :
    (AlgPoints.toPoint (L := G) (hc := hc) (T := K)
      (algPointsBaseChangeEquiv G hc H hH hmul x)).val =
      (AlgPoints.toPoint (L := H) (hc := hH) (T := K) x).val ≫
        pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
  baseChangeAlgPointsEquiv_point G hc H hH x

end GoodReductionJacobian.RelativeGroupLaw
