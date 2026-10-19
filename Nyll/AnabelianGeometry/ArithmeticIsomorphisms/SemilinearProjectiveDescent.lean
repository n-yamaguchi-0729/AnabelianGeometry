/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.ProjectiveLine.SchemeRigidity
import Nyll.AnabelianGeometry.ProjectiveLine.SemilinearConfigurationRigidity
import Nyll.AnabelianGeometry.WeightFiltration.SemilinearBoundaryCrossRatio
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver

/-! # From semilinear place actions to actual scheme equivariance

The function-field action is contravariant: the given place action is the
point action of the inverse scheme map. The comparison is established using
the actual rational sections. Matching three boundary labels then makes the
coordinate isomorphism equivariant as a scheme map, including its sheaf map.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.ProjSpace NeronModelInfra
open AnabelianGeometry.ProjectiveLine AnabelianGeometry.WeightFiltration

namespace AnabelianGeometry.ArithmeticIsomorphisms

attribute [local instance] MvPolynomial.gradedAlgebra
variable (K : Type) [Field K] [IsAlgClosed K]

/-- The semilinear field action gives the action of the inverse scheme map
on the literal homogeneous-coordinate points. -/
theorem semilinear_inverse_projectiveRationalPoint
    (θ : (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K)) ≅ (Proj
      (MvPolynomial.homogeneousSubmodule (Fin 2) K))) (σ : K ≃+* K) (g : SemilinearAut K
      (RatFunc K))
    (hθ : θ.hom ≫ (π K 1) = (π K 1) ≫ Spec.map (CommRingCat.ofHom σ.toRingHom))
    (hgpoint : ∀ x y : SchemeHomOver (𝟙 (Spec (.of K))) (π K 1),
      y.1 ≫ θ.hom = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x.1 →
        (projectiveLineRatFuncModel K).pointEquivPlace y = g • (projectiveLineRatFuncModel
          K).pointEquivPlace x)
    (p : Projectivization K (K × K)) :
    θ.inv (projectiveRationalPoint p) =
      projectiveRationalPoint (projectivePointSemilinearEquiv g p) := by
  let a : Spec (.of K) ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom σ.toRingHom)
  have : IsIso (CommRingCat.ofHom σ.toRingHom) :=
    inferInstanceAs (IsIso σ.toCommRingCatIso.hom)
  have : IsIso a := inferInstance
  let x : SchemeHomOver (𝟙 (Spec (.of K))) (π K 1) :=
    ⟨rationalPunctureSection p.rep p.rep_nonzero,
      rationalPunctureSection_comp_π p.rep p.rep_nonzero⟩
  have hx : (projectiveLineRatFuncModel K).pointEquivPlace x = projectiveRatFuncPlace p := by
    refine (CurveModel.pointEquivPlace_apply (projectiveLineRatFuncModel K) x).trans ?_
    calc
      (projectiveLineRatFuncModel K).placeOfPoint (pointEquivClosedPoint (π K 1) x) =
          (projectiveLineRatFuncModel K).placeOfPoint ⟨projectiveRationalPoint p,
            isClosed_singleton_rationalPuncturePoint p.rep p.rep_nonzero⟩ := by
        apply congrArg (projectiveLineRatFuncModel K).placeOfPoint
        apply Subtype.ext
        change rationalPunctureSection p.rep p.rep_nonzero (IsLocalRing.closedPoint K) =
          rationalPunctureSection p.rep p.rep_nonzero (coefficientFieldPoint (K := K))
        exact congrArg (rationalPunctureSection p.rep p.rep_nonzero)
          (Subsingleton.elim _ _)
      _ = projectiveRatFuncPlace p :=
        projectiveLineRatFuncModel_placeOfPoint_projectiveRationalPoint K p
  have hθinv : θ.inv ≫ (π K 1) ≫ a = (π K 1) := by
    rw [← hθ, θ.inv_hom_id_assoc]
  let y : SchemeHomOver (𝟙 (Spec (.of K))) (π K 1) :=
    ⟨a ≫ x.1 ≫ θ.inv, by
      apply (cancel_mono a).1
      rw [Category.assoc, Category.assoc, Category.assoc, hθinv, x.2,
        Category.comp_id, Category.id_comp]⟩
  have hyθ : y.1 ≫ θ.hom = a ≫ x.1 := by
    change (a ≫ x.1 ≫ θ.inv) ≫ θ.hom = _
    rw [Category.assoc, Category.assoc, θ.inv_hom_id, Category.comp_id]
  have hy : (projectiveLineRatFuncModel K).pointEquivPlace y = projectiveRatFuncPlace
    (projectivePointSemilinearEquiv g p) :=
    (hgpoint x y hyθ).trans ((congrArg (fun V => g • V) hx).trans
      (projectivePointSemilinearEquiv_place g p).symm)
  have hc : pointEquivClosedPoint (π K 1) y =
      ⟨projectiveRationalPoint (projectivePointSemilinearEquiv g p),
        isClosed_singleton_rationalPuncturePoint _ _⟩ := by
    apply (projectiveLineRatFuncModel K).placeOfPoint_bijective.1
    exact hy.trans
      (projectiveLineRatFuncModel_placeOfPoint_projectiveRationalPoint K _).symm
  have hp := congrArg Subtype.val hc
  change θ.inv (rationalPunctureSection p.rep p.rep_nonzero
    (a (IsLocalRing.closedPoint K))) = _ at hp
  rw [show a (IsLocalRing.closedPoint K) = coefficientFieldPoint (K := K) from
    Subsingleton.elim _ _] at hp
  exact hp

/-- Two actual semilinear scheme actions with the same coefficient action are
intertwined by a matching coordinate isomorphism once their boundary labels
are intertwined. The conclusion is equality of the actual scheme morphisms. -/
theorem pairLinearCoordinateIso_intertwines_of_semilinear_boundary
    (θX θY : (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K)) ≅ (Proj
      (MvPolynomial.homogeneousSubmodule (Fin 2) K))) (σ : K ≃+* K)
    (gX gY : SemilinearAut K (RatFunc K))
    (hX : θX.hom ≫ (π K 1) = (π K 1) ≫ Spec.map (CommRingCat.ofHom σ.toRingHom))
    (hY : θY.hom ≫ (π K 1) = (π K 1) ≫ Spec.map (CommRingCat.ofHom σ.toRingHom))
    (hgX : ∀ x y : SchemeHomOver (𝟙 (Spec (.of K))) (π K 1),
      y.1 ≫ θX.hom = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x.1 →
        (projectiveLineRatFuncModel K).pointEquivPlace y = gX • (projectiveLineRatFuncModel
          K).pointEquivPlace x)
    (hgY : ∀ x y : SchemeHomOver (𝟙 (Spec (.of K))) (π K 1),
      y.1 ≫ θY.hom = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x.1 →
        (projectiveLineRatFuncModel K).pointEquivPlace y = gY • (projectiveLineRatFuncModel
          K).pointEquivPlace x)
    (hgbase : SemilinearAut.baseAut gX = SemilinearAut.baseAut gY)
    {ι : Type} (x y : ι → Projectivization K (K × K)) (hx : Function.Injective x)
    (a b c : ι) (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (r : ι → ι)
    (hxr : ∀ i, gX • projectiveRatFuncPlace (x i) = projectiveRatFuncPlace (x (r i)))
    (hyr : ∀ i, gY • projectiveRatFuncPlace (y i) = projectiveRatFuncPlace (y (r i)))
    (F : (K × K) ≃ₗ[K] (K × K))
    (hF : ∀ i, projectiveLinearEquiv F (x i) = y i) :
    θX.hom ≫ (pairLinearCoordinateIso F).hom =
      (pairLinearCoordinateIso F).hom ≫ θY.hom := by
  let S := projectivePointSemilinearEquiv gX
  let T := projectivePointSemilinearEquiv gY
  have hS (i : ι) : S (x i) = x (r i) := by
    apply projectiveRatFuncPlace_injective
    exact (projectivePointSemilinearEquiv_place gX (x i)).trans (hxr i)
  have hT (i : ι) : T (y i) = y (r i) := by
    apply projectiveRatFuncPlace_injective
    exact (projectivePointSemilinearEquiv_place gY (y i)).trans (hyr i)
  have hcomm := projectiveLinearEquiv_intertwines_of_configuration x y hx a b c hab hca hcb
    S T (SemilinearAut.baseAut gX)
    (crossRatio_projectivePointSemilinearEquiv gX)
    (fun u v w z => (crossRatio_projectivePointSemilinearEquiv gY u v w z).trans
      (congrArg (fun f : K ≃+* K => f (crossRatio u v w z)) hgbase.symm))
    r hS hT F hF
  let α : Spec (.of K) ≅ Spec (.of K) := Scheme.Spec.mapIso σ.toCommRingCatIso.op
  have hInv (θ : (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K)) ≅ (Proj
    (MvPolynomial.homogeneousSubmodule (Fin 2) K)))
      (hθ : θ.hom ≫ π K 1 = π K 1 ≫ α.hom) :
      θ.inv ≫ π K 1 = π K 1 ≫ α.inv := by
    apply (cancel_mono α.hom).1
    calc
      (θ.inv ≫ π K 1) ≫ α.hom = θ.inv ≫ (π K 1 ≫ α.hom) := Category.assoc _ _ _
      _ = θ.inv ≫ (θ.hom ≫ π K 1) := congrArg (θ.inv ≫ ·) hθ.symm
      _ = π K 1 := θ.inv_hom_id_assoc _
      _ = (π K 1 ≫ α.inv) ≫ α.hom := by
        rw [Category.assoc, α.inv_hom_id, Category.comp_id]
  have hXI := hInv θX hX
  have hYI := hInv θY hY
  let I := pairLinearCoordinateIso F
  have hI : I.hom ≫ π K 1 = π K 1 := linearCoordinateIso_hom_comp_π (finCoordinateEquiv F)
  have hleft : (θX.inv ≫ I.hom) ≫ π K 1 = π K 1 ≫ α.inv := by
    rw [Category.assoc, hI, hXI]
  have hright : (I.hom ≫ θY.inv) ≫ π K 1 = π K 1 ≫ α.inv := by
    rw [Category.assoc, hYI, ← Category.assoc, hI]
  have hinverse : θX.inv ≫ I.hom = I.hom ≫ θY.inv := by
    have : IsIso α.inv := inferInstance
    have : LocallyOfFiniteType (π K 1) := inferInstance
    have : LocallyOfFiniteType (π K 1 ≫ α.inv) := locallyOfFiniteType_comp _ _
    have : LocallyOfFiniteType ((θX.inv ≫ I.hom) ≫ π K 1) :=
      hleft.symm ▸ inferInstance
    apply projectiveLine_hom_ext_of_comp_eq K _ _ (hleft.trans hright.symm)
    intro p
    change I.hom (θX.inv (projectiveRationalPoint p)) =
      θY.inv (I.hom (projectiveRationalPoint p))
    rw [semilinear_inverse_projectiveRationalPoint K θX σ gX hX hgX,
      pairLinearCoordinateIso_projectiveRationalPoint,
      pairLinearCoordinateIso_projectiveRationalPoint,
      semilinear_inverse_projectiveRationalPoint K θY σ gY hY hgY]
    exact congrArg projectiveRationalPoint (Equiv.congr_fun hcomm p)
  apply (cancel_mono θY.inv).1
  calc
    (θX.hom ≫ I.hom) ≫ θY.inv = θX.hom ≫ (I.hom ≫ θY.inv) := Category.assoc _ _ _
    _ = θX.hom ≫ (θX.inv ≫ I.hom) := congrArg (θX.hom ≫ ·) hinverse.symm
    _ = I.hom := θX.hom_inv_id_assoc _
    _ = (I.hom ≫ θY.hom) ≫ θY.inv := by
      rw [Category.assoc, θY.hom_inv_id, Category.comp_id]

end AnabelianGeometry.ArithmeticIsomorphisms
