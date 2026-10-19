/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.EtaleFundamentalGroups.GeometricFiber.EquivariantFiberCoverIso
import Nyll.EtaleFundamentalGroups.GeometricFiber.ConstantFieldInclusionFiberPoint
import Nyll.EtaleFundamentalGroups.GeometricFiber.CanonicalPointedMaps
import Nyll.EtaleFundamentalGroups.GeometricFiber.MatchedFiberCoverGroupTransport
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Matched Constant Point Coefficient Lift -/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.FiniteEtale

namespace AnabelianGeometry.WeightFiltration

theorem exists_coefficientClosure_lift_of_actualPoint
    (E κ : Type) [Field E] [Field κ] [Algebra E κ] [Algebra.IsAlgebraic E κ]
    {Y : Scheme} (c : Y ⟶ Spec (.of E))
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y) :
    ∃ (j : κ →+* Ω)
      (z : Spec (.of Ω) ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ))) c),
      j.comp (algebraMap E κ) = (Spec.preimage (y ≫ c)).hom ∧
      z ≫ pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap E κ))) c =
        Spec.map (CommRingCat.ofHom j) ∧
      z ≫ pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap E κ))) c = y := by
  let a : E →+* Ω := (Spec.preimage (y ≫ c)).hom
  let : Algebra E Ω := a.toAlgebra
  let j : κ →ₐ[E] Ω := IsAlgClosed.lift
  have hj : j.toRingHom.comp (algebraMap E κ) = a := by
    ext x
    exact j.commutes x
  have hpoint : Spec.map (CommRingCat.ofHom j.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap E κ)) = y ≫ c := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hj]
    exact Spec.map_preimage (y ≫ c)
  let z := pullback.lift (Spec.map (CommRingCat.ofHom j.toRingHom)) y hpoint
  exact ⟨j.toRingHom, z, hj, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

theorem exists_coefficientClosure_lift_of_constantFiberPoint
    (k E κ : Type) [Field k] [Field E] [Field κ]
    [Algebra k E] [Algebra E κ] [Algebra.IsAlgebraic E κ]
    [IsFiniteEtale (Spec.map (CommRingCat.ofHom (algebraMap k E)))]
    {X : Scheme} (f : X ⟶ Spec (.of k))
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶ X)
    (w : (fiber xi).obj ((FiniteEtale.pullback f).obj (originalConstantFieldCover k E))) :
    let W := (FiniteEtale.pullback f).obj (originalConstantFieldCover k E)
    let c := pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k E))) f
    ∃ (j : κ →+* Ω)
      (z : Spec (.of Ω) ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ))) c),
      j.comp (algebraMap E κ) =
        (Spec.preimage (actualFiberPointLift xi W w ≫ c)).hom ∧
      z ≫ pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap E κ))) c =
        Spec.map (CommRingCat.ofHom j) ∧
      z ≫ pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap E κ))) c =
        actualFiberPointLift xi W w ∧
      (z ≫ pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap E κ))) c) ≫ W.hom = xi := by
  intro W c
  obtain ⟨j, z, hj, hfst, hsnd⟩ :=
    exists_coefficientClosure_lift_of_actualPoint E κ c (actualFiberPointLift xi W w)
  refine ⟨j, z, hj, hfst, hsnd, ?_⟩
  exact (congrArg (· ≫ W.hom) hsnd).trans (actualFiberPointLift_comp xi W w)

theorem coefficientClosure_lift_retains_cover_point
    {X Y : Scheme} (b : Y ⟶ X)
    {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (x : Spec (.of Ω) ⟶ X) (hx : y ≫ b = x)
    (W : FiniteEtale X) (w : (fiber x).obj W) :
    actualFiberPointLift y ((FiniteEtale.pullback b).obj W)
        ((pointedPullbackFiberEquiv b y x hx W).symm w) ≫ pullback.fst W.hom b =
      actualFiberPointLift x W w := by
  subst x
  let wY := (pointedPullbackFiberEquiv b y (y ≫ b) rfl W).symm w
  have hpoint := pullbackFiberIso_hom_fiberObjEquivHom_left b y W wY
  have hwY : (pullbackFiberIso b y).hom.app W wY = w :=
    (pointedPullbackFiberEquiv b y (y ≫ b) rfl W).apply_symm_apply w
  exact hpoint.symm.trans (congrArg
    (fun v : (fiber (y ≫ b)).obj W => actualFiberPointLift (y ≫ b) W v) hwY)

end AnabelianGeometry.WeightFiltration
