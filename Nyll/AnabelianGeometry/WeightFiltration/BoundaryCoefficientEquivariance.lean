/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.BoundaryInertiaSemilinear
import Nyll.AnabelianGeometry.WeightFiltration.OpenBoundarySemilinear
import Nyll.AnabelianGeometry.WeightFiltration.GenericCoefficientDuality
import Nyll.AlgebraicCurves.Models.ConstantExtension.BaseChangeSemilinearAction

/-!
# Arithmetic coefficient equivariance of the original boundary inertia

The coefficient isomorphisms of the original open curve and compactification
supply boundary preservation and the function-field square. A single fixed
base-point correction gives the arithmetic action on all boundary parameters.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AlgebraicCurve
open AlgebraicGeometry.FiniteEtale AlgebraicGeometry.SmoothProperCurve
open SchemeTheory EtaleFundamentalGroups.Inertia
open ProCGroups.Abelian

namespace AnabelianGeometry.WeightFiltration

variable
    (k K : Type) [Field k] [Field K] [CharZero K] [IsAlgClosed K]
    [Algebra k K] [IsSepClosure k K]
    {C U : Scheme} [CompactSpace U] [QuasiSeparatedSpace U]
    (c : C ⟶ Spec (.of k)) (i : U ⟶ C)


variable
    [IsIntegral (Limits.pullback (specMap k K) (i ≫ c))] [CompactSpace ↑(Limits.pullback (specMap
      k K) (i ≫ c))]
    {F : Type} [Field F] [Algebra K F]
    (M : CurveModel K F)
    (eC : M.C ≅ pullback c (specMap k K))
    (heC : eC.hom ≫ pullback.snd c (specMap k K) = M.toBase)
    (j : (Limits.pullback (specMap k K) (i ≫ c)) ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
    (hproj : j ≫ eC.hom ≫ pullback.fst c (specMap k K) = pullback.snd (specMap k K) (i ≫ c) ≫ i)
    (hbase : j ≫ M.toBase = pullback.fst (specMap k K) (i ≫ c))
    [Algebra F (Limits.pullback (specMap k K) (i ≫ c)).functionField]
    (hfield : algebraMap F (Limits.pullback (specMap k K) (i ≫ c)).functionField =
      (j.functionFieldMap hj).comp M.ffEquiv.toRingHom)
    {Ω : Type} [Field Ω] [Algebra (Limits.pullback (specMap k K) (i ≫ c)).functionField Ω]
      [Algebra F Ω]
    [IsScalarTower F (Limits.pullback (specMap k K) (i ≫ c)).functionField Ω]
    [IsSepClosed Ω] [IsSepClosure (Limits.pullback (specMap k K) (i ≫ c)).functionField Ω]
      [IsSepClosure F Ω]
    [∀ p : M.openBoundaryPlaces j, Algebra p.val.toValuationSubring Ω]
    [∀ p : M.openBoundaryPlaces j, IsScalarTower p.val.toValuationSubring F Ω]
    [Algebra K Ω]
    [∀ p : M.openBoundaryPlaces j, IsScalarTower K p.val.toValuationSubring Ω]
    (Q : ∀ p : M.openBoundaryPlaces j,
      Ideal (normalizationCommAlgCat p.val.toValuationSubring Ω))
    [∀ p, (Q p).IsMaximal]

include eC heC hproj hbase in
/-- Every arithmetic coefficient automorphism acts on the original boundary
by its actual place action and its actual root action, after one fixed
base-point correction shared by all coefficient elements. -/
theorem exists_boundary_coefficient_equivariance :
    let η := Spec.map (CommRingCat.ofHom (algebraMap (Limits.pullback (specMap k K) (i ≫
      c)).functionField Ω))
    let xi := η ≫ (Limits.pullback (specMap k K) (i ≫ c)).fromSpecStalk (genericPoint
      (↑(Limits.pullback (specMap k K) (i ≫ c)) : Type))
    ∃ α : K ≃ₐ[k] K, ∀ σ : K ≃ₐ[k] K,
      ∃ (g : SemilinearAut K F), SemilinearAut.baseAut g = σ.toRingEquiv ∧
        ∃ hS : ∀ p : Place K F,
          p ∈ M.openBoundaryPlaces j ↔ g • p ∈ M.openBoundaryPlaces j,
        ∀ (p : M.openBoundaryPlaces j) (t : (primeToRootsSystem K K).inverseLimit),
          geometricAbelianGaloisAction k K U (i ≫ c) xi σ
              (geometricAbelianGaloisAction k K U (i ≫ c) xi α⁻¹
                (boundaryPlaceInertiaHom M j hj hfield Q p t)) =
            geometricAbelianGaloisAction k K U (i ≫ c) xi α⁻¹
              (boundaryPlaceInertiaHom M j hj hfield Q
                ⟨g • p.val, (hS p.val).mp p.property⟩
                (primeToRootsCoefficientMap K K σ.toRingHom t)) := by
  intro η xi
  classical
  obtain ⟨α, hα⟩ := exists_genericCoefficient_sourceAction k K U (i ≫ c) Ω xi rfl
  refine ⟨α, ?_⟩
  intro σ
  let θX := coefficientBaseChangeIso k K (i ≫ c) σ
  obtain ⟨θ, g, hθproj, hθbase, hgbase, hgfun, hgpoint⟩ :=
    M.exists_baseChange_semilinear_action c eC heC σ
  have hsquare : θX.hom ≫ j = j ≫ θ.hom := by
    apply (cancel_mono eC.hom).1
    apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [hproj, ← Category.assoc θX.hom (pullback.snd (specMap k K) (i ≫ c)) i,
        coefficientBaseChangeIso_hom_snd, hθproj, hproj]
    · simp only [Category.assoc, heC]
      rw [hbase, coefficientBaseChangeIso_hom_fst,
        hθbase, ← Category.assoc j M.toBase (Spec.map (CommRingCat.ofHom σ.toRingHom)), hbase]
  have hφM := M.functionFieldRingEquiv_semilinear θ g hgfun
  obtain ⟨hS, hφ⟩ := M.openBoundary_semilinear_compatibility j hj θX θ
    σ.toRingEquiv g hθbase hsquare hgpoint hφM
  refine ⟨g, hgbase, hS, ?_⟩
  obtain ⟨a, ha, hpoint, hlabel⟩ := hα σ
  let e := Scheme.Spec.mapIso a.toCommRingCatIso.op
  let p₀ := pullback.snd (specMap k K) (i ≫ c)
  have hp : e.hom ≫ xi = xi ≫ θX.hom := hpoint
  have hsource : e.hom ≫ (xi ≫ p₀) = xi ≫ p₀ := by
    rw [← Category.assoc, hp, Category.assoc, coefficientBaseChangeIso_hom_snd]
  let gA : Aut (fiber (xi ≫ p₀)) :=
    fiberSourceIso (xi ≫ p₀) e ≪≫ eqToIso (congrArg fiber hsource)
  change arithmeticFundamentalGroupHom k K (i ≫ c) (xi ≫ p₀) gA = α * σ * α⁻¹ at hlabel
  let A := geometricAbelianGaloisAction k K U (i ≫ c) xi
  intro p t
  have hb := boundaryPlaceInertiaHom_source_semilinear k K U (i ≫ c)
    M j hj hfield Q g hS θX.hom.functionFieldRingEquivOfIsOpenImmersion hφ a ha hsource p t
  change A (arithmeticFundamentalGroupHom k K (i ≫ c) (xi ≫ p₀) gA)
      (boundaryPlaceInertiaHom M j hj hfield Q p t) = _ at hb
  rw [hlabel, hgbase] at hb
  have hmul : σ * α⁻¹ = α⁻¹ * (α * σ * α⁻¹) := by simp [mul_assoc]
  calc
    A σ (A α⁻¹ (boundaryPlaceInertiaHom M j hj hfield Q p t)) =
        A (σ * α⁻¹) (boundaryPlaceInertiaHom M j hj hfield Q p t) := by
      rw [map_mul]
      rfl
    _ = A α⁻¹ (A (α * σ * α⁻¹) (boundaryPlaceInertiaHom M j hj hfield Q p t)) := by
      rw [hmul, map_mul]
      rfl
    _ = _ := congrArg (A α⁻¹) hb

end AnabelianGeometry.WeightFiltration
