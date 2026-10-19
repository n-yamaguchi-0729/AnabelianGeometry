/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.BoundaryRangeGaloisAction
import Nyll.AnabelianGeometry.WeightFiltration.BoundaryRangeSeparation
import Nyll.AnabelianGeometry.WeightFiltration.BoundaryInertiaSemilinear
import Nyll.AnabelianGeometry.WeightFiltration.OpenBoundarySemilinear
import Nyll.AnabelianGeometry.WeightFiltration.GenericCoefficientDuality
import Nyll.AlgebraicCurves.Models.ConstantExtension.BaseChangeSemilinearAction
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver

/-!
# Arithmetic coefficient equivariance of the original boundary inertia

The coefficient isomorphisms of the original open curve and compactification
supply boundary preservation and the function-field square. A single fixed
base-point correction gives the arithmetic action on all boundary parameters.
-/

noncomputable section
open NeronModelInfra

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AlgebraicCurve
open AlgebraicGeometry.FiniteEtale AlgebraicGeometry.SmoothProperCurve
open SchemeTheory EtaleFundamentalGroups.Inertia
open ProCGroups.Abelian

namespace AnabelianGeometry.WeightFiltration

/-- Correcting the target by the ratio of the two source corrections makes
an arithmetic-equivariant map intertwine the actual coefficient actions. -/
theorem correctedBoundaryEquiv_intertwines
    {Γ A B : Type*} [Group Γ] [Group A] [Group B]
    (ρ₁ : Γ →* MulAut A) (ρ₂ : Γ →* MulAut B)
    (e : A ≃* B) (he : ∀ σ x, e (ρ₁ σ x) = ρ₂ σ (e x))
    (α₁ α₂ σ : Γ) (x : A) :
    (e.trans (ρ₂ (α₂ * α₁⁻¹))) (ρ₁ (α₁ * σ * α₁⁻¹) x) =
      ρ₂ (α₂ * σ * α₂⁻¹) ((e.trans (ρ₂ (α₂ * α₁⁻¹))) x) := by
  change ρ₂ (α₂ * α₁⁻¹) (e (ρ₁ (α₁ * σ * α₁⁻¹) x)) =
    ρ₂ (α₂ * σ * α₂⁻¹) (ρ₂ (α₂ * α₁⁻¹) (e x))
  rw [he]
  have hmul : (α₂ * α₁⁻¹) * (α₁ * σ * α₁⁻¹) =
      (α₂ * σ * α₂⁻¹) * (α₂ * α₁⁻¹) := by
    simp only [mul_assoc, inv_mul_cancel_left]
  calc
    ρ₂ (α₂ * α₁⁻¹) (ρ₂ (α₁ * σ * α₁⁻¹) (e x)) =
        ρ₂ ((α₂ * α₁⁻¹) * (α₁ * σ * α₁⁻¹)) (e x) :=
      (congrArg (fun f : MulAut B => f (e x))
        (map_mul ρ₂ (α₂ * α₁⁻¹) (α₁ * σ * α₁⁻¹))).symm
    _ = ρ₂ ((α₂ * σ * α₂⁻¹) * (α₂ * α₁⁻¹)) (e x) := congrArg (fun γ => ρ₂ γ (e x)) hmul
    _ = ρ₂ (α₂ * σ * α₂⁻¹) (ρ₂ (α₂ * α₁⁻¹) (e x)) :=
      congrArg (fun f : MulAut B => f (e x))
        (map_mul ρ₂ (α₂ * σ * α₂⁻¹) (α₂ * α₁⁻¹))

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
/-- The actual coefficient action on boundary places, retaining the geometric
point formula and the single arithmetic source correction. In particular,
the semilinear map in the conclusion is tied to the literal coefficient
base change, rather than merely having the prescribed action on constants. -/
theorem exists_boundary_geometric_range_action :
    let η := Spec.map (CommRingCat.ofHom (algebraMap (Limits.pullback (specMap k K) (i ≫
      c)).functionField Ω))
    let xi := η ≫ (Limits.pullback (specMap k K) (i ≫ c)).fromSpecStalk (genericPoint
      (↑(Limits.pullback (specMap k K) (i ≫ c)) : Type))
    ∃ α : K ≃ₐ[k] K, ∀ σ : K ≃ₐ[k] K,
      ∃ (θ : M.C ≅ M.C) (g : SemilinearAut K F),
        θ.hom ≫ eC.hom ≫ pullback.fst c (specMap k K) =
          eC.hom ≫ pullback.fst c (specMap k K) ∧
        θ.hom ≫ M.toBase = M.toBase ≫ Spec.map (CommRingCat.ofHom σ.toRingHom) ∧
        SemilinearAut.baseAut g = σ.toRingEquiv ∧
        (∀ x y : SchemeHomOver (𝟙 (Spec (.of K))) M.toBase,
          y.1 ≫ θ.hom = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x.1 →
            M.pointEquivPlace y = g • M.pointEquivPlace x) ∧
        ∃ hS : ∀ p : Place K F,
          p ∈ M.openBoundaryPlaces j ↔ g • p ∈ M.openBoundaryPlaces j,
        ∀ p : M.openBoundaryPlaces j,
          ((boundaryPlaceInertiaHom M j hj hfield Q p).toMonoidHom.range).map
            (geometricAbelianGaloisAction k K U (i ≫ c) xi
              (α * σ * α⁻¹)).toMonoidHom =
            (boundaryPlaceInertiaHom M j hj hfield Q
              ⟨g • p.val, (hS p.val).mp p.property⟩).toMonoidHom.range := by
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
  have hb (p : M.openBoundaryPlaces j)
      (t : (primeToRootsSystem K K).inverseLimit) :
      A (α * σ * α⁻¹) (boundaryPlaceInertiaHom M j hj hfield Q p t) =
        boundaryPlaceInertiaHom M j hj hfield Q
          ⟨g • p.val, (hS p.val).mp p.property⟩
          (primeToRootsCoefficientMap K K σ.toRingHom t) := by
    have hb := boundaryPlaceInertiaHom_source_semilinear k K U (i ≫ c)
      M j hj hfield Q g hS θX.hom.functionFieldRingEquivOfIsOpenImmersion hφ a ha hsource p t
    change A (arithmeticFundamentalGroupHom k K (i ≫ c) (xi ≫ p₀) gA)
        (boundaryPlaceInertiaHom M j hj hfield Q p t) = _ at hb
    rw [hlabel, hgbase] at hb
    exact hb
  refine ⟨θ, g, hθproj, hθbase, hgbase, hgpoint, hS, ?_⟩
  intro p
  ext z
  constructor
  · rintro ⟨v, ⟨t, rfl⟩, rfl⟩
    exact ⟨primeToRootsCoefficientMap K K σ.toRingHom t, (hb p t).symm⟩
  · rintro ⟨t, rfl⟩
    obtain ⟨u, hu⟩ := (primeToRootsResidueEquiv K K σ.toRingEquiv).surjective t
    change primeToRootsCoefficientMap K K σ.toRingHom u = t at hu
    exact ⟨_, ⟨u, rfl⟩, (hb p u).trans
      (congrArg (boundaryPlaceInertiaHom M j hj hfield Q
        ⟨g • p.val, (hS p.val).mp p.property⟩) hu)⟩

end AnabelianGeometry.WeightFiltration
