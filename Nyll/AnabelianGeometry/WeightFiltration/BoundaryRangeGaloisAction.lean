/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.BoundaryCoefficientEquivariance
import Nyll.AnabelianGeometry.WeightFiltration.BoundaryInertiaCoordinateSeparation
import Nyll.EtaleFundamentalGroups.Inertia.PrimeToRootsResidueAction

/-! # Galois action on the actual boundary ranges

The source-action correction is retained. Consequently the ordinary geometric
boundary action is compared with the same corrected ranges on both sides;
no Galois equivariance of a prospective boundary correspondence is assumed.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AlgebraicCurve
open AlgebraicGeometry.FiniteEtale AlgebraicGeometry.SmoothProperCurve
open SchemeTheory EtaleFundamentalGroups.Inertia
open ProCGroups.Abelian

namespace AnabelianGeometry.WeightFiltration

/-- A correspondence between an injectively labelled family of subgroups is
equivariant whenever the ambient isomorphism intertwines the two actions.
This recovers equivariance of labels from equivariance on the ambient groups. -/
theorem boundaryRange_correspondence_equivariant
    {S T A B : Type*} [Group A] [Group B]
    (rS : S → Subgroup A) (rT : T → Subgroup B) (hrT : Function.Injective rT)
    (e : A ≃* B) (τ : S → T)
    (hτ : ∀ p, (rS p).map e.toMonoidHom = rT (τ p))
    (a : MulAut A) (b : MulAut B) (ha : S → S) (hb : T → T)
    (hS : ∀ p, (rS p).map a.toMonoidHom = rS (ha p))
    (hT : ∀ p, (rT p).map b.toMonoidHom = rT (hb p))
    (he : ∀ x, e (a x) = b (e x)) (p : S) :
    τ (ha p) = hb (τ p) := by
  apply hrT
  have hcomp : e.toMonoidHom.comp a.toMonoidHom =
      b.toMonoidHom.comp e.toMonoidHom := MonoidHom.ext he
  calc
    rT (τ (ha p)) = (rS (ha p)).map e.toMonoidHom := (hτ (ha p)).symm
    _ = ((rS p).map a.toMonoidHom).map e.toMonoidHom :=
      congrArg (fun H : Subgroup A => H.map e.toMonoidHom) (hS p).symm
    _ = ((rS p).map e.toMonoidHom).map b.toMonoidHom := by
      rw [Subgroup.map_map, hcomp, Subgroup.map_map]
    _ = rT (hb (τ p)) := by rw [hτ p, hT (τ p)]

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
/-- The full arithmetic Galois group permutes the corrected actual boundary
ranges through its actual coefficient action. The correction is fixed once,
and the roots coefficient action is eliminated using its proven bijectivity. -/
theorem exists_boundary_range_galois_action :
    let η := Spec.map (CommRingCat.ofHom (algebraMap (Limits.pullback (specMap k K) (i ≫
      c)).functionField Ω))
    let xi := η ≫ (Limits.pullback (specMap k K) (i ≫ c)).fromSpecStalk (genericPoint
      (↑(Limits.pullback (specMap k K) (i ≫ c)) : Type))
    ∃ α : K ≃ₐ[k] K, ∀ σ : K ≃ₐ[k] K,
      ∃ (g : SemilinearAut K F), SemilinearAut.baseAut g = σ.toRingEquiv ∧
        ∃ hS : ∀ p : Place K F,
          p ∈ M.openBoundaryPlaces j ↔ g • p ∈ M.openBoundaryPlaces j,
        ∀ p : M.openBoundaryPlaces j,
          (((boundaryPlaceInertiaHom M j hj hfield Q p).toMonoidHom.range).map
            (geometricAbelianGaloisAction k K U (i ≫ c) xi α⁻¹).toMonoidHom).map
              (geometricAbelianGaloisAction k K U (i ≫ c) xi σ).toMonoidHom =
            ((boundaryPlaceInertiaHom M j hj hfield Q
              ⟨g • p.val, (hS p.val).mp p.property⟩).toMonoidHom.range).map
                (geometricAbelianGaloisAction k K U (i ≫ c) xi α⁻¹).toMonoidHom := by
  intro η xi
  obtain ⟨α, hα⟩ := exists_boundary_coefficient_equivariance
    k K c i M eC heC j hj hproj hbase hfield Q
  refine ⟨α, ?_⟩
  intro σ
  obtain ⟨g, hg, hS, hb⟩ := hα σ
  refine ⟨g, hg, hS, ?_⟩
  intro p
  ext z
  constructor
  · rintro ⟨v, ⟨w, ⟨t, rfl⟩, rfl⟩, rfl⟩
    exact ⟨_, ⟨primeToRootsCoefficientMap K K σ.toRingHom t, rfl⟩, (hb p t).symm⟩
  · rintro ⟨v, ⟨t, rfl⟩, rfl⟩
    obtain ⟨u, hu⟩ := (primeToRootsResidueEquiv K K σ.toRingEquiv).surjective t
    change primeToRootsCoefficientMap K K σ.toRingHom u = t at hu
    refine ⟨_, ⟨_, ⟨u, rfl⟩, rfl⟩, ?_⟩
    exact (hb p u).trans (congrArg
      (fun r => geometricAbelianGaloisAction k K U (i ≫ c) xi α⁻¹
        (boundaryPlaceInertiaHom M j hj hfield Q
          ⟨g • p.val, (hS p.val).mp p.property⟩ r)) hu)

end AnabelianGeometry.WeightFiltration
