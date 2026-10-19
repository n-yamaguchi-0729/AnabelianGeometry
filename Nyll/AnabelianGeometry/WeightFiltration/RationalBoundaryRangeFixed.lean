/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.RationalBoundaryArithmeticEquivariance
import Nyll.EtaleFundamentalGroups.Inertia.PrimeToRootsResidueAction

/-! # Rational boundary ranges under arithmetic conjugation

Arithmetic elements over the field of definition of a puncture can act
nontrivially on inertia. Their action is cyclotomic, and therefore preserves
the entire abelian inertia range. This is the required statement for a finite
constant-cover correction, even when the correcting element is not geometric.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AlgebraicCurve
open AlgebraicGeometry.FiniteEtale AlgebraicGeometry.SmoothProperCurve
open SchemeTheory EtaleFundamentalGroups.Inertia ProCGroups.Abelian
open scoped RatFunc
attribute [local instance] Polynomial.algebra

namespace AnabelianGeometry.WeightFiltration

variable
    (k K : Type) [Field k] [Field K] [CharZero K] [IsAlgClosed K]
    [Algebra k K] [IsSepClosure k K]
    {C U : Scheme} [CompactSpace U] [QuasiSeparatedSpace U]
    (c : C ⟶ Spec (.of k)) (i : U ⟶ C)


variable
    [IsIntegral (Limits.pullback (specMap k K) (i ≫ c))] [CompactSpace ↑(Limits.pullback (specMap
      k K) (i ≫ c))]
    (M : CurveModel K (RatFunc K))
    (eC : M.C ≅ pullback c (specMap k K))
    (heC : eC.hom ≫ pullback.snd c (specMap k K) = M.toBase)
    (j : (Limits.pullback (specMap k K) (i ≫ c)) ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
    (hproj : j ≫ eC.hom ≫ pullback.fst c (specMap k K) = pullback.snd (specMap k K) (i ≫ c) ≫ i)
    (hbase : j ≫ M.toBase = pullback.fst (specMap k K) (i ≫ c))
    [Algebra (RatFunc K) (Limits.pullback (specMap k K) (i ≫ c)).functionField]
    (hfield : algebraMap (RatFunc K) (Limits.pullback (specMap k K) (i ≫ c)).functionField =
      (j.functionFieldMap hj).comp M.ffEquiv.toRingHom)
    {Ω : Type} [Field Ω] [Algebra (Limits.pullback (specMap k K) (i ≫ c)).functionField Ω]
      [Algebra (RatFunc K) Ω]
    [IsScalarTower (RatFunc K) (Limits.pullback (specMap k K) (i ≫ c)).functionField Ω]
    [IsSepClosed Ω] [IsSepClosure (Limits.pullback (specMap k K) (i ≫ c)).functionField Ω]
      [IsSepClosure (RatFunc K) Ω]
    [hPlaceAlgebra : ∀ p : M.openBoundaryPlaces j, Algebra p.val.toValuationSubring Ω]
    [hPlaceTower : ∀ p : M.openBoundaryPlaces j,
      @IsScalarTower p.val.toValuationSubring (RatFunc K) Ω
      (inferInstance : Algebra p.val.toValuationSubring (RatFunc K)).toSMul
      inferInstance inferInstance]
    [Algebra K Ω]
    [hConstantTower : ∀ p : M.openBoundaryPlaces j, IsScalarTower K p.val.toValuationSubring Ω]
    (Q : ∀ p : M.openBoundaryPlaces j,
      Ideal (normalizationCommAlgCat p.val.toValuationSubring Ω))
    [∀ p, (Q p).IsMaximal]


variable [IsIntegral C]

include eC heC hproj hbase hj hfield Q hPlaceAlgebra hPlaceTower hConstantTower in
/-- Every Galois element over the field of definition of an actual rational
puncture preserves its abelian inertia range. The roots action is allowed to
be nontrivial; its surjectivity, rather than an inner-conjugation argument,
proves equality of ranges. -/
theorem rational_boundaryPlaceInertiaHom_range_galois_fixed
    (hπ : DenseRange (eC.hom ≫ pullback.fst c (specMap k K)))
    (e0 : RatFunc k ≃+* C.functionField)
    (hchart : ∀ x : RatFunc k,
      (eC.hom ≫ pullback.fst c (specMap k K)).functionFieldMap hπ (e0 x) =
        M.ffEquiv (algebraMap (RatFunc k) (RatFunc K) x))
    (V : Place k (RatFunc k)) (hV : V.IsRational)
    (p : M.openBoundaryPlaces j)
    (hord : ∀ x : RatFunc k,
      p.val.ord (algebraMap (RatFunc k) (RatFunc K) x) = V.ord x)
    (σ : K ≃ₐ[k] K) :
    ((boundaryPlaceInertiaHom M j hj hfield Q p).toMonoidHom.range).map
      (geometricAbelianGaloisAction k K U (i ≫ c)
        ((Limits.pullback (specMap k K) (i ≫ c)).genericExtensionMorphism Ω)
        σ).toMonoidHom =
      (boundaryPlaceInertiaHom M j hj hfield Q p).toMonoidHom.range := by
  have hb := rational_boundaryPlaceInertiaHom_arithmetic_equivariance
    k K c i M eC heC j hj hproj hbase hfield Q hπ e0 hchart V hV p hord σ
  ext z
  constructor
  · rintro ⟨v, ⟨t, rfl⟩, rfl⟩
    exact ⟨primeToRootsCoefficientMap K K σ.toRingHom t, (hb t).symm⟩
  · rintro ⟨t, rfl⟩
    obtain ⟨u, hu⟩ := (primeToRootsResidueEquiv K K σ.toRingEquiv).surjective t
    change primeToRootsCoefficientMap K K σ.toRingHom u = t at hu
    exact ⟨_, ⟨u, rfl⟩, (hb u).trans
      (congrArg (boundaryPlaceInertiaHom M j hj hfield Q p) hu)⟩

end AnabelianGeometry.WeightFiltration
