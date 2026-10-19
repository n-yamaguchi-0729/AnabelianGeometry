/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.ArithmeticAlignedCoefficientEmbedding
import Nyll.AnabelianGeometry.WeightFiltration.BoundaryGeometricGaloisAction
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver

/-!
# Boundary Galois actions for an arithmetically aligned generic embedding

The alignment is the equality of actual field-fiber comparisons supplied by
exists_arithmeticAlignedCoefficientEmbedding. After using that embedding to
construct the geometric generic point, coefficient actions and arithmetic
labels agree exactly; the cusp labels require no subsequent correction.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AlgebraicCurve
open AlgebraicGeometry.FiniteEtale AlgebraicGeometry.SmoothProperCurve
open SchemeTheory EtaleFundamentalGroups.Inertia ProCGroups.Abelian NeronModelInfra

namespace AnabelianGeometry.WeightFiltration

/-- Lifting an actual coefficient automorphism to the geometric generic point
has its literal arithmetic label when the coefficient embedding realizes the
chosen arithmetic fiber comparison. -/
theorem genericCoefficient_sourceAction_of_alignedComparison
    (k K : Type) [Field k] [Field K] [Algebra k K]
    [IsSepClosure k K] [IsSepClosed K]
    (X : Scheme) (f : X ⟶ Spec (.of k))
    [IsIntegral (pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))) f)]
    (Ω : Type) [Field Ω] [IsSepClosed Ω]
    [Algebra (pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))) f).functionField Ω]
    [IsSepClosure
      (pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))) f).functionField Ω]
    [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (xi : Spec (.of Ω) ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))) f)
    (hxi : xi = (pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) f).genericExtensionMorphism Ω)
    (hcoef : xi ≫ pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k K))) f = ξ K Ω)
    (hbase : (xi ≫ pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k K))) f) ≫ f = ξ k Ω)
    (halign : fieldFiberExtensionIso k K Ω ≪≫
      (eqToIso (congrArg fiber hbase)).symm =
        ((nonempty_fiber_iso
          ((xi ≫ pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k K))) f) ≫ f)
          (ξ k K)).some).symm) :
    ∀ σ : Gal(K/k),
      ∃ (a : Ω ≃+* Ω)
        (_ha : ∀ z : (pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))) f).functionField,
          a (algebraMap _ Ω z) = algebraMap _ Ω
            ((coefficientBaseChangeIso k K f σ).hom.functionFieldRingEquivOfIsOpenImmersion z))
        (hpoint : Spec.map (CommRingCat.ofHom a.toRingHom) ≫ xi =
          xi ≫ (coefficientBaseChangeIso k K f σ).hom),
        let e := Scheme.Spec.mapIso a.toCommRingCatIso.op
        let p := pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k K))) f
        let hz : e.hom ≫ (xi ≫ p) = xi ≫ p := by
          change Spec.map (CommRingCat.ofHom a.toRingHom) ≫ (xi ≫ p) = xi ≫ p
          rw [← Category.assoc, hpoint, Category.assoc, coefficientBaseChangeIso_hom_snd]
        arithmeticFundamentalGroupHom k K f (xi ≫ p)
          (fiberSourceIso (xi ≫ p) e ≪≫ eqToIso (congrArg fiber hz)) = σ := by
  intro σ
  let θ := coefficientBaseChangeIso k K f σ
  obtain ⟨a, ha, hpoint₀⟩ := exists_genericPoint_sourceIso θ Ω
  let e := Scheme.Spec.mapIso a.toCommRingCatIso.op
  let p := pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k K))) f
  have hpoint : e.hom ≫ xi = xi ≫ θ.hom := by
    change Spec.map (CommRingCat.ofHom a.toRingHom) ≫ xi = xi ≫ θ.hom
    rw [hxi]
    exact hpoint₀
  refine ⟨a, ha, hpoint, ?_⟩
  have hz : e.hom ≫ (xi ≫ p) = xi ≫ p := by
    rw [← Category.assoc, hpoint, Category.assoc, coefficientBaseChangeIso_hom_snd]
  have hρspec : Spec.map (CommRingCat.ofHom (a.toRingHom.comp (algebraMap K Ω))) =
      Spec.map (CommRingCat.ofHom ((algebraMap K Ω).comp σ.toRingHom)) := by
    change Spec.map (CommRingCat.ofHom (algebraMap K Ω) ≫ CommRingCat.ofHom a.toRingHom) =
      Spec.map (CommRingCat.ofHom σ.toRingHom ≫ CommRingCat.ofHom (algebraMap K Ω))
    rw [Spec.map_comp, Spec.map_comp]
    change e.hom ≫ ξ K Ω = ξ K Ω ≫ Spec.map (CommRingCat.ofHom σ.toRingHom)
    rw [← hcoef, ← Category.assoc, hpoint, Category.assoc, coefficientBaseChangeIso_hom_fst]
    exact (Category.assoc _ _ _).symm
  have hρ : a.toRingHom.comp (algebraMap K Ω) =
      (algebraMap K Ω).comp σ.toRingHom :=
    congrArg (fun m => m.hom) (Spec.map_injective hρspec)
  exact arithmeticFundamentalGroupHom_sourceAction_of_alignedComparison
    k K Ω f (xi ≫ p) hbase halign e a.toRingHom rfl σ hρ hz

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
    [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    [∀ p : M.openBoundaryPlaces j, IsScalarTower K p.val.toValuationSubring Ω]
    (Q : ∀ p : M.openBoundaryPlaces j,
      Ideal (normalizationCommAlgCat p.val.toValuationSubring Ω))
    [∀ p, (Q p).IsMaximal]

include eC heC hproj hbase in
/-- With the generic coefficient embedding aligned before model construction,
the actual Galois action on boundary ranges has no source conjugator. -/
theorem boundary_geometric_range_action_of_alignedComparison :
    let η := Spec.map (CommRingCat.ofHom (algebraMap (Limits.pullback (specMap k K) (i ≫
      c)).functionField Ω))
    let xi := η ≫ (Limits.pullback (specMap k K) (i ≫ c)).fromSpecStalk (genericPoint
      (↑(Limits.pullback (specMap k K) (i ≫ c)) : Type))
    ∀ (_hcoef : xi ≫ pullback.fst (specMap k K) (i ≫ c) = ξ K Ω)
      (hactualBase : (xi ≫ pullback.snd (specMap k K) (i ≫ c)) ≫ (i ≫ c) = ξ k Ω)
      (_halign : fieldFiberExtensionIso k K Ω ≪≫
        (eqToIso (congrArg fiber hactualBase)).symm =
          ((nonempty_fiber_iso
            ((xi ≫ pullback.snd (specMap k K) (i ≫ c)) ≫ (i ≫ c))
            (ξ k K)).some).symm),
    ∀ σ : K ≃ₐ[k] K,
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
              σ).toMonoidHom =
            (boundaryPlaceInertiaHom M j hj hfield Q
              ⟨g • p.val, (hS p.val).mp p.property⟩).toMonoidHom.range := by
  intro η xi hcoef hactualBase halign σ
  classical
  have hα := genericCoefficient_sourceAction_of_alignedComparison
    k K U (i ≫ c) Ω xi rfl hcoef hactualBase halign
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
  change arithmeticFundamentalGroupHom k K (i ≫ c) (xi ≫ p₀) gA = σ at hlabel
  let A := geometricAbelianGaloisAction k K U (i ≫ c) xi
  have hb (p : M.openBoundaryPlaces j)
      (t : (primeToRootsSystem K K).inverseLimit) :
      A σ (boundaryPlaceInertiaHom M j hj hfield Q p t) =
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
