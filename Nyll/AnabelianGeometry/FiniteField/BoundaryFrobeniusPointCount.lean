/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AnabelianGeometry.FiniteField.FrobeniusPointDescent
public import Nyll.AnabelianGeometry.FiniteField.BoundaryPermutationTrace
public import Nyll.AlgebraicCurves.Models.Construction.Basic
public import Nyll.EtaleFundamentalGroups.GeometricFiber.CoefficientBaseChangeIso
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# The first boundary trace counts original rational omitted points

The actual coefficient action on geometric boundary places is compared with
the original scheme points. Its fixed points descend uniquely to rational
points on the original proper curve. Membership in the original open is
transported through the literal base-change square, so all nonrational
boundary orbits remain in the first-Frobenius calculation.

The resulting trace formula is for the actual rational residue quotient.
Neither a boundary-point comparison nor its trace is an input.
-/

@[expose] public section

universe uGeom uField

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AlgebraicCurve
open AlgebraicGeometry.SmoothProperCurve NeronModelInfra
open EtaleCohomology.Classical
open scoped TensorProduct

namespace AnabelianGeometry.FiniteField

section Points

variable {k K : Type uGeom} {F : Type uField} [Field k] [Fintype k] [Field K] [IsAlgClosed K]
  [Algebra k K] [Algebra.IsAlgebraic k K] [Field F] [Algebra K F]
  {C U : Scheme.{uGeom}} (c : C ⟶ Spec (.of k)) (i : U ⟶ C) [IsOpenImmersion i]
  (M : CurveModel K F) (eC : M.C ≅ pullback c (specMap k K))
  (heC : eC.hom ≫ pullback.snd c (specMap k K) = M.toBase)

private def modelValuedPointEquiv :
    SchemeHomOver (𝟙 (Spec (.of K))) M.toBase ≃
      SchemeHomOver (specMap k K) c where
  toFun p := ⟨p.val ≫ eC.hom ≫ pullback.fst c (specMap k K), by
    rw [Category.assoc, Category.assoc, pullback.condition,
      ← Category.assoc eC.hom (pullback.snd c (specMap k K)) (specMap k K), heC,
      ← Category.assoc p.val M.toBase (specMap k K), p.property, Category.id_comp]⟩
  invFun x := ⟨pullback.lift x.val (𝟙 (Spec (.of K)))
      (by rw [x.property, Category.id_comp]) ≫ eC.inv, by
    rw [Category.assoc, ← heC, eC.inv_hom_id_assoc, pullback.lift_snd]⟩
  left_inv p := by
    apply Subtype.ext
    apply (cancel_mono eC.hom).1
    rw [Category.assoc, eC.inv_hom_id, Category.comp_id]
    apply pullback.hom_ext
    · exact (pullback.lift_fst _ _ _).trans
        (Category.assoc p.val eC.hom (pullback.fst c (specMap k K))).symm
    · rw [pullback.lift_snd]
      rw [Category.assoc, heC, p.property]
  right_inv x := by
    apply Subtype.ext
    simp only [Category.assoc, eC.inv_hom_id_assoc, pullback.lift_fst]

private theorem modelPlace_closedPoint (v : Place K F) :
    (M.pointEquivPlace.symm v).val (IsLocalRing.closedPoint K) =
      (M.placeEquiv.symm v).val := by
  change ((pointEquivClosedPoint M.toBase)
    ((pointEquivClosedPoint M.toBase).symm (M.placeEquiv.symm v))).val = _
  exact congrArg Subtype.val ((pointEquivClosedPoint M.toBase).apply_symm_apply _)

variable (j : pullback (specMap k K) (i ≫ c) ⟶ M.C) [IsOpenImmersion j]
  (hproj : j ≫ eC.hom ≫ pullback.fst c (specMap k K) =
    pullback.snd (specMap k K) (i ≫ c) ≫ i)
  (hbase : j ≫ M.toBase = pullback.fst (specMap k K) (i ≫ c))

omit [Fintype k] [IsAlgClosed K] [Algebra.IsAlgebraic k K] [IsOpenImmersion j] in
include hproj hbase in
private theorem modelPoint_mem_open_iff
    (p : SchemeHomOver (𝟙 (Spec (.of K))) M.toBase) :
    p.val (IsLocalRing.closedPoint K) ∈ Set.range j ↔
      (modelValuedPointEquiv c M eC heC p).val (IsLocalRing.closedPoint K) ∈
        Set.range i := by
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨pullback.snd (specMap k K) (i ≫ c) z, ?_⟩
    have h := congrArg
      (fun f : pullback (specMap k K) (i ≫ c) ⟶ C => f z) hproj
    exact h.symm.trans
      (congrArg (eC.hom ≫ pullback.fst c (specMap k K)) hz)
  · intro hp
    let x := modelValuedPointEquiv c M eC heC p
    have hr : Set.range x.val ⊆ Set.range i := by
      rintro _ ⟨z, rfl⟩
      have hz : z = IsLocalRing.closedPoint K := Subsingleton.elim _ _
      rw [hz]
      exact hp
    let u := IsOpenImmersion.lift i x.val hr
    have hu : u ≫ i = x.val := IsOpenImmersion.lift_fac _ _ _
    have huc : u ≫ (i ≫ c) = specMap k K := by
      rw [← Category.assoc, hu, x.property]
    let z : Spec (.of K) ⟶ pullback (specMap k K) (i ≫ c) :=
      pullback.lift (𝟙 (Spec (.of K))) u
      (by rw [Category.id_comp]; exact huc.symm)
    have hz : z ≫ j = p.val := by
      apply (cancel_mono eC.hom).1
      apply pullback.hom_ext
      · simp only [Category.assoc]
        rw [hproj, ← Category.assoc z (pullback.snd (specMap k K) (i ≫ c)) i,
          pullback.lift_snd, hu]
        rfl
      · simp only [Category.assoc, heC]
        rw [hbase, pullback.lift_fst, p.property]
    exact ⟨z (IsLocalRing.closedPoint K),
      congrArg (fun f : Spec (.of K) ⟶ M.C => f (IsLocalRing.closedPoint K)) hz⟩

omit [IsOpenImmersion i] [IsOpenImmersion j] in
private theorem boundary_fixed_iff_coefficient_fixed
    (θ : M.C ≅ M.C)
    (hθproj : θ.hom ≫ eC.hom ≫ pullback.fst c (specMap k K) =
      eC.hom ≫ pullback.fst c (specMap k K))
    (hθbase : θ.hom ≫ M.toBase = M.toBase ≫ Spec.map (CommRingCat.ofHom
      (FiniteField.frobeniusAlgEquivOfAlgebraic k K).toRingHom))
    (e : Equiv.Perm (M.openBoundaryPlaces j))
    (hpoint : ∀ v : M.openBoundaryPlaces j,
      (M.placeEquiv.symm (e v).val).val = θ.inv ((M.placeEquiv.symm v.val).val))
    (v : M.openBoundaryPlaces j) :
    e v = v ↔
      Spec.map (CommRingCat.ofHom
        (FiniteField.frobeniusAlgEquivOfAlgebraic k K).toRingHom) ≫
          (modelValuedPointEquiv c M eC heC (M.pointEquivPlace.symm v.val)).val =
        (modelValuedPointEquiv c M eC heC (M.pointEquivPlace.symm v.val)).val := by
  let σ := FiniteField.frobeniusAlgEquivOfAlgebraic k K
  let a := Scheme.Spec.mapIso σ.toRingEquiv.toCommRingCatIso.op
  let pr := eC.hom ≫ pullback.fst c (specMap k K)
  let E := modelValuedPointEquiv c M eC heC
  have hθinv : θ.inv ≫ pr = pr := by
    calc
      θ.inv ≫ pr = θ.inv ≫ (θ.hom ≫ pr) := congrArg (θ.inv ≫ ·) hθproj.symm
      _ = pr := θ.inv_hom_id_assoc pr
  have hbaseinv : θ.inv ≫ M.toBase = M.toBase ≫ a.inv := by
    apply (cancel_mono a.hom).1
    calc
      (θ.inv ≫ M.toBase) ≫ a.hom = θ.inv ≫ (M.toBase ≫ a.hom) := Category.assoc _ _ _
      _ = θ.inv ≫ (θ.hom ≫ M.toBase) := congrArg (θ.inv ≫ ·) hθbase.symm
      _ = M.toBase := θ.inv_hom_id_assoc M.toBase
      _ = (M.toBase ≫ a.inv) ≫ a.hom := by
        rw [Category.assoc, a.inv_hom_id]
        exact (Category.comp_id M.toBase).symm
  let p := M.pointEquivPlace.symm v.val
  let y : SchemeHomOver (𝟙 (Spec (.of K))) M.toBase :=
    ⟨a.hom ≫ p.val ≫ θ.inv, by
      simp only [Category.assoc, hbaseinv]
      rw [← Category.assoc p.val M.toBase a.inv, p.property, Category.id_comp,
        a.hom_inv_id]
      rfl⟩
  have hyproj : (E y).val = a.hom ≫ (E p).val := by
    change (a.hom ≫ p.val ≫ θ.inv) ≫ pr = a.hom ≫ (p.val ≫ pr)
    rw [Category.assoc, Category.assoc, hθinv]
  have hyplace : M.pointEquivPlace y = (e v).val := by
    apply M.placeEquiv.symm.injective
    apply Subtype.ext
    change (M.placeEquiv.symm (M.placeEquiv (pointEquivClosedPoint M.toBase y))).val = _
    rw [M.placeEquiv.symm_apply_apply, hpoint]
    change θ.inv (p.val (a.hom (IsLocalRing.closedPoint K))) = _
    have ha : a.hom (IsLocalRing.closedPoint K) = IsLocalRing.closedPoint K :=
      AlgebraicGeometry.Spec_closedPoint
    rw [ha]
    exact congrArg θ.inv (modelPlace_closedPoint M v.val)
  constructor
  · intro hv
    have hyp : y = p := M.pointEquivPlace.injective
      ((hyplace.trans (congrArg Subtype.val hv)).trans
        (M.pointEquivPlace.apply_symm_apply v.val).symm)
    exact hyproj.symm.trans (congrArg (fun t => (E t).val) hyp)
  · intro hfix
    have hyp : y = p := E.injective (Subtype.ext (hyproj.trans hfix))
    apply Subtype.ext
    exact hyplace.symm.trans
      ((congrArg M.pointEquivPlace hyp).trans (M.pointEquivPlace.apply_symm_apply v.val))

omit [IsOpenImmersion j] in
include heC hproj hbase in
private theorem card_fixedBoundary_eq_rationalBoundary
    (θ : M.C ≅ M.C)
    (hθproj : θ.hom ≫ eC.hom ≫ pullback.fst c (specMap k K) =
      eC.hom ≫ pullback.fst c (specMap k K))
    (hθbase : θ.hom ≫ M.toBase = M.toBase ≫ Spec.map (CommRingCat.ofHom
      (FiniteField.frobeniusAlgEquivOfAlgebraic k K).toRingHom))
    (e : Equiv.Perm (M.openBoundaryPlaces j))
    (hpoint : ∀ v : M.openBoundaryPlaces j,
      (M.placeEquiv.symm (e v).val).val = θ.inv ((M.placeEquiv.symm v.val).val)) :
    Nat.card {v : M.openBoundaryPlaces j // e v = v} =
      Nat.card {y : SchemeHomOver (𝟙 (Spec (.of k))) c //
        y.val (IsLocalRing.closedPoint k) ∉ Set.range i} := by
  let P := SchemeHomOver (specMap k K) c
  let omitted (x : P) := x.val (IsLocalRing.closedPoint K) ∉ Set.range i
  let fixed (x : P) := Spec.map (CommRingCat.ofHom
    (FiniteField.frobeniusAlgEquivOfAlgebraic k K).toRingHom) ≫ x.val = x.val
  let E := M.pointEquivPlace.symm.trans (modelValuedPointEquiv c M eC heC)
  have hE (v : Place K F) : v ∈ M.openBoundaryPlaces j ↔ omitted (E v) := by
    change (M.placeEquiv.symm v).val ∉ Set.range j ↔ _
    rw [← modelPlace_closedPoint M v]
    exact not_congr (modelPoint_mem_open_iff c i M eC heC j hproj hbase
      (M.pointEquivPlace.symm v))
  let EB : M.openBoundaryPlaces j ≃ {x : P // omitted x} := E.subtypeEquiv hE
  let EF : {v : M.openBoundaryPlaces j // e v = v} ≃
      {x : {x : P // omitted x} // fixed x.val} :=
    EB.subtypeEquiv (fun v =>
      boundary_fixed_iff_coefficient_fixed c i M eC heC j θ hθproj hθbase e hpoint v)
  let D := rationalPointFrobeniusEquiv k K c
  have hD (y : SchemeHomOver (𝟙 (Spec (.of k))) c) :
      y.val (IsLocalRing.closedPoint k) ∉ Set.range i ↔ omitted (D y).val := by
    change y.val (IsLocalRing.closedPoint k) ∉ Set.range i ↔
      y.val ((Spec.algebraMap k K) (IsLocalRing.closedPoint K)) ∉ Set.range i
    rw [AlgebraicGeometry.Spec_closedPoint]
  let ED : {y : SchemeHomOver (𝟙 (Spec (.of k))) c //
      y.val (IsLocalRing.closedPoint k) ∉ Set.range i} ≃
      {x : {x : P // fixed x} // omitted x.val} := D.subtypeEquiv hD
  let swap : {x : {x : P // omitted x} // fixed x.val} ≃
      {x : {x : P // fixed x} // omitted x.val} :=
    { toFun := fun x => ⟨⟨x.val.val, x.property⟩, x.val.property⟩
      invFun := fun x => ⟨⟨x.val.val, x.property⟩, x.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Nat.card_congr ((EF.trans swap).trans ED.symm)

end Points

/-- The actual first-Frobenius residue quotient has trace `q` times the
number of original rational omitted points minus one. The permutation,
fixed-point descent and comparison with the original open are constructed. -/
theorem exists_boundaryFrobenius_rationalPoint_trace
    {k K : Type uGeom} {F : Type uField} [Field k] [Fintype k] [Field K] [IsAlgClosed K]
    [Algebra k K] [Algebra.IsAlgebraic k K] [Field F] [Algebra K F]
    [Algebra.EssFiniteType K F] [IsCurveOver K F]
    {C U : Scheme.{uGeom}} (c : C ⟶ Spec (.of k)) (i : U ⟶ C) [IsOpenImmersion i]
    [IsIntegral (pullback (specMap k K) (i ≫ c))]
    [CompactSpace ↑(pullback (specMap k K) (i ≫ c))]
    (M : CurveModel K F) (eC : M.C ≅ pullback c (specMap k K))
    (heC : eC.hom ≫ pullback.snd c (specMap k K) = M.toBase)
    (j : pullback (specMap k K) (i ≫ c) ⟶ M.C) [IsOpenImmersion j]
    (hj : DenseRange j)
    (hproj : j ≫ eC.hom ≫ pullback.fst c (specMap k K) =
      pullback.snd (specMap k K) (i ≫ c) ≫ i)
    (hbase : j ≫ M.toBase = pullback.fst (specMap k K) (i ≫ c))
    [Finite (M.openBoundaryPlaces j)] [Nonempty (M.openBoundaryPlaces j)]
    {Ω : Type uGeom} [Field Ω] [Algebra (pullback (specMap k K) (i ≫ c)).functionField Ω]
    [IsSepClosed Ω] [IsSepClosure (pullback (specMap k K) (i ≫ c)).functionField Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K)) :
    let X := pullback (specMap k K) (i ≫ c)
    let σ := FiniteField.frobeniusAlgEquivOfAlgebraic k K
    let θU := AlgebraicGeometry.FiniteEtale.coefficientBaseChangeIso k K (i ≫ c) σ
    let ξ := X.genericExtensionMorphism Ω
    ∃ T : Module.End ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℤ_[ℓ]] ellAdicBoundarySpace M j ℓ),
      (rationalEllAdicBoundaryMap M j hj ξ ℓ hℓ).comp
          (rationalEllAdicPullback θU.inv ℓ 1) =
        T.comp (rationalEllAdicBoundaryMap M j hj ξ ℓ hℓ) ∧
      LinearMap.trace ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℤ_[ℓ]] ellAdicBoundarySpace M j ℓ) T =
        (Fintype.card k : ℚ_[ℓ]) *
          ((Nat.card {y : SchemeHomOver (𝟙 (Spec (.of k))) c //
            y.val (IsLocalRing.closedPoint k) ∉ Set.range i} : ℚ_[ℓ]) - 1) := by
  intro X σ θU ξ
  let : Fintype (M.openBoundaryPlaces j) := Fintype.ofFinite _
  obtain ⟨θ, e, hθproj, hθbase, hpoint, _, hsquare⟩ :=
    exists_ellAdicBoundaryFrobenius_action c i M eC heC j hj hproj hbase
      (Ω := Ω) ℓ hℓ
  refine ⟨(Fintype.card k • (ellAdicBoundaryPermutation M j ℓ e).toLinearMap).baseChange
    ℚ_[ℓ], hsquare, ?_⟩
  rw [trace_rationalBoundaryFrobenius M j ℓ (Fintype.card k) e,
    card_fixedBoundary_eq_rationalBoundary c i M eC heC j hproj hbase
      θ hθproj hθbase e hpoint]

end AnabelianGeometry.FiniteField
