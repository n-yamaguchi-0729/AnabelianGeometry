/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.LiteralArithmeticBoundaryWeight
import Nyll.AnabelianGeometry.WeightFiltration.IntrinsicBoundaryWeight
import Nyll.EtaleFundamentalGroups.GeometricFiber.ArithmeticKernelEquivalence
import Nyll.AnabelianGeometry.WeightFiltration.BoundaryPreservingNumericalInvariants
import Nyll.AnabelianGeometry.ArithmeticIsomorphisms.GeometricBasePoint
import Nyll.AnabelianGeometry.GeometricFundamentalGroup.PropernessDetection
import Nyll.AlgebraicCurves.Models.Construction.LiteralArithmeticCurveModel
import Nyll.AlgebraicCurves.Geometry.Curves.GeometricGenus
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveTwoAffineCover
import Nyll.SchemeTheory.FunctionFields.GeometricIntegrality
import Nyll.SchemeTheory.Morphisms.GeometricallyIrreducibleConnected

/-! # Numerical invariants from the original arithmetic fundamental groups

For smooth proper compactifications with rational sections over a number
field, a Galois-equivariant isomorphism of the geometric abelianizations
determines the geometric genus and the boundary count minus one,
truncated at zero. The boundary counts therefore agree if both are positive
or if either count is at least two. The proof constructs
its literal function-field models, geometric base points and boundary
filtration comparison internally. The empty-boundary versus one-puncture
case is not decided by the abelian boundary filtration alone. For full
arithmetic groups, actual finite covers distinguish these cases in positive
genus. The exceptional genus-zero pair with zero or one puncture remains
excluded. Transport from arbitrary geometric base points is constructed.

The numerical calculation follows Yamaguchi, J. London Math. Soc. 109 (2024),
e12912, Lemma 1.6 and Proposition 1.7: https://doi.org/10.1112/jlms.12912.
The present result concerns full arithmetic fundamental groups over number
fields; it does not assert the paper's general finite-step reconstruction theorem.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory
open AlgebraicGeometry.FiniteEtale AlgebraicGeometry.SmoothProperCurve
open AlgebraicCurve NeronModelInfra EtaleFundamentalGroups ProCGroups.Abelian
open AnabelianGeometry.ArithmeticIsomorphisms
open scoped TensorProduct

namespace AnabelianGeometry.WeightFiltration

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

private theorem coefficientOpen_isOpenImmersion
    {T T' C U : Scheme} (phi : T' ⟶ T) (c : C ⟶ T)
    (i : U ⟶ C) [IsOpenImmersion i] :
    IsOpenImmersion (coefficientModelMap phi c i) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := (show MorphismProperty Scheme from IsOpenImmersion))
    (coefficientBaseChange_isPullback phi c i).flip (inferInstance : IsOpenImmersion i)

/-- Identify the geometric genus with the literal function field over the
supplied algebraically closed coefficient field, by actual Cech base change. -/
private theorem geometricGenus_eq_literal_genus
    (k κ : Type) [Field k] [Field κ] [Algebra k κ] [IsAlgClosed κ]
    {C : Scheme} (c : C ⟶ Spec (.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (.of k))) c) :
    let _ : Algebra κ (Limits.pullback c (specMap k κ)).functionField :=
      (baseToFunctionField (baseChange k c κ)).toAlgebra
    geometricGenus k c = genusFF κ (Limits.pullback c (specMap k κ)).functionField := by
  intro _
  obtain ⟨V, _, _⟩ := exists_twoAffineOpenCover_of_section k c ε
  let d := (V.structureSheafSections c).cechDiff
  have hex : Function.Exact d (LinearMap.range d).mkQ :=
    LinearMap.exact_map_mkQ_range d
  have hsurj : Function.Surjective (LinearMap.range d).mkQ :=
    Submodule.mkQ_surjective (LinearMap.range d)
  have hexκ : Function.Exact (d.baseChange κ) ((LinearMap.range d).mkQ.baseChange κ) := by
    have ht := lTensor_exact κ hex hsurj
    rwa [← LinearMap.baseChange_eq_ltensor, ← LinearMap.baseChange_eq_ltensor] at ht
  let e := hexκ.linearEquivOfSurjective (LinearMap.baseChange_surjective κ hsurj)
  calc
    geometricGenus k c = Module.finrank k (V.structureSheafSections c).H1 :=
      (finrank_H1_eq_geometricGenus k c V).symm
    _ = Module.finrank κ (κ ⊗[k] (V.structureSheafSections c).H1) :=
      Module.finrank_baseChange.symm
    _ = Module.finrank κ ((κ ⊗[k] (V.cover c).A01) ⧸
        LinearMap.range (d.baseChange κ)) := e.finrank_eq.symm
    _ = genusFF κ (Limits.pullback c (specMap k κ)).functionField :=
      (V.finrank_cechDiff_baseChange_of_isAlgClosed c κ).2.2

private def boundaryPlacesEquivClosedPoints
    {K F : Type} [Field K] [Field F] [Algebra K F]
    (M : CurveModel K F) {U : Scheme} (j : U ⟶ M.C) :
    M.openBoundaryPlaces j ≃ {x : closedPoints M.C // x.val ∉ Set.range j} where
  toFun p := ⟨M.placeEquiv.symm p.val, p.property⟩
  invFun x := ⟨M.placeEquiv x.val, by
    change (M.placeEquiv.symm (M.placeEquiv x.val)).val ∉ Set.range j
    rw [M.placeEquiv.symm_apply_apply]
    exact x.property⟩
  left_inv p := Subtype.ext (M.placeEquiv.apply_symm_apply p.val)
  right_inv x := Subtype.ext (M.placeEquiv.symm_apply_apply x.val)

/-- The zero-sum boundary count also includes the empty boundary: both zero
and one puncture give a residue group with one element. -/
theorem natCard_finiteResidue_range_eq_pow_boundaryCard_sub_one
    {K F : Type} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    [IsCurveOver K F] (M : CurveModel K F)
    (ε : SchemeHomOver (𝟙 (Spec (.of K))) M.toBase) (n : ℕ+)
    {X : Scheme} [IsIntegral X] [CompactSpace X]
    (j : X ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
    (hn : IsUnit ((n : ℕ) : K))
    {Ω : Type} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ X)
    [Fintype (M.openBoundaryPlaces j)] :
    Nat.card (finiteResidue M n j hj hn xi).range =
      (n : ℕ) ^ (Fintype.card (M.openBoundaryPlaces j) - 1) := by
  classical
  by_cases hB : Nonempty (M.openBoundaryPlaces j)
  · exact natCard_finiteResidue_range M ε n j hj hn xi (Classical.choice hB)
  · let : IsEmpty (M.openBoundaryPlaces j) := ⟨fun p => hB ⟨p⟩⟩
    rw [Fintype.card_eq_zero, Nat.zero_sub, pow_zero]
    exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩

/-- A Galois-equivariant isomorphism of the geometric abelianizations already
suffices for the genus and truncated boundary count. The points are generic
geometric points of the actual coefficient-base-changed opens; no isomorphism
of the full arithmetic groups or preservation of a boundary subgroup is an input. -/
theorem equivariantGeometricAbelianization_geometricGenus_and_boundaryCard_of_sections
    (k κ : Type) [Field k] [NumberField k]
    [Field κ] [CharZero κ] [IsAlgClosed κ] [Algebra k κ] [IsSepClosure k κ]
    {C₁ C₂ U₁ U₂ : Scheme}
    [CompactSpace U₁] [QuasiSeparatedSpace U₁]
    [CompactSpace U₂] [QuasiSeparatedSpace U₂]
    (c₁ : C₁ ⟶ Spec (.of k)) (c₂ : C₂ ⟶ Spec (.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : U₁ ⟶ C₁) (i₂ : U₂ ⟶ C₂) [IsOpenImmersion i₁] [IsOpenImmersion i₂]
    [IsIntegral (Limits.pullback (specMap k κ) (i₁ ≫ c₁))]
    [IsIntegral (Limits.pullback (specMap k κ) (i₂ ≫ c₂))]
    (ε₁ : SchemeHomOver (𝟙 (Spec (.of k))) c₁)
    (ε₂ : SchemeHomOver (𝟙 (Spec (.of k))) c₂)
    {Ω₁ Ω₂ : Type} [Field Ω₁] [Field Ω₂] [IsSepClosed Ω₁] [IsSepClosed Ω₂]
    [Algebra (Limits.pullback (specMap k κ) (i₁ ≫ c₁)).functionField Ω₁]
    [Algebra (Limits.pullback (specMap k κ) (i₂ ≫ c₂)).functionField Ω₂]
    [IsSepClosure (Limits.pullback (specMap k κ) (i₁ ≫ c₁)).functionField Ω₁]
    [IsSepClosure (Limits.pullback (specMap k κ) (i₂ ≫ c₂)).functionField Ω₂]
    (eAb :
      TopologicalAbelianization (Aut (fiber
        ((Limits.pullback (specMap k κ) (i₁ ≫ c₁)).genericExtensionMorphism Ω₁))) ≃ₜ*
      TopologicalAbelianization (Aut (fiber
        ((Limits.pullback (specMap k κ) (i₂ ≫ c₂)).genericExtensionMorphism Ω₂))))
    (hAb : ∀ (σ : κ ≃ₐ[k] κ) z,
      eAb (geometricAbelianGaloisAction k κ U₁ (i₁ ≫ c₁)
        ((Limits.pullback (specMap k κ) (i₁ ≫ c₁)).genericExtensionMorphism Ω₁) σ z) =
      geometricAbelianGaloisAction k κ U₂ (i₂ ≫ c₂)
        ((Limits.pullback (specMap k κ) (i₂ ≫ c₂)).genericExtensionMorphism Ω₂) σ (eAb z)) :
    let j₁ := coefficientModelMap (specMap k κ) c₁ i₁ ≫
      (Limits.pullbackSymmetry (specMap k κ) c₁).hom
    let j₂ := coefficientModelMap (specMap k κ) c₂ i₂ ≫
      (Limits.pullbackSymmetry (specMap k κ) c₂).hom
    let B₁ := {x : closedPoints (Limits.pullback c₁ (specMap k κ) : Scheme) |
      x.val ∉ Set.range j₁}
    let B₂ := {x : closedPoints (Limits.pullback c₂ (specMap k κ) : Scheme) |
      x.val ∉ Set.range j₂}
    geometricGenus k c₁ = geometricGenus k c₂ ∧
      (Nat.card B₁ - 1 = Nat.card B₂ - 1) ∧
      ((0 < Nat.card B₁ ∧ 0 < Nat.card B₂) ∨
        2 ≤ Nat.card B₁ ∨ 2 ≤ Nat.card B₂ → Nat.card B₁ = Nat.card B₂) := by
  intro j₁ j₂ B₁ B₂
  classical
  let φ := specMap k κ
  let Y₁ := Limits.pullback φ (i₁ ≫ c₁)
  let Y₂ := Limits.pullback φ (i₂ ≫ c₂)
  let : CompactSpace Y₁ := inferInstance
  let : CompactSpace Y₂ := inferInstance
  let : IsIntegral (Limits.pullback φ c₁) :=
    IsIntegral.of_isIso (Limits.pullbackSymmetry c₁ φ).hom
  let : IsIntegral (Limits.pullback φ c₂) :=
    IsIntegral.of_isIso (Limits.pullbackSymmetry c₂ φ).hom
  let x₁ := Y₁.genericExtensionMorphism Ω₁
  let x₂ := Y₂.genericExtensionMorphism Ω₂
  have hW : ((compactificationAbelianizationMap
      (coefficientModelMap φ c₁ i₁) x₁).toMonoidHom.ker).map
        eAb.toMulEquiv.toMonoidHom =
      (compactificationAbelianizationMap
        (coefficientModelMap φ c₂ i₂) x₂).toMonoidHom.ker := by
    rw [literalArithmetic_compactification_kernel_eq_openCyclotomicSpan k κ c₁ i₁ ε₁,
      literalArithmetic_compactification_kernel_eq_openCyclotomicSpan k κ c₂ i₂ ε₂]
    exact openCyclotomicSpan_map_equiv
      (fun σ : κ ≃ₐ[k] κ =>
        EtaleFundamentalGroups.Inertia.primeToRootsCoefficientMap κ κ σ.toRingHom)
      (fun σ => geometricAbelianGaloisAction k κ U₁ (i₁ ≫ c₁) x₁ σ)
      (fun σ => geometricAbelianGaloisAction k κ U₂ (i₂ ≫ c₂) x₂ σ)
      eAb.toMulEquiv hAb
  let Cbar₁ := Limits.pullback c₁ φ
  let Cbar₂ := Limits.pullback c₂ φ
  let cbar₁ : Cbar₁ ⟶ Spec (.of κ) := Limits.pullback.snd c₁ φ
  let cbar₂ : Cbar₂ ⟶ Spec (.of κ) := Limits.pullback.snd c₂ φ
  let : Algebra κ Cbar₁.functionField := (baseToFunctionField cbar₁).toAlgebra
  let : Algebra κ Cbar₂.functionField := (baseToFunctionField cbar₂).toAlgebra
  let M₁ : CurveModel κ Cbar₁.functionField := literalCurveModel cbar₁
  let M₂ : CurveModel κ Cbar₂.functionField := literalCurveModel cbar₂
  obtain ⟨hc₁, hf₁⟩ := literalCurveModel_functionField_properties cbar₁
  obtain ⟨hc₂, hf₂⟩ := literalCurveModel_functionField_properties cbar₂
  let : IsCurveOver κ Cbar₁.functionField := hc₁
  let : IsCurveOver κ Cbar₂.functionField := hc₂
  let : Algebra.EssFiniteType κ Cbar₁.functionField := hf₁
  let : Algebra.EssFiniteType κ Cbar₂.functionField := hf₂
  let J₁ := coefficientModelMap φ c₁ i₁
  let J₂ := coefficientModelMap φ c₂ i₂
  let : IsOpenImmersion J₁ := coefficientOpen_isOpenImmersion φ c₁ i₁
  let : IsOpenImmersion J₂ := coefficientOpen_isOpenImmersion φ c₂ i₂
  let : IsOpenImmersion j₁ := by dsimp only [j₁]; infer_instance
  let : IsOpenImmersion j₂ := by dsimp only [j₂]; infer_instance
  let : IsOpenImmersion (show Y₁ ⟶ M₁.C from j₁) :=
    (inferInstance : IsOpenImmersion j₁)
  let : IsOpenImmersion (show Y₂ ⟶ M₂.C from j₂) :=
    (inferInstance : IsOpenImmersion j₂)
  have hj₁ : DenseRange j₁ :=
    j₁.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace j₁
  have hj₂ : DenseRange j₂ :=
    j₂.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace j₂
  have hk₁ : (compactificationAbelianizationMap j₁ x₁).toMonoidHom.ker =
      (compactificationAbelianizationMap J₁ x₁).toMonoidHom.ker :=
    compactificationAbelianizationMap_ker_postcomp_iso J₁ x₁
      (Limits.pullbackSymmetry φ c₁)
  have hk₂ : (compactificationAbelianizationMap j₂ x₂).toMonoidHom.ker =
      (compactificationAbelianizationMap J₂ x₂).toMonoidHom.ker :=
    compactificationAbelianizationMap_ker_postcomp_iso J₂ x₂
      (Limits.pullbackSymmetry φ c₂)
  have hW' : ((compactificationAbelianizationMap j₁ x₁).toMonoidHom.ker).map
      eAb.toMulEquiv.toMonoidHom =
      (compactificationAbelianizationMap j₂ x₂).toMonoidHom.ker := by
    rw [hk₁, hk₂]
    exact hW
  have hg := genus_eq_of_boundary_preserving_abelianization_equiv
    M₁ M₂ j₁ hj₁ j₂ hj₂ x₁ x₂ eAb hW'
  let EB₁ := boundaryPlacesEquivClosedPoints M₁ j₁
  let EB₂ := boundaryPlacesEquivClosedPoints M₂ j₂
  let : Fintype (M₁.openBoundaryPlaces j₁) := (M₁.openBoundaryPlaces_finite j₁).fintype
  let : Fintype (M₂.openBoundaryPlaces j₂) := (M₂.openBoundaryPlaces_finite j₂).fintype
  have hb₁ : Nat.card B₁ = Fintype.card (M₁.openBoundaryPlaces j₁) :=
    (Nat.card_congr EB₁).symm.trans Nat.card_eq_fintype_card
  have hb₂ : Nat.card B₂ = Fintype.card (M₂.openBoundaryPlaces j₂) :=
    (Nat.card_congr EB₂).symm.trans Nat.card_eq_fintype_card
  obtain ⟨δ₁⟩ := M₁.nonempty_rationalPoint
  obtain ⟨δ₂⟩ := M₂.nonempty_rationalPoint
  let n : ℕ+ := ⟨2, by decide⟩
  have hn : IsUnit ((n : ℕ) : κ) :=
    isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr n.ne_zero)
  have hrange := (finiteResidue_card_eq_of_abelianization_equiv
    M₁ M₂ j₁ hj₁ j₂ hj₂ x₁ x₂ eAb hW' n hn).2
  rw [natCard_finiteResidue_range_eq_pow_boundaryCard_sub_one M₁ δ₁ n j₁ hj₁ hn x₁,
    natCard_finiteResidue_range_eq_pow_boundaryCard_sub_one M₂ δ₂ n j₂ hj₂ hn x₂] at hrange
  change 2 ^ (Fintype.card (M₁.openBoundaryPlaces j₁) - 1) =
    2 ^ (Fintype.card (M₂.openBoundaryPlaces j₂) - 1) at hrange
  have hlog := congrArg (Nat.log 2) hrange
  rw [Nat.log_pow (by decide : 1 < 2), Nat.log_pow (by decide : 1 < 2)] at hlog
  have hpred : Nat.card B₁ - 1 = Nat.card B₂ - 1 := by
    rw [hb₁, hb₂]
    exact hlog
  refine ⟨?_, hpred, ?_⟩
  · rw [geometricGenus_eq_literal_genus k κ c₁ ε₁,
      geometricGenus_eq_literal_genus k κ c₂ ε₂]
    exact hg
  · rintro (⟨h₁, h₂⟩ | h₁ | h₂) <;> omega

/-- The original full arithmetic groups determine the geometric genus and
the number of punctures in positive genus, or when both boundaries are
positive or either has at least two points. Only the actual curves,
compactification sections, arbitrary geometric base points and an isomorphism
over the fixed absolute Galois group are supplied. No boundary-preservation,
CurveModel, Jacobian or comparison package is an input. -/
theorem arithmeticEquiv_geometricGenus_and_boundaryCard_of_sections
    (k κ : Type) [Field k] [NumberField k]
    [Field κ] [CharZero κ] [IsAlgClosed κ] [Algebra k κ] [IsSepClosure k κ]
    {C₁ C₂ U₁ U₂ : Scheme}
    [CompactSpace U₁] [QuasiSeparatedSpace U₁]
    [CompactSpace U₂] [QuasiSeparatedSpace U₂]
    (c₁ : C₁ ⟶ Spec (.of k)) (c₂ : C₂ ⟶ Spec (.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : U₁ ⟶ C₁) (i₂ : U₂ ⟶ C₂) [IsOpenImmersion i₁] [IsOpenImmersion i₂]
    (ε₁ : SchemeHomOver (𝟙 (Spec (.of k))) c₁)
    (ε₂ : SchemeHomOver (𝟙 (Spec (.of k))) c₂)
    {Ω₁ Ω₂ : Type} [Field Ω₁] [Field Ω₂] [IsSepClosed Ω₁] [IsSepClosed Ω₂]
    (xi₁ : Spec (.of Ω₁) ⟶ U₁) (xi₂ : Spec (.of Ω₂) ⟶ U₂)
    (eP : π₁ᵉᵗ(xi₁) ≃ₜ* π₁ᵉᵗ(xi₂))
    (hP : ∀ γ, arithmeticFundamentalGroupHom k κ (i₂ ≫ c₂) xi₂ (eP γ) =
      arithmeticFundamentalGroupHom k κ (i₁ ≫ c₁) xi₁ γ) :
    let j₁ := coefficientModelMap (specMap k κ) c₁ i₁ ≫
      (Limits.pullbackSymmetry (specMap k κ) c₁).hom
    let j₂ := coefficientModelMap (specMap k κ) c₂ i₂ ≫
      (Limits.pullbackSymmetry (specMap k κ) c₂).hom
    let B₁ := {x : closedPoints (Limits.pullback c₁ (specMap k κ) : Scheme) |
      x.val ∉ Set.range j₁}
    let B₂ := {x : closedPoints (Limits.pullback c₂ (specMap k κ) : Scheme) |
      x.val ∉ Set.range j₂}
    geometricGenus k c₁ = geometricGenus k c₂ ∧
      (Nat.card B₁ - 1 = Nat.card B₂ - 1) ∧
      (0 < geometricGenus k c₁ ∨ (0 < Nat.card B₁ ∧ 0 < Nat.card B₂) ∨
        2 ≤ Nat.card B₁ ∨ 2 ≤ Nat.card B₂ → Nat.card B₁ = Nat.card B₂) := by
  intro j₁ j₂ B₁ B₂
  classical
  let : Nonempty U₁ := ⟨xi₁ (Classical.choice (inferInstance : Nonempty (Spec (.of Ω₁))))⟩
  let : Nonempty U₂ := ⟨xi₂ (Classical.choice (inferInstance : Nonempty (Spec (.of Ω₂))))⟩
  let : Surjective (i₁ ≫ c₁) := ⟨fun y => ⟨Nonempty.some inferInstance, Subsingleton.elim _ y⟩⟩
  let : Surjective (i₂ ≫ c₂) := ⟨fun y => ⟨Nonempty.some inferInstance, Subsingleton.elim _ y⟩⟩
  let : GeometricallyIntegral (i₁ ≫ c₁) :=
    GeometricallyIntegral.comp_of_isOpenImmersion i₁ c₁
  let : GeometricallyIntegral (i₂ ≫ c₂) :=
    GeometricallyIntegral.comp_of_isOpenImmersion i₂ c₂
  have : GeometricallyConnected (i₁ ≫ c₁) :=
    GeometricallyIrreducible.geometricallyConnected (i₁ ≫ c₁)
  have : GeometricallyConnected (i₂ ≫ c₂) :=
    GeometricallyIrreducible.geometricallyConnected (i₂ ≫ c₂)
  let φ := specMap k κ
  let Y₁ := Limits.pullback φ (i₁ ≫ c₁)
  let Y₂ := Limits.pullback φ (i₂ ≫ c₂)
  let : IsIntegral Y₁ :=
    IsIntegral.of_isIso (Limits.pullbackSymmetry (i₁ ≫ c₁) φ).hom
  let : IsIntegral Y₂ :=
    IsIntegral.of_isIso (Limits.pullbackSymmetry (i₂ ≫ c₂) φ).hom
  let : CompactSpace Y₁ := inferInstance
  let : CompactSpace Y₂ := inferInstance
  let : IsIntegral (Limits.pullback φ c₁) :=
    IsIntegral.of_isIso (Limits.pullbackSymmetry c₁ φ).hom
  let : IsIntegral (Limits.pullback φ c₂) :=
    IsIntegral.of_isIso (Limits.pullbackSymmetry c₂ φ).hom
  let O₁ := SeparableClosure Y₁.functionField
  let O₂ := SeparableClosure Y₂.functionField
  let : IsSepClosed O₁ := IsSepClosure.sep_closed Y₁.functionField
  let : IsSepClosed O₂ := IsSepClosure.sep_closed Y₂.functionField
  let x₁ := Y₁.genericExtensionMorphism O₁
  let x₂ := Y₂.genericExtensionMorphism O₂
  let z₁ := x₁ ≫ Limits.pullback.snd φ (i₁ ≫ c₁)
  let z₂ := x₂ ≫ Limits.pullback.snd φ (i₂ ≫ c₂)
  obtain ⟨t₁, ht₁⟩ := exists_arithmetic_preserving_fiberIso k κ (i₁ ≫ c₁) xi₁ z₁
  obtain ⟨t₂, ht₂⟩ := exists_arithmetic_preserving_fiberIso k κ (i₂ ≫ c₂) xi₂ z₂
  let T₁ := continuousConjAut t₁
  let T₂ := continuousConjAut t₂
  let E := T₁.symm.trans (eP.trans T₂)
  have hE : ∀ γ, arithmeticFundamentalGroupHom k κ (i₂ ≫ c₂) z₂ (E γ) =
      arithmeticFundamentalGroupHom k κ (i₁ ≫ c₁) z₁ γ := by
    intro γ
    change arithmeticFundamentalGroupHom k κ (i₂ ≫ c₂) z₂
      (T₂ (eP (T₁.symm γ))) = _
    rw [ht₂, hP, ← ht₁, T₁.apply_symm_apply]
  obtain ⟨eΔ, _hΔ, hAb⟩ := exists_geometricEquiv_equivariant_of_arithmeticEquiv
    k κ U₁ U₂ (i₁ ≫ c₁) (i₂ ≫ c₂) x₁ x₂ E hE
  obtain ⟨hg, hpred, hpositive⟩ :=
    equivariantGeometricAbelianization_geometricGenus_and_boundaryCard_of_sections
      k κ c₁ c₂ i₁ i₂ ε₁ ε₂ (TopologicalAbelianization.congr eΔ) hAb
  refine ⟨hg, hpred, ?_⟩
  rintro (hgpos | hboundary)
  · let Cbar₁ := Limits.pullback c₁ φ
    let Cbar₂ := Limits.pullback c₂ φ
    let cbar₁ : Cbar₁ ⟶ Spec (.of κ) := Limits.pullback.snd c₁ φ
    let cbar₂ : Cbar₂ ⟶ Spec (.of κ) := Limits.pullback.snd c₂ φ
    let : Algebra κ Cbar₁.functionField := (baseToFunctionField cbar₁).toAlgebra
    let : Algebra κ Cbar₂.functionField := (baseToFunctionField cbar₂).toAlgebra
    let M₁ : CurveModel κ Cbar₁.functionField := literalCurveModel cbar₁
    let M₂ : CurveModel κ Cbar₂.functionField := literalCurveModel cbar₂
    have hg₁ : 0 < genusFF κ Cbar₁.functionField := by
      rw [← geometricGenus_eq_literal_genus k κ c₁ ε₁]
      exact hgpos
    have hg₂ : 0 < genusFF κ Cbar₂.functionField := by
      rw [← geometricGenus_eq_literal_genus k κ c₂ ε₂, ← hg]
      exact hgpos
    have : IsOpenImmersion (coefficientModelMap φ c₁ i₁) :=
      coefficientOpen_isOpenImmersion φ c₁ i₁
    have : IsOpenImmersion (coefficientModelMap φ c₂ i₂) :=
      coefficientOpen_isOpenImmersion φ c₂ i₂
    have : IsOpenImmersion j₁ := by dsimp only [j₁]; infer_instance
    have : IsOpenImmersion j₂ := by dsimp only [j₂]; infer_instance
    let : IsOpenImmersion (show Y₁ ⟶ M₁.C from j₁) :=
      (inferInstance : IsOpenImmersion j₁)
    let : IsOpenImmersion (show Y₂ ⟶ M₂.C from j₂) :=
      (inferInstance : IsOpenImmersion j₂)
    have hzero := GeometricFundamentalGroup.openBoundary_card_eq_zero_iff_of_positive_genus
      M₁ M₂ hg₁ hg₂ j₁ j₂ x₁ x₂ eΔ
    have hb₁ : Nat.card (M₁.openBoundaryPlaces j₁) = Nat.card B₁ :=
      Nat.card_congr (boundaryPlacesEquivClosedPoints M₁ j₁)
    have hb₂ : Nat.card (M₂.openBoundaryPlaces j₂) = Nat.card B₂ :=
      Nat.card_congr (boundaryPlacesEquivClosedPoints M₂ j₂)
    rw [hb₁, hb₂] at hzero
    by_cases h₁ : Nat.card B₁ = 0
    · exact h₁.trans (hzero.mp h₁).symm
    · have h₂ : Nat.card B₂ ≠ 0 := fun h => h₁ (hzero.mpr h)
      exact hpositive (Or.inl ⟨Nat.pos_of_ne_zero h₁, Nat.pos_of_ne_zero h₂⟩)
  · exact hpositive hboundary

end AnabelianGeometry.WeightFiltration
