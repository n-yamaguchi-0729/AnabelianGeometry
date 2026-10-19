/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.GeometricFundamentalGroup.ProperCurveSlim
import Nyll.AnabelianGeometry.GeometricFundamentalGroup.OpenCurveSlim
import Nyll.AnabelianGeometry.GeometricFundamentalGroup.OpenCoverH1Numerics
import Nyll.EtaleFundamentalGroups.GeometricFiber.GeometricAbelianGaloisAction
import Nyll.EtaleFundamentalGroups.GeometricFiber.PullbackEquivalence
import Nyll.EtaleFundamentalGroups.GaloisCategories.FiberIso
import Nyll.AlgebraicCurves.Models.Construction.LiteralArithmeticCurveModel
import Nyll.AlgebraicCurves.Geometry.Curves.GeometricGenus
import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.ModelOverlap
import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.CoefficientPullback
import Nyll.SchemeTheory.FunctionFields.GeometricIntegrality
import Nyll.SchemeTheory.Morphisms.GeometricallyIrreducibleConnected
import Nyll.Yamaguchi26AbfaithfulGalois.FieldExamples.FinitelyGeneratedCharZero
import Nyll.ProCGroups.FiniteStepSolvableQuotients.Faithful
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Trivial centers of arithmetic hyperbolic curve groups

The arithmetic exact sequence reduces the claim to the actual geometric
curve group and the absolute Galois group. Geometric slimness supplies the
first center calculation; the finitely generated field theorem supplies
the second. The compactification may have no rational point, and the
geometric model and base point are constructed internally.

This concerns the full arithmetic fundamental group in characteristic zero.
It does not assert center-freeness of arbitrary finite-step quotients.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve EtaleFundamentalGroups
open CategoryTheory.PreGaloisCategory
open AlgebraicGeometry.SmoothProperCurve AlgebraicGeometry.FiniteEtale
open ProCGroups.FiniteStepSolvableQuotients

namespace AnabelianGeometry.ArithmeticIsomorphisms

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

private theorem center_eq_bot_of_mulEquiv
    {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (hH : Subgroup.center H = ⊥) : Subgroup.center G = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  have he : e z ∈ Subgroup.center H := by
    rw [Subgroup.mem_center_iff]
    intro a
    obtain ⟨b, rfl⟩ := e.surjective a
    exact (map_mul e b z).symm.trans
      ((congrArg e (Subgroup.mem_center_iff.mp hz b)).trans (map_mul e z b))
  have he1 : e z = 1 := Subgroup.mem_bot.mp (hH ▸ he)
  exact e.injective (he1.trans (map_one e).symm)

private theorem center_eq_bot_of_kernel_and_quotient
    {P G : Type*} [Group P] [Group G] (q : P →* G)
    (hq : Function.Surjective q)
    (hkernel : Subgroup.center q.ker = ⊥)
    (hquotient : Subgroup.center G = ⊥) : Subgroup.center P = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  have hqz : q z ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro a
    obtain ⟨b, rfl⟩ := hq a
    exact (map_mul q b z).symm.trans
      ((congrArg q (Subgroup.mem_center_iff.mp hz b)).trans (map_mul q z b))
  have hzker : z ∈ q.ker := Subgroup.mem_bot.mp (hquotient ▸ hqz)
  let n : q.ker := ⟨z, hzker⟩
  have hn : n ∈ Subgroup.center q.ker := by
    rw [Subgroup.mem_center_iff]
    intro a
    exact Subtype.ext (Subgroup.mem_center_iff.mp hz a.val)
  have hn1 : n = 1 := Subgroup.mem_bot.mp (hkernel ▸ hn)
  exact congrArg (fun x : q.ker => x.val) hn1

/-- The full arithmetic fundamental group of a hyperbolic curve over a
finitely generated characteristic-zero field has trivial center. Only the
original compactification, open immersion, and geometric base point are
inputs; no geometric model, rational section, or center calculation is assumed. -/
theorem arithmeticFundamentalGroup_center_eq_bot
    (k : Type) [Field k] [CharZero k] (hfg : Field.FG k)
    {C U : Scheme} (c : C ⟶ Spec (.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (i : U ⟶ C) [IsOpenImmersion i]
    {Ω : Type} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ U)
    (hhyperbolic :
      let j := coefficientModelMap (specMap k (AlgebraicClosure k)) c i ≫
        (Limits.pullbackSymmetry (specMap k (AlgebraicClosure k)) c).hom
      0 < 2 * (geometricGenus k c : ℤ) +
        (Nat.card {x : closedPoints (Limits.pullback c (specMap k (AlgebraicClosure k)) : Scheme) |
          x.val ∉ Set.range j} : ℤ) - 2) :
    Subgroup.center (π₁ᵉᵗ(xi)) = ⊥ := by
  classical
  let κ := AlgebraicClosure k
  let φ := specMap k κ
  let Y := Limits.pullback φ (i ≫ c)
  let Z := Limits.pullback c φ
  let cκ := baseChange k c κ
  let j := coefficientModelMap φ c i ≫ (Limits.pullbackSymmetry φ c).hom
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian c
  have : IsLocallyNoetherian U := isLocallyNoetherian_of_isOpenImmersion i
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace c
  have : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace i
  have : QuasiSeparatedSpace U := inferInstance
  have : Nonempty U := ⟨xi (Classical.choice (inferInstance : Nonempty (Spec (.of Ω))))⟩
  have : Surjective (i ≫ c) :=
    ⟨fun y => ⟨Nonempty.some inferInstance, Subsingleton.elim _ y⟩⟩
  have : GeometricallyIntegral (i ≫ c) :=
    GeometricallyIntegral.comp_of_isOpenImmersion i c
  have : GeometricallyConnected (i ≫ c) :=
    GeometricallyIrreducible.geometricallyConnected (i ≫ c)
  have : ConnectedSpace U :=
    GeometricallyConnected.connectedSpace_of_subsingleton (i ≫ c)
  have : IsIntegral Y := inferInstance
  have : IsIntegral Z := inferInstance
  have : IsProper cκ := inferInstance
  have : SmoothOfRelativeDimension 1 cκ := inferInstance
  have : IsOpenImmersion (coefficientModelMap φ c i) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := (show MorphismProperty Scheme from IsOpenImmersion))
      (coefficientBaseChange_isPullback φ c i).flip (inferInstance : IsOpenImmersion i)
  have : IsOpenImmersion j := by dsimp only [j]; infer_instance
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian cκ
  have : IsLocallyNoetherian Y := isLocallyNoetherian_of_isOpenImmersion j
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace cκ
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace j
  have : Smooth cκ := SmoothOfRelativeDimension.smooth 1 cκ
  have : IsIntegrallyClosed Γ(Spec (.of κ), ⊤) :=
    IsIntegrallyClosed.of_equiv (Scheme.ΓSpecIso (.of κ)).symm.commRingCatIsoToRingEquiv
  have : IsNormalIntegral Z := IsNormalIntegral.of_stalks Z
    (fun z => (Smooth.isDomain_and_isIntegrallyClosed_stalk cκ z).2)
  have : IsNormalIntegral Y := IsNormalIntegral.of_isOpenImmersion j
  let : Algebra κ Z.functionField := (baseToFunctionField cκ).toAlgebra
  have : IsCurveOver κ Z.functionField := (literalCurveModel_functionField_properties cκ).1
  let M := literalCurveModel cκ
  let jM : Y ⟶ M.C := j
  have : IsOpenImmersion jM := inferInstanceAs (IsOpenImmersion j)
  have : QuasiCompact jM := inferInstanceAs (QuasiCompact j)
  let xκ := Y.genericExtensionMorphism (AlgebraicClosure Y.functionField)
  let B := M.openBoundaryPlaces jM
  let eB : B ≃ {x : closedPoints Z // x.val ∉ Set.range jM} :=
    { toFun := fun v => ⟨M.placeEquiv.symm v.val, v.property⟩
      invFun := fun x => ⟨M.placeEquiv x.val, by
        change (M.placeEquiv.symm (M.placeEquiv x.val)).val ∉ Set.range jM
        exact (congrArg (fun y : closedPoints M.C => y.val ∉ Set.range jM)
          (M.placeEquiv.symm_apply_apply x.val)).mpr x.property⟩
      left_inv := fun v => Subtype.ext (M.placeEquiv.apply_symm_apply v.val)
      right_inv := fun x => Subtype.ext (M.placeEquiv.symm_apply_apply x.val) }
  have hB : Nat.card B = Nat.card {x : closedPoints Z // x.val ∉ Set.range jM} :=
    Nat.card_congr eB
  have hh : 0 < 2 * (genusFF κ Z.functionField : ℤ) + (Nat.card B : ℤ) - 2 := by
    rw [hB]
    exact hhyperbolic
  have hcenter : Subgroup.center (π₁ᵉᵗ(xκ)) = ⊥ := by
    by_cases hb : Nonempty B
    · have hfinite := M.openBoundaryPlaces_finite jM
      let : Fintype B := hfinite.fintype
      have hcard : hfinite.toFinset.card = Nat.card B := by
        rw [Set.Finite.card_toFinset, Nat.card_eq_fintype_card]
      apply center_eq_bot_of_isSlim
      apply isSlim_fundamentalGroup_open_hyperbolic M jM
        (show (M.openBoundaryPlaces jM).Nonempty from ⟨(Classical.choice hb).val,
          (Classical.choice hb).property⟩) _ xκ
      rw [hcard]
      exact hh
    · have : IsEmpty B := ⟨fun v => hb ⟨v⟩⟩
      have hz : Nat.card B = 0 := Nat.card_of_isEmpty
      have : IsIso jM := isIso_of_openBoundary_card_eq_zero M jM hz
      have hg : 2 ≤ genusFF κ Z.functionField := by rw [hz] at hh; omega
      let E : FiniteEtale M.C ≌ FiniteEtale Y :=
        MorphismProperty.Over.pullbackIso (@IsFiniteEtale : MorphismProperty Scheme) ⊤
          (asIso jM).symm
      have : (FiniteEtale.pullback jM).IsEquivalence := E.isEquivalence_functor
      exact center_eq_bot_of_mulEquiv
        (fundamentalGroupEquivOfPullbackEquivalence jM xκ).toMulEquiv
        (center_eq_bot_of_isSlim (isSlim_fundamentalGroup_proper_hyperbolic M hg (xκ ≫ jM)))
  let a := arithmeticFundamentalGroupHom k κ (i ≫ c)
    (xκ ≫ Limits.pullback.snd φ (i ≫ c))
  let E := geometricFundamentalGroupKernelEquiv k κ U (i ≫ c) xκ
  have hkernel : Subgroup.center a.toMonoidHom.ker = ⊥ :=
    center_eq_bot_of_mulEquiv E.symm.toMulEquiv hcenter
  have hquotient : Subgroup.center Gal(κ/k) = ⊥ :=
    center_eq_bot_of_isAbFaithful
      (Yamaguchi26AbfaithfulGalois.finitelyGenerated_charZero_isAbFaithful k hfg)
  have harith := center_eq_bot_of_kernel_and_quotient a.toMonoidHom
    (arithmetic_exactSequence_of_isSepClosure k κ U (i ≫ c) xκ).2.1 hkernel hquotient
  let t := (nonempty_fiber_iso xi (xκ ≫ Limits.pullback.snd φ (i ≫ c))).some
  exact center_eq_bot_of_mulEquiv (continuousConjAut t).toMulEquiv harith

end AnabelianGeometry.ArithmeticIsomorphisms
