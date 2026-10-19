/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.IntrinsicBoundaryWeight
import Nyll.AlgebraicCurves.Models.Construction.LiteralArithmeticCurveModel
import Nyll.AlgebraicCurves.Geometry.Picard.Representability.Existence
import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.CoefficientPullback
import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.ModelOverlap
import Nyll.SchemeTheory.FunctionFields.OpenImmersion

/-!
# Applying the existing weight theorem to the literal arithmetic curve

All auxiliary model, Picard, field-tower and normalization-prime data are
constructed here. The input is the actual arithmetic compactification and
its section. The geometric open, its function-field embedding into the
original Omega and its generic point are unchanged.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AlgebraicCurve
open AlgebraicGeometry.FiniteEtale AlgebraicGeometry.SmoothProperCurve
open AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
open SchemeTheory EtaleFundamentalGroups EtaleFundamentalGroups.Inertia
open ProCGroups.Abelian TopologicalSpace

namespace AnabelianGeometry.WeightFiltration

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

/-- The coefficient extension of an actual open immersion is open. This
small helper keeps the pullback comparison opaque in the weight proof. -/
private theorem coefficientModelMap_isOpenImmersion
    {T T' C U : Scheme} (phi : T' ⟶ T) (c : C ⟶ T)
    (i : U ⟶ C) [IsOpenImmersion i] :
    IsOpenImmersion (coefficientModelMap phi c i) := by
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := (show MorphismProperty Scheme from @IsOpenImmersion))
    (coefficientBaseChange_isPullback phi c i).flip (inferInstance : IsOpenImmersion i)

/-- The existing intrinsic weight theorem, with all its auxiliary geometry
supplied by the actual arithmetic curve and its literal compactification. -/
theorem literalArithmetic_compactification_kernel_eq_openCyclotomicSpan
    (E kappa : Type) [Field E] [NumberField E]
    [Field kappa] [CharZero kappa] [IsAlgClosed kappa]
    [Algebra E kappa] [IsSepClosure E kappa]
    {C U : Scheme} [CompactSpace U] [QuasiSeparatedSpace U]
    (c : C ⟶ Spec (.of E)) (i : U ⟶ C) [IsOpenImmersion i]
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    [IsIntegral (Limits.pullback (specMap E kappa) (i ≫ c))]
    {Omega : Type} [Field Omega] [IsSepClosed Omega]
    [Algebra (Limits.pullback (specMap E kappa) (i ≫ c)).functionField Omega]
    [IsSepClosure (Limits.pullback (specMap E kappa) (i ≫ c)).functionField Omega]
    (epsilon : SchemeHomOver (𝟙 (Spec (.of E))) c) :
    let Y := Limits.pullback (specMap E kappa) (i ≫ c)
    let J := coefficientModelMap (specMap E kappa) c i
    let xi := Y.genericExtensionMorphism Omega
    (compactificationAbelianizationMap J xi).toMonoidHom.ker =
      openCyclotomicSpan
        (fun sigma : kappa ≃ₐ[E] kappa =>
          primeToRootsCoefficientMap kappa kappa sigma.toRingHom)
        (fun sigma => geometricAbelianGaloisAction E kappa U (i ≫ c) xi sigma) := by
  classical
  let phi := specMap E kappa
  let Y : Scheme := Limits.pullback phi (i ≫ c)
  let Cbar : Scheme := Limits.pullback c phi
  let cbar : Cbar ⟶ Spec (.of kappa) := Limits.pullback.snd c phi
  let J : Y ⟶ Limits.pullback phi c := coefficientModelMap phi c i
  let j : Y ⟶ Cbar := J ≫ (pullbackSymmetry phi c).hom
  let : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace c
  let : QuasiSeparatedSpace C := quasiSeparatedSpace_of_quasiSeparated c
  let : CompactSpace Y := inferInstance
  let : IsIntegral Cbar := isIntegral_pullback_Spec_field E c phi
  let : IsIntegral (Limits.pullback phi c) :=
    IsIntegral.of_isIso (pullbackSymmetry c phi).hom
  let : IsProper cbar := inferInstance
  let : SmoothOfRelativeDimension 1 cbar := inferInstance
  let : IsOpenImmersion J := coefficientModelMap_isOpenImmersion phi c i
  let : IsOpenImmersion j := by dsimp only [j]; infer_instance
  have hj : DenseRange j :=
    j.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace j
  let : Algebra kappa Cbar.functionField := (baseToFunctionField cbar).toAlgebra
  let M : CurveModel kappa Cbar.functionField := literalCurveModel cbar
  let : IsOpenImmersion (show Y ⟶ M.C from j) :=
    (inferInstance : IsOpenImmersion j)
  obtain ⟨hcurve, hfinite⟩ := literalCurveModel_functionField_properties cbar
  let : IsCurveOver kappa Cbar.functionField := hcurve
  let : Algebra.EssFiniteType kappa Cbar.functionField := hfinite
  let eC : M.C ≅ Limits.pullback c phi := Iso.refl Cbar
  have heC : eC.hom ≫ Limits.pullback.snd c phi = M.toBase :=
    Category.id_comp cbar
  have hproj : j ≫ eC.hom ≫ Limits.pullback.fst c phi =
      Limits.pullback.snd phi (i ≫ c) ≫ i := by
    simp only [eC, Iso.refl_hom, Category.id_comp, j, Category.assoc,
      pullbackSymmetry_hom_comp_fst]
    exact Limits.pullback.lift_snd _ _ _
  have hbase : j ≫ M.toBase = Limits.pullback.fst phi (i ≫ c) := by
    change (J ≫ (pullbackSymmetry phi c).hom) ≫ Limits.pullback.snd c phi = _
    rw [Category.assoc, pullbackSymmetry_hom_comp_snd]
    exact Limits.pullback.lift_fst _ _ _
  let e := j.functionFieldRingEquivOfIsOpenImmersion
  let : Algebra Cbar.functionField Y.functionField := e.toRingHom.toAlgebra
  have hfield : algebraMap Cbar.functionField Y.functionField =
      (j.functionFieldMap hj).comp M.ffEquiv.toRingHom := rfl
  let : Algebra Cbar.functionField Omega :=
    ((algebraMap Y.functionField Omega).comp e.toRingHom).toAlgebra
  let : IsScalarTower Cbar.functionField Y.functionField Omega :=
    IsScalarTower.of_algebraMap_eq' rfl
  have he : (algebraMap Cbar.functionField Omega).comp e.symm.toRingHom =
      (RingEquiv.refl Omega).toRingHom.comp (algebraMap Y.functionField Omega) := by
    apply RingHom.ext
    intro a
    change algebraMap Y.functionField Omega (e (e.symm a)) =
      algebraMap Y.functionField Omega a
    rw [e.apply_symm_apply]
  let : Algebra.IsSeparable Cbar.functionField Omega :=
    Algebra.IsSeparable.of_equiv_equiv e.symm (RingEquiv.refl Omega) he
  let : IsSepClosure Cbar.functionField Omega :=
    ⟨inferInstance, inferInstance⟩
  let : Algebra kappa Omega :=
    ((algebraMap Cbar.functionField Omega).comp
      (algebraMap kappa Cbar.functionField)).toAlgebra
  let : IsScalarTower kappa Cbar.functionField Omega :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : CharZero Omega :=
    charZero_of_injective_algebraMap (algebraMap kappa Omega).injective
  let : IsAlgClosed Omega := inferInstance
  let (p : M.openBoundaryPlaces j) : Algebra p.val.toValuationSubring Omega :=
    Algebra.ofSubsemiring p.val.toValuationSubring
  let (p : M.openBoundaryPlaces j) :
      IsScalarTower p.val.toValuationSubring Cbar.functionField Omega :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let (p : M.openBoundaryPlaces j) :
      IsScalarTower kappa p.val.toValuationSubring Omega := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    change algebraMap kappa Omega a =
      algebraMap Cbar.functionField Omega (algebraMap kappa Cbar.functionField a)
    exact IsScalarTower.algebraMap_apply kappa Cbar.functionField Omega a
  let : Fintype (M.openBoundaryPlaces j) := (M.openBoundaryPlaces_finite j).fintype
  choose Q hQ using fun p : M.openBoundaryPlaces j => by
    let : Nontrivial (normalizationCommAlgCat p.val.toValuationSubring Omega) :=
      (inferInstance : Nontrivial (integralClosure p.val.toValuationSubring Omega))
    exact Ideal.exists_maximal (normalizationCommAlgCat p.val.toValuationSubring Omega)
  let (p : M.openBoundaryPlaces j) : (Q p).IsMaximal := hQ p
  obtain ⟨D, ⟨hD⟩, hSmooth, hProper, hConnected⟩ :=
    exists_representsRelSubPic_of_field E c epsilon
  let : Smooth D.toBase := hSmooth
  let : IsProper D.toBase := hProper
  let : GeometricallyConnected D.toBase := hConnected
  exact compactification_kernel_eq_openCyclotomicSpan
    E kappa c i M eC heC j hj hproj hbase hfield Q epsilon D hD

end AnabelianGeometry.WeightFiltration
