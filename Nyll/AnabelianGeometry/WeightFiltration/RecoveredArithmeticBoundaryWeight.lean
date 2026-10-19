/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.LiteralArithmeticBoundaryWeight
import Nyll.AlgebraicCurves.Geometry.Schemes.Points.FiniteIntermediateFieldSection
import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.ConstantFieldTower
import Nyll.SchemeTheory.FunctionFields.GenericFieldSourceNaturality

/-!
# Actual weight identification after a finite coefficient refinement

The original recovered geometric scheme W and its function-field embedding
in Omega are kept fixed. Only the coefficient field is refined inside the
fixed kappa. The recovery is the literal tower comparison followed by the
original R, and the base point is pulled back by its actual inverse.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AlgebraicCurve
open AlgebraicGeometry.FiniteEtale AlgebraicGeometry.SmoothProperCurve
open NeronModelInfra SchemeTheory EtaleFundamentalGroups
open EtaleFundamentalGroups.Inertia ProCGroups.Abelian TopologicalSpace

namespace AnabelianGeometry.WeightFiltration

private theorem isSepClosure_of_ringEquiv
    {K L Omega : Type} [Field K] [Field L] [Field Omega]
    [Algebra L Omega] [IsSepClosure L Omega] (e : K ≃+* L) :
    letI : Algebra K Omega :=
      ((algebraMap L Omega).comp e.toRingHom).toAlgebra
    IsSepClosure K Omega := by
  let : Algebra K Omega :=
    ((algebraMap L Omega).comp e.toRingHom).toAlgebra
  have he : (algebraMap K Omega).comp e.symm.toRingHom =
      (RingEquiv.refl Omega).toRingHom.comp (algebraMap L Omega) := by
    ext a
    change algebraMap L Omega (e (e.symm a)) = algebraMap L Omega a
    rw [e.apply_symm_apply]
  exact ⟨IsSepClosure.sep_closed L,
    Algebra.IsSeparable.of_equiv_equiv e.symm (RingEquiv.refl Omega) he⟩

/-- Opaque generic-point computation for arbitrary actual scheme objects. -/
private theorem genericPoint_of_recovery_inverse
    {Y W : Scheme} [IsIntegral Y] [IsIntegral W] (R : Y ≅ W)
    {Omega : Type} [Field Omega] [Algebra W.functionField Omega] :
    let e := R.inv.functionFieldRingEquivOfIsOpenImmersion
    letI : Algebra Y.functionField Omega :=
      ((algebraMap W.functionField Omega).comp e.toRingHom).toAlgebra
    Y.genericExtensionMorphism Omega = W.genericExtensionMorphism Omega ≫ R.inv := by
  let e := R.inv.functionFieldRingEquivOfIsOpenImmersion
  let : Algebra Y.functionField Omega :=
    ((algebraMap W.functionField Omega).comp e.toRingHom).toAlgebra
  let hR : DenseRange R.inv := R.inv.homeomorph.surjective.denseRange
  change Spec.map (CommRingCat.ofHom
    ((algebraMap W.functionField Omega).comp e.toRingHom)) ≫
      Y.fromSpecStalk (genericPoint Y) = _
  calc
    _ = Spec.map (CommRingCat.ofHom (algebraMap W.functionField Omega)) ≫
        Spec.map (CommRingCat.ofHom (R.inv.functionFieldMap hR)) ≫
          Y.fromSpecStalk (genericPoint Y) := by
      change Spec.map (CommRingCat.ofHom (R.inv.functionFieldMap hR) ≫
        CommRingCat.ofHom (algebraMap W.functionField Omega)) ≫ _ = _
      rw [Spec.map_comp, Category.assoc]
    _ = Spec.map (CommRingCat.ofHom (algebraMap W.functionField Omega)) ≫
        W.fromSpecStalk (genericPoint W) ≫ R.inv := by
      rw [Spec_functionFieldMap_fromSpecStalk R.inv hR]
    _ = W.genericExtensionMorphism Omega ≫ R.inv := (Category.assoc _ _ _).symm

/-- Apply the existing weight theorem at the original recovered point.
The embedding into Omega is transported through the actual inverse R.inv. -/
theorem recoveredArithmetic_compactification_kernel_eq_openCyclotomicSpan
    (E kappa : Type) [Field E] [NumberField E]
    [Field kappa] [CharZero kappa] [IsAlgClosed kappa]
    [Algebra E kappa] [IsSepClosure E kappa]
    {C U W : Scheme} [CompactSpace U] [QuasiSeparatedSpace U] [IsIntegral W]
    (c : C ⟶ Spec (.of E)) (i : U ⟶ C) [IsOpenImmersion i]
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (R : Limits.pullback (specMap E kappa) (i ≫ c) ≅ W)
    {Omega : Type} [Field Omega] [IsSepClosed Omega]
    [Algebra W.functionField Omega] [IsSepClosure W.functionField Omega]
    (epsilon : SchemeHomOver (𝟙 (Spec (.of E))) c) :
    letI : IsIntegral (Limits.pullback (specMap E kappa) (i ≫ c)) :=
      IsIntegral.of_isIso R.inv
    let x := W.genericExtensionMorphism Omega ≫ R.inv
    let J := coefficientModelMap (specMap E kappa) c i
    (compactificationAbelianizationMap J x).toMonoidHom.ker =
      openCyclotomicSpan
        (fun sigma : kappa ≃ₐ[E] kappa =>
          primeToRootsCoefficientMap kappa kappa sigma.toRingHom)
        (fun sigma => geometricAbelianGaloisAction E kappa U (i ≫ c) x sigma) := by
  let Y : Scheme := Limits.pullback (specMap E kappa) (i ≫ c)
  let : IsIntegral Y := IsIntegral.of_isIso R.inv
  let e := R.inv.functionFieldRingEquivOfIsOpenImmersion
  let : Algebra Y.functionField Omega :=
    ((algebraMap W.functionField Omega).comp e.toRingHom).toAlgebra
  let : IsSepClosure Y.functionField Omega := isSepClosure_of_ringEquiv e
  have hpoint : Y.genericExtensionMorphism Omega =
      W.genericExtensionMorphism Omega ≫ R.inv := genericPoint_of_recovery_inverse R
  have hweight := literalArithmetic_compactification_kernel_eq_openCyclotomicSpan
    E kappa c i (Omega := Omega) epsilon
  dsimp only at hweight
  rw [hpoint] at hweight
  exact hweight

/-- A finite subfield of the fixed closure supplies a section and the actual
weight identification, without changing the recovered geometric cover.
The displayed recovery and point are literal composites, not new choices. -/
theorem exists_finiteIntermediateField_recovered_compactification_weight
    (E kappa : Type) [Field E] [NumberField E]
    [Field kappa] [CharZero kappa] [IsAlgClosed kappa]
    [Algebra E kappa] [IsSepClosure E kappa]
    {C U W : Scheme} [CompactSpace U] [QuasiSeparatedSpace U] [IsIntegral W]
    (c : C ⟶ Spec (.of E)) (i : U ⟶ C) [IsOpenImmersion i]
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (R : Limits.pullback (specMap E kappa) (i ≫ c) ≅ W)
    {Omega : Type} [Field Omega] [IsSepClosed Omega]
    [Algebra W.functionField Omega] [IsSepClosure W.functionField Omega] :
    ∃ (F : IntermediateField E kappa) (hF : FiniteDimensional E F),
      letI : FiniteDimensional E F := hF
      letI : IsSepClosure F kappa :=
        ⟨IsSepClosure.sep_closed E,
          Algebra.isSeparable_tower_top_of_isSeparable E F kappa⟩
      let phiF := specMap E F
      let UF : Scheme := Limits.pullback phiF (i ≫ c)
      letI : CompactSpace UF := inferInstance
      letI : QuasiSeparatedSpace UF :=
        quasiSeparatedSpace_of_quasiSeparated (Limits.pullback.snd phiF (i ≫ c))
      let CF : Scheme := Limits.pullback c phiF
      let cF : CF ⟶ Spec (.of F) := Limits.pullback.snd c phiF
      let iF : UF ⟶ CF :=
        coefficientModelMap phiF c i ≫ (pullbackSymmetry phiF c).hom
      ∃ hiF : iF ≫ cF = Limits.pullback.fst phiF (i ≫ c),
        let RF : Limits.pullback (specMap F kappa) (iF ≫ cF) ≅ W :=
          Limits.pullback.congrHom rfl hiF ≪≫
            constantFieldTowerIso E kappa F U (i ≫ c) ≪≫ R
        letI : IsIntegral (Limits.pullback (specMap F kappa) (iF ≫ cF)) :=
          IsIntegral.of_isIso RF.inv
        let x := W.genericExtensionMorphism Omega ≫ RF.inv
        x ≫ RF.hom = W.genericExtensionMorphism Omega ∧
          (compactificationAbelianizationMap
            (coefficientModelMap (specMap F kappa) cF iF) x).toMonoidHom.ker =
            openCyclotomicSpan
              (fun sigma : kappa ≃ₐ[F] kappa =>
                primeToRootsCoefficientMap kappa kappa sigma.toRingHom)
              (fun sigma => geometricAbelianGaloisAction F kappa UF (iF ≫ cF) x sigma) := by
  classical
  let : IsIntegral (Limits.pullback (specMap E kappa) (i ≫ c)) :=
    IsIntegral.of_isIso R.inv
  let : Nonempty C := by
    obtain ⟨z⟩ := (inferInstance : Nonempty W)
    exact ⟨i (Limits.pullback.snd (specMap E kappa) (i ≫ c) (R.inv z))⟩
  obtain ⟨F, hF, _p, _hp, ⟨epsilon⟩⟩ :=
    Scheme.exists_finiteIntermediateField_section E kappa c
  let : FiniteDimensional E F := hF
  let : NumberField F := NumberField.of_module_finite E F
  let : IsSepClosure F kappa :=
    ⟨IsSepClosure.sep_closed E,
      Algebra.isSeparable_tower_top_of_isSeparable E F kappa⟩
  let phiF := specMap E F
  let UF : Scheme := Limits.pullback phiF (i ≫ c)
  let CF : Scheme := Limits.pullback c phiF
  let cF : CF ⟶ Spec (.of F) := Limits.pullback.snd c phiF
  let iF : UF ⟶ CF :=
    coefficientModelMap phiF c i ≫ (pullbackSymmetry phiF c).hom
  let epsilonF : SchemeHomOver (𝟙 (Spec (.of F))) cF := epsilon
  have hiF : iF ≫ cF = Limits.pullback.fst phiF (i ≫ c) := by
    simp only [iF, cF, Category.assoc, pullbackSymmetry_hom_comp_snd,
      coefficientModelMap, Limits.pullback.lift_fst]
  let RF : Limits.pullback (specMap F kappa) (iF ≫ cF) ≅ W :=
    Limits.pullback.congrHom rfl hiF ≪≫
      constantFieldTowerIso E kappa F U (i ≫ c) ≪≫ R
  let : IsIntegral (Limits.pullback (specMap F kappa) (iF ≫ cF)) :=
    IsIntegral.of_isIso RF.inv
  let : CompactSpace UF := inferInstance
  let : QuasiSeparatedSpace UF :=
    quasiSeparatedSpace_of_quasiSeparated (Limits.pullback.snd phiF (i ≫ c))
  let : IsProper cF := inferInstance
  let : SmoothOfRelativeDimension 1 cF := inferInstance
  let : GeometricallyIntegral cF := inferInstance
  let : IsOpenImmersion (coefficientModelMap phiF c i) := by
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := (show MorphismProperty Scheme from @IsOpenImmersion))
      (coefficientBaseChange_isPullback phiF c i).flip (inferInstance : IsOpenImmersion i)
  let : IsOpenImmersion iF := by dsimp only [iF]; infer_instance
  refine ⟨F, hF, hiF, ?_, ?_⟩
  · simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · exact recoveredArithmetic_compactification_kernel_eq_openCyclotomicSpan
      F kappa cF iF RF (Omega := Omega) epsilonF

end AnabelianGeometry.WeightFiltration
