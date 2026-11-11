/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Models.Construction.LiteralArithmeticCurveModel
public import Nyll.AlgebraicCurves.Models.Divisors.CurveFiniteCechDescentDegree
public import Nyll.AlgebraicCurves.Models.Kummer.CurveGaloisDivisorCochain
public import Nyll.AlgebraicCurves.Models.Kummer.CurveGenericKummerClass
public import Nyll.AlgebraicCurves.Models.Kummer.CurveNativeH1Picard
public import Nyll.EtaleCohomology.Classical.FiniteLevelCup
public import Nyll.EtaleCohomology.Classical.GenericUnitCohomology
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteGenericKummerDivisorExtension
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteKummerCupGaloisCover
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteKummerCupGaloisPrimitive
public import Nyll.EtaleFundamentalGroups.Cohomology.KummerPowerCoefficients
public import Nyll.EtaleFundamentalGroups.FiniteEtale.FunctionField
public import Nyll.EtaleFundamentalGroups.FiniteEtale.Integral
public import Nyll.EtaleFundamentalGroups.GaloisCovers.FunctionField
public import Nyll.GaloisCohomology.Kummer.Concrete.PrimitiveRootCoordinates
public import Nyll.JacobianVarieties.Kummer.CurveFiniteCupDivisor
public import Nyll.JacobianVarieties.Kummer.CurveNativeH2Degree
public import Nyll.JacobianVarieties.WeilPairing.Divisorial
public import Nyll.JacobianVarieties.WeilPairing.NativeCyclicNormCupPrimitive
public import Nyll.SchemeTheory.FunctionFields.ScalarFunctoriality
public import Nyll.SchemeTheory.LocalGeometry.SmoothStalks
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# The original finite cup and the divisorial Weil pairing

The original finite Kummer classes are represented by the specified
Weil divisors and functions. On their actual common Galois cover, the
norm primitive and its divisor vertex compute the original cup class.
The retained descent equation computes its native degree; cancellation
of the actual cover degree gives the original Weil evaluation with the
same coherent primitive root.
-/

@[expose] public section

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open CategoryTheory.PreGaloisCategory
open EtaleCohomology EtaleCohomology.Classical EtaleFundamentalGroups
open EtaleFundamentalGroups.Cohomology

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

section Representatives

variable {K F : Type u} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
  (M : CurveModel K F) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K)) (n : ℕ)

private def weilDivisorSections (d : WeilDatum K F (ℓ ^ (n + 1))) :
    Bool → Sheaf.H (etaleGenericUnitQuotient M.C) 0 := fun i =>
  M.genericUnitDivisorH0Equiv.symm (if i then d.D₂ else d.D₁)

private def weilFunctionSections (d : WeilDatum K F (ℓ ^ (n + 1))) :
    Bool → Sheaf.H (etaleGenericUnitShortComplex M.C).X₂ 0 := fun i =>
  M.genericUnitsH0FieldEquiv.symm
    (Additive.ofMul (if i then Units.mk0 d.f₂ d.f₂_ne_zero else Units.mk0 d.f₁ d.f₁_ne_zero))

omit [IsAlgClosed K] [Fact ℓ.Prime] in
private theorem weilSections_power (d : WeilDatum K F (ℓ ^ (n + 1))) (i : Bool) :
    Sheaf.H.map (etaleGenericUnitShortComplex M.C).g 0
        (weilFunctionSections M ℓ n d i) =
      ℓ ^ (n + 1) • weilDivisorSections M ℓ n d i := by
  cases i with
  | false =>
    exact M.genericUnitH0_powerDivisorEquation (ℓ ^ (n + 1))
      (Units.mk0 d.f₁ d.f₁_ne_zero) d.D₁ d.ord_f₁
  | true =>
    exact M.genericUnitH0_powerDivisorEquation (ℓ ^ (n + 1))
      (Units.mk0 d.f₂ d.f₂_ne_zero) d.D₂ d.ord_f₂

private theorem weilSections_nativeClass [HasPrincipalDivisors K F]
    (d : WeilDatum K F (ℓ ^ (n + 1))) (i : Bool) :
    let _ : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
    M.nativeFiniteLevelH1PicardTorsionEquiv ℓ hℓ n
        (finiteGenericKummerDivisorClass M.toBase ℓ hℓ n
          (weilDivisorSections M ℓ n d i) (weilFunctionSections M ℓ n d i)
          (weilSections_power M ℓ n d i)) =
      if i then d.classRight else d.classLeft := by
  intro hne
  apply Subtype.ext
  cases i with
  | false =>
    exact M.nativeFiniteLevelH1PicardTorsionEquiv_genericDivisorClass ℓ hℓ n
      (Units.mk0 d.f₁ d.f₁_ne_zero) d.degZeroLeft d.ord_f₁
  | true =>
    exact M.nativeFiniteLevelH1PicardTorsionEquiv_genericDivisorClass ℓ hℓ n
      (Units.mk0 d.f₂ d.f₂_ne_zero) d.degZeroRight d.ord_f₂

end Representatives

section Comparison

variable {K : Type u} [Field K] [IsAlgClosed K]
  {X : Scheme.{u}} [IsIntegral X]
  (c : X ⟶ Spec (.of K)) [IsProper c] [SmoothOfRelativeDimension 1 c]
  (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K)) (n : ℕ)

private theorem weilSections_cup_degree :
    let _ : Algebra K X.functionField := (baseToFunctionField c).toAlgebra
    let M := literalCurveModel c
    ∀ df : WeilDatum K X.functionField (ℓ ^ (n + 1)),
    let d := weilDivisorSections M ℓ n df
    let b := weilFunctionSections M ℓ n df
    let hb := weilSections_power M ℓ n df
    (((ellPowerRootsCoefficientEquiv K ℓ hℓ n
        (ULift.up (M.nativeFiniteLevelH2DegreeEquiv ℓ hℓ n
          (finiteLevelCup X ℓ n 1 1 2 rfl
            (finiteGenericKummerDivisorClass c ℓ hℓ n (d false) (b false) (hb false))
            (finiteGenericKummerDivisorClass c ℓ hℓ n
              (d true) (b true) (hb true)))))).toMul : Kˣ) : K) =
      df.pairing := by
  intro algKF M df d b hb
  have : Smooth c := SmoothOfRelativeDimension.smooth 1 c
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian c
  have : IsIntegrallyClosed Γ(Spec (.of K), ⊤) := IsIntegrallyClosed.of_equiv
    (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv
  have : IsNormalIntegral X := IsNormalIntegral.of_stalks X
    (fun x => (Smooth.isDomain_and_isIntegrallyClosed_stalk c x).2)
  have hMNormal : IsNormalIntegral M.C := inferInstanceAs (IsNormalIntegral X)
  have : IsLocallyNoetherian M.C := inferInstanceAs (IsLocallyNoetherian X)
  let : Algebra K M.C.functionField := algKF
  let dfM : WeilDatum K M.C.functionField (ℓ ^ (n + 1)) := df
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  let T : M.C.Etale := Scheme.Etale.mk (𝟙 M.C)
  let hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal
    (show MorphismProperty Scheme.{u} from @Etale) M.C
  let U := finiteKummerCupCommonCover M.toBase ℓ hℓ n d b hb hT
  let f := hT.from U
  obtain ⟨Y, hGalois, g, _, hgf⟩ :=
    finiteKummerCupCommonCover_exists_galois_refinement M.toBase ℓ hℓ n d b hb hT
  have : IsGalois Y := hGalois
  have : CategoryTheory.PreGaloisCategory.IsConnected Y := hGalois.toIsConnected
  have : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
  let fY : Y.left ⟶ M.C := Y.hom
  let : Algebra K Y.left.functionField :=
    (baseToFunctionField (fY ≫ M.toBase)).toAlgebra
  let : Algebra M.C.functionField Y.left.functionField := finiteEtaleFunctionFieldAlgebra Y
  have : IsScalarTower K M.C.functionField Y.left.functionField :=
    IsScalarTower.of_algebraMap_eq (fun a =>
      (Scheme.Hom.functionFieldMap_baseToFunctionField M.toBase fY
        (finiteEtale_hom_denseRange_of_isConnected Y) a).symm)
  have : FiniteDimensional M.C.functionField Y.left.functionField :=
    finiteDimensional_functionField_of_finiteEtale_isConnected Y
  have hleft : (genericPointUnitsH0Equiv M.C (b false)).toMul =
      Units.mk0 dfM.f₁ dfM.f₁_ne_zero := by
    exact M.genericPointUnitsH0Equiv_fieldUnit (Units.mk0 df.f₁ df.f₁_ne_zero)
  have hright : (genericPointUnitsH0Equiv M.C (b true)).toMul =
      Units.mk0 dfM.f₂ dfM.f₂_ne_zero := by
    exact M.genericPointUnitsH0Equiv_fieldUnit (Units.mk0 df.f₂ df.f₂_ne_zero)
  obtain ⟨a, D, m, hpairing, hdegree, hdivisor, hcup⟩ :=
    WeilDatum.exists_nativeCyclicNormCupPrimitive M.toBase ℓ hℓ n d b hb hT Y g
      dfM hleft hright
  let r := finiteKummerCupGaloisFieldCochain M.toBase ℓ hℓ n d b hb hT Y g a
  let v := M.galoisGenericUnitDivisorVertex Y D
  have hr := finiteKummerCupGaloisFieldCochain_boundary M.toBase ℓ hℓ n d b hb hT Y g a hcup
  let τ : Aut Y → Y.left.functionField ≃ₐ[K] Y.left.functionField :=
    fun σ => (finiteEtaleAutFunctionFieldAlgEquiv Y σ).restrictScalars K
  have hτ (σ : Aut Y) (z : Y.left.functionField) :
      σ.asIso.hom.left.functionFieldMap σ.asIso.hom.left.surjective.denseRange z = τ σ z :=
    (DFunLike.congr_fun (finiteEtaleAutFunctionFieldAlgEquiv_eq_functionFieldMap Y σ) z).symm
  have hv := M.galoisGenericUnitDivisorVertex_boundary Y hT (g ≫ f) D a τ hτ hdivisor
  have : IsFiniteEtale Y.hom := Y.prop
  have : IsProper (Y.hom ≫ M.toBase) := inferInstance
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace (Y.hom ≫ M.toBase)
  have hYCompact : QuasiCompact (terminal.from Y.left) :=
    (AlgebraicGeometry.compactSpace_iff_quasiCompact Y.left).1 inferInstance
  have : QuasiCompact (terminal.from ((finiteEtaleInclusion M.C).obj Y).left) := hYCompact
  obtain ⟨t₀, z, _, hz, _, hnative⟩ :=
    M.finiteKummerCup_exists_descendedDivisor_of_primitives ℓ hℓ n d b hb hT g hgf r v
      (hr.trans (by
        simp only [Category.assoc]
        let δ := (etaleConstantModuleForgetIso M.C (ULift.{u} (ZMod (ℓ ^ (n + 1))))).app
          (ModuleCat.of (ULift.{u} (ZMod (ℓ ^ (n + 1))))
            (ULift.{u} (ZMod (ℓ ^ (n + 1)))))
        let ι : etaleMultiplicativeGroupSheaf M.C ⟶
            (etaleGenericUnitShortComplex M.C).X₂ := (etaleGenericUnitShortComplex M.C).f
        exact congrArg
          (fun k : (constantSheaf M.C.smallEtaleTopology AddCommGrpCat).obj
              (ellPowerCoefficients ℓ n) ⟶ (etaleGenericUnitShortComplex M.C).X₂ =>
            abelianCechTriangleRefinement f g M.C.smallEtaleTopology ≫
              abelianCechSecondRelationMap M.C.smallEtaleTopology hT f ≫
                finiteKummerCupSecondCocycle M.toBase ℓ hℓ n d b hb hT ≫ δ.hom ≫ k)
          (Category.assoc (ellPowerConstantKummerKernelIso M.toBase ℓ hℓ n).hom
            (kernel.ι (etaleMultiplicativeGroupPower M.C (ℓ ^ (n + 1)))) ι))) hv
  have hdesc := M.degree_finiteCechDescendedDivisor Y hT (g ≫ f) (ℓ ^ (n + 1)) z t₀ v hz
  let q := finiteEtaleGenericUnitQuotientSectionsEquiv Y
  let N := M.finiteEtaleModel Y
  let e : Sheaf.H (etaleGenericUnitQuotient Y.left) 0 ≃+
      Divisor K Y.left.functionField := N.genericUnitDivisorH0Equiv
  have hs : freeAbelianSheafYonedaHomEquiv M.C.smallEtaleTopology
      ((finiteEtaleInclusion M.C).obj Y) (etaleGenericUnitQuotient M.C) v =
        q.symm (e.symm D) := M.galoisGenericUnitDivisorVertex_section Y D
  have hq := (congrArg q hs).trans (q.apply_symm_apply (e.symm D))
  have hD := (congrArg e hq).trans (e.apply_symm_apply D)
  have hdescD := hdesc.trans (congrArg
    (fun E : Divisor K Y.left.functionField =>
      -((ℓ ^ (n + 1) : ℕ) : ℤ) * Divisor.degree E) hD)
  have hdeg :
      Divisor.degree (M.genericUnitDivisorH0Equiv (CategoryTheory.Abelian.Ext.mk₀ z)) = m := by
    apply mul_left_cancel₀
      (show (Module.finrank M.C.functionField Y.left.functionField : ℤ) ≠ 0 from
        Int.natCast_ne_zero.mpr (Module.finrank_pos.ne'))
    exact hdescD.trans hdegree.symm
  have hcoefficient := congrArg
    (fun k : ZMod (ℓ ^ (n + 1)) =>
      (((ellPowerRootsCoefficientEquiv K ℓ hℓ n (ULift.up k)).toMul : Kˣ) : K))
    (hnative.trans (congrArg (fun k : ℤ => (k : ZMod (ℓ ^ (n + 1)))) hdeg))
  refine hcoefficient.trans ?_
  let hζ := (exists_compatible_ellPowerPrimitiveRoots K ℓ hℓ).choose_spec.1 n
  change ((KummerTheory.primitiveRootCoordinate hζ (m : ZMod (ℓ ^ (n + 1))) : Kˣ) : K) = _
  rw [KummerTheory.primitiveRootCoordinate_intCast, Units.val_zpow_eq_zpow_val]
  exact hpairing.symm

/-- The original finite étale cup, evaluated by the native degree,
is the divisorial Weil pairing of the same original Kummer classes.
The curve and its function field are literal; the coherent root is
exactly the root already used by the original coefficient comparison. -/
theorem nativeFiniteCup_eq_divisorialWeilPairing :
    let _ : Algebra K X.functionField := (baseToFunctionField c).toAlgebra
    let M := literalCurveModel c
    let _ : HasPrincipalDivisors K X.functionField :=
      (literalCurveModel_functionField_properties c).1.toHasPrincipalDivisors
    let _ : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
    ∀ (w : DivisorialWeilPairingData K X.functionField (ℓ ^ (n + 1)))
      (x y : finiteLevelCohomology X ℓ n 1),
    (((ellPowerRootsCoefficientEquiv K ℓ hℓ n
        (ULift.up (M.nativeFiniteLevelH2DegreeEquiv ℓ hℓ n
          (finiteLevelCup X ℓ n 1 1 2 rfl x y)))).toMul : Kˣ) : K) =
      w.pair (M.nativeFiniteLevelH1PicardTorsionEquiv ℓ hℓ n x)
        (M.nativeFiniteLevelH1PicardTorsionEquiv ℓ hℓ n y) := by
  intro algKF M hprincipal hne w x y
  obtain ⟨df, hx, hy⟩ := w.exists_datum
    (M.nativeFiniteLevelH1PicardTorsionEquiv ℓ hℓ n x)
    (M.nativeFiniteLevelH1PicardTorsionEquiv ℓ hℓ n y)
  let d := weilDivisorSections M ℓ n df
  let b := weilFunctionSections M ℓ n df
  let hb := weilSections_power M ℓ n df
  have hleft : finiteGenericKummerDivisorClass c ℓ hℓ n (d false) (b false) (hb false) = x := by
    apply (M.nativeFiniteLevelH1PicardTorsionEquiv ℓ hℓ n).injective
    exact (weilSections_nativeClass M ℓ hℓ n df false).trans hx
  have hright : finiteGenericKummerDivisorClass c ℓ hℓ n (d true) (b true) (hb true) = y := by
    apply (M.nativeFiniteLevelH1PicardTorsionEquiv ℓ hℓ n).injective
    exact (weilSections_nativeClass M ℓ hℓ n df true).trans hy
  rw [← hx, ← hy, w.compatible df, ← hleft, ← hright]
  exact weilSections_cup_degree c ℓ hℓ n df

end Comparison

end AlgebraicCurve.CurveModel
