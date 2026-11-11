/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.AlgebraicGeometry.Geometrically.Basic
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Nyll.AlgebraicCurves.Models.Construction.BasicPerfectField
public import Nyll.AlgebraicCurves.Models.Construction.CurveIsIntegral
public import Nyll.AlgebraicCurves.Models.Construction.GeometricallyIntegralOfConstants
public import Nyll.AlgebraicCurves.Models.FunctionFields.CurveModelIsoFunctionField
public import Nyll.AlgebraicCurves.FunctionFields.Rational.SeparatingRationalPresentation
public import Nyll.AlgebraicCurves.FunctionFields.Transcendence.EssFiniteTypeFunctionField
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FullConstants
public import Nyll.SchemeTheory.Pi1.FiniteEtale.Geometry
public import Nyll.SchemeTheory.FunctionFields.AlgebraicConstantFactorization
public import Nyll.GaloisCohomology.FieldTheory.FiniteAlgebraicConstants
public import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic

/-!
# Full constants on the original smooth proper model

The relative algebraic closure of a perfect ground field is finite-dimensional. Its
smooth proper model is compared with the original model using the identity
on the same function field. Transporting the new structural morphism gives
the original scheme a geometrically integral structure over its full
constants, retaining both the original ground-field map and the literal
generic-source coefficient map.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace AlgebraicCurve.CurveModel

/-- The original smooth proper model over a perfect field carries a smooth
proper geometrically integral structure over its actual full constants.
Both structural maps and the specified generic source remain compatible;
no model identification or constant-field marking is assumed. -/
theorem exists_fullConstants_structure_of_perfectField
    {k F : Type} [Field k] [PerfectField k] [Field F] [Algebra k F]
    (M : CurveModel k F) :
    Module.Finite k (algebraicClosure k F) ∧
      ∃ c : M.C ⟶ Spec (.of (algebraicClosure k F)),
        c ≫ Spec.map (CommRingCat.ofHom (algebraMap k (algebraicClosure k F))) = M.toBase ∧
        IsProper c ∧ SmoothOfRelativeDimension 1 c ∧ GeometricallyIntegral c ∧
        (Spec.map (CommRingCat.ofHom M.ffEquiv.symm.toRingHom) ≫
          M.C.fromSpecStalk (genericPoint M.C)) ≫ c =
            Spec.map (CommRingCat.ofHom (algebraMap (algebraicClosure k F) F)) := by
  have hcurve : IsCurveOver k F :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
      M.toBase M.ffEquiv M.ffEquiv_algebraMap
  have hfinite : Algebra.EssFiniteType k F := by
    let : Algebra k M.C.functionField := M.functionFieldAlgebra
    exact (Algebra.EssFiniteType.iff_of_algEquiv M.ffAlgEquiv).mpr
      (essFiniteType_functionField M.toBase)
  obtain ⟨aRF, hRF, hfiniteRF, _⟩ :=
    IsCurveOver.exists_separating_ratFunc_algebra (K := k) (F := F)
  let : Algebra (RatFunc k) F := aRF
  have : IsScalarTower k (RatFunc k) F := hRF
  have : FunctionField k F := hfiniteRF
  let E := algebraicClosure k F
  have hE : Module.Finite k E :=
    FieldTheory.finite_algebraic_subextension k E F
  have : Module.Finite k E := hE
  have : PerfectField E := Algebra.IsAlgebraic.perfectField k
  obtain ⟨N⟩ := CurveModel.nonempty_of_perfectField E F
    (FunctionField.exists_transcendental_finite_fullConstants k F)
  have hgeom : GeometricallyIntegral N.toBase :=
    N.geometricallyIntegral_of_constantsAreBase (FunctionField.constantsAreBase_fullConstants k F)
  let φ : Spec (.of E) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k E))
  have hφ : IsFiniteEtale φ := by
    change IsFiniteEtale (Spec.map (CommRingCat.ofHom (algebraMap k E)))
    rw [IsFiniteEtale.SpecMap_iff, CommRingCat.hom_ofHom,
      RingHom.finiteEtale_algebraMap_iff]
    let : Algebra.Etale k E :=
      ⟨.of_isSeparable k E, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
    constructor
  let cN : N.C ⟶ Spec (.of k) := N.toBase ≫ φ
  have : IsProper cN := by dsimp only [cN]; infer_instance
  have : Smooth N.toBase := SmoothOfRelativeDimension.smooth 1 N.toBase
  have : Smooth cN := by dsimp only [cN]; infer_instance
  let ψ : M.C.functionField ≅ N.C.functionField :=
    (M.ffEquiv.symm.trans N.ffEquiv).toCommRingCatIso
  let bM : CommRingCat.of k ⟶ M.C.functionField :=
    CommRingCat.ofHom (baseToFunctionField M.toBase)
  let bN : CommRingCat.of E ⟶ N.C.functionField :=
    CommRingCat.ofHom (baseToFunctionField N.toBase)
  have hbaseM : M.C.fromSpecStalk (genericPoint M.C) ≫ M.toBase = Spec.map bM :=
    fromSpecStalk_genericPoint_comp_base M.toBase
  have hbaseN : N.C.fromSpecStalk (genericPoint N.C) ≫ N.toBase = Spec.map bN :=
    fromSpecStalk_genericPoint_comp_base N.toBase
  have hb : CommRingCat.ofHom (algebraMap k E) ≫ bN ≫ ψ.inv = bM := by
    ext a
    change M.ffEquiv (N.ffEquiv.symm (baseToFunctionField N.toBase (algebraMap k E a))) =
      baseToFunctionField M.toBase a
    rw [← N.ffEquiv_algebraMap, N.ffEquiv.symm_apply_apply,
      ← IsScalarTower.algebraMap_apply k E F, M.ffEquiv_algebraMap]
  have hψ : Spec.map ψ.inv ≫ N.C.fromSpecStalk (genericPoint N.C) ≫ cN =
      M.C.fromSpecStalk (genericPoint M.C) ≫ M.toBase := by
    change Spec.map ψ.inv ≫ N.C.fromSpecStalk (genericPoint N.C) ≫ N.toBase ≫ φ = _
    rw [← Category.assoc (N.C.fromSpecStalk (genericPoint N.C)) N.toBase,
      hbaseN, hbaseM]
    change Spec.map ψ.inv ≫ Spec.map bN ≫
      Spec.map (CommRingCat.ofHom (algebraMap k E)) = Spec.map bM
    rw [← Spec.map_comp, ← Spec.map_comp, Category.assoc, hb]
  obtain ⟨e, he, hegen, _⟩ := Scheme.exists_iso_functionFieldMap_eq M.toBase cN ψ hψ
  let c : M.C ⟶ Spec (.of E) := e.hom ≫ N.toBase
  have hcproper : IsProper c := by dsimp only [c]; infer_instance
  have hcsmooth : SmoothOfRelativeDimension 1 c :=
    smoothOfRelativeDimension_comp 0 1 e.hom N.toBase
  have : MorphismProperty.RespectsIso
      (@GeometricallyIntegral : MorphismProperty Scheme.{0}) := by
    rw [GeometricallyIntegral.eq_geometrically, geometrically_eq_universally]
    exact MorphismProperty.universally_respectsIso _
  have hcgeom : GeometricallyIntegral c :=
    (MorphismProperty.cancel_left_of_respectsIso
      (P := @GeometricallyIntegral) e.hom N.toBase).mpr hgeom
  let iM : M.C.functionField ⟶ CommRingCat.of F :=
    CommRingCat.ofHom M.ffEquiv.symm.toRingHom
  let iN : N.C.functionField ⟶ CommRingCat.of F :=
    CommRingCat.ofHom N.ffEquiv.symm.toRingHom
  have hgen :
      (Spec.map iM ≫ M.C.fromSpecStalk (genericPoint M.C)) ≫ e.hom =
      Spec.map iN ≫ N.C.fromSpecStalk (genericPoint N.C) := by
    rw [Category.assoc, hegen, ← Category.assoc, ← Spec.map_comp]
    have hmap : ψ.inv ≫ iM = iN := by
      ext z
      exact M.ffEquiv.symm_apply_apply (N.ffEquiv.symm z)
    rw [hmap]
  refine ⟨hE, c, ?_, hcproper, hcsmooth, hcgeom, ?_⟩
  · exact (Category.assoc e.hom N.toBase φ).trans he
  · change (Spec.map iM ≫ M.C.fromSpecStalk (genericPoint M.C)) ≫
      (e.hom ≫ N.toBase) = _
    rw [← Category.assoc, hgen, Category.assoc, hbaseN, ← Spec.map_comp]
    apply congrArg Spec.map
    ext a
    change N.ffEquiv.symm (baseToFunctionField N.toBase a) = algebraMap E F a
    rw [← N.ffEquiv_algebraMap, N.ffEquiv.symm_apply_apply]


/-- Over a finite ground field the actual full constant field is finite,
and the original scheme has the same compatible full-constant structure. -/
theorem exists_fullConstants_structure
    {k F : Type} [Field k] [Finite k] [Field F] [Algebra k F]
    (M : CurveModel k F) :
    Finite (algebraicClosure k F) ∧
      ∃ c : M.C ⟶ Spec (.of (algebraicClosure k F)),
        c ≫ Spec.map (CommRingCat.ofHom (algebraMap k (algebraicClosure k F))) = M.toBase ∧
        IsProper c ∧ SmoothOfRelativeDimension 1 c ∧ GeometricallyIntegral c ∧
        (Spec.map (CommRingCat.ofHom M.ffEquiv.symm.toRingHom) ≫
          M.C.fromSpecStalk (genericPoint M.C)) ≫ c =
            Spec.map (CommRingCat.ofHom (algebraMap (algebraicClosure k F) F)) := by
  obtain ⟨hfinite, c, hbase, hproper, hsmooth, hgeom, hgeneric⟩ :=
    M.exists_fullConstants_structure_of_perfectField
  have : Module.Finite k (algebraicClosure k F) := hfinite
  exact ⟨Module.finite_of_finite k, c, hbase, hproper, hsmooth, hgeom, hgeneric⟩

/-- The full constants can be embedded in a prescribed algebraic closure
compatibly with an existing algebraic constant-field structure. Both the
intermediate embedding and its compatibility with the actual scheme map
are constructed from the original generic source. -/
theorem exists_fullConstants_structure_compatible
    {k F L κ : Type} [Field k] [Finite k] [Field F] [Algebra k F]
    [Field L] [Algebra k L] [Algebra.IsAlgebraic k L]
    [Field κ] [IsAlgClosed κ] [Algebra k κ] [Algebra L κ] [IsScalarTower k L κ]
    (M : CurveModel k F) (cL : M.C ⟶ Spec (.of L))
    (hcL : cL ≫ Spec.map (CommRingCat.ofHom (algebraMap k L)) = M.toBase) :
    Finite (algebraicClosure k F) ∧
      ∃ (cE : M.C ⟶ Spec (.of (algebraicClosure k F)))
        (φ : L →ₐ[k] algebraicClosure k F) (σ : algebraicClosure k F →ₐ[k] κ),
        cE ≫ Spec.map (CommRingCat.ofHom (algebraMap k (algebraicClosure k F))) =
          M.toBase ∧
        IsProper cE ∧ SmoothOfRelativeDimension 1 cE ∧ GeometricallyIntegral cE ∧
        (Spec.map (CommRingCat.ofHom M.ffEquiv.symm.toRingHom) ≫
          M.C.fromSpecStalk (genericPoint M.C)) ≫ cE =
            Spec.map (CommRingCat.ofHom (algebraMap (algebraicClosure k F) F)) ∧
        cL = cE ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) ∧
        ∀ a : L, σ (φ a) = algebraMap L κ a := by
  obtain ⟨hfinite, cE, hbase, hproper, hsmooth, hgeom, hgeneric⟩ :=
    M.exists_fullConstants_structure
  let E := algebraicClosure k F
  have : Finite E := hfinite
  let bM : CommRingCat.of k ⟶ M.C.functionField :=
    CommRingCat.ofHom (baseToFunctionField M.toBase)
  let iM : M.C.functionField ⟶ CommRingCat.of F :=
    CommRingCat.ofHom M.ffEquiv.symm.toRingHom
  have hbaseM : M.C.fromSpecStalk (genericPoint M.C) ≫ M.toBase = Spec.map bM :=
    fromSpecStalk_genericPoint_comp_base M.toBase
  let η : Spec (.of F) ⟶ M.C :=
    Spec.map iM ≫ M.C.fromSpecStalk (genericPoint M.C)
  have hηnative : IsDominant (M.C.fromSpecStalk (genericPoint M.C)) := by
    refine ⟨?_⟩
    have hmem : genericPoint M.C ∈ Set.range (M.C.fromSpecStalk (genericPoint M.C)) :=
      ⟨IsLocalRing.closedPoint _, Scheme.fromSpecStalk_closedPoint⟩
    have hd : Dense ({genericPoint M.C} : Set M.C) :=
      dense_iff_closure_eq.mpr (genericPoint_spec M.C).def
    exact hd.mono (Set.singleton_subset_iff.mpr hmem)
  have : IsIso iM :=
    inferInstanceAs (IsIso M.ffEquiv.symm.toCommRingCatIso.hom)
  have : IsDominant η := by dsimp only [η]; infer_instance
  have hηk : η ≫ M.toBase = Spec.map (CommRingCat.ofHom (algebraMap k F)) := by
    dsimp only [η]
    rw [Category.assoc, hbaseM, ← Spec.map_comp]
    apply congrArg Spec.map
    ext a
    change M.ffEquiv.symm (baseToFunctionField M.toBase a) = algebraMap k F a
    rw [← M.ffEquiv_algebraMap, M.ffEquiv.symm_apply_apply]
  obtain ⟨φ, hφ, _⟩ := Scheme.existsUnique_factor_through_algebraicConstants
    η M.toBase hηk cE hgeneric cL hcL
  let : Algebra L E := φ.toRingHom.toAlgebra
  have : IsScalarTower k L E :=
    IsScalarTower.of_algebraMap_eq (fun a => (φ.commutes a).symm)
  let ψ : E →ₐ[L] κ := IsAlgClosed.lift
  let σ : E →ₐ[k] κ := ψ.restrictScalars k
  refine ⟨hfinite, cE, φ, σ, hbase, hproper, hsmooth, hgeom, hgeneric, hφ, ?_⟩
  intro a
  exact ψ.commutes a

end AlgebraicCurve.CurveModel
