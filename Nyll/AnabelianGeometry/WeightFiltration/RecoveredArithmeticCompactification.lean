/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Models.Construction.LiteralArithmeticCurveModel
import Nyll.EtaleFundamentalGroups.GaloisCovers.OpenCoverSquareBoundary
import Nyll.EtaleFundamentalGroups.GeometricFiber.RecoveredCoverGeometricIntegrality
import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.ModelOverlap
import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.CoefficientPullback
import Nyll.SchemeTheory.Pi1.FiniteEtale.Geometry
import Mathlib.RingTheory.Etale.Field

/-! # Compactifying the actual recovered arithmetic cover

The original descended finite-etale source is retained. Its geometric
integrality, and hence its connectedness, is proved using the supplied
recovery of the original geometric cover. The literal arithmetic base model
then supplies a compactification of this very source. No relative relation,
compactification kernel, weight comparison, or freeness is a hypothesis.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open CategoryTheory.PreGaloisCategory TopologicalSpace

namespace EtaleFundamentalGroups

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

/-- Compactify a recovered finite-etale cover of the actual arithmetic open.
The structure map of the source is an arbitrary specified map `f0`, with its
literal equality to the open-curve structure map recorded in `hi0`. -/
theorem exists_recovered_arithmetic_open_cover_compactification
    {E κ : Type} [Field E] [CharZero E]
    [Field κ] [IsAlgClosed κ] [Algebra E κ]
    {C0 X W : Scheme} [IsIntegral W]
    (c0 : C0 ⟶ Spec (.of E))
    [IsProper c0] [SmoothOfRelativeDimension 1 c0] [GeometricallyIntegral c0]
    (i0 : X ⟶ C0) [IsOpenImmersion i0]
    (f0 : X ⟶ Spec (.of E)) (hi0 : i0 ≫ c0 = f0)
    (N : FiniteEtale X)
    (R : Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
      (N.hom ≫ f0) ≅ W) :
    ∃ (C : Scheme) (c : C ⟶ Spec (.of E)) (j : N.left ⟶ C),
      IsProper c ∧ SmoothOfRelativeDimension 1 c ∧ GeometricallyIntegral c ∧
      IsOpenImmersion j ∧ j ≫ c = N.hom ≫ f0 ∧ DenseRange j ∧
      ∃ d : C ⟶ C0, IsFinite d ∧ d ≫ c0 = c ∧
        j ≫ d = N.hom ≫ i0 ∧
        ∀ z : C, z ∉ Set.range j ↔ d z ∉ Set.range i0 := by
  classical
  let : Smooth c0 := SmoothOfRelativeDimension.smooth 1 c0
  let : IsIntegral C0 := GeometricallyIntegral.isIntegral_of_subsingleton c0
  let : IsLocallyNoetherian C0 := LocallyOfFiniteType.isLocallyNoetherian c0
  let : Smooth f0 := by rw [← hi0]; infer_instance
  let : LocallyOfFiniteType f0 := inferInstance
  let : IsFiniteEtale (show N.left ⟶ X from N.hom) := N.prop
  let cN : N.left ⟶ Spec (.of E) := N.hom ≫ f0
  let : LocallyOfFiniteType cN := by dsimp only [cN]; infer_instance
  let : GeometricallyIntegral cN :=
    geometricallyIntegral_of_integral_recovered_cover cN R
  let : IsIntegral N.left := GeometricallyIntegral.isIntegral_of_subsingleton cN
  let : Nonempty X := Nonempty.map N.hom (inferInstance : Nonempty N.left)
  let : IsIntegral X := isIntegral_of_isOpenImmersion i0
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f0
  let : IsIntegrallyClosed Γ(Spec (.of E), ⊤) := IsIntegrallyClosed.of_equiv
    (Scheme.ΓSpecIso (.of E)).symm.commRingCatIsoToRingEquiv
  let : IsNormalIntegral X := IsNormalIntegral.of_stalks X
    (fun x => (Smooth.isDomain_and_isIntegrallyClosed_stalk f0 x).2)
  let : IsConnected N := FiniteEtale.isConnected_of_connectedSpace_left N
  let : Algebra E C0.functionField := (baseToFunctionField c0).toAlgebra
  let M0 : CurveModel E C0.functionField := literalCurveModel c0
  let : IsOpenImmersion (show X ⟶ M0.C from i0) :=
    (inferInstance : IsOpenImmersion i0)
  let : QuasiCompact (show X ⟶ M0.C from i0) :=
    (inferInstance : QuasiCompact i0)
  let : QuasiSeparated (show X ⟶ M0.C from i0) :=
    (inferInstance : QuasiSeparated i0)
  let : IsIntegral ((Functor.id Scheme).obj N.left) :=
    (inferInstance : IsIntegral N.left)
  let : Algebra E N.left.functionField :=
    (baseToFunctionField (C := N.left)
      (N.hom ≫ (show X ⟶ M0.C from i0) ≫ M0.toBase)).toAlgebra
  obtain ⟨M, d, j, hd, hfinite, hj, hsquare, hboundary⟩ :=
    exists_open_cover_curveModel_square_boundary M0 i0 N
  change d ≫ c0 = M.toBase at hd
  change j ≫ d = N.hom ≫ i0 at hsquare
  let : IsOpenImmersion j := hj
  let : Smooth M.toBase := SmoothOfRelativeDimension.smooth 1 M.toBase
  let : IsLocallyNoetherian M.C := LocallyOfFiniteType.isLocallyNoetherian M.toBase
  let : QuasiCompact j := inferInstance
  have hjDense : DenseRange j :=
    j.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace j
  have hstruct : j ≫ M.toBase = cN := by
    exact (congrArg (fun q : M.C ⟶ Spec (.of E) => j ≫ q) hd.symm).trans
      ((Category.assoc j (show M.C ⟶ C0 from d) c0).symm.trans
        ((congrArg (fun q : N.left ⟶ C0 => q ≫ c0) hsquare).trans
          ((Category.assoc (show N.left ⟶ X from N.hom) i0 c0).trans
            (congrArg (fun q : X ⟶ Spec (.of E) =>
              (show N.left ⟶ X from N.hom) ≫ q) hi0))))
  have hGI : GeometricallyIntegral M.toBase :=
    geometricallyIntegral_compactification_of_recovered_cover
      cN R M.toBase j hjDense hstruct
  exact ⟨M.C, M.toBase, j, inferInstance, inferInstance, hGI, hj,
    hstruct, hjDense, d, hfinite, hd, hsquare, hboundary⟩

/-- Apply the preceding construction to the literal finite coefficient
extension of the original arithmetic curve. The map back to the original
open is the original descended covering map followed by coefficient
projection. The old recovery is retained by the displayed `congrHom` only. -/
theorem exists_recovered_finiteStage_arithmetic_compactification
    {k E κ : Type} [Field k] [CharZero k]
    [Field E] [Algebra k E] [FiniteDimensional k E]
    [Field κ] [IsAlgClosed κ] [Algebra E κ]
    {C0 X W : Scheme} [IsIntegral W]
    (c0 : C0 ⟶ Spec (.of k))
    [IsProper c0] [SmoothOfRelativeDimension 1 c0] [GeometricallyIntegral c0]
    (i0 : X ⟶ C0) [IsOpenImmersion i0]
    (f : X ⟶ Spec (.of k)) (hi0 : i0 ≫ c0 = f)
    (N : FiniteEtale (Limits.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k E))) f))
    (R : Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
      (N.hom ≫ Limits.pullback.fst
        (Spec.map (CommRingCat.ofHom (algebraMap k E))) f) ≅ W) :
    let φE := Spec.map (CommRingCat.ofHom (algebraMap k E))
    let ψ := Spec.map (CommRingCat.ofHom (algebraMap E κ))
    let cN := N.hom ≫ Limits.pullback.fst φE f
    let a := N.hom ≫ Limits.pullback.snd φE f
    ∃ (C : Scheme) (c : C ⟶ Spec (.of E)) (j : N.left ⟶ C),
      IsProper c ∧ SmoothOfRelativeDimension 1 c ∧ GeometricallyIntegral c ∧
      IsOpenImmersion j ∧ ∃ hj : j ≫ c = cN,
      IsFiniteEtale a ∧ a ≫ f = (j ≫ c) ≫ φE ∧
      ∃ R' : Limits.pullback ψ (j ≫ c) ≅ W,
        R' = Limits.pullback.congrHom rfl hj ≪≫ R := by
  classical
  intro φE ψ cN a
  let : CharZero E := Algebra.charZero_of_charZero (R := k) (A := E)
  let : Algebra.Etale k E :=
    ⟨Algebra.FormallyEtale.of_isSeparable k E,
      Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  let : IsFiniteEtale φE := by
    change IsFiniteEtale (Spec.map (CommRingCat.ofHom (algebraMap k E)))
    rw [IsFiniteEtale.SpecMap_iff, CommRingCat.hom_ofHom,
      RingHom.finiteEtale_algebraMap_iff]
    exact ⟨⟩
  let C0E : Scheme := Limits.pullback φE c0
  let c0E : C0E ⟶ Spec (.of E) := Limits.pullback.fst φE c0
  let XE : Scheme := Limits.pullback φE f
  let fE : XE ⟶ Spec (.of E) := Limits.pullback.fst φE f
  let e : XE ≅ Limits.pullback φE (i0 ≫ c0) :=
    Limits.pullback.congrHom rfl hi0.symm
  let iE : XE ⟶ C0E := e.hom ≫ coefficientModelMap φE c0 i0
  let : IsOpenImmersion (coefficientModelMap φE c0 i0) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := (show MorphismProperty Scheme from @IsOpenImmersion))
      (coefficientBaseChange_isPullback φE c0 i0).flip inferInstance
  let : IsOpenImmersion iE := by dsimp only [iE]; infer_instance
  have hiE : iE ≫ c0E = fE := by
    dsimp only [iE, c0E, fE, e, coefficientModelMap]
    simp only [Category.assoc, Limits.pullback.lift_fst,
      Limits.pullback.congrHom_hom, Limits.pullback.lift_fst,
      Category.comp_id]
  let : IsProper c0E := inferInstance
  let : SmoothOfRelativeDimension 1 c0E := by
    change SmoothOfRelativeDimension 1 (Limits.pullback.fst φE c0)
    let : MorphismProperty.IsStableUnderBaseChange
        (show MorphismProperty Scheme from @SmoothOfRelativeDimension 1) :=
      smoothOfRelativeDimension_isStableUnderBaseChange 1
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := (show MorphismProperty Scheme from @SmoothOfRelativeDimension 1))
      (IsPullback.of_hasPullback φE c0).flip
      (inferInstance : SmoothOfRelativeDimension 1 c0)
  let : GeometricallyIntegral c0E := inferInstance
  obtain ⟨C, c, j, hc, hsm, hGI, hj, hstruct, _⟩ :=
    exists_recovered_arithmetic_open_cover_compactification c0E iE fE hiE N R
  let : IsFiniteEtale (show N.left ⟶ XE from N.hom) := N.prop
  have haFinite : IsFiniteEtale a := by dsimp only [a]; infer_instance
  have ha : a ≫ f = (j ≫ c) ≫ φE := by
    rw [hstruct]
    change (N.hom ≫ Limits.pullback.snd φE f) ≫ f =
      (N.hom ≫ Limits.pullback.fst φE f) ≫ φE
    simp only [Category.assoc]
    exact congrArg (fun q => N.hom ≫ q) Limits.pullback.condition.symm
  exact ⟨C, c, j, hc, hsm, hGI, hj, hstruct, haFinite, ha,
    Limits.pullback.congrHom rfl hstruct ≪≫ R, rfl⟩

end EtaleFundamentalGroups
