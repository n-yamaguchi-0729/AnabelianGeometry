/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.SchemeTheory.Normalization.FiniteSeparable
import Nyll.EtaleFundamentalGroups.GeometricFiber.MatchedFiberCoverGroupTransport
import Nyll.AlgebraicCurves.Models.Rational.RationalConfigurationIteratedBaseChange
import Nyll.SchemeTheory.FunctionFields.GenericFieldSourceNaturality
import Nyll.EtaleFundamentalGroups.FiniteEtale.Integral
import Nyll.SchemeTheory.FunctionFields.Functoriality
import Nyll.SchemeTheory.FunctionFields.OpenImmersion
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.MorphismProperty.Comma

/-! # Named Square Literal Base Transport -/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.FiniteEtale AlgebraicGeometry.ProjSpace
open EtaleFundamentalGroups

namespace AnabelianGeometry.WeightFiltration

/-- Transport a finite etale cover along a base isomorphism by composing its structure map. -/
def namedCoverOnIsomorphicBase {U V : Scheme} (e : U ≅ V)
    (W : FiniteEtale U) : FiniteEtale V :=
  have : IsFiniteEtale W.hom := W.prop
  have : IsFiniteEtale e.hom := ⟨⟩
  FiniteEtale.mk (W.hom ≫ e.hom)

theorem namedCoverOnIsomorphicBase_model_projection
    {U V N : Scheme} (e : U ≅ V) (W : FiniteEtale U)
    (J : W.left ≅ N) (q : N ⟶ U) (hJq : J.hom ≫ q = W.hom) :
    J.hom ≫ (q ≫ e.hom) = (namedCoverOnIsomorphicBase e W).hom := by
  change J.hom ≫ (q ≫ e.hom) = W.hom ≫ e.hom
  rw [← Category.assoc, hJq]

/-- Transport a cover fiber point along a base isomorphism, retaining its lift to the cover. -/
def namedCoverOnIsomorphicBasePoint
    {U V : Scheme} (e : U ≅ V) (W : FiniteEtale U)
    {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶ U) (w : (fiber xi).obj W) :
    (fiber (xi ≫ e.hom)).obj (namedCoverOnIsomorphicBase e W) :=
  (fiberObjEquivHom (xi ≫ e.hom) (namedCoverOnIsomorphicBase e W)).symm
    (Over.homMk (actualFiberPointLift xi W w) (by
      change actualFiberPointLift xi W w ≫ (W.hom ≫ e.hom) = xi ≫ e.hom
      rw [← Category.assoc, actualFiberPointLift_comp]))

theorem namedCoverOnIsomorphicBasePoint_lift
    {U V : Scheme} (e : U ≅ V) (W : FiniteEtale U)
    {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶ U) (w : (fiber xi).obj W) :
    actualFiberPointLift (xi ≫ e.hom) (namedCoverOnIsomorphicBase e W)
        (namedCoverOnIsomorphicBasePoint e W xi w) = actualFiberPointLift xi W w := by
  unfold actualFiberPointLift namedCoverOnIsomorphicBasePoint
  rw [Equiv.apply_symm_apply]
  rfl

/-- Transport the ambient field algebra along the function field map of a base isomorphism. -/
abbrev namedBaseTransportAmbientAlgebra
    {U V : Scheme} [IsIntegral U] [IsIntegral V] (e : U ≅ V)
    (Ω : Type) [Field Ω] [Algebra U.functionField Ω] : Algebra V.functionField Ω :=
  ((algebraMap U.functionField Ω).comp
    (e.hom.functionFieldMap e.hom.homeomorph.surjective.denseRange)).toAlgebra

theorem namedBaseTransport_genericPoint
    {U V : Scheme} [IsIntegral U] [IsIntegral V] (e : U ≅ V)
    (Ω : Type) [Field Ω] [Algebra U.functionField Ω] :
    let _ : Algebra V.functionField Ω := namedBaseTransportAmbientAlgebra e Ω
    U.genericExtensionMorphism Ω ≫ e.hom = V.genericExtensionMorphism Ω := by
  intro A
  simp only [Scheme.genericExtensionMorphism, Category.assoc]
  rw [← Spec_functionFieldMap_fromSpecStalk e.hom
    e.hom.homeomorph.surjective.denseRange, ← Category.assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem namedBaseTransport_isAlgClosure
    {U V : Scheme} [IsIntegral U] [IsIntegral V] (e : U ≅ V)
    (Ω : Type) [Field Ω] [Algebra U.functionField Ω]
    [@IsAlgClosure U.functionField Ω _ _ _
      DivisionSemiring.to_moduleIsTorsionFree] :
    let _ : Algebra V.functionField Ω := namedBaseTransportAmbientAlgebra e Ω
    @IsAlgClosure V.functionField Ω _ _ _
      DivisionSemiring.to_moduleIsTorsionFree := by
  intro A
  have : Module.IsTorsionFree U.functionField Ω :=
    DivisionSemiring.to_moduleIsTorsionFree
  have : Module.IsTorsionFree V.functionField Ω :=
    DivisionSemiring.to_moduleIsTorsionFree
  let eF := e.hom.functionFieldRingEquivOfIsOpenImmersion
  let : Algebra V.functionField U.functionField := eF.toRingHom.toAlgebra
  let : IsScalarTower V.functionField U.functionField Ω :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.IsAlgebraic V.functionField U.functionField := by
    refine ⟨fun z => ?_⟩
    obtain ⟨x, rfl⟩ := eF.surjective z
    apply IsIntegral.isAlgebraic
    exact isIntegral_algebraMap
  exact IsAlgClosure.ofAlgebraic V.functionField U.functionField Ω

private theorem isConnected_equivalence_obj
    {C D : Type*} [Category C] [Category D]
    (E : C ≌ D) (X : C) [CategoryTheory.PreGaloisCategory.IsConnected X] :
    CategoryTheory.PreGaloisCategory.IsConnected (E.functor.obj X) := by
  constructor
  · intro hInitial
    exact CategoryTheory.PreGaloisCategory.IsConnected.notInitial
      (X := X) (hInitial.isInitialOfObj E.functor X)
  · intro Y i hi hY
    let j : E.inverse.obj Y ⟶ X :=
      E.inverse.map i ≫ (E.unitIso.app X).inv
    let : Mono j := by
      dsimp only [j]
      infer_instance
    let : IsIso j :=
      CategoryTheory.PreGaloisCategory.IsConnected.noTrivialComponent
        (E.inverse.obj Y) j (fun hInitial ↦
          hY ((hInitial.isInitialObj E.functor _).ofIso (E.counitIso.app Y)))
    have hMap : IsIso (E.inverse.map i) := by
      have hFactor : j ≫ (E.unitIso.app X).hom = E.inverse.map i := by
        simp only [j, Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rw [← hFactor]
      infer_instance
    exact isIso_of_reflects_iso i E.inverse

theorem namedCoverOnIsomorphicBase_isConnected
    {U V : Scheme} (e : U ≅ V) (W : FiniteEtale U)
    [CategoryTheory.PreGaloisCategory.IsConnected W] :
    CategoryTheory.PreGaloisCategory.IsConnected (namedCoverOnIsomorphicBase e W) := by
  have hLocal : IsZariskiLocalAtTarget (@IsFiniteEtale : MorphismProperty Scheme) :=
    ((HasAffineProperty.iff (P := (@IsFiniteEtale : MorphismProperty Scheme))
      (Q := affineAnd RingHom.FiniteEtale)).mp inferInstance).1
  have : MorphismProperty.RespectsIso (@IsFiniteEtale : MorphismProperty Scheme) :=
    hLocal.toRespects
  let E : FiniteEtale U ≌ FiniteEtale V :=
    MorphismProperty.Comma.mapRightIso
      (P := (@IsFiniteEtale : MorphismProperty Scheme)) (Q := ⊤) (W := ⊤)
      (Functor.id Scheme) (Discrete.natIso fun _ ↦ e)
  change CategoryTheory.PreGaloisCategory.IsConnected (E.functor.obj W)
  exact isConnected_equivalence_obj E W

theorem namedCoverOnIsomorphicBase_exists_same_model_point
    {U V N : Scheme} [IsIntegral U] [IsIntegral V]
    (e : U ≅ V) (W : FiniteEtale U) (J : W.left ≅ N)
    (Ω : Type) [Field Ω] [IsSepClosed Ω] [Algebra U.functionField Ω]
    (w : (fiber (U.genericExtensionMorphism Ω)).obj W) :
    let _ : Algebra V.functionField Ω := namedBaseTransportAmbientAlgebra e Ω
    ∃ wV : (fiber (V.genericExtensionMorphism Ω)).obj (namedCoverOnIsomorphicBase e W),
      actualFiberPointLift (V.genericExtensionMorphism Ω)
          (namedCoverOnIsomorphicBase e W) wV ≫ J.hom =
        actualFiberPointLift (U.genericExtensionMorphism Ω) W w ≫ J.hom := by
  intro A
  rw [← namedBaseTransport_genericPoint e Ω]
  refine ⟨namedCoverOnIsomorphicBasePoint e W (U.genericExtensionMorphism Ω) w, ?_⟩
  rw [namedCoverOnIsomorphicBasePoint_lift]
  rfl

theorem namedBaseTransport_chart_functionFieldMap
    {U V M : Scheme} [IsIntegral U] [IsIntegral V] [IsIntegral M]
    (e : U ≅ V) (jU : U ⟶ M) (jV : V ⟶ M)
    (hU : DenseRange jU) (hV : DenseRange jV) (hchart : e.hom ≫ jV = jU) :
    (e.hom.functionFieldMap e.hom.homeomorph.surjective.denseRange).comp
        (jV.functionFieldMap hV) = jU.functionFieldMap hU := by
  have h := functionFieldMap_comp_of_dense jV hV e.hom
    e.hom.homeomorph.surjective.denseRange
  subst jU
  exact h

theorem namedCoverOnIsomorphicBase_chart_field_square
    {U V M : Scheme} [IsIntegral U] [IsIntegral V] [IsIntegral M]
    (e : U ≅ V) (W : FiniteEtale U) [IsIntegral W.left]
    (hW : DenseRange W.hom)
    (jU : U ⟶ M) (jV : V ⟶ M)
    (hU : DenseRange jU) (hV : DenseRange jV) (hchart : e.hom ≫ jV = jU)
    (z : M.functionField) :
    let hWV : DenseRange (namedCoverOnIsomorphicBase e W).hom :=
      e.hom.homeomorph.surjective.denseRange.comp hW e.hom.continuous
    (show W.left ⟶ V from (namedCoverOnIsomorphicBase e W).hom).functionFieldMap hWV
        (jV.functionFieldMap hV z) =
      (show W.left ⟶ U from W.hom).functionFieldMap hW (jU.functionFieldMap hU z) := by
  intro hWV
  have hcover := functionFieldMap_comp_of_dense e.hom
    e.hom.homeomorph.surjective.denseRange (show W.left ⟶ U from W.hom) hW
  have hcoordinate := namedBaseTransport_chart_functionFieldMap e jU jV hU hV hchart
  calc
    (show W.left ⟶ V from (namedCoverOnIsomorphicBase e W).hom).functionFieldMap hWV
        (jV.functionFieldMap hV z) =
        (show W.left ⟶ U from W.hom).functionFieldMap hW
          (e.hom.functionFieldMap e.hom.homeomorph.surjective.denseRange
            (jV.functionFieldMap hV z)) :=
      (RingHom.congr_fun hcover (jV.functionFieldMap hV z)).symm
    _ = (show W.left ⟶ U from W.hom).functionFieldMap hW (jU.functionFieldMap hU z) :=
      congrArg ((show W.left ⟶ U from W.hom).functionFieldMap hW) (RingHom.congr_fun hcoordinate z)

/-- Transport a cover of the iterated coefficient extension to the direct geometric base change. -/
def namedSquareCoverOnLiteralGeometricBase
    (k E κ : Type) [Field k] [Field E] [Field κ]
    [Algebra k E] [Algebra E κ] [Algebra k κ] [IsScalarTower k E κ]
    (s : Finset (Projectivization k (k × k)))
    (W : FiniteEtale (pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
      (rationalConfigurationBaseChangeChart k E s ≫ π E 1))) :
    FiniteEtale (pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
      ((rationalConfigurationOpen s).ι ≫ π k 1)) :=
  namedCoverOnIsomorphicBase (rationalConfigurationIteratedBaseChangeIso k E κ s) W

end AnabelianGeometry.WeightFiltration
