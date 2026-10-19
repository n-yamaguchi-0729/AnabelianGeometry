/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Kummer.ArithmeticTateComparison
import Nyll.AnabelianGeometry.WeightFiltration.GenericPointNaturality
import Nyll.SchemeTheory.FunctionFields.OpenImmersion
import Mathlib.FieldTheory.Separable

/-!
# The arithmetic Tate comparison at an open curve's generic point

The function-field isomorphism of the original open immersion transports
its supplied separable closure. The actual generic-point square then gives
the existing proper Tate comparison at the required compactification point.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
open AlgebraicGeometry.FiniteEtale NeronModelInfra GoodReductionJacobian
open ProCGroups.Abelian

namespace AnabelianGeometry.WeightFiltration

/-- The existing equivariant Tate comparison uses the actual image of an
open generic point, without a further choice of a fiber-functor isomorphism. -/
theorem exists_arithmetic_fullTate_equiv_at_open_generic
    {k K : Type} [Field k] [Field K] [IsAlgClosed K] [CharZero K]
    [Algebra k K] [IsSepClosure k K]
    {C : Scheme} (c : C ⟶ Spec (.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (.of k))) c)
    (D : RelativePic0Designation k c)
    (hD : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    [Smooth D.toBase] [IsProper D.toBase] [GeometricallyConnected D.toBase] :
    let : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace c
    let : QuasiSeparatedSpace C := quasiSeparatedSpace_of_quasiSeparated c
    let Y := pullback c (specMap k K)
    let : IsIntegral Y := isIntegral_pullback_Spec_field k c (specMap k K)
    let s := pullbackSymmetry c (specMap k K)
    let : IsIntegral (pullback (specMap k K) c) := IsIntegral.of_isIso s.hom
    let G := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD
    let hc : G.IsCommutative :=
      RepresentsRelSubPic.relativeGroupLaw_isCommutative (P := algEquivZeroGroupCut c ε) hD
    ∀ (X : Scheme) [IsIntegral X] (j : X ⟶ pullback (specMap k K) c)
      [IsOpenImmersion j] (Ω : Type) [Field Ω] [IsAlgClosed Ω]
      [Algebra X.functionField Ω] [IsSepClosure X.functionField Ω],
    let xi := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) ≫
      X.fromSpecStalk (genericPoint X)
    ∃ E : TopologicalAbelianization (Aut (fiber (xi ≫ j))) ≃ₜ*
        Multiplicative (ProCGroups.FullTateModule (G.AlgPoints hc K)),
      ∀ (σ : K ≃ₐ[k] K) (x : TopologicalAbelianization (Aut (fiber (xi ≫ j)))),
        E (geometricAbelianGaloisAction k K C c (xi ≫ j) σ x) =
          ProCGroups.FullTateModule.mapHom
            (RelativeGroupLaw.AlgPoints.map (L := G) (hc := hc) σ.toAlgHom) (E x) := by
  intro hcompact hqs Y hY s hYL G hc X hX j hj Ω hΩ hΩclosed hFΩ hsep xi
  let v := j ≫ s.inv
  let e := v.functionFieldRingEquivOfIsOpenImmersion
  let : Algebra Y.functionField Ω :=
    ((algebraMap X.functionField Ω).comp e.toRingHom).toAlgebra
  let : Algebra.IsSeparable Y.functionField Ω :=
    Algebra.IsSeparable.of_equiv_equiv e.symm (RingEquiv.refl Ω) (by
      ext z
      change algebraMap X.functionField Ω (e (e.symm z)) = algebraMap X.functionField Ω z
      rw [e.apply_symm_apply])
  let : IsSepClosure Y.functionField Ω :=
    { sep_closed := inferInstance
      separable := inferInstance }
  have hv : DenseRange v := v.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace _
  let η := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω))
  let ηY := Spec.map (CommRingCat.ofHom (algebraMap Y.functionField Ω))
  let qY := Y.fromSpecStalk (genericPoint Y)
  have hη : ηY = η ≫ Spec.map (CommRingCat.ofHom e.toRingHom) :=
    Spec.map_comp _ _
  have hq : Spec.map (CommRingCat.ofHom e.toRingHom) ≫ qY =
      X.fromSpecStalk (genericPoint X) ≫ v := functionFieldMap_genericPoint v hv
  have hpoint : (ηY ≫ qY) ≫ s.hom = xi ≫ j := by
    rw [hη, Category.assoc η, hq]
    simp only [v, xi, η, Category.assoc, s.inv_hom_id, Category.comp_id]
  have hT := JacobianVarieties.Kummer.exists_arithmetic_abelJacobi_fullTate_equiv
    (k := k) (K := K) c ε D hD Ω
  change ∃ E : TopologicalAbelianization (Aut (fiber ((ηY ≫ qY) ≫ s.hom))) ≃ₜ*
      Multiplicative (ProCGroups.FullTateModule (G.AlgPoints hc K)),
    ∀ (σ : K ≃ₐ[k] K)
      (x : TopologicalAbelianization (Aut (fiber ((ηY ≫ qY) ≫ s.hom)))),
      E (geometricAbelianGaloisAction k K C c ((ηY ≫ qY) ≫ s.hom) σ x) =
        ProCGroups.FullTateModule.mapHom
          (RelativeGroupLaw.AlgPoints.map (L := G) (hc := hc) σ.toAlgHom) (E x) at hT
  rw [hpoint] at hT
  exact hT

end AnabelianGeometry.WeightFiltration
