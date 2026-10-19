/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.GenusZeroFiniteReconstruction
import Nyll.AnabelianGeometry.WeightFiltration.RationalConfigurationCorrectionRemoval
import Nyll.AnabelianGeometry.WeightFiltration.RationalModelOriginalPoint
import Nyll.AnabelianGeometry.WeightFiltration.NamedSquareLiteralPointModel
import Nyll.AnabelianGeometry.WeightFiltration.SameModelIsoInertia
import Nyll.AnabelianGeometry.WeightFiltration.RationalModelOriginalChart
import Nyll.AnabelianGeometry.WeightFiltration.RationalModelArithmeticSquare
import Nyll.AnabelianGeometry.WeightFiltration.FiniteRationalReconstructionGeometry
import Nyll.AnabelianGeometry.WeightFiltration.BoundaryGaloisCorrespondence
import Nyll.AnabelianGeometry.ArithmeticIsomorphisms.ProjectiveModelEquivariance
import Nyll.AnabelianGeometry.ArithmeticIsomorphisms.GeometricAbelianizationEquivariance
import Nyll.AnabelianGeometry.ProjectiveLine.ConfigurationScalarExtension
import Nyll.AnabelianGeometry.ProjectiveLine.LinearFieldMap
import Nyll.AlgebraicCurves.Models.Rational.RationalConfigurationPairCrossRatio
import Nyll.ProCGroups.Abelian.TopologicalAbelianization
import Nyll.ProCGroups.Topologies.ArithmeticInnerCorrectionFiberTransport
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Algebra.Group.Subgroup.Map

/-! # Weak reconstruction of genus-zero opens over number fields

Finite rational models and aligned generic points are constructed from the
original curves. The same inertia correspondence recovered over a splitting
field is equivariant over the original field. Three-point rigidity and
effective descent then give an actual isomorphism over that field.
-/

noncomputable section
open scoped RatFunc
open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.FiniteEtale AlgebraicGeometry.ProjSpace
open AlgebraicGeometry.SmoothProperCurve ProCGroups.Abelian
open SchemeTheory EtaleFundamentalGroups.Inertia
open AnabelianGeometry.ArithmeticIsomorphisms
open AnabelianGeometry.GeometricFundamentalGroup AnabelianGeometry.ProjectiveLine

namespace AnabelianGeometry.WeightFiltration

attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra
  CurveModel.isIntegral literalPoint_projectiveIntegral
  rationalConfigurationGeometricFieldAlgebra rationalConfigurationGeometricConstantAlgebra
  rationalConfigurationGeometricField_scalarTower
  placeBaseAmbientAlgebra placeBaseAmbientTower placeConstantAmbientTower

/-- Transporting a group equivalence through two model comparisons gives the
same commuting square on topological abelianizations. -/
private theorem abelianization_model_comparisons_comp
    {G₁ : Type*} {H₁ : Type*} {G₂ : Type*} {H₂ : Type*}
    [TopologicalSpace G₁] [Group G₁] [IsTopologicalGroup G₁]
    [TopologicalSpace H₁] [Group H₁] [IsTopologicalGroup H₁]
    [TopologicalSpace G₂] [Group G₂] [IsTopologicalGroup G₂]
    [TopologicalSpace H₂] [Group H₂] [IsTopologicalGroup H₂]
    (bs : G₁ ≃ₜ* H₁) (bt : G₂ ≃ₜ* H₂) (e : H₁ ≃ₜ* H₂) :
    (TopologicalAbelianization.congr bt).toMonoidHom.comp
        (TopologicalAbelianization.congr (bs.trans (e.trans bt.symm))).toMonoidHom =
      (TopologicalAbelianization.congr e).toMonoidHom.comp
        (TopologicalAbelianization.congr bs).toMonoidHom := by
  apply MonoidHom.ext
  intro z
  obtain ⟨v, rfl⟩ := TopologicalAbelianization.surjective_mk G₁ z
  change TopologicalAbelianization.congr bt
      (TopologicalAbelianization.congr (bs.trans (e.trans bt.symm))
        (TopologicalAbelianization.mk G₁ v)) =
    TopologicalAbelianization.congr e
      (TopologicalAbelianization.congr bs (TopologicalAbelianization.mk G₁ v))
  simp only [TopologicalAbelianization.congr_apply_mk,
    ContinuousMulEquiv.trans_apply, ContinuousMulEquiv.apply_symm_apply]

/-- A specified inner correction is carried through the same model comparisons
by conjugation with the image of its original correcting element. -/
private theorem corrected_model_comparison
    {G₁ : Type*} {H₁ : Type*} {G₂ : Type*} {H₂ : Type*}
    [TopologicalSpace G₁] [Group G₁] [TopologicalSpace H₁] [Group H₁]
    [TopologicalSpace G₂] [Group G₂] [IsTopologicalGroup G₂]
    [TopologicalSpace H₂] [Group H₂]
    (es : G₁ ≃ₜ* H₁) (et : G₂ ≃ₜ* H₂) (α : G₁ ≃ₜ* G₂) (d : G₂) (v : H₁) :
    (es.symm.trans ((ProCGroups.innerCorrectedGroupEquiv α d).trans et)) v =
      et d * (es.symm.trans (α.trans et)) v * (et d)⁻¹ := by
  simp only [ContinuousMulEquiv.trans_apply, ProCGroups.innerCorrectedGroupEquiv_apply,
    map_mul, map_inv]

/-- Remove the constructed inner correction through the same model comparisons. -/
private theorem remove_corrected_model_comparison
    (E κ : Type) [Field E] [CharZero E]
    [Field κ] [CharZero κ] [IsAlgClosed κ] [Algebra E κ] [IsAlgClosure E κ]
    (s t : Finset (Projectivization E (E × E)))
    (Ω₁ Ω₂ : Type) [Field Ω₁] [Field Ω₂] [IsAlgClosed Ω₁] [IsAlgClosed Ω₂]
    [Algebra (rationalConfigurationGeometricScheme E κ s).functionField Ω₁]
    [Algebra (rationalConfigurationGeometricScheme E κ t).functionField Ω₂]
    [IsAlgClosure (rationalConfigurationGeometricScheme E κ s).functionField Ω₁]
    [IsAlgClosure (rationalConfigurationGeometricScheme E κ t).functionField Ω₂]
    {G₁ G₂ : Type*}
    [TopologicalSpace G₁] [Group G₁]
    [TopologicalSpace G₂] [Group G₂] [IsTopologicalGroup G₂]
    (es : G₁ ≃ₜ* rationalConfigurationArithmeticGroup E κ s Ω₁)
    (et : G₂ ≃ₜ* rationalConfigurationArithmeticGroup E κ t Ω₂)
    (αE : G₁ ≃ₜ* G₂) (d : G₂)
    (eΔ : rationalConfigurationGeometricGroup E κ s Ω₁ ≃ₜ*
      rationalConfigurationGeometricGroup E κ t Ω₂)
    (heΔ : ∀ v, rationalConfigurationGeometricInclusion E κ t Ω₂ (eΔ v) =
      (es.symm.trans ((ProCGroups.innerCorrectedGroupEquiv αE d).trans et))
        (rationalConfigurationGeometricInclusion E κ s Ω₁ v))
    (σ : s ≃ t)
    (hσ : ∀ p : s, ∃ a : rationalConfigurationGeometricGroup E κ t Ω₂,
      (rationalConfigurationChosenInertia E κ s Ω₁
        (rationalConfigurationBoundaryPlace E κ s p)).map eΔ.toMonoidHom =
      (rationalConfigurationChosenInertia E κ t Ω₂
        (rationalConfigurationBoundaryPlace E κ t (σ p))).map
          (MulAut.conj a).toMonoidHom) :
    let β₀ := es.symm.trans (αE.trans et)
    let τ := (rationalConfigurationBoundaryPlaceEquiv E κ s).symm.trans
      (σ.trans (rationalConfigurationBoundaryPlaceEquiv E κ t))
    ∃ e₀ : rationalConfigurationGeometricGroup E κ s Ω₁ ≃ₜ*
        rationalConfigurationGeometricGroup E κ t Ω₂,
      (∀ v, rationalConfigurationGeometricInclusion E κ t Ω₂ (e₀ v) =
        β₀ (rationalConfigurationGeometricInclusion E κ s Ω₁ v)) ∧
      ∀ p,
        ((rationalConfigurationChosenInertia E κ s Ω₁ p).map
          (TopologicalAbelianization.mk (rationalConfigurationGeometricGroup E κ s Ω₁))).map
            (TopologicalAbelianization.congr e₀).toMonoidHom =
          (rationalConfigurationChosenInertia E κ t Ω₂ (τ p)).map
            (TopologicalAbelianization.mk (rationalConfigurationGeometricGroup E κ t Ω₂)) := by
  intro β₀ τ
  have heΔ' (v : rationalConfigurationGeometricGroup E κ s Ω₁) :
      rationalConfigurationGeometricInclusion E κ t Ω₂ (eΔ v) =
        et d * β₀ (rationalConfigurationGeometricInclusion E κ s Ω₁ v) * (et d)⁻¹ :=
    (heΔ v).trans
      (corrected_model_comparison es et αE d
        (rationalConfigurationGeometricInclusion E κ s Ω₁ v))
  exact rationalConfiguration_remove_arithmetic_correction_same_punctures
    E κ s t Ω₁ Ω₂ β₀ eΔ (et d) heΔ' σ hσ


/-- Transport a family of subgroups through an injective comparison square. -/
private theorem subgroup_correspondence_of_comparison_square
    {G₁ H₁ G₂ H₂ : Type*}
    [Group G₁] [Group H₁] [Group G₂] [Group H₂]
    {P₁ Q₁ P₂ Q₂ : Type*}
    (As : G₁ →* H₁) (At : G₂ →* H₂)
    (A₀ : H₁ →* H₂) (Aorig : G₁ →* G₂)
    (hAt : Function.Injective At)
    (Es : P₁ ≃ Q₁) (Et : P₂ ≃ Q₂) (τ : Q₁ ≃ Q₂)
    (Rs : P₁ → Subgroup G₁) (Rt : P₂ → Subgroup G₂)
    (Cs : Q₁ → Subgroup H₁) (Ct : Q₂ → Subgroup H₂)
    (hcomp : At.comp Aorig = A₀.comp As)
    (hRs : ∀ p, (Rs p).map As = Cs (Es p))
    (hRt : ∀ p, (Rt p).map At = Ct (Et p))
    (hτrange : ∀ p, (Cs p).map A₀ = Ct (τ p))
    (p : P₁) :
    (Rs p).map Aorig = Rt ((Es.trans (τ.trans Et.symm)) p) := by
  apply Subgroup.map_injective hAt
  calc
    ((Rs p).map Aorig).map At = (Cs (Es p)).map A₀ := by
      rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hRs p]
    _ = Ct (τ (Es p)) := hτrange (Es p)
    _ = Ct (Et ((Es.trans (τ.trans Et.symm)) p)) := by
      change Ct (τ (Es p)) = Ct (Et (Et.symm (τ (Es p))))
      rw [Et.apply_symm_apply]
    _ = (Rt ((Es.trans (τ.trans Et.symm)) p)).map At :=
      (hRt ((Es.trans (τ.trans Et.symm)) p)).symm


/-- Reindex fixed boundary labels under the same equivariant correspondence. -/
private theorem boundary_labels_reindex_of_equivariance
    {X Y P : Type*} {S : Set X} {T : Set Y}
    (e : P ≃ S) (τ : S → T) (x : P → X) (y : P → Y)
    (f : X → X) (g : Y → Y)
    (hS : ∀ z, z ∈ S ↔ f z ∈ S)
    (hx : ∀ p, (e p).val = x p)
    (hy : ∀ p, (τ (e p)).val = y p)
    (hτ : ∀ q : S, (τ ⟨f q.val, (hS q.val).mp q.property⟩).val = g (τ q).val) :
    ∃ r : P → P, (∀ p, f (x p) = x (r p)) ∧ (∀ p, g (y p) = y (r p)) := by
  let r : P → P := fun p => e.symm ⟨f (e p).val, (hS (e p).val).mp (e p).property⟩
  have hr (p : P) :
      e (r p) = ⟨f (e p).val, (hS (e p).val).mp (e p).property⟩ :=
    e.apply_symm_apply _
  refine ⟨r, fun p => ?_, fun p => ?_⟩
  · exact ((congrArg f (hx p).symm).trans
      (congrArg Subtype.val (hr p)).symm).trans (hx (r p))
  · calc
      g (y p) = g (τ (e p)).val := congrArg g (hy p).symm
      _ = (τ ⟨f (e p).val, (hS (e p).val).mp (e p).property⟩).val := (hτ (e p)).symm
      _ = (τ (e (r p))).val := congrArg (fun q : S => (τ q).val) (hr p).symm
      _ = y (r p) := hy (r p)


/-- The constructed finite models, their original pointed comparison, and the
same boundary correspondence descend the reconstructed isomorphism. The ambient
fields remain abstract while the original geometric charts are compared. -/
private theorem exists_schemeIso_of_geometric_model_comparison
    (k E κ Ω₁ Ω₂ : Type) [Field k] [NumberField k]
    [Field E] [NumberField E] [Algebra k E] [FiniteDimensional k E] [_root_.IsGalois k E]
    [Field κ] [CharZero κ] [IsAlgClosed κ]
    [Algebra k κ] [Algebra E κ] [IsScalarTower k E κ]
    [IsAlgClosure k κ] [IsAlgClosure E κ]
    [Field Ω₁] [Field Ω₂] [IsAlgClosed Ω₁] [IsAlgClosed Ω₂]
    [IsSepClosed Ω₁] [IsSepClosed Ω₂]
    [Algebra k Ω₁] [Algebra κ Ω₁] [IsScalarTower k κ Ω₁]
    [Algebra k Ω₂] [Algebra κ Ω₂] [IsScalarTower k κ Ω₂]
    {C₁ C₂ : Scheme}
    (c₁ : C₁ ⟶ Spec (.of k)) (c₂ : C₂ ⟶ Spec (.of k))
    (U₁ : C₁.Opens) (U₂ : C₂.Opens)
    [IsIntegral (U₁ : Scheme)] [IsIntegral (U₂ : Scheme)]
    [CompactSpace (U₁ : Scheme)] [QuasiSeparatedSpace (U₁ : Scheme)]
    [CompactSpace (U₂ : Scheme)] [QuasiSeparatedSpace (U₂ : Scheme)]
    [GeometricallyIntegral (U₁.ι ≫ c₁)] [GeometricallyIntegral (U₂.ι ≫ c₂)]
    (s t : Finset (Projectivization E (E × E))) (hs : 3 ≤ s.card) (ht : 3 ≤ t.card)
    [Algebra (rationalConfigurationGeometricScheme E κ s).functionField Ω₁]
    [Algebra (rationalConfigurationGeometricScheme E κ t).functionField Ω₂]
    [IsAlgClosure (rationalConfigurationGeometricScheme E κ s).functionField Ω₁]
    [IsAlgClosure (rationalConfigurationGeometricScheme E κ t).functionField Ω₂]
    (I₁ : pullback c₁ (specMap k E) ≅ (projectiveLineRatFuncModel E).C)
    (I₂ : pullback c₂ (specMap k E) ≅ (projectiveLineRatFuncModel E).C)
    (hproper₁ : I₁.hom ≫ (projectiveLineRatFuncModel E).toBase =
      pullback.snd c₁ (specMap k E))
    (hproper₂ : I₂.hom ≫ (projectiveLineRatFuncModel E).toBase =
      pullback.snd c₂ (specMap k E))
    (Js : pullback (specMap k E) (U₁.ι ≫ c₁) ≅ (rationalConfigurationOpen s : Scheme))
    (Jt : pullback (specMap k E) (U₂.ι ≫ c₂) ≅ (rationalConfigurationOpen t : Scheme))
    (hJs : Js.hom ≫ ((rationalConfigurationOpen s).ι ≫ π E 1) =
      pullback.fst (specMap k E) (U₁.ι ≫ c₁))
    (hJt : Jt.hom ≫ ((rationalConfigurationOpen t).ι ≫ π E 1) =
      pullback.fst (specMap k E) (U₂.ι ≫ c₂))
    (hJsambient : Js.hom ≫ (rationalConfigurationOpen s).ι =
      (openBaseChangeIso c₁ (specMap k E) U₁).hom ≫
        (pullback.fst c₁ (specMap k E) ⁻¹ᵁ U₁).ι ≫ I₁.hom)
    (hJtambient : Jt.hom ≫ (rationalConfigurationOpen t).ι =
      (openBaseChangeIso c₂ (specMap k E) U₂).hom ≫
        (pullback.fst c₂ (specMap k E) ⁻¹ᵁ U₂).ι ≫ I₂.hom)
    (xi₁ : Spec (.of Ω₁) ⟶ (U₁ : Scheme)) (xi₂ : Spec (.of Ω₂) ⟶ (U₂ : Scheme))
    (hbase₁ : xi₁ ≫ (U₁.ι ≫ c₁) = ξ k Ω₁)
    (hbase₂ : xi₂ ≫ (U₂.ι ≫ c₂) = ξ k Ω₂)
    (halign₁ : fieldFiberExtensionIso k κ Ω₁ ≪≫
      (eqToIso (congrArg fiber hbase₁)).symm =
      ((nonempty_fiber_iso (xi₁ ≫ (U₁.ι ≫ c₁)) (ξ k κ)).some).symm)
    (halign₂ : fieldFiberExtensionIso k κ Ω₂ ≪≫
      (eqToIso (congrArg fiber hbase₂)).symm =
      ((nonempty_fiber_iso (xi₂ ≫ (U₂.ι ≫ c₂)) (ξ k κ)).some).symm)
    (hcoefS : (rationalConfigurationGeometricScheme E κ s).genericExtensionMorphism Ω₁ ≫
      pullback.fst (specMap E κ) ((rationalConfigurationOpen s).ι ≫ π E 1) = ξ κ Ω₁)
    (hcoefT : (rationalConfigurationGeometricScheme E κ t).genericExtensionMorphism Ω₂ ≫
      pullback.fst (specMap E κ) ((rationalConfigurationOpen t).ι ≫ π E 1) = ξ κ Ω₂)
    (α : π₁ᵉᵗ(xi₁) ≃ₜ* π₁ᵉᵗ(xi₂))
    (hα : ∀ v, arithmeticFundamentalGroupHom k κ (U₂.ι ≫ c₂) xi₂ (α v) =
      arithmeticFundamentalGroupHom k κ (U₁.ι ≫ c₁) xi₁ v)
    (e₀ : rationalConfigurationGeometricGroup E κ s Ω₁ ≃ₜ*
      rationalConfigurationGeometricGroup E κ t Ω₂)
    (σ : s ≃ t) (F : (E × E) ≃ₗ[E] (E × E))
    (hF : ∀ p : s, projectiveLinearEquiv F p.val = (σ p).val)
    (I : (rationalConfigurationOpen s : Scheme) ≅ (rationalConfigurationOpen t : Scheme))
    (hIambient : I.hom ≫ (rationalConfigurationOpen t).ι =
      (rationalConfigurationOpen s).ι ≫ (pairLinearCoordinateIso F).hom)
    (hIbase : I.hom ≫ (rationalConfigurationOpen t).ι ≫ π E 1 =
      (rationalConfigurationOpen s).ι ≫ π E 1) :
    let fs := U₁.ι ≫ c₁
    let ft := U₂.ι ≫ c₂
    let gs := (rationalConfigurationOpen s).ι ≫ π E 1
    let gt := (rationalConfigurationOpen t).ι ≫ π E 1
    let Zs := rationalConfigurationGeometricScheme E κ s
    let Zt := rationalConfigurationGeometricScheme E κ t
    let Xs := pullback (specMap k κ) fs
    let Xt := pullback (specMap k κ) ft
    let _hXs : IsIntegral Xs := IsIntegral.of_isIso (pullbackSymmetry fs (specMap k κ)).hom
    let _hXt : IsIntegral Xt := IsIntegral.of_isIso (pullbackSymmetry ft (specMap k κ)).hom
    let Bs : Xs ≅ Zs := scalarExtensionModelIso k E κ fs gs Js hJs
    let Bt : Xt ≅ Zt := scalarExtensionModelIso k E κ ft gt Jt hJt
    let _AXs : Algebra Xs.functionField Ω₁ := namedBaseTransportAmbientAlgebra Bs.symm Ω₁
    let _AXt : Algebra Xt.functionField Ω₂ := namedBaseTransportAmbientAlgebra Bt.symm Ω₂
    let xsg := Xs.genericExtensionMorphism Ω₁
    let xtg := Xt.genericExtensionMorphism Ω₂
    ∀ (hBs : xsg ≫ Bs.hom = Zs.genericExtensionMorphism Ω₁)
      (hBt : xtg ≫ Bt.hom = Zt.genericExtensionMorphism Ω₂)
      (_hcoef₁ : xsg ≫ pullback.fst (specMap k κ) fs = ξ κ Ω₁)
      (_hcoef₂ : xtg ≫ pullback.fst (specMap k κ) ft = ξ κ Ω₂)
      (hxi₁ : xsg ≫ pullback.snd (specMap k κ) fs = xi₁)
      (hxi₂ : xtg ≫ pullback.snd (specMap k κ) ft = xi₂),
    let bs := namedModelPointedGroupEquiv Bs xsg (Zs.genericExtensionMorphism Ω₁) hBs
    let bt := namedModelPointedGroupEquiv Bt xtg (Zt.genericExtensionMorphism Ω₂) hBt
    let eOrig := bs.trans (e₀.trans bt.symm)
    ∀ (_hOrig : ∀ v,
      pointedFundamentalGroupHom (pullback.snd (specMap k κ) ft) xtg xi₂ hxi₂ (eOrig v) =
        α (pointedFundamentalGroupHom (pullback.snd (specMap k κ) fs) xsg xi₁ hxi₁ v)),
    let τ := (rationalConfigurationBoundaryPlaceEquiv E κ s).symm.trans
      (σ.trans (rationalConfigurationBoundaryPlaceEquiv E κ t))
    ∀ (_hτ : ∀ p,
      ((rationalConfigurationChosenInertia E κ s Ω₁ p).map
        (TopologicalAbelianization.mk (rationalConfigurationGeometricGroup E κ s Ω₁))).map
          (TopologicalAbelianization.congr e₀).toMonoidHom =
        (rationalConfigurationChosenInertia E κ t Ω₂ (τ p)).map
          (TopologicalAbelianization.mk (rationalConfigurationGeometricGroup E κ t Ω₂))),
    ∃ J : (U₁ : Scheme) ≅ (U₂ : Scheme), J.hom ≫ (U₂.ι ≫ c₂) = U₁.ι ≫ c₁ := by
  classical
  intro fs ft gs gt Zs Zt Xs Xt hXs hXt Bs Bt AXs AXt xsg xtg
    hBs hBt hcoef₁ hcoef₂ hxi₁ hxi₂ bs bt eOrig hOrig τ hτ
  have : CompactSpace Xs :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst (specMap k κ) fs)
  have : CompactSpace Xt :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst (specMap k κ) ft)
  let M := projectiveLineRatFuncModel κ
  have hRatCurve : IsCurveOver κ (RatFunc κ) := AlgebraicCurve.instIsCurveOverRatFunc κ
  have hConnectedFs : GeometricallyConnected fs :=
    GeometricallyIrreducible.geometricallyConnected fs
  let js₀ : Zs ⟶ M.C := rationalConfigurationBaseChangeChart E κ s
  let jt₀ : Zt ⟶ M.C := rationalConfigurationBaseChangeChart E κ t
  have hOpenJs₀ : IsOpenImmersion js₀ :=
    rationalConfigurationBaseChangeChart_isOpenImmersion E κ s
  have hOpenJt₀ : IsOpenImmersion jt₀ :=
    rationalConfigurationBaseChangeChart_isOpenImmersion E κ t
  have hjs₀ : DenseRange js₀ := rationalConfigurationBaseChangeChart_denseRange E κ s
  have hjt₀ : DenseRange jt₀ := rationalConfigurationBaseChangeChart_denseRange E κ t
  have hfieldS := rationalConfigurationGeometricFunctionFieldEquiv_hfield E κ s
  have hfieldT := rationalConfigurationGeometricFunctionFieldEquiv_hfield E κ t
  let AFS : Algebra (RatFunc κ) Ω₁ := rationalConfigurationGeometricAmbientAlgebra E κ s Ω₁
  let AFT : Algebra (RatFunc κ) Ω₂ := rationalConfigurationGeometricAmbientAlgebra E κ t Ω₂
  have hFZS : IsScalarTower (RatFunc κ) Zs.functionField Ω₁ :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hFZT : IsScalarTower (RatFunc κ) Zt.functionField Ω₂ :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hκFS : IsScalarTower κ (RatFunc κ) Ω₁ :=
    rationalConfiguration_fixedConstant_scalarTower E κ s Ω₁ hcoefS
  have hκFT : IsScalarTower κ (RatFunc κ) Ω₂ :=
    rationalConfiguration_fixedConstant_scalarTower E κ t Ω₂ hcoefT
  have : CharZero Zs.functionField :=
    Algebra.charZero_of_charZero (R := κ) (A := Zs.functionField)
  have : CharZero Zt.functionField :=
    Algebra.charZero_of_charZero (R := κ) (A := Zt.functionField)
  have hFΩ₁ : IsAlgClosure (RatFunc κ) Ω₁ :=
    rationalConfigurationAmbient_isAlgClosure_geometric E κ s Ω₁
  have hFΩ₂ : IsAlgClosure (RatFunc κ) Ω₂ :=
    rationalConfigurationAmbient_isAlgClosure_geometric E κ t Ω₂
  let js : Xs ⟶ M.C := Bs.hom ≫ js₀
  let jt : Xt ⟶ M.C := Bt.hom ≫ jt₀
  have hOpenJs : IsOpenImmersion js := by
    change IsOpenImmersion (Bs.hom ≫ js₀)
    infer_instance
  have hOpenJt : IsOpenImmersion jt := by
    change IsOpenImmersion (Bt.hom ≫ jt₀)
    infer_instance
  have hjs : DenseRange js :=
    js.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace js
  have hjt : DenseRange jt :=
    jt.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace jt
  let AFXs : Algebra (RatFunc κ) Xs.functionField :=
    ((js.functionFieldMap hjs).comp M.ffEquiv.toRingHom).toAlgebra
  let AFXt : Algebra (RatFunc κ) Xt.functionField :=
    ((jt.functionFieldMap hjt).comp M.ffEquiv.toRingHom).toAlgebra
  have hFXs : IsScalarTower (RatFunc κ) Xs.functionField Ω₁ :=
    sameModelIso_chart_scalarTower M Bs js₀ hjs₀ hfieldS
  have hFXt : IsScalarTower (RatFunc κ) Xt.functionField Ω₂ :=
    sameModelIso_chart_scalarTower M Bt jt₀ hjt₀ hfieldT
  have hSepXs : IsSepClosure Xs.functionField Ω₁ := namedBaseTransport_isSepClosure Bs.symm Ω₁
  have hSepXt : IsSepClosure Xt.functionField Ω₂ := namedBaseTransport_isSepClosure Bt.symm Ω₂
  let Es := Set.equivOfEq (openBoundaryPlaces_comp_iso M Bs js₀)
  let Et := Set.equivOfEq (openBoundaryPlaces_comp_iso M Bt jt₀)
  let Qs₀ := M.boundaryNormalizationPrimes (Ω := Ω₁) js₀
  let Qt₀ := M.boundaryNormalizationPrimes (Ω := Ω₂) jt₀
  have hQs₀ : ∀ p, (Qs₀ p).IsMaximal :=
    fun p => M.boundaryNormalizationPrimes_isMaximal (Ω := Ω₁) js₀ p
  have hQt₀ : ∀ p, (Qt₀ p).IsMaximal :=
    fun p => M.boundaryNormalizationPrimes_isMaximal (Ω := Ω₂) jt₀ p
  let Qs : ∀ p : M.openBoundaryPlaces js,
      Ideal (normalizationCommAlgCat p.val.toValuationSubring Ω₁) := fun p => Qs₀ (Es p)
  let Qt : ∀ p : M.openBoundaryPlaces jt,
      Ideal (normalizationCommAlgCat p.val.toValuationSubring Ω₂) := fun p => Qt₀ (Et p)
  have hQs : ∀ p, (Qs p).IsMaximal := fun p => hQs₀ (Es p)
  have hQt : ∀ p, (Qt p).IsMaximal := fun p => hQt₀ (Et p)
  let Rs := fun p : M.openBoundaryPlaces js =>
    (boundaryPlaceInertiaHom M js hjs rfl Qs p).toMonoidHom.range
  let Rt := fun p : M.openBoundaryPlaces jt =>
    (boundaryPlaceInertiaHom M jt hjt rfl Qt p).toMonoidHom.range
  let Cs := fun p : M.openBoundaryPlaces js₀ =>
    (boundaryPlaceInertiaHom M js₀ hjs₀ hfieldS Qs₀ p).toMonoidHom.range
  let Ct := fun p : M.openBoundaryPlaces jt₀ =>
    (boundaryPlaceInertiaHom M jt₀ hjt₀ hfieldT Qt₀ p).toMonoidHom.range
  have hRs (p) : (Rs p).map (TopologicalAbelianization.congr bs).toMonoidHom = Cs (Es p) :=
    sameModelIso_boundary_range M Bs js₀ hjs₀ hfieldS Qs₀ p
  have hRt (p) : (Rt p).map (TopologicalAbelianization.congr bt).toMonoidHom = Ct (Et p) :=
    sameModelIso_boundary_range M Bt jt₀ hjt₀ hfieldT Qt₀ p
  have hτrange (p) :
      (Cs p).map (TopologicalAbelianization.congr e₀).toMonoidHom = Ct (τ p) := by
    change ((boundaryPlaceInertiaHom M js₀ hjs₀ hfieldS Qs₀ p).toMonoidHom.range).map _ =
      (boundaryPlaceInertiaHom M jt₀ hjt₀ hfieldT Qt₀ (τ p)).toMonoidHom.range
    rw [boundaryPlaceInertiaHom_range M js₀ hjs₀ hfieldS Qs₀ p,
      boundaryPlaceInertiaHom_range M jt₀ hjt₀ hfieldT Qt₀ (τ p)]
    exact hτ p
  let τOrig := Es.trans (τ.trans Et.symm)
  let As := TopologicalAbelianization.congr bs
  let At := TopologicalAbelianization.congr bt
  let A₀ := TopologicalAbelianization.congr e₀
  let Aorig := TopologicalAbelianization.congr eOrig
  have hcomp : At.toMonoidHom.comp Aorig.toMonoidHom =
      A₀.toMonoidHom.comp As.toMonoidHom :=
    abelianization_model_comparisons_comp bs bt e₀
  have hτOrig (p) : (Rs p).map Aorig.toMonoidHom = Rt (τOrig p) :=
    subgroup_correspondence_of_comparison_square
      As.toMonoidHom At.toMonoidHom A₀.toMonoidHom Aorig.toMonoidHom At.injective
      Es Et τ Rs Rt Cs Ct hcomp hRs hRt hτrange p
  have hAorig := geometricAbelianization_equivariant_of_pointed_arithmetic_square
    k κ (U₁ : Scheme) (U₂ : Scheme) fs ft xsg xtg xi₁ xi₂ hxi₁ hxi₂ α hα eOrig hOrig
  obtain ⟨eC₁, heC₁, hproj₁, hmodelbase₁⟩ := exists_original_rationalModel_chart
    k E κ c₁ U₁ I₁ hproper₁ s Js hJsambient hJs
  obtain ⟨eC₂, heC₂, hproj₂, hmodelbase₂⟩ := exists_original_rationalModel_chart
    k E κ c₂ U₂ I₂ hproper₂ t Jt hJtambient hJt
  have hactualBase₁ : (xsg ≫ pullback.snd (specMap k κ) fs) ≫ fs = ξ k Ω₁ := by
    rw [hxi₁]
    exact hbase₁
  have hactualBase₂ : (xtg ≫ pullback.snd (specMap k κ) ft) ≫ ft = ξ k Ω₂ := by
    rw [hxi₂]
    exact hbase₂
  have hAlignOrig₁ : fieldFiberExtensionIso k κ Ω₁ ≪≫
      (eqToIso (congrArg fiber hactualBase₁)).symm =
      ((nonempty_fiber_iso
        ((xsg ≫ pullback.snd (specMap k κ) fs) ≫ fs) (ξ k κ)).some).symm := by
    cases hxi₁
    exact halign₁
  have hAlignOrig₂ : fieldFiberExtensionIso k κ Ω₂ ≪≫
      (eqToIso (congrArg fiber hactualBase₂)).symm =
      ((nonempty_fiber_iso
        ((xtg ≫ pullback.snd (specMap k κ) ft) ≫ ft) (ξ k κ)).some).symm := by
    cases hxi₂
    exact halign₂
  have hthree : 3 ≤ Nat.card (M.openBoundaryPlaces jt) := by
    rw [Nat.card_congr Et, rationalConfigurationBoundaryPlaces_card]
    exact ht
  have hGalois := boundary_correspondence_galois_equivariance_of_alignedComparison
    k κ c₁ U₁.ι M eC₁ heC₁ js hjs hproj₁ hmodelbase₁ rfl Qs
    c₂ U₂.ι M eC₂ heC₂ jt hjt hproj₂ hmodelbase₂ rfl Qt
    hcoef₁ hactualBase₁ hAlignOrig₁ hcoef₂ hactualBase₂ hAlignOrig₂
    hthree Aorig.toMulEquiv hAorig τOrig hτOrig
  let IE := finiteRationalModelReconstructionIso k E fs ft Js Jt I
  have hIE : IE.hom ≫ pullback.fst (specMap k E) ft =
      pullback.fst (specMap k E) fs :=
    finiteRationalModelReconstructionIso_hom_base k E fs ft gs gt Js Jt hJs hJt I hIbase
  let Iκ := constantCoverIsoScalarExtension k E κ fs ft IE hIE
  let Fκ := linearEquivFieldMap (algebraMap E κ) F
  have hIκ : Iκ.hom ≫ jt = js ≫ (pairLinearCoordinateIso Fκ).hom :=
    finiteRationalModelReconstructionIso_geometric_chart
      k E κ fs ft s t Js Jt hJs hJt I hIbase F hIambient
  have hpointMap (p : Projectivization E (E × E)) :
      rationalConfigurationProjectivePoint E κ p = projectiveFieldMap (algebraMap E κ) p := by
    apply projectiveRationalPoint_injective
    rw [rationalConfigurationProjectivePoint_actualPoint,
      projectiveRationalPoint_projectiveFieldMap]
  let xp : s → Projectivization κ (κ × κ) :=
    fun p => rationalConfigurationProjectivePoint E κ p.val
  let yp : s → Projectivization κ (κ × κ) :=
    fun p => rationalConfigurationProjectivePoint E κ (σ p).val
  have hxp : Function.Injective xp := fun _ _ h =>
    Subtype.ext ((rationalConfigurationProjectivePoint_injective E κ) h)
  have hFp (p : s) : projectiveLinearEquiv Fκ (xp p) = yp p := by
    change projectiveLinearEquiv Fκ (rationalConfigurationProjectivePoint E κ p.val) =
      rationalConfigurationProjectivePoint E κ (σ p).val
    rw [hpointMap, hpointMap, projectiveLinearEquiv_fieldMap, hF p]
  let Ps := (rationalConfigurationBoundaryPlaceEquiv E κ s).trans Es.symm
  let Pt := (rationalConfigurationBoundaryPlaceEquiv E κ t).trans Et.symm
  have hPs (p : s) : (Ps p).val = projectiveRatFuncPlace (xp p) :=
    rationalConfigurationBoundaryPlace_eq_projectiveRatFuncPlace E κ s p
  have hPt (p : t) : (Pt p).val =
      projectiveRatFuncPlace (rationalConfigurationProjectivePoint E κ p.val) :=
    rationalConfigurationBoundaryPlace_eq_projectiveRatFuncPlace E κ t p
  have hτPs (p : s) : τOrig (Ps p) = Pt (σ p) := by
    change Et.symm (rationalConfigurationBoundaryPlaceEquiv E κ t
      (σ ((rationalConfigurationBoundaryPlaceEquiv E κ s).symm
        (Es (Es.symm (rationalConfigurationBoundaryPlaceEquiv E κ s p)))))) =
      Et.symm (rationalConfigurationBoundaryPlaceEquiv E κ t (σ p))
    rw [Es.apply_symm_apply, Equiv.symm_apply_apply]
  have hcard : Fintype.card (Fin 3) ≤ Fintype.card s := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using hs
  obtain ⟨ι⟩ : Nonempty (Fin 3 ↪ s) := Function.Embedding.nonempty_of_card_le hcard
  have h01 : ι 0 ≠ ι 1 := fun h => (by decide : (0 : Fin 3) ≠ 1) (ι.injective h)
  have h20 : ι 2 ≠ ι 0 := fun h => (by decide : (2 : Fin 3) ≠ 0) (ι.injective h)
  have h21 : ι 2 ≠ ι 1 := fun h => (by decide : (2 : Fin 3) ≠ 1) (ι.injective h)
  have hequiv (γ : Gal(κ/k)) :
      (coefficientBaseChangeIso k κ fs γ).hom ≫ Iκ.hom =
        Iκ.hom ≫ (coefficientBaseChangeIso k κ ft γ).hom := by
    obtain ⟨θ₁, θ₂, g₁, g₂,
      ⟨hθ₁proj, hθ₁base, hg₁base, hg₁point⟩,
      ⟨hθ₂proj, hθ₂base, hg₂base, hg₂point⟩, hS₁, hS₂, hτγ⟩ := hGalois γ
    obtain ⟨r, hxr, hyr⟩ := boundary_labels_reindex_of_equivariance
      Ps τOrig (fun p => projectiveRatFuncPlace (xp p))
      (fun p => projectiveRatFuncPlace (yp p)) (g₁ • ·) (g₂ • ·) hS₁ hPs
      (fun p => (congrArg Subtype.val (hτPs p)).trans (hPt (σ p)))
      (fun q => congrArg Subtype.val (hτγ q))
    have hOpenJtNative :
        @IsOpenImmersion (pullback (specMap k κ) (U₂.ι ≫ c₂))
          (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) κ)) jt := hOpenJt
    exact geometricOpenIso_equivariant_of_projective_boundary k κ
      c₁ U₁.ι c₂ U₂.ι eC₁ eC₂ heC₁ heC₂ js jt
      hproj₁ hproj₂ hmodelbase₁ hmodelbase₂ Iκ Fκ hIκ
      γ θ₁ θ₂ g₁ g₂ hθ₁proj hθ₂proj hθ₁base hθ₂base hg₁point hg₂point
      (hg₁base.trans hg₂base.symm) xp yp hxp (ι 0) (ι 1) (ι 2) h01 h20 h21
      r hxr hyr hFp
  obtain ⟨J, hJ, _hJE⟩ := exists_schemeIso_of_geometricGalois_equivariant
    k E κ fs ft xi₁ IE hIE hequiv
  exact ⟨J, hJ⟩


/-- The original generic points and arithmetic square come from the same finite models. -/
private theorem exists_schemeIso_of_corrected_finite_models
    (k E κ Ω₁ Ω₂ : Type) [Field k] [NumberField k]
    [Field E] [NumberField E] [Algebra k E] [FiniteDimensional k E] [_root_.IsGalois k E]
    [Field κ] [CharZero κ] [IsAlgClosed κ]
    [Algebra k κ] [Algebra E κ] [IsScalarTower k E κ]
    [IsAlgClosure k κ] [IsAlgClosure E κ]
    [Field Ω₁] [Field Ω₂] [IsAlgClosed Ω₁] [IsAlgClosed Ω₂]
    [IsSepClosed Ω₁] [IsSepClosed Ω₂]
    [Algebra k Ω₁] [Algebra κ Ω₁] [IsScalarTower k κ Ω₁]
    [Algebra k Ω₂] [Algebra κ Ω₂] [IsScalarTower k κ Ω₂]
    {C₁ C₂ : Scheme}
    (c₁ : C₁ ⟶ Spec (.of k)) (c₂ : C₂ ⟶ Spec (.of k))
    (U₁ : C₁.Opens) (U₂ : C₂.Opens)
    [IsIntegral (U₁ : Scheme)] [IsIntegral (U₂ : Scheme)]
    [CompactSpace (U₁ : Scheme)] [QuasiSeparatedSpace (U₁ : Scheme)]
    [CompactSpace (U₂ : Scheme)] [QuasiSeparatedSpace (U₂ : Scheme)]
    [GeometricallyIntegral (U₁.ι ≫ c₁)] [GeometricallyIntegral (U₂.ι ≫ c₂)]
    (s t : Finset (Projectivization E (E × E))) (hs : 3 ≤ s.card) (ht : 3 ≤ t.card)
    [Algebra (rationalConfigurationGeometricScheme E κ s).functionField Ω₁]
    [Algebra (rationalConfigurationGeometricScheme E κ t).functionField Ω₂]
    [IsAlgClosure (rationalConfigurationGeometricScheme E κ s).functionField Ω₁]
    [IsAlgClosure (rationalConfigurationGeometricScheme E κ t).functionField Ω₂]
    (I₁ : pullback c₁ (specMap k E) ≅ (projectiveLineRatFuncModel E).C)
    (I₂ : pullback c₂ (specMap k E) ≅ (projectiveLineRatFuncModel E).C)
    (hproper₁ : I₁.hom ≫ (projectiveLineRatFuncModel E).toBase =
      pullback.snd c₁ (specMap k E))
    (hproper₂ : I₂.hom ≫ (projectiveLineRatFuncModel E).toBase =
      pullback.snd c₂ (specMap k E))
    (Js : pullback (specMap k E) (U₁.ι ≫ c₁) ≅ (rationalConfigurationOpen s : Scheme))
    (Jt : pullback (specMap k E) (U₂.ι ≫ c₂) ≅ (rationalConfigurationOpen t : Scheme))
    (hJs : Js.hom ≫ ((rationalConfigurationOpen s).ι ≫ π E 1) =
      pullback.fst (specMap k E) (U₁.ι ≫ c₁))
    (hJt : Jt.hom ≫ ((rationalConfigurationOpen t).ι ≫ π E 1) =
      pullback.fst (specMap k E) (U₂.ι ≫ c₂))
    (hJsambient : Js.hom ≫ (rationalConfigurationOpen s).ι =
      (openBaseChangeIso c₁ (specMap k E) U₁).hom ≫
        (pullback.fst c₁ (specMap k E) ⁻¹ᵁ U₁).ι ≫ I₁.hom)
    (hJtambient : Jt.hom ≫ (rationalConfigurationOpen t).ι =
      (openBaseChangeIso c₂ (specMap k E) U₂).hom ≫
        (pullback.fst c₂ (specMap k E) ⁻¹ᵁ U₂).ι ≫ I₂.hom)
    (xi₁ : Spec (.of Ω₁) ⟶ (U₁ : Scheme)) (xi₂ : Spec (.of Ω₂) ⟶ (U₂ : Scheme))
    (hbase₁ : xi₁ ≫ (U₁.ι ≫ c₁) = ξ k Ω₁)
    (hbase₂ : xi₂ ≫ (U₂.ι ≫ c₂) = ξ k Ω₂)
    (halign₁ : fieldFiberExtensionIso k κ Ω₁ ≪≫
      (eqToIso (congrArg fiber hbase₁)).symm =
      ((nonempty_fiber_iso (xi₁ ≫ (U₁.ι ≫ c₁)) (ξ k κ)).some).symm)
    (halign₂ : fieldFiberExtensionIso k κ Ω₂ ≪≫
      (eqToIso (congrArg fiber hbase₂)).symm =
      ((nonempty_fiber_iso (xi₂ ≫ (U₂.ι ≫ c₂)) (ξ k κ)).some).symm)
    (hcoefS : (rationalConfigurationGeometricScheme E κ s).genericExtensionMorphism Ω₁ ≫
      pullback.fst (specMap E κ) ((rationalConfigurationOpen s).ι ≫ π E 1) = ξ κ Ω₁)
    (hcoefT : (rationalConfigurationGeometricScheme E κ t).genericExtensionMorphism Ω₂ ≫
      pullback.fst (specMap E κ) ((rationalConfigurationOpen t).ι ≫ π E 1) = ξ κ Ω₂)
    (α : π₁ᵉᵗ(xi₁) ≃ₜ* π₁ᵉᵗ(xi₂))
    (hα : ∀ v, arithmeticFundamentalGroupHom k κ (U₂.ι ≫ c₂) xi₂ (α v) =
      arithmeticFundamentalGroupHom k κ (U₁.ι ≫ c₁) xi₁ v)
    (e₀ : rationalConfigurationGeometricGroup E κ s Ω₁ ≃ₜ*
      rationalConfigurationGeometricGroup E κ t Ω₂)
    (σ : s ≃ t) (F : (E × E) ≃ₗ[E] (E × E))
    (hF : ∀ p : s, projectiveLinearEquiv F p.val = (σ p).val)
    (I : (rationalConfigurationOpen s : Scheme) ≅ (rationalConfigurationOpen t : Scheme))
    (hIambient : I.hom ≫ (rationalConfigurationOpen t).ι =
      (rationalConfigurationOpen s).ι ≫ (pairLinearCoordinateIso F).hom)
    (hIbase : I.hom ≫ (rationalConfigurationOpen t).ι ≫ π E 1 =
      (rationalConfigurationOpen s).ι ≫ π E 1) :
    let fs := U₁.ι ≫ c₁
    let ft := U₂.ι ≫ c₂
    let _gs := (rationalConfigurationOpen s).ι ≫ π E 1
    let _gt := (rationalConfigurationOpen t).ι ≫ π E 1
    let _Zs := rationalConfigurationGeometricScheme E κ s
    let _Zt := rationalConfigurationGeometricScheme E κ t
    ∀ (hxs : arithmeticConstantFieldLift k E κ fs xi₁ ≫ Js.hom =
        rationalConfigurationArithmeticBasePoint E κ s Ω₁)
      (hxt : arithmeticConstantFieldLift k E κ ft xi₂ ≫ Jt.hom =
        rationalConfigurationArithmeticBasePoint E κ t Ω₂),
    let _hconnS : ConnectedSpace (pullback (specMap k E) fs : Scheme) :=
      Js.hom.homeomorph.connectedSpace_iff.mpr inferInstance
    let _hconnT : ConnectedSpace (pullback (specMap k E) ft : Scheme) :=
      Jt.hom.homeomorph.connectedSpace_iff.mpr inferInstance
    let es := namedModelPointedGroupEquiv Js (arithmeticConstantFieldLift k E κ fs xi₁)
      (rationalConfigurationArithmeticBasePoint E κ s Ω₁) hxs
    let et := namedModelPointedGroupEquiv Jt (arithmeticConstantFieldLift k E κ ft xi₂)
      (rationalConfigurationArithmeticBasePoint E κ t Ω₂) hxt
    let αE := arithmeticConstantFieldCoverGroupTransport k E κ fs ft xi₁ xi₂ α hα
    let β₀ := es.symm.trans (αE.trans et)
    ∀ (_he₀ : ∀ v, rationalConfigurationGeometricInclusion E κ t Ω₂ (e₀ v) =
      β₀ (rationalConfigurationGeometricInclusion E κ s Ω₁ v)),
    let τ := (rationalConfigurationBoundaryPlaceEquiv E κ s).symm.trans
      (σ.trans (rationalConfigurationBoundaryPlaceEquiv E κ t))
    ∀ (_hτ : ∀ p,
      ((rationalConfigurationChosenInertia E κ s Ω₁ p).map
        (TopologicalAbelianization.mk (rationalConfigurationGeometricGroup E κ s Ω₁))).map
          (TopologicalAbelianization.congr e₀).toMonoidHom =
        (rationalConfigurationChosenInertia E κ t Ω₂ (τ p)).map
          (TopologicalAbelianization.mk (rationalConfigurationGeometricGroup E κ t Ω₂))),
    ∃ J : (U₁ : Scheme) ≅ (U₂ : Scheme), J.hom ≫ (U₂.ι ≫ c₂) = U₁.ι ≫ c₁ := by
  classical
  intro fs ft gs gt Zs Zt hxs hxt hconnS hconnT es et αE β₀ he₀ τ hτ
  let Xs := pullback (specMap k κ) fs
  let Xt := pullback (specMap k κ) ft
  have hXs : IsIntegral Xs := IsIntegral.of_isIso (pullbackSymmetry fs (specMap k κ)).hom
  have hXt : IsIntegral Xt := IsIntegral.of_isIso (pullbackSymmetry ft (specMap k κ)).hom
  have : CompactSpace Xs :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst (specMap k κ) fs)
  have : CompactSpace Xt :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst (specMap k κ) ft)
  let Bs := scalarExtensionModelIso k E κ fs gs Js hJs
  let Bt := scalarExtensionModelIso k E κ ft gt Jt hJt
  let AXs : Algebra Xs.functionField Ω₁ := namedBaseTransportAmbientAlgebra Bs.symm Ω₁
  let AXt : Algebra Xt.functionField Ω₂ := namedBaseTransportAmbientAlgebra Bt.symm Ω₂
  obtain ⟨hAXs, hBs, hcoef₁, hxi₁⟩ :=
    scalarExtensionModelIso_original_genericPoint k E κ Ω₁ fs s Js hJs xi₁ hxs.symm hcoefS
  obtain ⟨hAXt, hBt, hcoef₂, hxi₂⟩ :=
    scalarExtensionModelIso_original_genericPoint k E κ Ω₂ ft t Jt hJt xi₂ hxt.symm hcoefT
  let xsg := Xs.genericExtensionMorphism Ω₁
  let xtg := Xt.genericExtensionMorphism Ω₂
  let bs := namedModelPointedGroupEquiv Bs xsg (Zs.genericExtensionMorphism Ω₁) hBs
  let bt := namedModelPointedGroupEquiv Bt xtg (Zt.genericExtensionMorphism Ω₂) hBt
  let eOrig := bs.trans (e₀.trans bt.symm)
  have hOrig := scalarExtensionModels_original_arithmetic_square k E κ
    fs ft gs gt Js Jt xi₁ xi₂
    (Zs.genericExtensionMorphism Ω₁) (Zt.genericExtensionMorphism Ω₂)
    hxs hxt hJs hJt xsg xtg hBs hBt hxi₁ hxi₂ α hα e₀ he₀
  exact exists_schemeIso_of_geometric_model_comparison k E κ Ω₁ Ω₂ c₁ c₂ U₁ U₂
    s t hs ht I₁ I₂ hproper₁ hproper₂ Js Jt hJs hJt hJsambient hJtambient
    xi₁ xi₂ hbase₁ hbase₂ halign₁ halign₂ hcoefS hcoefT α hα e₀ σ F hF I hIambient hIbase
    hBs hBt hcoef₁ hcoef₂ hxi₁ hxi₂ hOrig hτ


/-- Weak reconstruction for genus-zero opens with at least three geometric
punctures, including nonsplit compactifications and nonrational punctures.
Only the original pointed arithmetic isomorphism is supplied. -/
theorem exists_schemeIso_of_genusZero_arithmeticFundamentalGroupEquiv
    (k : Type) [Field k] [NumberField k]
    {C₁ C₂ : Scheme}
    (c₁ : C₁ ⟶ Spec (.of k)) (c₂ : C₂ ⟶ Spec (.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (U₁ : C₁.Opens) (U₂ : C₂.Opens)
    (hg₁ : geometricGenus k c₁ = 0) (hg₂ : geometricGenus k c₂ = 0)
    (hr₁ : 3 ≤ Nat.card
      {x : closedPoints (pullback c₁ (specMap k (AlgebraicClosure k)) : Scheme) //
        x.val ∉ pullback.fst c₁ (specMap k (AlgebraicClosure k)) ⁻¹ᵁ U₁})
    (hr₂ : 3 ≤ Nat.card
      {x : closedPoints (pullback c₂ (specMap k (AlgebraicClosure k)) : Scheme) //
        x.val ∉ pullback.fst c₂ (specMap k (AlgebraicClosure k)) ⁻¹ᵁ U₂})
    {Λ₁ Λ₂ : Type} [Field Λ₁] [Field Λ₂] [IsSepClosed Λ₁] [IsSepClosed Λ₂]
    (x₁ : Spec (.of Λ₁) ⟶ (U₁ : Scheme)) (x₂ : Spec (.of Λ₂) ⟶ (U₂ : Scheme))
    (eP : π₁ᵉᵗ(x₁) ≃ₜ* π₁ᵉᵗ(x₂))
    (hP : ∀ γ, arithmeticFundamentalGroupHom k (AlgebraicClosure k)
        (U₂.ι ≫ c₂) x₂ (eP γ) =
      arithmeticFundamentalGroupHom k (AlgebraicClosure k) (U₁.ι ≫ c₁) x₁ γ) :
    ∃ I : (U₁ : Scheme) ≅ (U₂ : Scheme),
      I.hom ≫ (U₂.ι ≫ c₂) = U₁.ι ≫ c₁ := by
  classical
  let κ := AlgebraicClosure k
  have hC₁ : IsIntegral C₁ := GeometricallyIntegral.isIntegral_of_subsingleton c₁
  have hC₂ : IsIntegral C₂ := GeometricallyIntegral.isIntegral_of_subsingleton c₂
  have hU₁ : (U₁ : Set C₁).Nonempty :=
    ⟨(x₁ (IsLocalRing.closedPoint Λ₁)).val, (x₁ (IsLocalRing.closedPoint Λ₁)).property⟩
  have hU₂ : (U₂ : Set C₂).Nonempty :=
    ⟨(x₂ (IsLocalRing.closedPoint Λ₂)).val, (x₂ (IsLocalRing.closedPoint Λ₂)).property⟩
  have hN₁ : Nonempty (U₁ : Scheme) := ⟨⟨hU₁.choose, hU₁.choose_spec⟩⟩
  have hN₂ : Nonempty (U₂ : Scheme) := ⟨⟨hU₂.choose, hU₂.choose_spec⟩⟩
  have hI₁ : IsIntegral (U₁ : Scheme) := isIntegral_of_isOpenImmersion U₁.ι
  have hI₂ : IsIntegral (U₂ : Scheme) := isIntegral_of_isOpenImmersion U₂.ι
  have : IsLocallyNoetherian C₁ := LocallyOfFiniteType.isLocallyNoetherian c₁
  have : IsLocallyNoetherian C₂ := LocallyOfFiniteType.isLocallyNoetherian c₂
  have : CompactSpace C₁ := QuasiCompact.compactSpace_of_compactSpace c₁
  have : CompactSpace C₂ := QuasiCompact.compactSpace_of_compactSpace c₂
  have : CompactSpace (U₁ : Scheme) := QuasiCompact.compactSpace_of_compactSpace U₁.ι
  have : CompactSpace (U₂ : Scheme) := QuasiCompact.compactSpace_of_compactSpace U₂.ι
  let Ω₁ := AlgebraicClosure (U₁ : Scheme).functionField
  let Ω₂ := AlgebraicClosure (U₂ : Scheme).functionField
  let xi₁ := (U₁ : Scheme).genericExtensionMorphism Ω₁
  let xi₂ := (U₂ : Scheme).genericExtensionMorphism Ω₂
  let fs := U₁.ι ≫ c₁
  let ft := U₂.ι ≫ c₂
  have : Surjective fs := ⟨fun y => ⟨Nonempty.some hN₁, Subsingleton.elim _ y⟩⟩
  have : Surjective ft := ⟨fun y => ⟨Nonempty.some hN₂, Subsingleton.elim _ y⟩⟩
  have : GeometricallyIntegral fs := GeometricallyIntegral.comp_of_isOpenImmersion U₁.ι c₁
  have : GeometricallyIntegral ft := GeometricallyIntegral.comp_of_isOpenImmersion U₂.ι c₂
  have : GeometricallyConnected fs := GeometricallyIrreducible.geometricallyConnected fs
  have : GeometricallyConnected ft := GeometricallyIrreducible.geometricallyConnected ft
  obtain ⟨t₁, t₂, _ht₁, _ht₂, H⟩ :=
    exists_genusZero_finite_reconstruction k c₁ c₂ U₁ U₂ hU₁ hU₂
      hg₁ hg₂ hr₁ hr₂ x₁ x₂ eP hP
  let α := (continuousConjAut t₁).symm.trans (eP.trans (continuousConjAut t₂))
  obtain ⟨hα, H⟩ := H
  let AkΩ₁ : Algebra k Ω₁ := (Spec.preimage (xi₁ ≫ fs)).hom.toAlgebra
  let AkΩ₂ : Algebra k Ω₂ := (Spec.preimage (xi₂ ≫ ft)).hom.toAlgebra
  obtain ⟨b₁, b₂, H⟩ := H
  let AκΩ₁ : Algebra κ Ω₁ := b₁.toRingHom.toAlgebra
  let AκΩ₂ : Algebra κ Ω₂ := b₂.toRingHom.toAlgebra
  have hkκΩ₁ : IsScalarTower k κ Ω₁ :=
    IsScalarTower.of_algebraMap_eq (fun a => (b₁.commutes a).symm)
  have hkκΩ₂ : IsScalarTower k κ Ω₂ :=
    IsScalarTower.of_algebraMap_eq (fun a => (b₂.commutes a).symm)
  have hbase₁ : xi₁ ≫ fs = ξ k Ω₁ := (Spec.map_preimage (xi₁ ≫ fs)).symm
  have hbase₂ : xi₂ ≫ ft = ξ k Ω₂ := (Spec.map_preimage (xi₂ ≫ ft)).symm
  obtain ⟨halign₁, halign₂, E, H⟩ := H
  have hE : NumberField E := NumberField.of_module_finite k E
  have hEκ : IsAlgClosure E κ :=
    ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := k) (L := E) (A := κ)⟩
  have hFE : IsFiniteEtale (specMap k E) := constantField_specMap_isFiniteEtale k E
  obtain ⟨s, t, hs, ht, I₁, I₂, hproper₁, hproper₂,
    Js, Jt, hJs, hJt, hJsambient, hJtambient, H⟩ := H
  let gs := (rationalConfigurationOpen s).ι ≫ π E 1
  let gt := (rationalConfigurationOpen t).ι ≫ π E 1
  let Ys := pullback (specMap E κ) (pullback.fst (specMap k E) fs)
  let Yt := pullback (specMap E κ) (pullback.fst (specMap k E) ft)
  let Zs := rationalConfigurationGeometricScheme E κ s
  let Zt := rationalConfigurationGeometricScheme E κ t
  let Jκs := rationalModelGeometricIso k E κ fs s Js hJs
  let Jκt := rationalModelGeometricIso k E κ ft t Jt hJt
  obtain ⟨hYs, hYt, aS, aT, H⟩ := H
  let AYs : Algebra Ys.functionField Ω₁ := aS.toAlgebra
  let AYt : Algebra Yt.functionField Ω₂ := aT.toAlgebra
  obtain ⟨hAYs, hAYt, H⟩ := H
  let AZs : Algebra Zs.functionField Ω₁ := namedBaseTransportAmbientAlgebra Jκs Ω₁
  let AZt : Algebra Zt.functionField Ω₂ := namedBaseTransportAmbientAlgebra Jκt Ω₂
  obtain ⟨hAZs, hAZt, _hJκs, _hJκt, hcoefS, hcoefT, hxs, hxt, H⟩ := H
  let xsE := arithmeticConstantFieldLift k E κ fs xi₁
  let xtE := arithmeticConstantFieldLift k E κ ft xi₂
  let xs := rationalConfigurationArithmeticBasePoint E κ s Ω₁
  let xt := rationalConfigurationArithmeticBasePoint E κ t Ω₂
  have hconnS : ConnectedSpace (pullback (specMap k E) fs : Scheme) :=
    Js.hom.homeomorph.connectedSpace_iff.mpr inferInstance
  have hconnT : ConnectedSpace (pullback (specMap k E) ft : Scheme) :=
    Jt.hom.homeomorph.connectedSpace_iff.mpr inferInstance
  let es := namedModelPointedGroupEquiv Js xsE xs hxs
  let et := namedModelPointedGroupEquiv Jt xtE xt hxt
  obtain ⟨d, _hd, H⟩ := H
  let αE := arithmeticConstantFieldCoverGroupTransport k E κ fs ft xi₁ xi₂ α hα
  let β := es.symm.trans ((ProCGroups.innerCorrectedGroupEquiv αE d).trans et)
  obtain ⟨eΔ, heΔ, σ, hσ, F, hF, I, hIambient, hIbase⟩ := H
  let β₀ := es.symm.trans (αE.trans et)
  let τ := (rationalConfigurationBoundaryPlaceEquiv E κ s).symm.trans
    (σ.trans (rationalConfigurationBoundaryPlaceEquiv E κ t))
  obtain ⟨e₀, he₀, hτ⟩ := remove_corrected_model_comparison
    E κ s t Ω₁ Ω₂ es et αE d eΔ heΔ σ hσ
  exact exists_schemeIso_of_corrected_finite_models k E κ Ω₁ Ω₂ c₁ c₂ U₁ U₂
    s t hs ht I₁ I₂ hproper₁ hproper₂ Js Jt hJs hJt hJsambient hJtambient
    xi₁ xi₂ hbase₁ hbase₂ halign₁ halign₂ hcoefS hcoefT α hα e₀ σ F hF I hIambient hIbase
    hxs hxt he₀ hτ

end AnabelianGeometry.WeightFiltration
