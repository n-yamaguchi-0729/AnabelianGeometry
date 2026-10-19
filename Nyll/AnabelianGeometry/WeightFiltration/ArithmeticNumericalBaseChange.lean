/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.ArithmeticNumericalInvariants
import Nyll.AlgebraicCurves.Geometry.Schemes.Points.FiniteIntermediateFieldSection
import Nyll.AlgebraicCurves.Geometry.Curves.GeometricGenusBaseChange
import Nyll.AlgebraicCurves.Models.Construction.Transport
import Nyll.EtaleFundamentalGroups.GeometricFiber.ArithmeticConstantFieldStrictTransport
import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.ConstantFieldTower
import Nyll.SchemeTheory.Morphisms.ConstantTwistTower
import Nyll.SchemeTheory.Morphisms.GeometricallyIrreducibleConnected
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.FieldTheory.Galois.Basic

/-! # Numerical reconstruction without rational-point inputs

A common finite Galois coefficient field supplies rational sections of both
compactifications. Strict transport of the original arithmetic isomorphism
then permits the intrinsic weight calculation over that field. The actual
constant-base-change squares identify the geometric boundaries, and geometric
genus is unchanged. No section, model or boundary-preservation comparison is
required at the public reconstruction endpoint.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AlgebraicCurve
open AlgebraicGeometry.FiniteEtale AlgebraicGeometry.SmoothProperCurve
open NeronModelInfra EtaleFundamentalGroups

namespace AnabelianGeometry.WeightFiltration

private theorem exists_common_finiteGalois_sections
    (k κ : Type) [Field k] [Field κ] [Algebra k κ] [IsGalois k κ] [IsAlgClosed κ]
    {C₁ C₂ : Scheme} [Nonempty C₁] [Nonempty C₂]
    (c₁ : C₁ ⟶ Spec (.of k)) (c₂ : C₂ ⟶ Spec (.of k))
    [LocallyOfFiniteType c₁] [LocallyOfFiniteType c₂] :
    ∃ E : IntermediateField k κ, Module.Finite k E ∧ IsGalois k E ∧
      Nonempty (SchemeHomOver (𝟙 (Spec (.of E))) (baseChange k c₁ E)) ∧
      Nonempty (SchemeHomOver (𝟙 (Spec (.of E))) (baseChange k c₂ E)) := by
  obtain ⟨F₁, hF₁, p₁, hp₁, _⟩ := Scheme.exists_finiteIntermediateField_section k κ c₁
  obtain ⟨F₂, hF₂, p₂, hp₂, _⟩ := Scheme.exists_finiteIntermediateField_section k κ c₂
  let : Module.Finite k F₁ := hF₁
  let : Module.Finite k F₂ := hF₂
  let D : IntermediateField k κ := F₁ ⊔ F₂
  let : Module.Finite k D := IntermediateField.finiteDimensional_sup F₁ F₂
  let E : IntermediateField k κ := IntermediateField.normalClosure k D κ
  let : Module.Finite k E := normalClosure.is_finiteDimensional k D κ
  let : IsGalois k E := IsGalois.normalClosure k D κ
  have h₁ : F₁ ≤ E := le_sup_left.trans (IntermediateField.le_normalClosure D)
  have h₂ : F₂ ≤ E := le_sup_right.trans (IntermediateField.le_normalClosure D)
  let a₁ := IntermediateField.inclusion h₁
  let a₂ := IntermediateField.inclusion h₂
  let q₁ := Spec.map (CommRingCat.ofHom a₁.toRingHom) ≫ p₁
  let q₂ := Spec.map (CommRingCat.ofHom a₂.toRingHom) ≫ p₂
  have hq₁ : q₁ ≫ c₁ = specMap k E := by
    change (Spec.map (CommRingCat.ofHom a₁.toRingHom) ≫ p₁) ≫ c₁ = _
    rw [Category.assoc, hp₁, ← Spec.map_comp]
    congr 1
  have hq₂ : q₂ ≫ c₂ = specMap k E := by
    change (Spec.map (CommRingCat.ofHom a₂.toRingHom) ≫ p₂) ≫ c₂ = _
    rw [Category.assoc, hp₂, ← Spec.map_comp]
    congr 1
  refine ⟨E, inferInstance, inferInstance, ⟨?_⟩, ⟨?_⟩⟩
  · exact ⟨pullback.lift q₁ (𝟙 _) (hq₁.trans (Category.id_comp _).symm),
      pullback.lift_snd _ _ _⟩
  · exact ⟨pullback.lift q₂ (𝟙 _) (hq₂.trans (Category.id_comp _).symm),
      pullback.lift_snd _ _ _⟩

private def geometricOpenMap
    {T T' C U : Scheme} (φ : T' ⟶ T) (c : C ⟶ T) (i : U ⟶ C) :
    pullback φ (i ≫ c) ⟶ pullback c φ :=
  coefficientModelMap φ c i ≫ (pullbackSymmetry φ c).hom

private theorem geometricOpenMap_fst
    {T T' C U : Scheme} (φ : T' ⟶ T) (c : C ⟶ T) (i : U ⟶ C) :
    geometricOpenMap φ c i ≫ pullback.fst c φ = pullback.snd φ (i ≫ c) ≫ i := by
  simp only [geometricOpenMap, Category.assoc, pullbackSymmetry_hom_comp_fst,
    coefficientModelMap, pullback.lift_snd]

private theorem geometricOpenMap_snd
    {T T' C U : Scheme} (φ : T' ⟶ T) (c : C ⟶ T) (i : U ⟶ C) :
    geometricOpenMap φ c i ≫ pullback.snd c φ = pullback.fst φ (i ≫ c) := by
  simp only [geometricOpenMap, Category.assoc, pullbackSymmetry_hom_comp_snd,
    coefficientModelMap, pullback.lift_fst]

private theorem closedBoundary_card_eq_of_square
    {C₁ C₂ U₁ U₂ : Scheme} (i₁ : U₁ ⟶ C₁) (i₂ : U₂ ⟶ C₂)
    (I : C₁ ≅ C₂) (J : U₁ ≅ U₂) (h : J.hom ≫ i₂ = i₁ ≫ I.hom) :
    Nat.card {x : closedPoints C₁ // x.val ∉ Set.range i₁} =
      Nat.card {x : closedPoints C₂ // x.val ∉ Set.range i₂} := by
  let e := (CurveModel.closedPointsEquivOfIso I).symm
  apply Nat.card_congr (e.subtypeEquiv ?_)
  intro x
  apply not_congr
  change x.val ∈ Set.range i₁ ↔ I.hom x.val ∈ Set.range i₂
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨J.hom u, ?_⟩
    exact (congrArg (fun f : U₁ ⟶ C₂ => f u) h).trans (congrArg I.hom hu)
  · rintro ⟨v, hv⟩
    obtain ⟨u, rfl⟩ := J.hom.homeomorph.surjective v
    refine ⟨u, I.hom.homeomorph.injective ?_⟩
    exact (congrArg (fun f : U₁ ⟶ C₂ => f u) h).symm.trans hv

/-- The actual geometric boundary is unchanged by an intermediate constant
extension. Both proper and open schemes are compared by their pullback maps. -/
private theorem boundaryCard_constantBaseChange
    (k κ : Type) [Field k] [Field κ] [Algebra k κ]
    (E : IntermediateField k κ) {C U : Scheme}
    (c : C ⟶ Spec (.of k)) (i : U ⟶ C) :
    let cE := baseChange k c E
    let iE := geometricOpenMap (specMap k E) c i
    Nat.card {x : closedPoints (pullback cE (specMap E κ) : Scheme) //
      x.val ∉ Set.range (geometricOpenMap (specMap E κ) cE iE)} =
        Nat.card {x : closedPoints (pullback c (specMap k κ) : Scheme) //
          x.val ∉ Set.range (geometricOpenMap (specMap k κ) c i)} := by
  intro cE iE
  let φ := specMap k E
  let ψ := specMap E κ
  let b := specMap k κ
  let f := i ≫ c
  have hiE : iE ≫ cE = pullback.fst φ f := geometricOpenMap_snd φ c i
  let T := Scheme.constantBaseChangeTowerIso k E κ c
  let tower : pullback ψ (pullback.fst φ f) ≅ pullback b f :=
    constantFieldTowerIso k κ E U f
  let R : pullback ψ (iE ≫ cE) ≅ pullback b f :=
    pullback.congrHom rfl hiE ≪≫ tower
  have htowerFst : (tower).hom ≫ pullback.fst b f =
      pullback.fst ψ (pullback.fst φ f) :=
    constantFieldTowerIso_hom_fst k κ E U f
  have htowerSnd : (tower).hom ≫ pullback.snd b f =
      pullback.snd ψ (pullback.fst φ f) ≫ pullback.snd φ f :=
    constantFieldTowerIso_hom_snd k κ E U f
  have hRfst : R.hom ≫ pullback.fst b f = pullback.fst ψ (iE ≫ cE) := by
    dsimp only [R, Iso.trans]
    rw [Category.assoc, htowerFst]
    simp only [pullback.congrHom_hom, pullback.map, pullback.lift_fst, Category.comp_id]
  have hRsnd : R.hom ≫ pullback.snd b f =
      pullback.snd ψ (iE ≫ cE) ≫ pullback.snd φ f := by
    dsimp only [R, Iso.trans]
    rw [Category.assoc, htowerSnd, ← Category.assoc]
    simp only [pullback.congrHom_hom, pullback.map, pullback.lift_snd, Category.comp_id]
  apply closedBoundary_card_eq_of_square
    (geometricOpenMap ψ cE iE) (geometricOpenMap b c i) T R
  apply pullback.hom_ext
  · calc
      (R.hom ≫ geometricOpenMap b c i) ≫ pullback.fst c b =
          R.hom ≫ (pullback.snd b f ≫ i) := by
        rw [Category.assoc, geometricOpenMap_fst]
      _ = (pullback.snd ψ (iE ≫ cE) ≫ pullback.snd φ f) ≫ i := by
        rw [← Category.assoc, hRsnd]
      _ = pullback.snd ψ (iE ≫ cE) ≫ (iE ≫ pullback.fst c φ) := by
        rw [Category.assoc, geometricOpenMap_fst φ c i]
      _ = (geometricOpenMap ψ cE iE ≫ pullback.fst cE ψ) ≫
          pullback.fst c φ := by
        rw [geometricOpenMap_fst ψ cE iE, Category.assoc]
      _ = (geometricOpenMap ψ cE iE ≫ T.hom) ≫ pullback.fst c b := by
        exact (Category.assoc _ _ _).trans
          ((congrArg (fun z => geometricOpenMap ψ cE iE ≫ z)
            (Scheme.constantBaseChangeTowerIso_fst k E κ c).symm).trans
              (Category.assoc _ _ _).symm)
  · calc
      (R.hom ≫ geometricOpenMap b c i) ≫ pullback.snd c b =
          R.hom ≫ pullback.fst b f :=
        (Category.assoc _ _ _).trans
          (congrArg (fun z => R.hom ≫ z) (geometricOpenMap_snd b c i))
      _ = pullback.fst ψ (iE ≫ cE) := hRfst
      _ = geometricOpenMap ψ cE iE ≫ pullback.snd cE ψ :=
        (geometricOpenMap_snd ψ cE iE).symm
      _ = (geometricOpenMap ψ cE iE ≫ T.hom) ≫ pullback.snd c b :=
        (congrArg (fun z => geometricOpenMap ψ cE iE ≫ z)
          (Scheme.constantBaseChangeTowerIso_snd k E κ c).symm).trans
            (Category.assoc _ _ _).symm

/-- Numerical reconstruction from the original arithmetic groups, without
rational sections or auxiliary geometric models as inputs. The boundary
cardinality conclusion distinguishes empty and one-point boundaries in
positive genus. In genus zero, the indistinguishable zero/one-point pair
is excluded; one boundary with at least two points suffices. -/
theorem arithmeticEquiv_geometricGenus_and_boundaryCard
    (k κ : Type) [Field k] [NumberField k]
    [Field κ] [CharZero κ] [IsAlgClosed κ] [Algebra k κ] [IsSepClosure k κ]
    {C₁ C₂ U₁ U₂ : Scheme}
    (c₁ : C₁ ⟶ Spec (.of k)) (c₂ : C₂ ⟶ Spec (.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : U₁ ⟶ C₁) (i₂ : U₂ ⟶ C₂) [IsOpenImmersion i₁] [IsOpenImmersion i₂]
    {Ω₁ Ω₂ : Type} [Field Ω₁] [Field Ω₂] [IsSepClosed Ω₁] [IsSepClosed Ω₂]
    (xi₁ : Spec (.of Ω₁) ⟶ U₁) (xi₂ : Spec (.of Ω₂) ⟶ U₂)
    (eP : π₁ᵉᵗ(xi₁) ≃ₜ* π₁ᵉᵗ(xi₂))
    (hP : ∀ γ, arithmeticFundamentalGroupHom k κ (i₂ ≫ c₂) xi₂ (eP γ) =
      arithmeticFundamentalGroupHom k κ (i₁ ≫ c₁) xi₁ γ) :
    let j₁ := coefficientModelMap (specMap k κ) c₁ i₁ ≫
      (pullbackSymmetry (specMap k κ) c₁).hom
    let j₂ := coefficientModelMap (specMap k κ) c₂ i₂ ≫
      (pullbackSymmetry (specMap k κ) c₂).hom
    let B₁ := {x : closedPoints (pullback c₁ (specMap k κ) : Scheme) | x.val ∉ Set.range j₁}
    let B₂ := {x : closedPoints (pullback c₂ (specMap k κ) : Scheme) | x.val ∉ Set.range j₂}
    geometricGenus k c₁ = geometricGenus k c₂ ∧
      (Nat.card B₁ - 1 = Nat.card B₂ - 1) ∧
      (0 < geometricGenus k c₁ ∨ (0 < Nat.card B₁ ∧ 0 < Nat.card B₂) ∨
        2 ≤ Nat.card B₁ ∨ 2 ≤ Nat.card B₂ → Nat.card B₁ = Nat.card B₂) := by
  intro j₁ j₂ B₁ B₂
  classical
  have : IsLocallyNoetherian C₁ := LocallyOfFiniteType.isLocallyNoetherian c₁
  have : IsLocallyNoetherian C₂ := LocallyOfFiniteType.isLocallyNoetherian c₂
  have : IsLocallyNoetherian U₁ := isLocallyNoetherian_of_isOpenImmersion i₁
  have : IsLocallyNoetherian U₂ := isLocallyNoetherian_of_isOpenImmersion i₂
  have : CompactSpace C₁ := QuasiCompact.compactSpace_of_compactSpace c₁
  have : CompactSpace C₂ := QuasiCompact.compactSpace_of_compactSpace c₂
  have : CompactSpace U₁ := QuasiCompact.compactSpace_of_compactSpace i₁
  have : CompactSpace U₂ := QuasiCompact.compactSpace_of_compactSpace i₂
  have : QuasiSeparatedSpace U₁ := inferInstance
  have : QuasiSeparatedSpace U₂ := inferInstance
  let : Nonempty U₁ := ⟨xi₁ (Classical.choice (inferInstance : Nonempty (Spec (.of Ω₁))))⟩
  let : Nonempty U₂ := ⟨xi₂ (Classical.choice (inferInstance : Nonempty (Spec (.of Ω₂))))⟩
  let : Nonempty C₁ := ⟨i₁ (Nonempty.some inferInstance)⟩
  let : Nonempty C₂ := ⟨i₂ (Nonempty.some inferInstance)⟩
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
  let : ConnectedSpace U₁ := GeometricallyConnected.connectedSpace_of_subsingleton (i₁ ≫ c₁)
  let : ConnectedSpace U₂ := GeometricallyConnected.connectedSpace_of_subsingleton (i₂ ≫ c₂)
  let : IsGalois k κ := inferInstance
  obtain ⟨E, hfinite, hGalois, ⟨ε₁⟩, ⟨ε₂⟩⟩ :=
    exists_common_finiteGalois_sections k κ c₁ c₂
  let : Module.Finite k E := hfinite
  let : IsGalois k E := hGalois
  let : NumberField E := NumberField.of_module_finite k E
  let : IsSepClosure E κ :=
    ⟨IsSepClosure.sep_closed k, Algebra.isSeparable_tower_top_of_isSeparable k E κ⟩
  let : IsFiniteEtale (Spec.map (CommRingCat.ofHom (algebraMap k E))) :=
    constantField_specMap_isFiniteEtale k E
  let φ := specMap k E
  let UE₁ := pullback φ (i₁ ≫ c₁)
  let UE₂ := pullback φ (i₂ ≫ c₂)
  let cE₁ := baseChange k c₁ E
  let cE₂ := baseChange k c₂ E
  let iE₁ := geometricOpenMap φ c₁ i₁
  let iE₂ := geometricOpenMap φ c₂ i₂
  have hiE₁ : iE₁ ≫ cE₁ = pullback.fst φ (i₁ ≫ c₁) :=
    geometricOpenMap_snd φ c₁ i₁
  have hiE₂ : iE₂ ≫ cE₂ = pullback.fst φ (i₂ ≫ c₂) :=
    geometricOpenMap_snd φ c₂ i₂
  let : CompactSpace UE₁ := inferInstance
  let : CompactSpace UE₂ := inferInstance
  let : QuasiSeparatedSpace UE₁ :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd φ (i₁ ≫ c₁))
  let : QuasiSeparatedSpace UE₂ :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd φ (i₂ ≫ c₂))
  let : IsOpenImmersion (coefficientModelMap φ c₁ i₁) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := (show MorphismProperty Scheme from IsOpenImmersion))
      (coefficientBaseChange_isPullback φ c₁ i₁).flip (inferInstance : IsOpenImmersion i₁)
  let : IsOpenImmersion (coefficientModelMap φ c₂ i₂) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := (show MorphismProperty Scheme from IsOpenImmersion))
      (coefficientBaseChange_isPullback φ c₂ i₂).flip (inferInstance : IsOpenImmersion i₂)
  let : IsOpenImmersion iE₁ := by dsimp only [iE₁, geometricOpenMap]; infer_instance
  let : IsOpenImmersion iE₂ := by dsimp only [iE₂, geometricOpenMap]; infer_instance
  let xE₁ := arithmeticConstantFieldLift k E κ (i₁ ≫ c₁) xi₁
  let xE₂ := arithmeticConstantFieldLift k E κ (i₂ ≫ c₂) xi₂
  obtain ⟨d, _hd, hstrict⟩ := exists_arithmeticConstantFieldCover_strict_transport
    k E κ (i₁ ≫ c₁) (i₂ ≫ c₂) xi₁ xi₂ eP hP
  let αE := ProCGroups.innerCorrectedGroupEquiv
    (arithmeticConstantFieldCoverGroupTransport k E κ (i₁ ≫ c₁) (i₂ ≫ c₂)
      xi₁ xi₂ eP hP) d
  have hαE : ∀ γ, arithmeticFundamentalGroupHom E κ (iE₂ ≫ cE₂) xE₂ (αE γ) =
      arithmeticFundamentalGroupHom E κ (iE₁ ≫ cE₁) xE₁ γ := by
    intro γ
    rw [hiE₁, hiE₂]
    exact hstrict γ
  have hnum := arithmeticEquiv_geometricGenus_and_boundaryCard_of_sections
    E κ cE₁ cE₂ iE₁ iE₂ ε₁ ε₂ xE₁ xE₂ αE hαE
  have hb₁ : Nat.card {x : closedPoints (pullback cE₁ (specMap E κ) : Scheme) |
      x.val ∉ Set.range (coefficientModelMap (specMap E κ) cE₁ iE₁ ≫
        (pullbackSymmetry (specMap E κ) cE₁).hom)} = Nat.card B₁ :=
    boundaryCard_constantBaseChange k κ E c₁ i₁
  have hb₂ : Nat.card {x : closedPoints (pullback cE₂ (specMap E κ) : Scheme) |
      x.val ∉ Set.range (coefficientModelMap (specMap E κ) cE₂ iE₂ ≫
        (pullbackSymmetry (specMap E κ) cE₂).hom)} = Nat.card B₂ :=
    boundaryCard_constantBaseChange k κ E c₂ i₂
  dsimp only [cE₁, cE₂, iE₁, iE₂, φ, geometricOpenMap] at hnum hb₁ hb₂
  simpa only [geometricGenus_baseChange_of_finite_of_section k c₁ E ε₁,
    geometricGenus_baseChange_of_finite_of_section k c₂ E ε₂, hb₁, hb₂] using hnum

/-- The genus and geometric boundary count are recovered from the original
full arithmetic fundamental group, excluding only the genus-zero cases
with zero or one puncture on the first curve. Neither a section nor a
chosen geometric model is an input. -/
theorem arithmeticEquiv_type_eq_of_nonexceptional
    (k κ : Type) [Field k] [NumberField k]
    [Field κ] [CharZero κ] [IsAlgClosed κ] [Algebra k κ] [IsSepClosure k κ]
    {C₁ C₂ U₁ U₂ : Scheme}
    (c₁ : C₁ ⟶ Spec (.of k)) (c₂ : C₂ ⟶ Spec (.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : U₁ ⟶ C₁) (i₂ : U₂ ⟶ C₂) [IsOpenImmersion i₁] [IsOpenImmersion i₂]
    {Ω₁ Ω₂ : Type} [Field Ω₁] [Field Ω₂] [IsSepClosed Ω₁] [IsSepClosed Ω₂]
    (xi₁ : Spec (.of Ω₁) ⟶ U₁) (xi₂ : Spec (.of Ω₂) ⟶ U₂)
    (eP : π₁ᵉᵗ(xi₁) ≃ₜ* π₁ᵉᵗ(xi₂))
    (hP : ∀ γ, arithmeticFundamentalGroupHom k κ (i₂ ≫ c₂) xi₂ (eP γ) =
      arithmeticFundamentalGroupHom k κ (i₁ ≫ c₁) xi₁ γ) :
    let j₁ := coefficientModelMap (specMap k κ) c₁ i₁ ≫
      (pullbackSymmetry (specMap k κ) c₁).hom
    let j₂ := coefficientModelMap (specMap k κ) c₂ i₂ ≫
      (pullbackSymmetry (specMap k κ) c₂).hom
    let B₁ := {x : closedPoints (pullback c₁ (specMap k κ) : Scheme) | x.val ∉ Set.range j₁}
    let B₂ := {x : closedPoints (pullback c₂ (specMap k κ) : Scheme) | x.val ∉ Set.range j₂}
    (0 < geometricGenus k c₁ ∨ 2 ≤ Nat.card B₁) →
      geometricGenus k c₁ = geometricGenus k c₂ ∧ Nat.card B₁ = Nat.card B₂ := by
  intro j₁ j₂ B₁ B₂ hnonexceptional
  obtain ⟨hg, _hpred, hr⟩ := arithmeticEquiv_geometricGenus_and_boundaryCard
    k κ c₁ c₂ i₁ i₂ xi₁ xi₂ eP hP
  refine ⟨hg, hr ?_⟩
  rcases hnonexceptional with hgpos | hrpos
  · exact Or.inl hgpos
  · exact Or.inr (Or.inr (Or.inl hrpos))

end AnabelianGeometry.WeightFiltration
