/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AnabelianGeometry.FiniteField.GeometricBoundaryCount
public import Nyll.AlgebraicCurves.Models.Construction.OfSmoothProperCurve
public import Nyll.AlgebraicCurves.Models.Construction.FullConstantStructure
public import Nyll.EtaleFundamentalGroups.GaloisCovers.ConnectedCurveModel

/-!
# Boundary growth on the actual full-constant component

A connected proper finite étale cover dominating a geometrically integral
finite-constant model acquires its own full constants on the original
scheme. An embedding of those constants into the prescribed algebraic
closure is constructed compatibly with the dominated cover. The geometric
boundary therefore cannot shrink on that single component; no compatibility
or boundary-surjectivity premise is assumed.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve TopologicalSpace
open CategoryTheory.PreGaloisCategory EtaleFundamentalGroups

namespace AnabelianGeometry.FiniteField

/-- Literal recovery of a geometric proper model identifies its omitted
places with the original finite-constant model's geometric boundary.
The same map to the ground curve determines both complements. -/
theorem geometricBoundary_card_eq_of_recovered_model
    (L κ : Type) [Field L] [Field κ] [IsAlgClosed κ] [Algebra L κ]
    {F : Type} [Field F] [Algebra κ F] (M : CurveModel κ F)
    {N C : Scheme} (cN : N ⟶ Spec (.of L))
    (a : N ⟶ C) (d : M.C ⟶ C) (U : C.Opens)
    (R : Limits.pullback (Spec.algebraMap L κ) cN ≅ M.C)
    (hcoeff : R.hom ≫ M.toBase = Limits.pullback.fst (Spec.algebraMap L κ) cN)
    (hbase : R.hom ≫ d = Limits.pullback.snd (Spec.algebraMap L κ) cN ≫ a) :
    Nat.card (GeometricBoundaryPoint L κ cN (a ⁻¹ᵁ U).ι) =
      Nat.card (M.openBoundaryPlaces (d ⁻¹ᵁ U).ι) := by
  let ψ := Spec.algebraMap L κ
  let P (v : Place κ F) := M.pointEquivPlace.symm v
  let q (v : Place κ F) := (P v).val ≫ R.inv
  have hqfst (v : Place κ F) : q v ≫ Limits.pullback.fst ψ cN = 𝟙 _ := by
    dsimp only [q]
    rw [Category.assoc, ← hcoeff, R.inv_hom_id_assoc, (P v).property]
  have hqR (v : Place κ F) : q v ≫ R.hom = (P v).val := by
    dsimp only [q]
    rw [Category.assoc, R.inv_hom_id, Category.comp_id]
  have hqbase (v : Place κ F) : (P v).val ≫ d =
      (q v ≫ Limits.pullback.snd ψ cN) ≫ a := by
    rw [← hqR v, Category.assoc, hbase, ← Category.assoc]
  have hcenter (v : Place κ F) : (P v).val (IsLocalRing.closedPoint κ) =
      (M.placeEquiv.symm v).val := by
    change (pointEquivClosedPoint M.toBase
      ((pointEquivClosedPoint M.toBase).symm (M.placeEquiv.symm v))).val = _
    exact congrArg Subtype.val ((pointEquivClosedPoint M.toBase).apply_symm_apply _)
  let mapB : M.openBoundaryPlaces (d ⁻¹ᵁ U).ι →
      GeometricBoundaryPoint L κ cN (a ⁻¹ᵁ U).ι := fun v =>
    ⟨⟨q v.val ≫ Limits.pullback.snd ψ cN, by
      rw [Category.assoc, ← Limits.pullback.condition, ← Category.assoc,
        hqfst, Category.id_comp]⟩, by
      have hv := v.property
      change (M.placeEquiv.symm v.val).val ∉ Set.range (d ⁻¹ᵁ U).ι at hv
      rw [← hcenter v.val, Scheme.Opens.range_ι] at hv
      rw [Scheme.Opens.range_ι]
      change ((q v.val ≫ Limits.pullback.snd ψ cN) ≫ a)
        (IsLocalRing.closedPoint κ) ∉ U
      rw [← hqbase]
      exact hv⟩
  have hinj : Function.Injective mapB := by
    intro v w hvw
    have hsnd : q v.val ≫ Limits.pullback.snd ψ cN =
        q w.val ≫ Limits.pullback.snd ψ cN :=
      congrArg (fun b => b.val.val) hvw
    have hq : q v.val = q w.val := by
      apply Limits.pullback.hom_ext
      · exact (hqfst v.val).trans (hqfst w.val).symm
      · exact hsnd
    have hP : P v.val = P w.val := Subtype.ext
      ((hqR v.val).symm.trans ((congrArg (fun z => z ≫ R.hom) hq).trans (hqR w.val)))
    exact Subtype.ext (M.pointEquivPlace.symm.injective hP)
  have hsurj : Function.Surjective mapB := by
    intro b
    let s := Limits.pullback.lift (𝟙 (Spec (.of κ))) b.val.val
      ((Category.id_comp ψ).trans b.val.property.symm)
    have hsfst : s ≫ Limits.pullback.fst ψ cN = 𝟙 _ := Limits.pullback.lift_fst _ _ _
    have hssnd : s ≫ Limits.pullback.snd ψ cN = b.val.val := Limits.pullback.lift_snd _ _ _
    let p : {p : Spec (.of κ) ⟶ M.C // p ≫ M.toBase = 𝟙 _} :=
      ⟨s ≫ R.hom, by rw [Category.assoc, hcoeff, hsfst]⟩
    let v := M.pointEquivPlace p
    have hPv : P v = p := M.pointEquivPlace.symm_apply_apply p
    have hqv : q v = s := by
      dsimp only [q]
      rw [hPv]
      change (s ≫ R.hom) ≫ R.inv = s
      rw [Category.assoc, R.hom_inv_id, Category.comp_id]
    have hv : v ∈ M.openBoundaryPlaces (d ⁻¹ᵁ U).ι := by
      change (M.placeEquiv.symm v).val ∉ Set.range (d ⁻¹ᵁ U).ι
      rw [← hcenter v, Scheme.Opens.range_ι]
      change ((P v).val ≫ d) (IsLocalRing.closedPoint κ) ∉ U
      rw [hqbase v, hqv, hssnd]
      intro hmem
      exact b.property ((congrArg
        (fun S : Set N => b.val.val (IsLocalRing.closedPoint κ) ∈ S)
        (Scheme.Opens.range_ι (a ⁻¹ᵁ U))).mpr hmem)
    refine ⟨⟨v, hv⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change q v ≫ Limits.pullback.snd ψ cN = b.val.val
    rw [hqv, hssnd]
  exact (Nat.card_eq_of_bijective mapB ⟨hinj, hsurj⟩).symm


/-- Actual finite étale domination supplies compatible full constants and
preserves the geometric boundary of the dominated finite-constant cover.
The original scheme, map to the ground curve and generic source are retained. -/
theorem exists_fullConstants_boundary_domination
    (k L κ : Type) [Field k] [Finite k] [Field L] [Field κ] [IsAlgClosed κ]
    [Algebra k L] [FiniteDimensional k L]
    [Algebra k κ] [Algebra L κ] [IsScalarTower k L κ]
    {C : Scheme} [IsIntegral C] (c : C ⟶ Spec (.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c]
    (B A : AlgebraicGeometry.FiniteEtale C) [IsConnected B]
    (cL : A.left ⟶ Spec (.of L)) [GeometricallyIntegral cL]
    (hcL : cL ≫ Spec.map (CommRingCat.ofHom (algebraMap k L)) = A.hom ≫ c)
    (t : B.left ⟶ A.left) (ht : t ≫ A.hom = B.hom)
    (U : C.Opens) (hU : (U : Set C).Nonempty) :
    ∃ (_ : IsIntegral B.left),
      let : Algebra k B.left.functionField :=
        (baseToFunctionField (C := B.left) (B.hom ≫ c)).toAlgebra
      let E := algebraicClosure k B.left.functionField
      Finite E ∧ ∃ (cE : B.left ⟶ Spec (.of E)) (σ : E →ₐ[k] κ),
        cE ≫ Spec.map (CommRingCat.ofHom (algebraMap k E)) = B.hom ≫ c ∧
        IsProper cE ∧ SmoothOfRelativeDimension 1 cE ∧ GeometricallyIntegral cE ∧
        B.left.fromSpecStalk (genericPoint B.left) ≫ cE =
          Spec.map (CommRingCat.ofHom (algebraMap E B.left.functionField)) ∧
        let : Algebra E κ := σ.toRingHom.toAlgebra
        Nat.card (GeometricBoundaryPoint L κ cL (A.hom ⁻¹ᵁ U).ι) ≤
          Nat.card (GeometricBoundaryPoint E κ cE (B.hom ⁻¹ᵁ U).ι) := by
  have : Smooth c := SmoothOfRelativeDimension.smooth 1 c
  have : IsIntegrallyClosed Γ(Spec (.of k), ⊤) :=
    IsIntegrallyClosed.of_equiv (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv
  have : IsNormalIntegral C := IsNormalIntegral.of_stalks C
    (fun x => (Smooth.isDomain_and_isIntegrallyClosed_stalk c x).2)
  have hBIntegral : IsIntegral B.left := isIntegral_left_of_isConnected_finiteEtale B
  refine ⟨hBIntegral, ?_⟩
  intro fieldAlgebra E
  have : IsFiniteEtale B.hom := B.prop
  have : IsProper (B.hom ≫ c) := inferInstance
  have : SmoothOfRelativeDimension 1 (B.hom ≫ c) :=
    smoothOfRelativeDimension_comp 0 1 B.hom c
  let M : CurveModel k B.left.functionField :=
    CurveModel.ofSmoothProperCurve (C := B.left) (B.hom ≫ c)
  have htL : (t ≫ cL) ≫ Spec.map (CommRingCat.ofHom (algebraMap k L)) = M.toBase := by
    change (t ≫ cL) ≫ Spec.map (CommRingCat.ofHom (algebraMap k L)) = B.hom ≫ c
    rw [Category.assoc, hcL, ← Category.assoc, ht]
  obtain ⟨hfinite, cModel, φ, σ, hbase, hproper, hsmooth, hgeom, hgeneric, hstruct, hcoeff⟩ :=
    M.exists_fullConstants_structure_compatible (κ := κ) (t ≫ cL) htL
  let cE : B.left ⟶ Spec (.of E) := cModel
  have hcEproper : IsProper cE := hproper
  have hcEsmooth : SmoothOfRelativeDimension 1 cE := hsmooth
  have hcEgeom : GeometricallyIntegral cE := hgeom
  have : Finite E := hfinite
  have hgeneric' : B.left.fromSpecStalk (genericPoint B.left) ≫ cE =
      Spec.map (CommRingCat.ofHom (algebraMap E B.left.functionField)) := by
    change (Spec.map (CommRingCat.ofHom (RingHom.id B.left.functionField)) ≫
      B.left.fromSpecStalk (genericPoint B.left)) ≫ cE = _ at hgeneric
    simpa only [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp] using hgeneric
  refine ⟨hfinite, cE, σ, hbase, hproper, hsmooth, hgeom, hgeneric', ?_⟩
  intro coefficientAlgebra
  have : IsScalarTower k E κ :=
    IsScalarTower.of_algebraMap_eq (fun a => (σ.commutes a).symm)
  have hcoeffSpec : Spec.map (CommRingCat.ofHom (algebraMap E κ)) ≫
      Spec.map (CommRingCat.ofHom φ.toRingHom) =
        Spec.map (CommRingCat.ofHom (algebraMap L κ)) := by
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    ext a
    exact hcoeff a
  exact boundaryCard_le_of_cover_domination_constant_rebase k E L κ c B A cE cL
    hbase hcL t ht (Spec.map (CommRingCat.ofHom φ.toRingHom)) hcoeffSpec hstruct U hU

end AnabelianGeometry.FiniteField
