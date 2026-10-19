/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Kummer.OpenKummerGenericSemilinear
import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldSourceGaloisNaturality
import Nyll.EtaleFundamentalGroups.GeometricFiber.CanonicalPointedMaps

/-!
# Restriction of a named arithmetic Kummer fiber

Scalar extension of the named unit and the actual field-coordinate equations
identify the two generic root equations. Actual field-source naturality and
surjectivity then identify the original geometric actions. No equality of
characters, restriction of covers, or equivariant fiber isomorphism is an input.
-/

noncomputable section
open AlgebraicGeometry AlgebraicGeometry.FiniteEtale AlgebraicCurve
open CategoryTheory CategoryTheory.PreGaloisCategory TopologicalSpace
open JacobianVarieties.Kummer
open scoped FintypeCatDiscrete

namespace AlgebraicCurve.CurveModel.OpenKummer

private theorem pointScalar_of_basepoint
    {κ Ω : Type} [Field κ] [Field Ω] [Algebra κ Ω]
    {Y : Scheme} (c : Y ⟶ Spec (.of κ)) (xi : Spec (.of Ω) ⟶ Y)
    (h : xi ≫ c = Spec.map (CommRingCat.ofHom (algebraMap κ Ω))) (z : κ) :
    pointScalar c xi z = algebraMap κ Ω z := by
  change (Scheme.ΓSpecIso (.of Ω)).hom
    ((xi ≫ c).appTop ((Scheme.ΓSpecIso (.of κ)).inv z)) = _
  rw [h]
  have hn := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap κ Ω)))
    ((Scheme.ΓSpecIso (.of κ)).inv z)
  change (Scheme.ΓSpecIso (.of Ω)).hom
    ((Spec.map (CommRingCat.ofHom (algebraMap κ Ω))).appTop
      ((Scheme.ΓSpecIso (.of κ)).inv z)) =
    algebraMap κ Ω ((Scheme.ΓSpecIso (.of κ)).hom ((Scheme.ΓSpecIso (.of κ)).inv z)) at hn
  rw [Iso.inv_hom_id_apply] at hn
  exact hn

private theorem pointedHom_eq_conjugation
    {X Y : Scheme} {Ω : Type} [Field Ω]
    (f : Y ⟶ X) (x : Spec (.of Ω) ⟶ Y) (y : Spec (.of Ω) ⟶ X)
    (h : x ≫ f = y) (g : π₁ᵉᵗ(x)) :
    pointedFundamentalGroupHom f x y h g =
      continuousConjAut (eqToIso (congrArg fiber h)) (fundamentalGroupHom f x g) := by
  subst y
  rfl

/-- Actual named Kummer fibers under scalar extension have a coefficient-
and geometric-equivariant comparison. The arithmetic torsor is chosen using
precisely the root coordinate used in this comparison. -/
theorem exists_namedKummer_geometricRestriction_equiv_with_rootCoordinate
    {k κ F L Ω : Type} [Field k] [Field κ] [Field F] [Field L] [Field Ω]
    [IsAlgClosed κ] [IsSepClosed Ω] [Algebra k F] [Algebra κ L] [Algebra F L]
    (M : CurveModel k F) (N : CurveModel κ L)
    (S : Set (Place k F)) (T : Set (Place κ L)) (n : ℕ+)
    (wa : Pic0.openKummerUnits k F S n) (wg : Pic0.openKummerUnits κ L T n)
    (hunit : (wg.val : L) = algebraMap F L (wa.val : F))
    {X Y : Scheme} [IsIntegral X] [IsNormalIntegral X] [CompactSpace X]
    [IsIntegral Y] [IsNormalIntegral Y] [CompactSpace Y]
    (jA : X ⟶ M.C) [IsOpenImmersion jA] (hjA : DenseRange jA)
    (jG : Y ⟶ N.C) [IsOpenImmersion jG] (hjG : DenseRange jG)
    (hiA : ∀ (y : X) (x : closedPoints M.C), x.val = jA y → M.placeOfPoint x ∉ S)
    (hiG : ∀ (y : Y) (x : closedPoints N.C), x.val = jG y → N.placeOfPoint x ∉ T)
    (hn : IsUnit ((n : ℕ) : k)) (hnκ : IsUnit ((n : ℕ) : κ))
    [Algebra F X.functionField] [Algebra L Y.functionField]
    [Algebra F Ω] [Algebra L Ω] [Algebra X.functionField Y.functionField]
    [Algebra X.functionField Ω] [Algebra Y.functionField Ω]
    [IsScalarTower F X.functionField Ω] [IsScalarTower L Y.functionField Ω]
    [IsScalarTower F L Ω] [IsScalarTower X.functionField Y.functionField Ω]
    [Algebra k X.functionField] [Algebra k κ] [Algebra k Ω] [Algebra κ Ω]
    [IsScalarTower k X.functionField Ω] [IsScalarTower k κ Ω]
    [IsSepClosure k κ] [IsSepClosure X.functionField Ω] [IsSepClosure Y.functionField Ω]
    (hfieldA : algebraMap F X.functionField = (jA.functionFieldMap hjA).comp M.ffEquiv.toRingHom)
    (hfieldG : algebraMap L Y.functionField = (jG.functionFieldMap hjG).comp N.ffEquiv.toRingHom)
    (a : Y ⟶ X)
    (hpoint : (Spec.map (CommRingCat.ofHom (algebraMap Y.functionField Ω)) ≫
      Y.fromSpecStalk (genericPoint Y)) ≫ a =
        Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) ≫
          X.fromSpecStalk (genericPoint X))
    (hbaseA : (Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) ≫
      X.fromSpecStalk (genericPoint X)) ≫ (jA ≫ M.toBase) =
        Spec.map (CommRingCat.ofHom (algebraMap k Ω)))
    (hbaseG : (Spec.map (CommRingCat.ofHom (algebraMap Y.functionField Ω)) ≫
      Y.fromSpecStalk (genericPoint Y)) ≫ (jG ≫ N.toBase) =
        Spec.map (CommRingCat.ofHom (algebraMap κ Ω))) :
    let xiA := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) ≫
      X.fromSpecStalk (genericPoint X)
    let xiG := Spec.map (CommRingCat.ofHom (algebraMap Y.functionField Ω)) ≫
      Y.fromSpecStalk (genericPoint Y)
    let WA := M.openKummerCover S n hn wa jA hjA hiA
    let WG := N.openKummerCover T n hnκ wg jG hjG hiG
    let q := arithmeticFundamentalGroupHom k κ (jA ≫ M.toBase) xiA
    let inc := pointedFundamentalGroupHom a xiG xiA hpoint
    letI := kummerGeometricRootAction N T n wg jG hjG hiG hnκ xiG
    ∃ tA : Torsor (rootsOfUnity (n : ℕ) κ) ((fiber xiA).obj WA),
      ∃ E : (fiber xiG).obj WG ≃ (fiber xiA).obj WA,
      ∃ eA : (fiber xiA).obj WA ≃
          {β : Ω // β ^ (n : ℕ) = algebraMap X.functionField Ω
            (jA.functionFieldMap hjA (M.ffEquiv (wa.val : F)))},
        (∀ (ζ : rootsOfUnity (n : ℕ) κ) x,
          (eA (tA.toMulAction.toSMul.smul ζ x)).val =
            algebraMap κ Ω (ζ.val : κ) * (eA x).val) ∧
        (∀ (σ : Gal(Ω/X.functionField)) (x : (fiber xiA).obj WA),
          (eA ((show π₁ᵉᵗ(xiA) from
            fundamentalGroupHom (X.fromSpecStalk (genericPoint X))
              (Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)))
              (toAut (fib X.functionField Ω) Gal(Ω/X.functionField) σ)) • x)).val =
                σ (eA x).val) ∧
        (∀ (ζ : rootsOfUnity (n : ℕ) κ) x,
          E (ζ • x) = tA.toMulAction.toSMul.smul ζ (E x)) ∧
        (∀ (g : π₁ᵉᵗ(xiG)) x, E (g • x) = inc g • E x) ∧
        ∀ (p : π₁ᵉᵗ(xiA)) (ζ : rootsOfUnity (n : ℕ) κ) x,
          p • (tA.toMulAction.toSMul.smul ζ x) =
            tA.toMulAction.toSMul.smul
              (restrictRootsOfUnity (q p).toRingHom (n : ℕ) ζ) (p • x) := by
  intro xiA xiG WA WG q inc
  let := kummerGeometricRootAction N T n wg jG hjG hiG hnκ xiG
  obtain ⟨eA, tA, _hscaleA, htA, hgA, hsemiA⟩ :=
    exists_arithmeticKummerFiber_genericSemilinearTorsor_with_genericEvaluation
      M S n wa jA hjA hiA hn (κ := κ) (Ω := Ω) hbaseA
  obtain ⟨eG, hscaleG, hgG⟩ := exists_arithmeticKummerFiber_genericRootEquiv
    N T n wg jG hjG hiG hnκ (Ω := Ω)
  have hA : algebraMap F Ω (wa.val : F) =
      algebraMap X.functionField Ω (jA.functionFieldMap hjA (M.ffEquiv (wa.val : F))) := by
    rw [IsScalarTower.algebraMap_eq F X.functionField Ω, hfieldA]
    rfl
  have hG : algebraMap L Ω (wg.val : L) =
      algebraMap Y.functionField Ω (jG.functionFieldMap hjG (N.ffEquiv (wg.val : L))) := by
    rw [IsScalarTower.algebraMap_eq L Y.functionField Ω, hfieldG]
    rfl
  have hval :
      algebraMap Y.functionField Ω (jG.functionFieldMap hjG (N.ffEquiv (wg.val : L))) =
      algebraMap X.functionField Ω (jA.functionFieldMap hjA (M.ffEquiv (wa.val : F))) := by
    calc
      _ = algebraMap L Ω (wg.val : L) := hG.symm
      _ = algebraMap L Ω (algebraMap F L (wa.val : F)) := congrArg (algebraMap L Ω) hunit
      _ = algebraMap F Ω (wa.val : F) := by rw [IsScalarTower.algebraMap_eq F L Ω]; rfl
      _ = _ := hA
  let er :
      {β : Ω // β ^ (n : ℕ) =
        algebraMap Y.functionField Ω (jG.functionFieldMap hjG (N.ffEquiv (wg.val : L)))} ≃
      {β : Ω // β ^ (n : ℕ) =
        algebraMap X.functionField Ω (jA.functionFieldMap hjA (M.ffEquiv (wa.val : F)))} := {
    toFun := fun β => ⟨β.val, β.property.trans hval⟩
    invFun := fun β => ⟨β.val, β.property.trans hval.symm⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  let E := eG.trans (er.trans eA.symm)
  have hE (x : (fiber xiG).obj WG) : (eA (E x)).val = (eG x).val :=
    congrArg Subtype.val (eA.apply_symm_apply (er (eG x)))
  refine ⟨tA, E, eA, htA, hgA, ?_, ?_, hsemiA⟩
  · intro ζ x
    apply eA.injective
    apply Subtype.ext
    exact (hE (ζ • x)).trans ((hscaleG ζ x).trans
      ((congrArg (fun c : Ω => c * (eG x).val)
        (pointScalar_of_basepoint (jG ≫ N.toBase) xiG hbaseG (ζ.val : κ))).trans
        ((congrArg (algebraMap κ Ω (ζ.val : κ) * ·) (hE x).symm).trans
          (htA ζ (E x)).symm)))
  · intro γ x
    let θG := fieldSourceAbsoluteGaloisHom Y.functionField Ω
      (Y.fromSpecStalk (genericPoint Y))
    let θA := fieldSourceAbsoluteGaloisHom X.functionField Ω
      (X.fromSpecStalk (genericPoint X))
    let : IsDominant (Y.fromSpecStalk (genericPoint Y)) := genericPoint_isDominant Y
    let : QuasiCompact (Y.fromSpecStalk (genericPoint Y)) :=
      { isCompact_preimage := fun V _ _ =>
          (Set.toFinite (Y.fromSpecStalk (genericPoint Y) ⁻¹' V)).isCompact }
    obtain ⟨σ, rfl⟩ := (fieldSourceAbsoluteGaloisHom_surjective Y.functionField Ω
      (Y.fromSpecStalk (genericPoint Y))) γ
    have hincl : inc (θG σ) = θA (σ.restrictScalars X.functionField) := by
      exact (pointedHom_eq_conjugation a xiG xiA hpoint (θG σ)).trans
        (fieldSourceAbsoluteGaloisHom_naturality X.functionField Y.functionField Ω a
          (Y.fromSpecStalk (genericPoint Y)) (X.fromSpecStalk (genericPoint X)) hpoint σ)
    have hθG : θG σ = fundamentalGroupHom (Y.fromSpecStalk (genericPoint Y))
        (Spec.map (CommRingCat.ofHom (algebraMap Y.functionField Ω)))
        (toAut (fib Y.functionField Ω) Gal(Ω/Y.functionField) σ) := by
      change fundamentalGroupHom (Y.fromSpecStalk (genericPoint Y))
        (Spec.map (CommRingCat.ofHom (algebraMap Y.functionField Ω)))
        (toAutHomeo (fib Y.functionField Ω) Gal(Ω/Y.functionField) σ) = _
      rw [toAutHomeo_apply]
    have hθA : θA (σ.restrictScalars X.functionField) =
        fundamentalGroupHom (X.fromSpecStalk (genericPoint X))
          (Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)))
          (toAut (fib X.functionField Ω) Gal(Ω/X.functionField)
            (σ.restrictScalars X.functionField)) := by
      change fundamentalGroupHom (X.fromSpecStalk (genericPoint X))
        (Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)))
        (toAutHomeo (fib X.functionField Ω) Gal(Ω/X.functionField)
          (σ.restrictScalars X.functionField)) = _
      rw [toAutHomeo_apply]
    apply eA.injective
    apply Subtype.ext
    have hAG : (eA (θA (σ.restrictScalars X.functionField) • E x)).val =
        σ (eA (E x)).val := by
      rw [hθA]
      exact hgA (σ.restrictScalars X.functionField) (E x)
    have hGG : (eG (θG σ • x)).val = σ (eG x).val := by
      rw [hθG]
      exact hgG σ x
    change (eA (E (θG σ • x))).val = (eA (inc (θG σ) • E x)).val
    rw [hincl]
    exact (hE (θG σ • x)).trans
      (hGG.trans ((congrArg σ (hE x).symm).trans hAG.symm))

/-- Backward-compatible projection of the comparison retaining the same
arithmetic generic-root coordinate. -/
theorem exists_namedKummer_geometricRestriction_equiv
    {k κ F L Ω : Type} [Field k] [Field κ] [Field F] [Field L] [Field Ω]
    [IsAlgClosed κ] [IsSepClosed Ω] [Algebra k F] [Algebra κ L] [Algebra F L]
    (M : CurveModel k F) (N : CurveModel κ L)
    (S : Set (Place k F)) (T : Set (Place κ L)) (n : ℕ+)
    (wa : Pic0.openKummerUnits k F S n) (wg : Pic0.openKummerUnits κ L T n)
    (hunit : (wg.val : L) = algebraMap F L (wa.val : F))
    {X Y : Scheme} [IsIntegral X] [IsNormalIntegral X] [CompactSpace X]
    [IsIntegral Y] [IsNormalIntegral Y] [CompactSpace Y]
    (jA : X ⟶ M.C) [IsOpenImmersion jA] (hjA : DenseRange jA)
    (jG : Y ⟶ N.C) [IsOpenImmersion jG] (hjG : DenseRange jG)
    (hiA : ∀ (y : X) (x : closedPoints M.C), x.val = jA y → M.placeOfPoint x ∉ S)
    (hiG : ∀ (y : Y) (x : closedPoints N.C), x.val = jG y → N.placeOfPoint x ∉ T)
    (hn : IsUnit ((n : ℕ) : k)) (hnκ : IsUnit ((n : ℕ) : κ))
    [Algebra F X.functionField] [Algebra L Y.functionField]
    [Algebra F Ω] [Algebra L Ω] [Algebra X.functionField Y.functionField]
    [Algebra X.functionField Ω] [Algebra Y.functionField Ω]
    [IsScalarTower F X.functionField Ω] [IsScalarTower L Y.functionField Ω]
    [IsScalarTower F L Ω] [IsScalarTower X.functionField Y.functionField Ω]
    [Algebra k X.functionField] [Algebra k κ] [Algebra k Ω] [Algebra κ Ω]
    [IsScalarTower k X.functionField Ω] [IsScalarTower k κ Ω]
    [IsSepClosure k κ] [IsSepClosure X.functionField Ω] [IsSepClosure Y.functionField Ω]
    (hfieldA : algebraMap F X.functionField = (jA.functionFieldMap hjA).comp M.ffEquiv.toRingHom)
    (hfieldG : algebraMap L Y.functionField = (jG.functionFieldMap hjG).comp N.ffEquiv.toRingHom)
    (a : Y ⟶ X)
    (hpoint : (Spec.map (CommRingCat.ofHom (algebraMap Y.functionField Ω)) ≫
      Y.fromSpecStalk (genericPoint Y)) ≫ a =
        Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) ≫
          X.fromSpecStalk (genericPoint X))
    (hbaseA : (Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) ≫
      X.fromSpecStalk (genericPoint X)) ≫ (jA ≫ M.toBase) =
        Spec.map (CommRingCat.ofHom (algebraMap k Ω)))
    (hbaseG : (Spec.map (CommRingCat.ofHom (algebraMap Y.functionField Ω)) ≫
      Y.fromSpecStalk (genericPoint Y)) ≫ (jG ≫ N.toBase) =
        Spec.map (CommRingCat.ofHom (algebraMap κ Ω))) :
    let xiA := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) ≫
      X.fromSpecStalk (genericPoint X)
    let xiG := Spec.map (CommRingCat.ofHom (algebraMap Y.functionField Ω)) ≫
      Y.fromSpecStalk (genericPoint Y)
    let WA := M.openKummerCover S n hn wa jA hjA hiA
    let WG := N.openKummerCover T n hnκ wg jG hjG hiG
    let q := arithmeticFundamentalGroupHom k κ (jA ≫ M.toBase) xiA
    let inc := pointedFundamentalGroupHom a xiG xiA hpoint
    letI := kummerGeometricRootAction N T n wg jG hjG hiG hnκ xiG
    ∃ tA : Torsor (rootsOfUnity (n : ℕ) κ) ((fiber xiA).obj WA),
      ∃ E : (fiber xiG).obj WG ≃ (fiber xiA).obj WA,
        (∀ (ζ : rootsOfUnity (n : ℕ) κ) x,
          E (ζ • x) = tA.toMulAction.toSMul.smul ζ (E x)) ∧
        (∀ (g : π₁ᵉᵗ(xiG)) x, E (g • x) = inc g • E x) ∧
        ∀ (p : π₁ᵉᵗ(xiA)) (ζ : rootsOfUnity (n : ℕ) κ) x,
          p • (tA.toMulAction.toSMul.smul ζ x) =
            tA.toMulAction.toSMul.smul
              (restrictRootsOfUnity (q p).toRingHom (n : ℕ) ζ) (p • x) := by
  intro xiA xiG WA WG q inc
  let := kummerGeometricRootAction N T n wg jG hjG hiG hnκ xiG
  obtain ⟨tA, E, _eA, _htA, _hgA, hμ, hI, hsemi⟩ :=
    exists_namedKummer_geometricRestriction_equiv_with_rootCoordinate
      M N S T n wa wg hunit jA hjA jG hjG hiA hiG hn hnκ
      hfieldA hfieldG a hpoint hbaseA hbaseG
  exact ⟨tA, E, hμ, hI, hsemi⟩

end AlgebraicCurve.CurveModel.OpenKummer
