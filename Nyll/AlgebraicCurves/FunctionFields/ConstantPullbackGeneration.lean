/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Geometry.Schemes.FunctionFields.FunctionFieldConstantExtension
public import Nyll.SchemeTheory.FunctionFields.StalkFunctoriality
public import Nyll.SchemeTheory.FunctionFields.ScalarFunctoriality
public import Nyll.SchemeTheory.FunctionFields.OpenImmersion
public import Nyll.SchemeTheory.FunctionFields.GenericFieldSourceNaturality
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs

/-!
# Generation for the literal projection of a constant pullback

The tensor-product generation theorem is transported to any actual pullback
square. Its old-field map is the canonical function-field map of the literal
projection, and its constants come from the literal structure morphism.
In particular this applies to the reversed pullback used by finite étale
covers, without postulating a comparison of function-field maps.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve TopologicalSpace
open EtaleFundamentalGroups Scheme.TwoAffineOpenCover

namespace AlgebraicGeometry

/-- In any actual constant pullback square, the canonical map of the
projection and the actual new constants generate its function field. -/
theorem constantPullback_adjoin_functionFieldMap
    {K : Type} [Field K] (K' : Type) [Field K'] [Algebra K K']
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (c : X ⟶ Spec (.of K)) (p : Y ⟶ X) (q : Y ⟶ Spec (.of K'))
    (hsq : IsPullback p q c (specMap K K')) (hp : DenseRange p) :
    let _ : Algebra K' Y.functionField := (baseToFunctionField q).toAlgebra
    IntermediateField.adjoin K' (Set.range (p.functionFieldMap hp)) = ⊤ := by
  intro instK'Y
  let Z := pullback c (specMap K K')
  let e : Y ≅ Z := hsq.isoPullback
  have : IsIntegral Z := IsIntegral.of_isIso e.hom
  let π : Z ⟶ X := pullback.fst c (specMap K K')
  let b : Z ⟶ Spec (.of K') := pullback.snd c (specMap K K')
  have heπ : e.hom ≫ π = p := hsq.isoPullback_hom_fst
  have heb : e.hom ≫ b = q := hsq.isoPullback_hom_snd
  have heiπ : e.inv ≫ p = π := hsq.isoPullback_inv_fst
  have he : DenseRange e.hom := e.hom.surjective.denseRange
  have hei : DenseRange e.inv := e.inv.surjective.denseRange
  have hπ : DenseRange π := by
    rw [← heiπ]
    exact hp.comp hei p.continuous
  let _ : Algebra K' Z.functionField := (baseToFunctionField b).toAlgebra
  let U := (X.affineCover.f (X.affineCover.idx (genericPoint X))).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange (X.affineCover.f _)
  have hη : genericPoint X ∈ U := X.affineCover.covers _
  have : Nonempty U := ⟨⟨genericPoint X, hη⟩⟩
  have : Nonempty (π ⁻¹ᵁ U) := by
    refine ⟨⟨genericPoint Z, ?_⟩⟩
    change π (genericPoint Z) ∈ U
    rw [π.map_genericPoint_of_denseRange hπ]
    exact hη
  have hgen : IntermediateField.adjoin K'
      (Set.range (π.functionFieldMap hπ)) = ⊤ := by
    apply adjoin_range_functionField_baseChange K' c U hU (π.functionFieldMap hπ)
    intro a
    exact (DFunLike.congr_fun (π.functionFieldMap_comp_germToFunctionField hπ U) a).symm
  let E : Z.functionField ≃+* Y.functionField :=
    e.hom.functionFieldRingEquivOfIsOpenImmersion
  have hE (a : K') : E (baseToFunctionField b a) = baseToFunctionField q a := by
    change e.hom.functionFieldMap he (baseToFunctionField b a) = _
    rw [Scheme.Hom.functionFieldMap_baseToFunctionField, heb]
  let A : Z.functionField ≃ₐ[K'] Y.functionField :=
    { E with commutes' := hE }
  have hcongr {r s : Y ⟶ X} (hrs : r = s) (hr : DenseRange r) (hs : DenseRange s) :
      r.functionFieldMap hr = s.functionFieldMap hs := by
    cases hrs
    rfl
  have hmap (a : X.functionField) :
      A (π.functionFieldMap hπ a) = p.functionFieldMap hp a := by
    have h := DFunLike.congr_fun (functionFieldMap_comp_of_dense π hπ e.hom he) a
    exact h.trans (DFunLike.congr_fun
      (hcongr heπ (hπ.comp he π.continuous) hp) a)
  have himage : A '' Set.range (π.functionFieldMap hπ) =
      Set.range (p.functionFieldMap hp) := by
    ext y
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨a, (hmap a).symm⟩
    · rintro ⟨a, rfl⟩
      exact ⟨π.functionFieldMap hπ a, ⟨a, rfl⟩, hmap a⟩
  have hm := congrArg (IntermediateField.map A.toAlgHom) hgen
  rw [IntermediateField.adjoin_map, AlgEquiv.coe_toAlgHom, himage] at hm
  rw [hm]
  apply top_unique
  intro y _
  obtain ⟨z, rfl⟩ := A.surjective y
  exact ⟨z, trivial, rfl⟩

end AlgebraicGeometry
