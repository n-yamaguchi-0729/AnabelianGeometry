/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.SchemeTheory.FunctionFields.OpenImmersion

/-! # Sections under the function-field map of an open immersion -/
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.Hom

local instance topNonempty {X : Scheme} [Nonempty X] : Nonempty (⊤ : X.Opens) :=
  ⟨⟨Classical.choice inferInstance, trivial⟩⟩
local instance imageTopNonempty {X Y : Scheme} [Nonempty X]
    (f : X ⟶ Y) [IsOpenImmersion f] : Nonempty (f ''ᵁ ⊤ : Y.Opens) :=
  ⟨⟨f (Classical.choice inferInstance), Classical.choice inferInstance, trivial, rfl⟩⟩

/-- The literal open-immersion function-field map reads the section carried
back by the literal section isomorphism. -/
theorem functionFieldMap_germToFunctionField_appIso_inv
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsOpenImmersion f] (hf : DenseRange f) (s : Γ(X, ⊤)) :
    f.functionFieldMap hf
      (Y.germToFunctionField (f ''ᵁ ⊤) ((f.appIso ⊤).inv s)) =
        X.germToFunctionField ⊤ s := by
  let U : Y.Opens := f ''ᵁ ⊤
  let h : genericPoint Y = f (genericPoint X) :=
    (f.map_genericPoint_of_denseRange hf).symm
  have hEq : eqToHom (show
      Y.presheaf.stalk (genericPoint Y) =
        Y.presheaf.stalk (f (genericPoint X)) by
      rw [f.map_genericPoint_of_denseRange hf]) =
      (Y.presheaf.stalkCongr (.of_eq h)).hom := by
    have aux : ∀ {y y' : Y} (e : y = y'),
        eqToHom (congrArg (fun z => Y.presheaf.stalk z) e) =
          (Y.presheaf.stalkCongr (.of_eq e)).hom := by
      intro y y' e
      subst y'
      exact (Y.presheaf.stalkSpecializes_refl y).symm
    exact aux h
  have hx : genericPoint X ∈ f ⁻¹ᵁ U :=
    ⟨genericPoint X, trivial, rfl⟩
  have hnat : Y.germToFunctionField U ≫
      CommRingCat.ofHom (f.functionFieldMap hf) =
      f.app U ≫ X.presheaf.germ (f ⁻¹ᵁ U) (genericPoint X) hx := by
    unfold functionFieldMap
    change Y.germToFunctionField U ≫ (_ ≫ f.stalkMap (genericPoint X)) = _
    rw [hEq]
    simp only [TopCat.Presheaf.stalkCongr_hom]
    rw [← Category.assoc]
    erw [TopCat.Presheaf.germ_stalkSpecializes]
    exact f.germ_stalkMap U (genericPoint X) hx
  have hn := congrArg (fun g : Γ(Y, U) ⟶ X.functionField =>
      g ((f.appIso ⊤).inv s)) hnat
  simp only [CategoryTheory.comp_apply] at hn
  change f.functionFieldMap hf
      (Y.germToFunctionField U ((f.appIso ⊤).inv s)) = _ at hn
  rw [hn]
  have hs := CategoryTheory.ConcreteCategory.congr_hom (f.appIso_inv_app ⊤) s
  rw [CategoryTheory.comp_apply] at hs
  rw [hs]
  exact X.presheaf.germ_res_apply
    (eqToHom (f.preimage_image_eq ⊤)) (genericPoint X) hx s

end AlgebraicGeometry.Scheme.Hom
