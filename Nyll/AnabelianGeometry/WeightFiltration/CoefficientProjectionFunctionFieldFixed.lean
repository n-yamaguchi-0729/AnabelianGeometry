/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.GenericPointNaturality
import Nyll.AlgebraicCurves.Models.ConstantExtension.SemilinearFunctionField
import Nyll.AlgebraicCurves.Models.ConstantExtension.BaseChangeSemilinearAction

/-! # CoefficientProjectionFunctionFieldFixed -/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open CategoryTheory.Limits AlgebraicGeometry.SmoothProperCurve NeronModelInfra

namespace AnabelianGeometry.WeightFiltration

/-- The actual coefficient square fixes the original function-field image. -/
theorem functionFieldMap_fixed_of_projection_square
    {C Y : Scheme} [IsIntegral C] [IsIntegral Y]
    (π : Y ⟶ C) (hπ : DenseRange π) (θ : Y ≅ Y)
    (hsquare : θ.hom ≫ π = π) :
    θ.hom.functionFieldRingEquivOfIsOpenImmersion.toRingHom.comp
      (π.functionFieldMap hπ) = π.functionFieldMap hπ := by
  let qC := C.fromSpecStalk (genericPoint C)
  let qY := Y.fromSpecStalk (genericPoint Y)
  let φ := θ.hom.functionFieldRingEquivOfIsOpenImmersion.toRingHom
  let ψ := π.functionFieldMap hπ
  have hθdense : DenseRange θ.hom :=
    θ.hom.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace θ.hom
  have hθ : Spec.map (CommRingCat.ofHom φ) ≫ qY = qY ≫ θ.hom :=
    functionFieldMap_genericPoint θ.hom hθdense
  have hp : Spec.map (CommRingCat.ofHom ψ) ≫ qC = qY ≫ π :=
    functionFieldMap_genericPoint π hπ
  have hspec : Spec.map (CommRingCat.ofHom (φ.comp ψ)) =
      Spec.map (CommRingCat.ofHom ψ) := by
    apply (cancel_mono qC).1
    change (Spec.map (CommRingCat.ofHom ψ ≫ CommRingCat.ofHom φ)) ≫ qC = _
    rw [Spec.map_comp, Category.assoc, hp, ← Category.assoc, hθ,
      Category.assoc, hsquare, ← hp]
  exact congrArg (fun f : CommRingCat.of C.functionField ⟶
      CommRingCat.of Y.functionField => f.hom)
    (Spec.map_injective hspec)

/-- No moved-place or inertia preservation is an input: fixedness follows
from the same scheme projection square and the actual function-field action. -/
theorem semilinear_fixed_arithmeticFunctionField
    {K F : Type} [Field K] [Field F] [Algebra K F]
    (M : CurveModel K F)
    {C : Scheme} [IsIntegral C]
    (π : M.C ⟶ C) (hπ : DenseRange π)
    (θ : M.C ≅ M.C) (g : SemilinearAut K F)
    (hsquare : θ.hom ≫ π = π)
    (hfun : ∀ z : F,
      θ.hom.functionFieldRingEquivOfIsOpenImmersion (M.ffEquiv z) =
        M.ffEquiv (SemilinearAut.toRingAut g z))
    (z : C.functionField) :
    SemilinearAut.toRingAut g (M.ffEquiv.symm (π.functionFieldMap hπ z)) =
      M.ffEquiv.symm (π.functionFieldMap hπ z) := by
  apply M.ffEquiv.injective
  rw [← hfun, M.ffEquiv.apply_symm_apply]
  exact congrArg (fun f : C.functionField →+* M.C.functionField => f z)
    (functionFieldMap_fixed_of_projection_square π hπ θ hsquare)

end AnabelianGeometry.WeightFiltration
