/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GaloisCovers.OpenPlaceTransport
import Nyll.EtaleFundamentalGroups.GaloisCovers.FunctionField

/-! # The same constant-field algebra on an actual finite cover -/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve TopologicalSpace
open CategoryTheory.PreGaloisCategory

namespace EtaleFundamentalGroups

/-- The literal cover field extension agrees on constants with the original
structural morphism, once the base model's generic identification is fixed. -/
theorem finiteEtaleFunctionField_constants_eq_structural
    {κ : Type} [Field κ]
    {X : Scheme} [IsIntegral X] [IsNormalIntegral X]
    [Algebra κ X.functionField]
    (M : CurveModel κ X.functionField)
    (j : X ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
    (hbase : algebraMap X.functionField X.functionField =
      (j.functionFieldMap hj).comp M.ffEquiv.toRingHom)
    (W : FiniteEtale X) [IsConnected W] :
    letI : IsIntegral W.left := isIntegral_left_of_isConnected_finiteEtale W
    letI : Algebra X.functionField W.left.functionField := finiteEtaleFunctionFieldAlgebra W
    ∀ a : κ, algebraMap X.functionField W.left.functionField
        (algebraMap κ X.functionField a) =
      baseToFunctionField ((show W.left ⟶ X from W.hom) ≫ j ≫ M.toBase) a := by
  let : IsIntegral W.left := isIntegral_left_of_isConnected_finiteEtale W
  let : Algebra X.functionField W.left.functionField := finiteEtaleFunctionFieldAlgebra W
  intro a
  have hbaseScalar : algebraMap κ X.functionField a =
      baseToFunctionField (j ≫ M.toBase) a := by
    calc
      algebraMap κ X.functionField a =
          j.functionFieldMap hj (M.ffEquiv (algebraMap κ X.functionField a)) :=
        DFunLike.congr_fun hbase (algebraMap κ X.functionField a)
      _ = baseToFunctionField (j ≫ M.toBase) a :=
        M.openFunctionFieldEquiv_algebraMap j a
  change (show W.left ⟶ X from W.hom).functionFieldMap
    (finiteEtale_hom_denseRange_of_isConnected W) (algebraMap κ X.functionField a) = _
  rw [hbaseScalar]
  exact Scheme.Hom.functionFieldMap_baseToFunctionField
    (j ≫ M.toBase) (show W.left ⟶ X from W.hom) (finiteEtale_hom_denseRange_of_isConnected W) a

/-- The pointed-cover composite algebra and the curve-model structural
algebra are equal, rather than merely abstractly isomorphic. -/
theorem finiteEtaleFunctionField_constantAlgebra_eq
    {κ : Type} [Field κ]
    {X : Scheme} [IsIntegral X] [IsNormalIntegral X]
    [Algebra κ X.functionField]
    (M : CurveModel κ X.functionField)
    (j : X ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
    (hbase : algebraMap X.functionField X.functionField =
      (j.functionFieldMap hj).comp M.ffEquiv.toRingHom)
    (W : FiniteEtale X) [IsConnected W] :
    letI : IsIntegral W.left := isIntegral_left_of_isConnected_finiteEtale W
    letI : Algebra X.functionField W.left.functionField := finiteEtaleFunctionFieldAlgebra W
    ((algebraMap X.functionField W.left.functionField).comp
      (algebraMap κ X.functionField)).toAlgebra =
        (baseToFunctionField ((show W.left ⟶ X from W.hom) ≫ j ≫ M.toBase)).toAlgebra := by
  let : IsIntegral W.left := isIntegral_left_of_isConnected_finiteEtale W
  let : Algebra X.functionField W.left.functionField := finiteEtaleFunctionFieldAlgebra W
  apply Algebra.algebra_ext
  exact finiteEtaleFunctionField_constants_eq_structural M j hj hbase W

end EtaleFundamentalGroups
