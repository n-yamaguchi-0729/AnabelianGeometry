/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Models.Construction.Basic
import Nyll.AlgebraicCurves.Divisors.Maps.Semilinear
import Nyll.SchemeTheory.FunctionFields.StalkFunctoriality
import Nyll.SchemeTheory.FunctionFields.OpenImmersion

/-!
# The actual function-field map of a semilinear curve automorphism

Compatibility on local sections identifies the existing semilinear field
map with the actual function-field pullback of the scheme automorphism.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry

namespace AlgebraicCurve.CurveModel

/-- Local-germ compatibility determines the actual function-field pullback. -/
theorem functionFieldRingEquiv_semilinear
    {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F]
    (M : CurveModel K F) (θ : M.C ≅ M.C) (g : SemilinearAut K F)
    (hg : ∀ (U : M.C.Opens) [Nonempty (Scheme.Opens.toScheme U)]
        [Nonempty (Scheme.Opens.toScheme (θ.hom ⁻¹ᵁ U))] (t : Γ(M.C, U)),
      g • M.ffEquiv.symm (M.C.germToFunctionField U t) =
        M.ffEquiv.symm (M.C.germToFunctionField (θ.hom ⁻¹ᵁ U) ((θ.hom.app U).hom t)))
    (r : F) :
    θ.hom.functionFieldRingEquivOfIsOpenImmersion (M.ffEquiv r) =
      M.ffEquiv (SemilinearAut.toRingAut g r) := by
  have hd : DenseRange θ.hom :=
    θ.hom.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace θ.hom
  obtain ⟨U, hU, t, ht⟩ := M.C.presheaf.exists_germ_eq (M.ffEquiv r)
  have : Nonempty U := ⟨⟨genericPoint M.C, hU⟩⟩
  have : Nonempty (θ.hom ⁻¹ᵁ U) := ⟨⟨genericPoint M.C, by
    change θ.hom (genericPoint M.C) ∈ U
    rw [θ.hom.map_genericPoint_of_denseRange hd]
    exact hU⟩⟩
  have ht' : M.C.germToFunctionField U t = M.ffEquiv r := ht
  have hmap := congrArg (fun f : Γ(M.C, U) →+* M.C.functionField => f t)
    (θ.hom.functionFieldMap_comp_germToFunctionField hd U)
  change θ.hom.functionFieldMap hd (M.C.germToFunctionField U t) =
    M.C.germToFunctionField (θ.hom ⁻¹ᵁ U) ((θ.hom.app U).hom t) at hmap
  rw [ht'] at hmap
  have hsemi := congrArg M.ffEquiv (hg U t)
  rw [ht', M.ffEquiv.symm_apply_apply, M.ffEquiv.apply_symm_apply] at hsemi
  exact hmap.trans hsemi.symm

end AlgebraicCurve.CurveModel
