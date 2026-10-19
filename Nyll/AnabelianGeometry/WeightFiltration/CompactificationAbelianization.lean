/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GeometricFiber.OpenImmersionSurjective
import Nyll.EtaleFundamentalGroups.GeometricFiber.CanonicalPointedMaps
import Nyll.ProCGroups.Abelian.TopologicalAbelianizationKernel
import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# The actual compactification map on abelianized fundamental groups

Restriction of finite étale covers defines the map. For a normal locally
Noetherian integral compactification, this map is surjective; its kernel is
the image of the kernel before abelianization. Identifying this kernel with
the boundary Tate module is a further geometric calculation.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open ProCGroups.Abelian

namespace AnabelianGeometry.WeightFiltration

variable {X U : Scheme} [IsIntegral X] [IsIntegral U]
  (j : U ⟶ X) [IsOpenImmersion j]
  {Ω : Type} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ U)

/-- The map induced by the actual open immersion and actual fiber functor. -/
def compactificationAbelianizationMap :
    TopologicalAbelianization (Aut (FiniteEtale.fiber ξ)) →ₜ*
      TopologicalAbelianization (Aut (FiniteEtale.fiber (ξ ≫ j))) :=
  TopologicalAbelianization.map (FiniteEtale.fundamentalGroupHom j ξ)

omit [IsIntegral X] [IsIntegral U] [IsOpenImmersion j] [IsSepClosed Ω] in
/-- The map on abelianizations retains the original fundamental-group map. -/
theorem compactificationAbelianizationMap_mk (g : Aut (FiniteEtale.fiber ξ)) :
    compactificationAbelianizationMap j ξ
      (TopologicalAbelianization.mk _ g) =
        TopologicalAbelianization.mk _ (FiniteEtale.fundamentalGroupHom j ξ g) := rfl

omit [IsIntegral U] [IsOpenImmersion j] in
/-- An actual isomorphism of compactifications leaves the original kernel unchanged. -/
theorem compactificationAbelianizationMap_ker_postcomp_iso
    {Z : Scheme} [IsIntegral Z] (e : X ≅ Z) :
    (compactificationAbelianizationMap (j ≫ e.hom) ξ).toMonoidHom.ker =
      (compactificationAbelianizationMap j ξ).toMonoidHom.ker := by
  let epull : FiniteEtale Z ≌ FiniteEtale X :=
    MorphismProperty.Over.pullbackIso (@IsFiniteEtale : MorphismProperty Scheme) ⊤ e.symm
  let : (FiniteEtale.pullback e.hom).IsEquivalence := epull.isEquivalence_functor
  let eπ := FiniteEtale.fundamentalGroupEquivOfPullbackEquivalence e.hom (ξ ≫ j)
  have hinj (z : Spec (.of Ω) ⟶ Z) (h : (ξ ≫ j) ≫ e.hom = z) :
      Function.Injective (TopologicalAbelianization.map
        (FiniteEtale.pointedFundamentalGroupHom e.hom (ξ ≫ j) z h)) := by
    subst z
    change Function.Injective (TopologicalAbelianization.congr eπ)
    exact (TopologicalAbelianization.congr eπ).injective
  let post := TopologicalAbelianization.map
    (FiniteEtale.pointedFundamentalGroupHom e.hom (ξ ≫ j) (ξ ≫ (j ≫ e.hom))
      (Category.assoc ξ j e.hom))
  have hp : Function.Injective post := hinj _ _
  have hm := congrArg TopologicalAbelianization.map
    (FiniteEtale.pointedFundamentalGroupHom_comp j e.hom ξ (ξ ≫ j)
      (ξ ≫ (j ≫ e.hom)) rfl (Category.assoc ξ j e.hom))
  rw [TopologicalAbelianization.map_comp] at hm
  have hcomp : post.comp (compactificationAbelianizationMap j ξ) =
      compactificationAbelianizationMap (j ≫ e.hom) ξ := hm
  rw [← hcomp]
  exact MonoidHom.ker_comp_of_injective
    (compactificationAbelianizationMap j ξ).toMonoidHom post.toMonoidHom hp

variable [IsNormalIntegral X] [IsLocallyNoetherian X]

/-- Every abelianized proper-curve class lifts to the open curve. -/
theorem compactificationAbelianizationMap_surjective :
    Function.Surjective (compactificationAbelianizationMap j ξ) :=
  TopologicalAbelianization.surjective_map_of_surjective
    (FiniteEtale.fundamentalGroupHom j ξ)
    (FiniteEtale.fundamentalGroupHom_surjective_of_isOpenImmersion j ξ)

/-- The boundary kernel after abelianization is exactly the image of the
actual compactification kernel, rather than an additional chosen subgroup. -/
theorem compactificationAbelianizationMap_ker :
    (compactificationAbelianizationMap j ξ).toMonoidHom.ker =
      (FiniteEtale.fundamentalGroupHom j ξ).toMonoidHom.ker.map
        (TopologicalAbelianization.mk (Aut (FiniteEtale.fiber ξ))) :=
  TopologicalAbelianization.ker_map_of_surjective
    (FiniteEtale.fundamentalGroupHom j ξ)
    (FiniteEtale.fundamentalGroupHom_surjective_of_isOpenImmersion j ξ)

end AnabelianGeometry.WeightFiltration
