/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Geometry.Schemes.Morphisms.IsoCompEqOpenImmersion
import Nyll.AnabelianGeometry.WeightFiltration.CompactificationAbelianization

/-!
# Comparing the actual kernels of two compactifications of the same open curve

Both open immersions and their common structural morphism are retained. The
isomorphism of proper curves is constructed by the existing extension theorem;
neither a kernel comparison nor an inertia-preservation equality is an input.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace AnabelianGeometry.WeightFiltration

/-- Two smooth proper compactifications of the same actual open curve induce
the same kernel on its abelianized fundamental group at the same point. -/
theorem compactificationAbelianizationMap_ker_eq_of_common_open
    {K : Type} [Field K]
    {U C C' : Scheme} [IsIntegral U] [IsIntegral C] [IsIntegral C']
    (c : C ⟶ Spec (.of K)) (c' : C' ⟶ Spec (.of K))
    [IsProper c] [SmoothOfRelativeDimension 1 c]
    [IsProper c'] [Smooth c']
    (j : U ⟶ C) (j' : U ⟶ C')
    [IsOpenImmersion j] [IsOpenImmersion j']
    (hbase : j ≫ c = j' ≫ c')
    {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶ U) :
    (compactificationAbelianizationMap j xi).toMonoidHom.ker =
      (compactificationAbelianizationMap j' xi).toMonoidHom.ker := by
  classical
  let V : C.Opens := j.opensRange
  let eU : U ≅ (V : Scheme) := j.isoOpensRange
  let t : (V : Scheme) ⟶ C' := eU.inv ≫ j'
  let : IsOpenImmersion t := by
    dsimp only [t]
    infer_instance
  have hV : (V : Set C).Nonempty := by
    obtain ⟨z⟩ := (inferInstance : Nonempty U)
    exact ⟨j z, Set.mem_range_self z⟩
  have ht : t ≫ c' = V.ι ≫ c := by
    change (j.isoOpensRange.inv ≫ j') ≫ c' = _
    rw [Category.assoc, ← hbase, ← Category.assoc,
      Scheme.Hom.isoOpensRange_inv_comp]
  obtain ⟨e, _, he⟩ :=
    Scheme.exists_iso_comp_eq_of_isOpenImmersion_of_isProper c c' V hV t ht
  have hje : j ≫ e.hom = j' := by
    calc
      j ≫ e.hom = eU.hom ≫ V.ι ≫ e.hom := by
        rw [← Category.assoc]
        exact congrArg (fun q => q ≫ e.hom) j.isoOpensRange_hom_ι.symm
      _ = eU.hom ≫ t := congrArg (fun q => eU.hom ≫ q) he
      _ = j' := by
        dsimp only [t]
        rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have hker := compactificationAbelianizationMap_ker_postcomp_iso j xi e
  rw [hje] at hker
  exact hker.symm

end AnabelianGeometry.WeightFiltration
