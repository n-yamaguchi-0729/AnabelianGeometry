/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AnabelianGeometry.WeightFiltration.OpenBoundarySemilinear
public import Nyll.AlgebraicCurves.Models.ConstantExtension.BaseChangeSemilinearAction
public import Nyll.EtaleFundamentalGroups.GeometricFiber.CoefficientBaseChangeIso
public import Mathlib.GroupTheory.OrderOfElement

/-!
# A common period of the actual geometric boundary

The coefficient automorphism acts on the actual base-changed open curve and
its compactification. The resulting semilinear function-field action preserves
the omitted places. Their finiteness supplies one positive period for all
boundary places, independent of every torsion coefficient level.
-/

@[expose] public section

universe u v

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AlgebraicCurve
open AlgebraicGeometry.SmoothProperCurve AlgebraicGeometry.FiniteEtale NeronModelInfra

namespace AnabelianGeometry.FiniteField

/-- Actual coefficient base change supplies the boundary permutation, its
function-field formula, and a common positive period of all omitted places. -/
theorem exists_boundary_coefficient_period
    {k K : Type u} {F : Type v} [Field k] [Field K] [IsAlgClosed K] [Algebra k K]
    [Field F] [Algebra K F]
    {C U : Scheme.{u}} (c : C ⟶ Spec (.of k)) (i : U ⟶ C)
    [IsIntegral (pullback (specMap k K) (i ≫ c))]
    (M : CurveModel K F) (eC : M.C ≅ pullback c (specMap k K))
    (heC : eC.hom ≫ pullback.snd c (specMap k K) = M.toBase)
    (j : pullback (specMap k K) (i ≫ c) ⟶ M.C) [IsOpenImmersion j]
    (hj : DenseRange j)
    (hproj : j ≫ eC.hom ≫ pullback.fst c (specMap k K) =
      pullback.snd (specMap k K) (i ≫ c) ≫ i)
    (hbase : j ≫ M.toBase = pullback.fst (specMap k K) (i ≫ c))
    (σ : K ≃ₐ[k] K) :
    let θU := coefficientBaseChangeIso k K (i ≫ c) σ
    ∃ (θ : M.C ≅ M.C) (g : SemilinearAut K F),
      θU.hom ≫ j = j ≫ θ.hom ∧
      θ.hom ≫ M.toBase = M.toBase ≫ Spec.map (CommRingCat.ofHom σ.toRingHom) ∧
      SemilinearAut.baseAut g = σ.toRingEquiv ∧
      (∀ z : F, θU.hom.functionFieldRingEquivOfIsOpenImmersion
          (j.functionFieldMap hj (M.ffEquiv z)) =
        j.functionFieldMap hj (M.ffEquiv (SemilinearAut.toRingAut g z))) ∧
      (∀ p : Place K F, p ∈ M.openBoundaryPlaces j ↔ g • p ∈ M.openBoundaryPlaces j) ∧
      ∃ r : ℕ+, ∀ p : M.openBoundaryPlaces j, (g ^ (r : ℕ)) • p.val = p.val := by
  intro θU
  obtain ⟨θ, g, hθproj, hθbase, hgbase, hgfun, hgpoint⟩ :=
    M.exists_baseChange_semilinear_action c eC heC σ
  have hsquare : θU.hom ≫ j = j ≫ θ.hom := by
    apply (cancel_mono eC.hom).1
    apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [hproj, ← Category.assoc θU.hom (pullback.snd (specMap k K) (i ≫ c)) i,
        coefficientBaseChangeIso_hom_snd, hθproj, hproj]
    · simp only [Category.assoc, heC]
      rw [hbase, coefficientBaseChangeIso_hom_fst, hθbase,
        ← Category.assoc j M.toBase (Spec.map (CommRingCat.ofHom σ.toRingHom)), hbase]
  obtain ⟨hS, hfield⟩ := M.openBoundary_semilinear_compatibility j hj θU θ
    σ.toRingEquiv g hθbase hsquare hgpoint (M.functionFieldRingEquiv_semilinear θ g hgfun)
  refine ⟨θ, g, hsquare, hθbase, hgbase, hfield, hS, ?_⟩
  let : Fintype (M.openBoundaryPlaces j) := (M.openBoundaryPlaces_finite j).fintype
  let a := MulAction.toPermHom (SemilinearAut K F) (Place K F)
  have hSa (p : Place K F) :
      (a g) p ∈ M.openBoundaryPlaces j ↔ p ∈ M.openBoundaryPlaces j := (hS p).symm
  let e : Equiv.Perm (M.openBoundaryPlaces j) :=
    (a g).subtypePerm hSa
  have hpow (n : ℕ) (p : M.openBoundaryPlaces j) :
      ((e ^ n) p).val = (g ^ n) • p.val := by
    have hp := congrArg (fun f : Equiv.Perm (M.openBoundaryPlaces j) => (f p).val)
      (Equiv.Perm.subtypePerm_pow (a g) n hSa)
    change ((e ^ n) p).val = ((a g) ^ n) p.val at hp
    exact hp.trans (congrArg (fun f : Equiv.Perm (Place K F) => f p.val)
      (map_pow a g n).symm)
  let r : ℕ+ := ⟨orderOf e, orderOf_pos e⟩
  refine ⟨r, ?_⟩
  intro p
  exact (hpow (orderOf e) p).symm.trans
    (congrArg (fun f : Equiv.Perm (M.openBoundaryPlaces j) => (f p).val)
      (pow_orderOf_eq_one e))

end AnabelianGeometry.FiniteField
