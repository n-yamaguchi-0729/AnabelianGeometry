/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.FieldChartBoundaryCentralizer
import Nyll.EtaleFundamentalGroups.Inertia.PrimeToRootsProcyclic

/-! # Geometric self-normalization of actual boundary inertia -/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.FiniteEtale SchemeTheory EtaleFundamentalGroups.Inertia
open ProCGroups.Abelian

namespace AnabelianGeometry.WeightFiltration

private theorem normalizer_eq_of_commutative_quotient
    {G A : Type*} [Group G] [CommGroup A]
    (I : Subgroup G) (q : G →* A) (hq : Set.InjOn q I.carrier)
    (x : G) (hx : x ∈ I)
    (hcentralizer : Subgroup.centralizer ({x} : Set G) = I) :
    Subgroup.normalizer I.carrier = I := by
  apply le_antisymm
  · intro g hg
    have hconj : g * x * g⁻¹ ∈ I :=
      (Subgroup.mem_set_normalizer_iff.mp hg x).mp hx
    have hab : q (g * x * g⁻¹) = q x := by
      rw [map_mul, map_mul, map_inv, mul_comm (q g) (q x),
        mul_assoc, mul_inv_cancel, mul_one]
    have heq : g * x * g⁻¹ = x := hq hconj hx hab
    have hcomm : g * x = x * g := by
      have h := congrArg (fun y : G => y * g) heq
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using h
    have hgcent : g ∈ Subgroup.centralizer ({x} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hcomm
    exact hcentralizer ▸ hgcent
  · intro g hg
    apply Subgroup.mem_set_normalizer_iff.mpr
    intro y
    constructor
    · intro hy
      exact I.mul_mem (I.mul_mem hg hy) (I.inv_mem hg)
    · intro hy
      change y ∈ I
      have h := I.mul_mem (I.mul_mem (I.inv_mem hg) hy) hg
      simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using h

/-- A boundary subgroup is geometrically self-normalizing. Abelianization
separates inertia elements, so every geometric normalizer centralizes inertia;
the actual geometric centralizer theorem then applies. -/
theorem fieldChart_boundaryInertia_self_normalizing
    {κ F : Type} [Field κ] [CharZero κ] [IsAlgClosed κ]
    [Field F] [Algebra κ F] [IsCurveOver κ F]
    {U : Scheme} [IsIntegral U] [IsNormalIntegral U]
    [IsLocallyNoetherian U] [ConnectedSpace U] [CompactSpace U]
    [Algebra κ U.functionField] [Algebra F U.functionField]
    [IsScalarTower κ F U.functionField]
    {Ω : Type} [Field Ω] [Algebra U.functionField Ω] [Algebra F Ω]
    [IsScalarTower F U.functionField Ω]
    [IsSepClosure U.functionField Ω] [IsSepClosure F Ω] [IsSepClosed Ω]
    [Algebra κ Ω] [IsScalarTower κ U.functionField Ω]
    (M : CurveModel κ F)
    (j : U ⟶ M.C) [IsOpenImmersion j] [QuasiCompact j] [QuasiSeparated j]
    (hj : DenseRange j)
    (hfield : algebraMap F U.functionField =
      (j.functionFieldMap hj).comp M.ffEquiv.toRingHom)
    [∀ p : M.openBoundaryPlaces j, Algebra p.val.toValuationSubring Ω]
    [∀ p : M.openBoundaryPlaces j, IsScalarTower p.val.toValuationSubring F Ω]
    [∀ p : M.openBoundaryPlaces j, IsScalarTower κ p.val.toValuationSubring Ω]
    [Finite (M.openBoundaryPlaces j)] [Nontrivial (M.openBoundaryPlaces j)]
    (hthree : 3 ≤ Nat.card (M.openBoundaryPlaces j))
    (Qfamily : ∀ p : M.openBoundaryPlaces j,
      Ideal (normalizationCommAlgCat p.val.toValuationSubring Ω))
    [∀ p, (Qfamily p).IsMaximal]
    (v : M.openBoundaryPlaces j) :
    Subgroup.normalizer (genericPlaceInertia U v.val (Qfamily v) : Set _) =
      genericPlaceInertia U v.val (Qfamily v) := by
  let G := π₁ᵉᵗ(U.genericExtensionMorphism Ω)
  let I : Subgroup G := genericPlaceInertia U v.val (Qfamily v)
  let f : (primeToRootsSystem κ κ).inverseLimit →ₜ* G :=
    boundaryPlaceInertiaLift M j hj hfield Qfamily v
  have hf : f.toMonoidHom.range = I :=
    boundaryPlaceInertiaLift_range M j hj hfield Qfamily v
  have hinj : Function.Injective f :=
    boundaryPlaceInertiaLift_injective M j hj hfield Qfamily v
  obtain ⟨t, ht⟩ := primeToRoots_exists_ne_one κ κ
  have hxrange : f t ∈ f.toMonoidHom.range := ⟨t, rfl⟩
  have hx : f t ∈ I := hf ▸ hxrange
  have hx1 : f t ≠ 1 := by
    intro h
    exact ht (hinj (h.trans (map_one f).symm))
  have hab : Set.InjOn (TopologicalAbelianization.mk G) I.carrier :=
    boundaryInertia_abelianization_injOn M j hj hfield Qfamily v
  have hc : Subgroup.centralizer ({f t} : Set G) = I :=
    fieldChart_boundaryInertia_centralizer_eq M j hj hfield hthree v
      (Qfamily v) hx hx1
  exact normalizer_eq_of_commutative_quotient I
    (TopologicalAbelianization.mk G) hab (f t) hx hc

end AnabelianGeometry.WeightFiltration
